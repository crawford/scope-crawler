use anyhow::{Context, Result};
use stack_graphs::arena::Handle;
use stack_graphs::graph::NodeID;
use stack_graphs::graph::StackGraph;
use stack_graphs::partial::PartialPaths;
use stack_graphs::stitching::GraphEdgeCandidates;
use stack_graphs::stitching::StitcherConfig;
use std::collections::HashMap;
use std::collections::HashSet;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::time::Duration;
use tree_sitter_stack_graphs::Variables;

#[derive(clap::Parser)]
struct Options {
    file: PathBuf,
    line: std::num::NonZeroUsize, // one-indexed
    column: Option<usize>,        // zero-indexed

    #[arg(long = "timeout", short = 't', default_value = "5", value_parser = parse_duration)]
    timeout: Duration,

    #[arg(action = clap::ArgAction::Count, long = "verbose", short = 'v')]
    verbosity: u8,
}

fn parse_duration(arg: &str) -> Result<Duration, std::num::ParseIntError> {
    let seconds = arg.parse()?;
    Ok(Duration::from_secs(seconds))
}

fn init_logging(verbosity: u8) {
    fn filter(v: u8) -> log::LevelFilter {
        use log::LevelFilter::*;
        match v {
            0 => Warn,
            1 => Info,
            2 => Debug,
            _ => Trace,
        }
    }

    pretty_env_logger::formatted_builder()
        .filter_level(filter(verbosity))
        .filter_module("tree_sitter_graph", filter(verbosity.saturating_sub(2)))
        .try_init()
        .expect("initializing logging");
}

fn main() -> Result<()> {
    use clap::Parser;

    let options = Options::parse();
    init_logging(options.verbosity);

    let source = SourceCode::from_path(&options.file)
        .context(anyhow::anyhow!("reading {}", options.file.display()))?;

    let mut references =
        HashMap::<Handle<stack_graphs::graph::Node>, Vec<Handle<stack_graphs::graph::Node>>>::new();

    macro_rules! display_span {
        ($span:expr) => {{
            format!(
                "[{}, {}] - [{}, {}]",
                $span.start.line + 1,
                $span.start.column.utf8_offset,
                $span.end.line + 1,
                $span.end.column.utf8_offset
            )
        }};
    }

    for node in source
        .graph
        .iter_nodes()
        .filter(|n| source.graph[*n].is_reference())
    {
        let config = StitcherConfig::default();
        let mut partials = PartialPaths::new();
        let mut candidates = GraphEdgeCandidates::new(&source.graph, &mut partials, None);

        stack_graphs::stitching::ForwardPartialPathStitcher::find_all_complete_partial_paths(
            &mut candidates,
            [node],
            config,
            &stack_graphs::NoCancellation,
            |graph, _partials, partial| {
                let start = display_span!(graph.source_info(partial.start_node).unwrap().span);
                let end = display_span!(graph.source_info(partial.end_node).unwrap().span);
                let symbol = &graph[graph[partial.start_node]
                    .symbol()
                    .expect("reference without symbol")];

                log::debug!("reference: '{symbol}' {start} -> {end}",);

                references
                    .entry(partial.end_node)
                    .or_insert_with(|| Vec::new())
                    .push(partial.start_node);

                graph
                    .node_debug_info(partial.start_node)
                    .expect("debug info")
                    .iter()
                    .for_each(|entry| {
                        let key = &source.graph[entry.key];
                        let value = &source.graph[entry.value];
                        log::trace!("{key:?} = {value}",);
                    });
            },
        )?;
    }

    let symbol = source
        .symbol_at_point(tree_sitter::Point {
            row: options.line.get() - 1,
            column: options.column.unwrap_or(999),
        })
        .expect("symbol");

    println!("{:#?}", symbol);

    fn find_references_for_symbol<'a>(
        symbol: SymbolBody,
        source: &'a SourceCode,
        references: &HashMap<
            Handle<stack_graphs::graph::Node>,
            Vec<Handle<stack_graphs::graph::Node>>,
        >,
    ) -> HashSet<SymbolBody<'a>> {
        log::debug!("visiting: {symbol:#?}",);
        references
            .iter()
            .map(|(def, refs)| (source.graph.source_info(*def).unwrap(), refs))
            .fold(HashSet::new(), |symbols, (def, refs)| {
                match symbol.body.child_by_field_name("name") {
                    Some(node)
                        if def.span.start == node.start_position()
                            && def.span.end == node.end_position() =>
                    {
                        log::trace!("enclosing body {}", format!("{:?}", symbol.body));

                        refs.iter()
                            .map(|r| source.graph.source_info(*r).unwrap())
                            .fold(symbols, |mut symbols, r#ref| {
                                log::debug!(
                                    "considering definition: {} <- {}",
                                    display_span!(def.span),
                                    display_span!(r#ref.span),
                                );
                                let symbol =
                                    source.symbol_at_point(r#ref.span.start.as_point()).unwrap();

                                log::debug!("found: {symbol:#?}",);
                                symbols.insert(symbol);

                                symbols
                            })
                    }
                    _ => symbols,
                }
            })
    }

    let mut unvisited = vec![symbol];
    let mut visited: HashSet<SymbolBody> = HashSet::new();
    while let Some(symbol) = unvisited.pop() {
        let new: Vec<SymbolBody> = find_references_for_symbol(symbol, &source, &references)
            .into_iter()
            .filter(|symbol| !visited.contains(symbol))
            .inspect(|symbol| println!("{symbol:#?}"))
            .collect();
        visited.extend(new.clone());
        unvisited.extend(new);
    }

    Ok(())
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct SymbolBody<'a> {
    identifier: Identifier<'a>,
    body: tree_sitter::Node<'a>,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum IdentifierPart<'a> {
    Export(&'a str),
    Class(&'a str),
    Interface(&'a str),
    Function(&'a str),
    Method(&'a str),
    Anonymous(&'a str),
}

impl std::fmt::Display for IdentifierPart<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use IdentifierPart::*;

        match self {
            Export(name) | Class(name) | Function(name) | Method(name) | Anonymous(name)
            | Interface(name) => {
                write!(f, "{name}")
            }
        }
    }
}

#[derive(Clone, Eq, Hash, PartialEq)]
struct Identifier<'a> {
    node: tree_sitter::Node<'a>,
    file: &'a Path,
    parts: Vec<IdentifierPart<'a>>,
}

impl std::fmt::Display for Identifier<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut parts = self.parts.iter().rev();
        match parts.next() {
            Some(part) => write!(f, "{}:{part}", self.file.display())?,
            None => return Ok(()),
        }
        for part in parts {
            write!(f, "::{part}")?;
        }

        Ok(())
    }
}

impl std::fmt::Debug for Identifier<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let start = self.node.start_position();
        let end = self.node.end_position();
        write!(
            f,
            "{self} @ [{}, {}] - [{}, {}]",
            start.row + 1,
            start.column,
            end.row + 1,
            end.column,
        )
    }
}

struct SourceCode<'a> {
    path: &'a Path,
    source: String,
    tree: tree_sitter::Tree,
    graph: StackGraph,
}

impl<'a> SourceCode<'a> {
    fn from_path(path: &'a Path) -> Result<SourceCode<'a>> {
        let mut parser = tree_sitter::Parser::new();
        parser
            .set_language(tree_sitter_typescript::language_typescript())
            .context("loading typescript grammar")?;
        let source = std::fs::read_to_string(path).context("opening {path}")?;
        let tree = parser.parse(&source, None).context("parsing source code")?;

        let mut graph = StackGraph::new();
        let globals = Variables::new();
        let file = graph
            .add_file(&path.to_string_lossy())
            .expect("file not present in empty graph");
        let language = tree_sitter_stack_graphs_typescript::try_language_configuration(
            &tree_sitter_stack_graphs::NoCancellation,
        )
        .context("loading typescript TSG")?;
        language
            .sgl
            .build_stack_graph_into(
                &mut graph,
                file,
                &source,
                &globals,
                &tree_sitter_stack_graphs::NoCancellation,
            )
            .context("building stack graph")?;

        // XXX: manually amend the graph to include a relationship between Square and Shape
        // 222 - [syntax node new_expression(12, 6)] @gen_expr.applied_type
        // 238 - [syntax node type_identifier(12, 22)] @type.type
        // let specialization = graph.node_for_id(NodeID::new_in_file(file, 262)).unwrap();
        // let generalization = graph.node_for_id(NodeID::new_in_file(file, 278)).unwrap();
        // graph.add_edge(generalization, specialization, 0);

        let mut partials = PartialPaths::new();
        let mut db = stack_graphs::stitching::Database::new();

        // Populate the database to get the paths in the visualization
        let mut candidates = GraphEdgeCandidates::new(&graph, &mut partials, None);
        stack_graphs::stitching::ForwardPartialPathStitcher::find_all_complete_partial_paths(
            &mut candidates,
            graph
                .iter_nodes()
                .filter(|n| graph[*n].is_reference())
                .collect::<Vec<_>>(),
            StitcherConfig::default(),
            &stack_graphs::NoCancellation,
            |g, ps, p| {
                db.add_partial_path(g, ps, p.clone());
            },
        )?;

        let contents = graph.to_html_string(
            "test",
            &mut partials,
            &mut db,
            &stack_graphs::serde::NoFilter,
        )?;
        let mut file = std::fs::File::create("graph.html").context("opening graph.html")?;
        file.write_all(contents.as_bytes())?;

        Ok(SourceCode {
            path,
            source,
            tree,
            graph,
        })
    }

    // Finds the smallest enclosing scope of at interesting type.
    fn symbol_at_point(&'a self, point: tree_sitter::Point) -> Result<SymbolBody<'a>> {
        let ident = self.find_ident(point)?;
        let mut node = ident.node;
        let body = loop {
            match node.kind() {
                "program"
                | "class_declaration"
                | "interface_declaration"
                | "arrow_function"
                | "function_declaration"
                | "method_definition" => break Some(node),
                "call_expression" if self.export_name(node).is_some() => {
                    return Ok(SymbolBody {
                        identifier: self.find_ident(node.start_position()).unwrap_or(ident),
                        body: node,
                    });
                }
                _ => {}
            }
            match node.parent() {
                Some(parent) => node = parent,
                None => break Some(node),
            }
        }
        .context("finding symbol body")?;
        let identifier = body
            .child_by_field_name("name")
            .and_then(|node| Some(self.find_ident(node.start_position())))
            .unwrap_or(Ok(ident))
            .context("finding symbol identifier")?;
        Ok(SymbolBody { identifier, body })
    }

    fn export_name(&'a self, node: tree_sitter::Node) -> Option<&'a str> {
        if let Some(expr) = node.child_by_field_name("function") {
            // XXX: this is fragile
            if expr.utf8_text(self.source.as_bytes()) == Ok("Object.defineProperty") {
                let args = node
                    .child_by_field_name("arguments")
                    .expect("call expression without 'arguments'");
                let mut cursor = self.tree.walk();
                let mut subject = None;
                let mut name = None;
                let mut object = None;
                args.children(&mut cursor).for_each(|n| match n.kind() {
                    "identifier" => subject = Some(n),
                    "string" => name = Some(n),
                    "object" => object = Some(node),
                    "(" | ")" | "," => {}
                    kind => log::warn!("{kind}"),
                });

                if let (Some(subject), Some(name)) = (subject, name) {
                    if subject.utf8_text(self.source.as_bytes()) == Ok("exports") {
                        return Some(name
                            .utf8_text(self.source.as_bytes())
                            .unwrap()
                            .trim_matches('\''));
                    }
                }
            }
        }
        None
    }

    fn find_ident(&'a self, point: tree_sitter::Point) -> Result<Identifier<'a>> {
        let node = self
            .tree
            .root_node()
            .descendant_for_point_range(point, point)
            .context("finding descendant at point")?;

        // self.log_tree(node);

        macro_rules! field {
            ($node:ident, $name:literal) => {{
                $node
                    .child_by_field_name($name)
                    .ok_or(anyhow::anyhow!("field '{}' not found", $name))
                    .and_then(|name| name.utf8_text(self.source.as_bytes()).map_err(Into::into))
            }};
        }

        let mut parts = Vec::new();
        let mut parent = node;

        macro_rules! capture {
            ($ident:path) => {{
                field!(parent, "name")
                    .and_then(|name| Ok(parts.push($ident(name))))
                    .context("couldn't get node name")
            }};
        }

        loop {
            use IdentifierPart::*;

            match parent.kind() {
                "statement_block"
                | "class_body"
                | "class"
                | "program"
                | "}"
                | "parenthesized_expression"
                | "identifier"
                | "property_identifier"
                | "member_expression"
                | "variable_declarator"
                | "lexical_declaration"
                | "if_statement"
                | "export_statement"
                | "return_statement"
                | "expression_statement" => {}
                "arrow_function" => parts.push(Anonymous("<fn>")),
                "function_declaration" => capture!(Function)
                    .context(format!("couldn't get name of function at {parent:?}"))?,
                "method_definition" => capture!(Method)
                    .context(format!("couldn't get name of method at {parent:?}"))?,
                "class_declaration" => {
                    capture!(Class).context(format!("couldn't get name of class at {parent:?}"))?
                }
                "interface_declaration" => capture!(Interface)
                    .context(format!("couldn't get name of interface at {parent:?}"))?,
                "call_expression" => {
                    if let Some(name) = self.export_name(parent) {
                        parts.push(Export(name));
                    }
                }
                k => log::trace!("unrecognized node ({parent:?}) kind '{k}'"),
            }
            match parent.parent() {
                Some(p) => parent = p,
                None => break,
            }
        }

        let file = self.path;
        Ok(Identifier { node, file, parts })
    }
}
