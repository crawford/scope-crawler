use anyhow::{Context, Result};
use stack_graphs::arena::Handle;
// use stack_graphs::graph::PushSymbolNode;
// use stack_graphs::graph::ScopeNode;
use stack_graphs::graph::StackGraph;
use stack_graphs::partial::PartialPaths;
// use stack_graphs::stitching::ForwardPartialPathStitcher;
use stack_graphs::stitching::GraphEdgeCandidates;
// use stack_graphs::stitching::GraphEdgeCandidates;
use stack_graphs::stitching::StitcherConfig;
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::time::Duration;
// use tree_sitter::{Node, Point};
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

fn main() -> Result<()> {
    use clap::Parser;

    let options = Options::parse();

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
        .filter_level(filter(options.verbosity))
        .filter_module(
            "tree_sitter_graph",
            filter(options.verbosity.saturating_sub(2)),
        )
        .try_init()
        .expect("initializing logging");

    // macro_rules! row {
    //     ($row:expr) => {
    //         tree_sitter::Point {
    //             row: $row,
    //             column: 999,
    //         }
    //     };
    // }

    // let cancel = stack_graphs::CancelAfterDuration::new(options.timeout);
    let source = SourceCode::from_path(&options.file)
        .context(anyhow::anyhow!("reading {}", options.file.display()))?;

    let mut references =
        HashMap::<Handle<stack_graphs::graph::Node>, Vec<Handle<stack_graphs::graph::Node>>>::new();

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
                let start_span = &graph.source_info(partial.start_node).unwrap().span;
                let end_span = &graph.source_info(partial.end_node).unwrap().span;
                log::debug!(
                    "reference: '{}' [{}:{}] - [{}:{}] -> [{}:{}] - [{}:{}]",
                    &graph[graph[partial.start_node]
                        .symbol()
                        .expect("reference missing symbol")],
                    start_span.start.line + 1,
                    start_span.start.column.utf8_offset,
                    start_span.end.line + 1,
                    start_span.end.column.utf8_offset,
                    end_span.start.line + 1,
                    end_span.start.column.utf8_offset,
                    end_span.end.line + 1,
                    end_span.end.column.utf8_offset,
                );

                references
                    .entry(partial.end_node)
                    .or_insert_with(|| Vec::new())
                    .push(partial.start_node);

                let info = graph
                    .node_debug_info(partial.start_node)
                    .expect("debug info");
                info.iter().for_each(|entry| {
                    log::trace!(
                        "{:?} = {}",
                        &source.graph[entry.key],
                        &source.graph[entry.value]
                    );
                });
            },
        )?;
    }

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

    let symbol = source
        .symbol_at_point(tree_sitter::Point {
            row: options.line.get() - 1,
            column: options.column.unwrap_or(999),
        })
        .expect("symbol");

    println!("{:#?}", symbol);

    fn walk_symbol_call_tree(
        symbol: SymbolBody,
        source: &SourceCode,
        references: &HashMap<
            Handle<stack_graphs::graph::Node>,
            Vec<Handle<stack_graphs::graph::Node>>,
        >,
    ) {
        for (def, refs) in references {
            refs.iter().for_each(|r| {
                log::debug!(
                    "considering definition: {} <- {}",
                    display_span!(source.graph.source_info(*def).unwrap().span),
                    display_span!(source.graph.source_info(*r).unwrap().span),
                );

                let info = source.graph.source_info(*def).unwrap();
                if info.span.start >= symbol.body.start_position()
                    && info.span.end <= symbol.body.end_position()
                    && info.span.start.line == symbol.body.start_position().row
                {
                    let symbol = source
                        .symbol_at_point(
                            source.graph.source_info(*r).unwrap().span.start.as_point(),
                        )
                        .unwrap();

                    println!("{symbol:#?}",);

                    walk_symbol_call_tree(symbol, source, references)
                }
            });
        }
    }
    walk_symbol_call_tree(symbol, &source, &references);

    // println!(
    //     "{}",
    //     source
    //         .graph
    //         .iter_nodes()
    //         .filter(|node| source.graph[*node].is_definition())
    //         .find(|node| {
    //             log::debug!(
    //                 "node: {} ({})",
    //                 node.display(&source.graph),
    //                 display_span!(source.graph.source_info(*node).expect("source info").span)
    //             );

    //             // `node` is the identifier of the function; not the body
    //             // source
    //             //     .tree
    //             source
    //                 .graph
    //                 .source_info(*node)
    //                 .expect("source info")
    //                 .span
    //                 .contains_point(&row!(options.line.get() - 1))
    //         })
    //         .expect("find node")
    //         .display(&source.graph)
    // );

    // let ident = source
    //     .find_ident(row!(options.line.get() - 1))
    //     .context("finding identifier")?;
    // let parent = source
    //     .find_scope(row!(options.line.get() - 1))
    //     .context("finding parent scope")?;

    // log::info!("{ident:?} in {parent:?}");

    // // println!("'{ident}' called by:");
    // // for (point, source, caller) in source.callers(&parent).context("getting callers")? {
    // //     println!("- '{caller}' @ {}:{}", source.path.display(), point.row);
    // // }

    // println!("'{parent}' calls:");
    // for call in source.references(&ident).context("getting calls")? {
    //     println!("- '{call:?}'");
    // }

    Ok(())
}

#[derive(Debug)]
struct SymbolBody<'a> {
    identifier: Identifier<'a>,
    body: tree_sitter::Node<'a>,
}

#[derive(Debug)]
enum IdentifierPart<'a> {
    Class(&'a str),
    Function(&'a str),
    Method(&'a str),
}

impl std::fmt::Display for IdentifierPart<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use IdentifierPart::*;

        match self {
            Class(name) | Function(name) | Method(name) => write!(f, "{name}"),
        }
    }
}

struct Identifier<'a> {
    node: tree_sitter::Node<'a>,
    parts: Vec<IdentifierPart<'a>>,
}

impl std::fmt::Display for Identifier<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut parts = self.parts.iter().rev();
        match parts.next() {
            Some(part) => write!(f, "{part}")?,
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

        Ok(SourceCode {
            path,
            source,
            tree,
            graph,
        })
    }

    fn symbol_at_point(&'a self, point: tree_sitter::Point) -> Result<SymbolBody<'a>> {
        let identifier = self.find_ident(point)?;
        let mut node = identifier.node;
        let body = loop {
            match node.kind() {
                "method_definition" => break Some(node),
                "function_declaration" => break Some(node),
                _ => {}
            }
            match node.parent() {
                Some(parent) => node = parent,
                None => break None,
            }
        }
        .context("finding symbol body")?;
        Ok(SymbolBody { identifier, body })
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
                | "call_expression"
                | "identifier"
                | "property_identifier"
                | "member_expression"
                | "variable_declarator"
                | "lexical_declaration"
                | "if_statement"
                | "export_statement"
                | "return_statement"
                | "expression_statement" => {}
                "function_declaration" => capture!(Function)
                    .context(format!("couldn't get name of function at {parent:?}",))?,
                "method_definition" => capture!(Method)
                    .context(format!("couldn't get name of method at {parent:?}",))?,
                "class_declaration" => {
                    capture!(Class).context(format!("couldn't get name of class at {parent:?}",))?
                }
                k => log::debug!("unrecognized node kind: {k}"),
            }
            match parent.parent() {
                Some(p) => parent = p,
                None => break,
            }
        }

        Ok(Identifier { node, parts })
    }

    /// Find the owning scope at the given point
    ///
    /// This uses tree_sitter to walk up the syntax tree to find the nearest definition that
    /// contains the given point. The identifier is returned, though I don't know how useful that is
    /// anymore, along with the definition's point.
    fn find_scope(&'a self, point: tree_sitter::Point) -> Result<Identifier<'a>> {
        let mut node = self
            .tree
            .root_node()
            .descendant_for_point_range(point, point)
            .context("finding descendant at point")?;

        self.log_tree(node);

        macro_rules! field {
            ($node:ident, $name:literal) => {{
                $node
                    .child_by_field_name($name)
                    .ok_or(anyhow::anyhow!("{} not found", $name))
                    .and_then(|name| name.utf8_text(self.source.as_bytes()).map_err(Into::into))
            }};
        }

        let mut parts = Vec::new();

        macro_rules! capture {
            ($ident:path) => {{
                parts.push($ident(field!(node, "name").unwrap()));
            }};
        }

        loop {
            use IdentifierPart::*;

            match node.kind() {
                "statement_block"
                | "class_body"
                | "class"
                | "program"
                | "}"
                | "parenthesized_expression"
                | "call_expression"
                | "identifier"
                | "property_identifier"
                | "member_expression"
                | "variable_declarator"
                | "lexical_declaration"
                | "if_statement"
                | "export_statement"
                | "return_statement"
                | "expression_statement" => {}
                "function_declaration" | "function" => capture!(Function),
                "method_definition" => capture!(Method),
                "class_declaration" => capture!(Class),
                k => log::debug!("unrecognized node kind: {k}"),
            }
            match node.parent() {
                Some(parent) => node = parent,
                None => break,
            }
        }

        Ok(Identifier { node, parts })
    }

    fn log_tree(&self, node: tree_sitter::Node) {
        fn climb(node: tree_sitter::Node, source: &str, depth: usize) -> usize {
            let max_depth = match node.parent() {
                Some(parent) => climb(parent, source, depth + 1),
                None => depth,
            };

            let indent = " ".repeat(max_depth - depth);
            macro_rules! show {
                ($name:literal, $fmt:literal $(, $args:tt)*) => {{
                    match node.child_by_field_name($name) {
                        Some(name) => {
                            let name = name.utf8_text(source.as_bytes()).unwrap();
                            log::debug!(concat!("{}", $fmt), indent, name,  $($args)*);
                        }
                        None => log::debug!(concat!("missing ", $name)),
                    }
                }};
                ($str:expr, $($args:tt), *) => {{
                    log::debug!(concat!("{}", $str), indent, $($args)*)
                }};
            }

            match node.kind() {
                "function_declaration" => show!("name", "function {}"),
                "method_definition" => show!("name", "method {}"),
                "class_declaration" => show!("name", "class {}"),
                k => show!("{{{}}}", k),
            }

            max_depth
        }

        climb(node, &self.source, 0);
    }

    fn references(&'a self, ident: &Identifier<'_>) -> Result<Vec<Identifier<'a>>> {
        // - read all of the symbol references (function calls, variable use) and store them in a map
        //   of references to definitions
        // - build an index of definitions to their references

        use IdentifierPart::*;

        let name = ident
            .parts
            .first()
            .map(|p| match p {
                Method(name) | Class(name) | Function(name) => *name,
            })
            .context("getting name of identifier")?;
        let symbol = self
            .graph
            .iter_symbols()
            .find(|s| name == &self.graph[*s])
            .context(format!("finding symbol for {ident}"))?;

        log::error!(
            "[{}, {}] - [{}, {}]",
            ident.node.start_position().row,
            ident.node.start_position().column,
            ident.node.end_position().row,
            ident.node.end_position().column,
        );
        let node = self
            .graph
            .iter_nodes()
            .find(|n| {
                if !self.graph[*n].is_definition() {
                    return false;
                }

                self.graph
                    .source_info(*n)
                    .map(|i| {
                        log::error!(
                            "at: {} [{}, {}] - [{}, {}]",
                            n.display(&self.graph),
                            i.span.start.line,
                            i.span.start.column.utf8_offset,
                            i.span.end.line,
                            i.span.end.column.utf8_offset,
                        );
                        i.span.start.line == ident.node.start_position().row
                        // && i.span.end.line == ident.node.end_position().row
                    })
                    .unwrap_or(false)
            })
            .context(format!("finding node for {ident}"))?;
        log::error!("symbol: {}", &self.graph[symbol]);
        log::error!("node:   {}", node.display(&self.graph));

        log::error!(
            "{}",
            self.graph
                .iter_nodes()
                .find(|n| {
                    let node = &self.graph[*n];
                    if !node.is_reference() {
                        return false;
                    }

                    if name != &self.graph[node.symbol().expect("references have a symbol")] {
                        return false;
                    }

                    let config = StitcherConfig::default();
                    let mut partials = PartialPaths::new();
                    let mut candidates = GraphEdgeCandidates::new(&self.graph, &mut partials, None);

                    let mut found= false;
                    let _ =
                        stack_graphs::stitching::ForwardPartialPathStitcher::find_all_complete_partial_paths(
                            &mut candidates,
                            [*n],
                            config,
                            &stack_graphs::NoCancellation,
                            |graph, _partials, partial| {
                                let start_span = &graph.source_info(partial.start_node).unwrap().span;
                                let end_span = &graph.source_info(partial.end_node).unwrap().span;
                                log::debug!(
                                    "potential call-site: [{}:{}] - [{}:{}] -> [{}:{}] - [{}:{}]",
                                    start_span.start.line + 1,
                                    start_span.start.column.utf8_offset,
                                    start_span.end.line + 1,
                                    start_span.end.column.utf8_offset,
                                    end_span.start.line + 1,
                                    end_span.start.column.utf8_offset,
                                    end_span.end.line + 1,
                                    end_span.end.column.utf8_offset,
                                );

                                found = true;

                                // if ((end_span.start.line > ident.node.start_position().row)
                                //     || (end_span.start.line == ident.node.start_position().row
                                //         && end_span.start.column.grapheme_offset
                                //         >= ident.node.start_position().column))
                                //     && ((end_span.end.line == ident.node.end_position().row
                                //          && end_span.end.column.grapheme_offset
                                //          <= ident.node.end_position().column)
                                //         || (end_span.end.line < ident.node.end_position().row))
                                // {
                                //     // callsites.push(partial);
                                //     match self.find_scope(tree_sitter::Point {
                                //         row: start_span.start.line,
                                //         column: start_span.start.column.utf8_offset,
                                //     }) {
                                //         Ok(ident) => println!("- {}", ident),
                                //         Err(err) => log::error!("{err}"),
                                //     }
                                //     // println!("- {}", partial.start_node.display(&graph));
                                // }
                            },
                        );
                    found
                })
                .unwrap()
                .display(&self.graph)
        );
        Ok(Vec::new())
    }

    fn callers(
        &'a self,
        ident: &Identifier<'_>,
    ) -> Result<Vec<(tree_sitter::Point, &'a SourceCode<'a>, Identifier<'a>)>> {
        let language = tree_sitter_stack_graphs_typescript::try_language_configuration(
            &tree_sitter_stack_graphs::NoCancellation,
        )
        .context("loading typescript TSG")?;
        let mut graph = StackGraph::new();
        let file = graph
            .add_file(&self.path.to_string_lossy())
            .expect("file not present in empty graph");
        let globals = Variables::new();
        language
            .sgl
            .build_stack_graph_into(
                &mut graph,
                file,
                &self.source,
                &globals,
                &tree_sitter_stack_graphs::NoCancellation,
            )
            .context("building stack graph")?;

        let name = match ident.parts.first() {
            Some(s) => s,
            None => return Ok(Vec::new()),
        };

        let mut partials = PartialPaths::new();
        let mut candidates = GraphEdgeCandidates::new(&graph, &mut partials, None);

        // Doesn't capture the surrounding scope
        // #[cfg(FALSE)]
        let mut definitions = graph
            .get_file(&self.path.to_string_lossy())
            .into_iter()
            .flat_map(|file| {
                graph.nodes_for_file(file).filter_map(|node| {
                    if !graph[node].is_definition() {
                        return None;
                    }

                    let source_info = graph.source_info(node)?;

                    log::trace!("considering: {}", node.display(&graph));
                    log::trace!("  {:?}", source_info.span);
                    log::trace!("  {:?}", ident.node.range());

                    if source_info.span.start.line == ident.node.start_position().row {
                        Some(node)
                    } else {
                        None
                    }
                })
            });

        let definition = definitions.next().context("finding definition")?;
        definitions
            .for_each(|def| log::warn!("additional definition found: {}", def.display(&graph)));
        // let nodes = graph.nodes_for_file(file).filter_map(|node| None);

        log::debug!("finding references to {}", definition.display(&graph));
        let references = graph
            .get_file(&self.path.to_string_lossy())
            .into_iter()
            .flat_map(|file| {
                graph.nodes_for_file(file).filter_map(|node| {
                    if !graph[node].is_reference() {
                        return Option::<stack_graphs::arena::Handle<stack_graphs::graph::Node>>::None;
                    }

                    use IdentifierPart::*;
                    match name {
                        Class(name) | Method(name) | Function(name) => {
                            if *name != &graph[graph[node].symbol().unwrap()] {
                                return None;
                            }
                        }
                    }

                    log::debug!("considering: {}", node.display(&graph));
                    Some(node)
                })
            });

        let config = StitcherConfig::default();
        // let callsites = Vec::new();
        let _ =
            stack_graphs::stitching::ForwardPartialPathStitcher::find_all_complete_partial_paths(
                &mut candidates,
                references,
                config,
                &stack_graphs::NoCancellation,
                |graph, _partials, partial| {
                    let start_span = &graph.source_info(partial.start_node).unwrap().span;
                    let end_span = &graph.source_info(partial.end_node).unwrap().span;
                    log::debug!(
                        "potential call-site: [{}:{}] - [{}:{}] -> [{}:{}] - [{}:{}]",
                        start_span.start.line + 1,
                        start_span.start.column.utf8_offset,
                        start_span.end.line + 1,
                        start_span.end.column.utf8_offset,
                        end_span.start.line + 1,
                        end_span.start.column.utf8_offset,
                        end_span.end.line + 1,
                        end_span.end.column.utf8_offset,
                    );

                    if ((end_span.start.line > ident.node.start_position().row)
                        || (end_span.start.line == ident.node.start_position().row
                            && end_span.start.column.grapheme_offset
                                >= ident.node.start_position().column))
                        && ((end_span.end.line == ident.node.end_position().row
                            && end_span.end.column.grapheme_offset
                                <= ident.node.end_position().column)
                            || (end_span.end.line < ident.node.end_position().row))
                    {
                        // callsites.push(partial);
                        match self.find_scope(tree_sitter::Point {
                            row: start_span.start.line,
                            column: start_span.start.column.utf8_offset,
                        }) {
                            Ok(ident) => println!("- {}", ident),
                            Err(err) => log::error!("{err}"),
                        }
                        // println!("- {}", partial.start_node.display(&graph));
                    }
                },
            );
        return Ok(Vec::new());

        // return Ok(callsites.into_iter()
        //     .inspect(|partial| log::debug!("{}", partial.display(&graph, partials)))
        //     .filter_map(|node| {
        //         let span = &graph.source_info(node)?.span;
        //         let point = tree_sitter::Point {
        //             row: span.start.line,
        //             column: span.start.column.utf8_offset,
        //         };
        //         let ident = self.find_scope(point);
        //         let mut callers = Vec::new();
        //         // let mut callers = match self.callers(&ident) {
        //         //     Ok(callers) => callers,
        //         //     Err(err) => {
        //         //         log::error!("{err}");
        //         //         return None;
        //         //     }
        //         // };
        //         callers.insert(0, (point, self, ident));
        //         Some(callers)
        //     })
        //     .flatten()
        //     .collect());

        #[cfg(FALSE)]
        let _ = ForwardPartialPathStitcher::find_minimal_partial_path_set_in_file(
            &graph,
            &mut partials,
            // &mut candidates,
            // [node],
            file,
            StitcherConfig::default(),
            &stack_graphs::NoCancellation,
            |graph, _partials, partial| {
                // println!("{}", graph[partial.end_node].symbol().unwrap().display(&graph));

                // match name {
                //     Class(name) | Method(name) | Function(name) => {
                //         if *name != &graph[graph[partial.end_node].symbol().unwrap()] {
                //             return;
                //         }
                //     }
                // }

                use stack_graphs::graph::Node::*;
                match &graph[partial.start_node] {
                    Scope(ScopeNode {
                        id, is_exported, ..
                    }) => println!("{} {is_exported}", id.display(graph)),
                    PushSymbol(PushSymbolNode {
                        id,
                        is_reference,
                        symbol,
                        ..
                    }) => {
                        // let node = graph.iter_nodes().find(|n| graph[*n].id() == *id).unwrap();
                        let node = graph.node_for_id(*id).unwrap();
                        println!(
                            "{}{} {}:{}",
                            match is_reference {
                                true => "&",
                                false => "",
                            },
                            symbol.display(graph),
                            match id.file() {
                                Some(file) => {
                                    || -> Box<dyn std::fmt::Display> {
                                        Box::new(file.display(graph))
                                    }()
                                }
                                None => {
                                    || -> Box<dyn std::fmt::Display> {
                                        Box::new(format!("<empty>"))
                                    }()
                                }
                            },
                            // id.local_id(),
                            node.display(graph),
                        );
                    }
                    _node => {}
                }

                // println!(
                //     "{:?} {} -> {}",
                //     graph[partial.start_node].symbol().map(|sym| &graph[sym]),
                //     graph[partial.start_node].
                //     partial.end_node.display(graph)
                // );
                // println!("{partials:?}");
            },
        );

        // if !graph[node].is_reference() {
        //     return None;
        // }

        // match name {
        //     Class(name) | Method(name) | Function(name) => {
        //         if *name != &graph[graph[node].symbol()?] {
        //             return None;
        //         }
        //     }
        // }

        // Some(node)
        // });

        // let mut partials = PartialPaths::new();
        // let mut candidates = GraphEdgeCandidates::new(&graph, &mut partials, None);
        // let _ = ForwardPartialPathStitcher::find_all_complete_partial_paths(
        //     &mut candidates,
        //     references,
        //     StitcherConfig::default(),
        //     &stack_graphs::NoCancellation,
        //     |graph, _partials, partial| {
        //         // println!("{}", graph[partial.end_node].symbol().unwrap().display(&graph));

        //         // match name {
        //         //     Class(name) | Method(name) | Function(name) => {
        //         //         if *name != &graph[graph[partial.end_node].symbol().unwrap()] {
        //         //             return;
        //         //         }
        //         //     }
        //         // }

        //         println!(
        //             "{} -> {}",
        //             partial.start_node.display(graph),
        //             partial.end_node.display(graph)
        //         );
        //         // println!("{partials:?}");
        //     },
        // );
        // Ok(Vec::new())

        // Ok(references
        //     .inspect(|node| log::debug!("{}", node.display(&graph)))
        //     .filter_map(|node| {
        //         let span = &graph.source_info(node)?.span;
        //         let point = Point {
        //             row: span.start.line,
        //             column: span.start.column.utf8_offset,
        //         };
        //         let ident = self.build_identifier(point);
        //         let mut callers = Vec::new();
        //         // let mut callers = match self.callers(&ident) {
        //         //     Ok(callers) => callers,
        //         //     Err(err) => {
        //         //         log::error!("{err}");
        //         //         return None;
        //         //     }
        //         // };
        //         callers.insert(0, (point, self, ident));
        //         Some(callers)
        //     })
        //     .flatten()
        //     .collect())
    }
}
