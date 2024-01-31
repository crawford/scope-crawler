use anyhow::{Context, Result};
use stack_graphs::graph::StackGraph;
use std::path::{Path, PathBuf};
use tree_sitter::{Node, Point};
use tree_sitter_stack_graphs::NoCancellation;
use tree_sitter_stack_graphs::Variables;

#[derive(clap::Parser)]
struct Options {
    file: PathBuf,
    line: usize,

    #[arg(action = clap::ArgAction::Count, long = "verbose", short = 'v')]
    verbosity: u8,
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
            filter(options.verbosity.saturating_sub(1)),
        )
        .try_init()
        .expect("initializing logging");

    macro_rules! row {
        ($row:expr) => {
            Point {
                row: $row,
                column: 0,
            }
        };
    }

    let source = SourceCode::from_path(&options.file)
        .context(anyhow::anyhow!("reading {}", options.file.display()))?;
    let ident = source.build_identifier(row!(options.line));

    println!("'{ident}' called by:");
    for (point, source, caller) in source.callers(&ident).context("getting callers")? {
        println!("- '{caller}' @ {}:{}", source.path.display(), point.row);
    }

    Ok(())
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

struct Identifier<'a>(Vec<IdentifierPart<'a>>);

impl std::fmt::Display for Identifier<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut parts = self.0.iter().rev();
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

struct SourceCode<'a> {
    path: &'a Path,
    source: String,
    graph: StackGraph,
}

impl<'a> SourceCode<'a> {
    fn from_path(path: &'a Path) -> Result<SourceCode<'a>> {
        let mut code = SourceCode {
            path,
            source: std::fs::read_to_string(path).context("opening {path}")?,
            graph: StackGraph::new(),
        };

        // XXX: Why does this line panic?
        let language = tree_sitter_stack_graphs_javascript::language_configuration(&NoCancellation);
        // let mut graph = StackGraph::new();
        // let file = graph
        //     .add_file(&path.to_string_lossy())
        //     .expect("file not present in empty graph");
        // let globals = Variables::new();
        // language
        //     .sgl
        //     .build_stack_graph_into(
        //         &mut code.graph,
        //         file,
        //         &code.source,
        //         &globals,
        //         &NoCancellation,
        //     )
        //     .context("building stack graph")?;

        Ok(code)
    }

    fn build_identifier(&'a self, point: Point) -> Identifier<'a> {
        let mut parser = tree_sitter::Parser::new();

        let language = tree_sitter_javascript::language();
        parser
            .set_language(language)
            .expect("Error loading JavaScript grammar");

        let parsed_tree = parser
            .parse(&self.source, None)
            .expect("Failed to parse code");
        let root_node: Node<'_> = parsed_tree.root_node();
        let mut node = match root_node.descendant_for_point_range(point, point) {
            Some(root) => root,
            None => {
                log::error!("couldn't find node at {}", point);
                return Identifier(Vec::new());
            }
        };
        self.log_tree(node);

        macro_rules! field {
            ($node:ident, $name:literal) => {{
                $node
                    .child_by_field_name($name)
                    .ok_or(anyhow::anyhow!("{} not found", $name))
                    .and_then(|name| name.utf8_text(self.source.as_bytes()).map_err(Into::into))
            }};
        }

        let mut ident = Identifier(Vec::new());
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
                | "expression_statement" => {}
                "function_declaration" | "function" => {
                    ident.0.push(Function(field!(node, "name").unwrap()))
                }
                "method_definition" => ident.0.push(Method(field!(node, "name").unwrap())),
                "class_declaration" => ident.0.push(Class(field!(node, "name").unwrap())),
                k => log::warn!("unrecognized node kind: {k}"),
            }
            match node.parent() {
                Some(parent) => node = parent,
                None => break,
            }
        }

        ident
    }

    fn log_tree(&self, node: Node) {
        fn climb(node: Node, source: &str, depth: usize) -> usize {
            let max_depth = match node.parent() {
                Some(parent) => climb(parent, source, depth + 1),
                None => depth,
            };

            let indent = " ".repeat((max_depth - depth) * 2);
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

    fn callers(
        &'a self,
        ident: &Identifier<'_>,
    ) -> Result<Vec<(Point, &'a SourceCode<'a>, Identifier<'a>)>> {
        let language =
            tree_sitter_stack_graphs_javascript::try_language_configuration(&NoCancellation)
                .context("loading javascript TSG")?;
        let mut graph = StackGraph::new();
        let file = graph
            .add_file(&self.path.to_string_lossy())
            .expect("file not present in empty graph");
        let globals = Variables::new();
        language
            .sgl
            .build_stack_graph_into(&mut graph, file, &self.source, &globals, &NoCancellation)
            .context("building stack graph")?;

        let name = match ident.0.first() {
            Some(s) => s,
            None => return Ok(Vec::new()),
        };
        let references = graph.iter_nodes().filter_map(|node| {
            use IdentifierPart::*;

            if !graph[node].is_reference() {
                return None;
            }

            match name {
                Class(name) | Method(name) | Function(name) => {
                    if *name != &graph[graph[node].symbol()?] {
                        return None;
                    }
                }
            }

            Some(node)
        });
        Ok(references
            .inspect(|node| log::debug!("{}", node.display(&graph)))
            .filter_map(|node| {
                let span = &graph.source_info(node)?.span;
                let point = Point {
                    row: span.start.line,
                    column: span.start.column.utf8_offset,
                };
                let ident = self.build_identifier(point);
                let mut callers = match self.callers(&ident) {
                    Ok(callers) => callers,
                    Err(err) => {
                        log::error!("{err}");
                        return None;
                    }
                };
                callers.insert(0, (point, self, ident));
                Some(callers)
            })
            .flatten()
            .collect())
    }
}
