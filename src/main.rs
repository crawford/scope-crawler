use anyhow::{Context, Result};
// use stack_graphs::graph::PushSymbolNode;
// use stack_graphs::graph::ScopeNode;
use stack_graphs::graph::StackGraph;
use stack_graphs::partial::PartialPaths;
// use stack_graphs::stitching::ForwardPartialPathStitcher;
use stack_graphs::stitching::GraphEdgeCandidates;
// use stack_graphs::stitching::GraphEdgeCandidates;
use stack_graphs::stitching::StitcherConfig;
use std::path::{Path, PathBuf};
use std::time::Duration;
// use tree_sitter::{Node, Point};
use tree_sitter_stack_graphs::Variables;

#[derive(clap::Parser)]
struct Options {
    file: PathBuf,
    line: usize,

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
            filter(options.verbosity.saturating_sub(1)),
        )
        .try_init()
        .expect("initializing logging");

    macro_rules! row {
        ($row:expr) => {
            tree_sitter::Point {
                row: $row,
                column: 0,
            }
        };
    }

    // let cancel = stack_graphs::CancelAfterDuration::new(options.timeout);
    let source = SourceCode::from_path(&options.file)
        .context(anyhow::anyhow!("reading {}", options.file.display()))?;
    let (ident, range) = source.find_scope(row!(options.line))?;

    log::info!(
        "{ident} @ [{}:{}] - [{}:{}]",
        range.start_point.row + 1,
        range.start_point.column,
        range.end_point.row + 1,
        range.end_point.column
    );
    // std::thread::sleep(std::time::Duration::from_secs(1));
    // let _ = tree_sitter_stack_graphs_javascript::try_language_configuration(&tree_sitter_stack_graphs::NoCancellation)
    //     .map_err(|err| log::error!("main() failed to load TSG: {err}"));

    println!("'{ident}' called by:");
    for (point, source, caller) in source.callers(&ident, range).context("getting callers")? {
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
    // graph: StackGraph,
}

impl<'a> SourceCode<'a> {
    fn from_path(path: &'a Path) -> Result<SourceCode<'a>> {
        let code = SourceCode {
            path,
            source: std::fs::read_to_string(path).context("opening {path}")?,
            // graph: StackGraph::new(),
        };

        // XXX: Why does this line panic?
        // let language = tree_sitter_stack_graphs_javascript::language_configuration(&tree_sitter_stack_graphs::NoCancellation);
        // let language =
        //     tree_sitter_stack_graphs_javascript::try_language_configuration(&tree_sitter_stack_graphs::NoCancellation)
        //         .context("loading javascript TSG")?;

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
        //         &tree_sitter_stack_graphs::NoCancellation,
        //     )
        //     .context("building stack graph")?;

        Ok(code)
    }

    /// Find the owning scope at the given point
    ///
    /// This uses tree_sitter to walk up the syntax tree to find the nearest definition that
    /// contains the given point. The identifier is returned, though I don't know how useful that is
    /// anymore, along with the definition's point.
    fn find_scope(
        &'a self,
        point: tree_sitter::Point,
    ) -> Result<(Identifier<'a>, tree_sitter::Range)> {
        let mut parser = tree_sitter::Parser::new();
        parser
            .set_language(tree_sitter_typescript::language_typescript())
            .context("loading typescript grammar")?;

        let parsed_tree = parser
            .parse(&self.source, None)
            .expect("Failed to parse code");
        let root_node: tree_sitter::Node<'_> = parsed_tree.root_node();
        let mut node = root_node
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

        let mut ident = Identifier(Vec::new());
        let mut range = None;

        macro_rules! capture {
            ($ident:path) => {{
                ident.0.push($ident(field!(node, "name").unwrap()));
                if range.is_none() {
                    range = Some(node.range());
                }
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
                k => log::info!("unrecognized node kind: {k}"),
            }
            match node.parent() {
                Some(parent) => node = parent,
                None => break,
            }
        }

        Ok((ident, range.context("finding enclosing definition")?))
    }

    fn log_tree(&self, node: tree_sitter::Node) {
        fn climb(node: tree_sitter::Node, source: &str, depth: usize) -> usize {
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
        range: tree_sitter::Range,
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

        let name = match ident.0.first() {
            Some(s) => s,
            None => return Ok(Vec::new()),
        };
        // let references = graph.iter_nodes().filter_map(|node| {
        //     use IdentifierPart::*;

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
                    // println!("ALEX: reference node");

                    let source_info = graph.source_info(node)?;
                    // println!("{} {:?}", node.display(&graph), source_info.span);

                    // let line = point.row - 1;
                    log::trace!("considering: {}", node.display(&graph));
                    log::trace!("  {:?}", source_info.span);
                    log::trace!("  {range:?}");
                    // if ((source_info.span.start.line < (range.start_point.row + 1))
                    //     || (source_info.span.start.line == (range.start_point.row + 1)
                    //         && source_info.span.start.column.grapheme_offset
                    //             <= range.start_point.column))
                    //     && ((source_info.span.end.line == (range.end_point.row + 1)
                    //         && source_info.span.end.column.grapheme_offset
                    //             >= range.end_point.column)
                    //         || (source_info.span.end.line > (range.end_point.row + 1)))
                    // {
                    if source_info.span.start.line == range.start_point.row {
                        // if source_info.span.start.line <= line && source_info.span.end.line >= line {
                        // println!("ALEX: {}", node.display(&graph));
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
                    // println!("ALEX: reference node");

                    // let source_info = graph.source_info(node)?;
                    // println!("{} {:?}", node.display(&graph), source_info.span);

                    use IdentifierPart::*;
                    match name {
                        Class(name) | Method(name) | Function(name) => {
                            if *name != &graph[graph[node].symbol().unwrap()] {
                                return None;
                            }
                        }
                    }

                    log::debug!("considering: {}", node.display(&graph));
                    // log::debug!("  {:?}", source_info.span);
                    // log::debug!("  {range:?}");
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

                    if ((end_span.start.line > range.start_point.row)
                        || (end_span.start.line == range.start_point.row
                            && end_span.start.column.grapheme_offset >= range.start_point.column))
                        && ((end_span.end.line == range.end_point.row
                            && end_span.end.column.grapheme_offset <= range.end_point.column)
                            || (end_span.end.line < range.end_point.row))
                    {
                        // callsites.push(partial);
                        match self.find_scope(tree_sitter::Point {
                            row: start_span.start.line,
                            column: start_span.start.column.utf8_offset,
                        }) {
                            Ok((ident, _range)) => println!("- '{}'", ident),
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
