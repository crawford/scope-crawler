use anyhow::{Context, Result};
use std::path::{Path, PathBuf};
use tree_sitter::{Node, Point, Query, QueryCursor};

#[derive(clap::Parser)]
struct Options {
    file: PathBuf,
    line: usize,

    #[arg(action = clap::ArgAction::Count, long = "verbose", short = 'v')]
    verbosity: u8,
}

fn main() {
    use clap::Parser;

    let options = Options::parse();

    pretty_env_logger::formatted_builder()
        .filter_level(match options.verbosity {
            0 => log::LevelFilter::Warn,
            1 => log::LevelFilter::Info,
            2 => log::LevelFilter::Debug,
            _ => log::LevelFilter::Trace,
        })
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

    let source = SourceCode::from_path(&options.file).expect("Failed to read file");
    let ident = source.build_identifier(row!(options.line));

    println!("'{ident}' called by:");
    for (point, source, caller) in source.callers(&ident) {
        println!("- '{caller}' @ {}:{}", source.path.display(), point.row);
    }
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
}

impl<'a> SourceCode<'a> {
    fn from_path(path: &'a Path) -> Result<SourceCode<'a>> {
        Ok(SourceCode {
            path,
            source: std::fs::read_to_string(path).context("opening {path}")?,
        })
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
                | "expression_statement" => {}
                "function_declaration" | "function" => {
                    ident.0.push(Function(field!(node, "name").unwrap()))
                }
                "method_definition" => ident.0.push(Method(field!(node, "name").unwrap())),
                "class_declaration" => ident.0.push(Class(field!(node, "name").unwrap())),
                k => log::error!("unrecognized node kind: {k}"),
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

    fn callers(&'a self, ident: &Identifier<'_>) -> Vec<(Point, &'a SourceCode<'a>, Identifier<'a>)> {
        let mut parser = tree_sitter::Parser::new();

        let language = tree_sitter_javascript::language();
        parser
            .set_language(language)
            .expect("Error loading JavaScript grammar");

        let parsed_tree = parser
            .parse(&self.source, None)
            .expect("Failed to parse source");
        let root_node: Node<'_> = parsed_tree.root_node();
        let mut cursor = QueryCursor::new();
        let query = Query::new(
            language,
            &format!(
                r#"(call_expression (identifier) @func (arguments) @args (#match? @func "{}"))"#,
                ident.0.first().unwrap()
            ),
        )
        .unwrap();

        let mut callers = Vec::new();
        for m in cursor.matches(
            &query,
            root_node,
            |node: Node<'_>| match node.utf8_text(self.source.as_bytes()) {
                Ok(name) => return std::iter::once(name.as_bytes()),
                Err(err) => panic!("{err}"),
            }, //&source
        ) {
            let mut captures = m.captures.iter();
            let ident = captures.next().expect("identifier").node;
            let args = captures.next().expect("args").node;
            log::debug!(
                "{}{} @ {}:{}",
                ident.utf8_text(self.source.as_bytes()).unwrap(),
                args.utf8_text(self.source.as_bytes()).unwrap(),
                self.path.display(),
                ident.start_position().row,
            );
            let start = ident.start_position();
            callers.push((start, self, self.build_identifier(start)))
        }
        callers
    }
}
