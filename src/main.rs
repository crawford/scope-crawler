use std::path::PathBuf;

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

    let source_code = std::fs::read_to_string(options.file).expect("Failed to read file");
    let mut parser = tree_sitter::Parser::new();

    let language = tree_sitter_javascript::language();
    parser
        .set_language(language)
        .expect("Error loading JavaScript grammar");

    let parsed_tree = parser
        .parse(&source_code, None)
        .expect("Failed to parse code");

    let root_node: tree_sitter::Node<'_> = parsed_tree.root_node();

    // let module: Module = Module {
    //     source: source_code.clone(),
    // };

    // module.walk(&root_node, 0);

    macro_rules! row {
        ($row:expr) => {{
            tree_sitter::Point {
                row: $row,
                column: 0,
            }
        }};
    }

    fn climb(node: tree_sitter::Node, source: &str, depth: usize) -> usize {
        let max_depth = match node.parent() {
            Some(parent) => climb(parent, source, depth + 1),
            None => depth,
        };

        // let indent = " ".repeat((max_depth - depth) * 2);
        // macro_rules! show {
        //     ($str:expr) => {{
        //         print!("{indent}");
        //         println!($str)
        //     }};
        //     ($name:literal, $fmt:literal) => {{
        //         match node.child_by_field_name($name) {
        //             Some(name) => {
        //                 print!("{indent}");
        //                 println!($fmt, name.utf8_text(source.as_bytes()).unwrap());
        //             }
        //             None => log::error!(concat!("missing ", $name)),
        //         }
        //     }};
        // }

        // match node.kind() {
        //     "statement_block" => show!("{{statement block}}"),
        //     "function_declaration" => show!("name", "(Function) {}"),
        //     "method_definition" => show!("name", "(Method) {}"),
        //     "class_body" | "class" => {}
        //     "class_declaration" => show!("name", "(Class) {}"),
        //     "program" => show!("(Program)"),
        //     k => {
        //         log::error!("unrecognized node kind: {k}");
        //     }
        // }

        macro_rules! show {
            ($name:literal, $fmt:literal) => {{
                match node.child_by_field_name($name) {
                    Some(name) => {
                        print!($fmt, name.utf8_text(source.as_bytes()).unwrap());
                    }
                    None => log::error!(concat!("missing ", $name)),
                }
            }};
        }

        match node.kind() {
            "statement_block" => {}
            "function_declaration" => show!("name", "{}"),
            "method_definition" => show!("name", "::{}"),
            "class_body" | "class" => {}
            "class_declaration" => show!("name", "{}"),
            "program" => {},
            k => {
                log::error!("unrecognized node kind: {k}");
            }
        }

        if depth == 0 {
            println!();
        }

        max_depth
    }

    match root_node.descendant_for_point_range(row!(options.line), row!(options.line)) {
        Some(root) => {
            climb(root, &source_code, 0);
        }
        None => log::error!("couldn't find node at line {}", options.line),
    }

    // macro_rules! show {
    //     ($node:ident, $name:literal, $fmt:expr) => {{
    //         match $node.child_by_field_name($name) {
    //             Some(name) => print!($fmt, name.utf8_text(source_code.as_bytes()).unwrap()),
    //             None => log::error!(concat!("missing ", $name)),
    //         }
    //     }};
    // }

    // let mut node = root_node.descendant_for_point_range(row!(options.line), row!(options.line));
    // loop {
    //     match node {
    //         Some(n) => {
    //             match n.kind() {
    //                 "statement_block" => print!("{{statement block}}"),
    //                 "function_declaration" => show!(n, "name", "::{}::"),
    //                 "method_definition" => show!(n, "name", "::{}"),
    //                 "class_body" => {}
    //                 "class_declaration" => show!(n, "name", "::{}"),
    //                 "program" => {
    //                     println!();
    //                     break;
    //                 }
    //                 k => {
    //                     log::error!("unrecognized node kind: {k}");
    //                 }
    //             }
    //             node = n.parent();
    //         }
    //         None => {
    //             println!();
    //             break;
    //         }
    //     }
    // }
}

enum IdentifierPart<'a> {
    Method(&'a str),
    Function(&'a str),
    Class(&'a str),
}

type Identifier<'a> = Vec<IdentifierPart<'a>>;

fn build_identifier(point: tree_sitter::Point, source: &str) -> Identifier<'_> {
    
}

// struct Module {
//     source: String,
// }

// impl Module {
//     fn walk(&self, node: &tree_sitter::Node<'_>, depth: usize) {
//         let indent = " ".repeat(depth * 2);

//         println!(
//             "{}{}: [{}] - [{}]",
//             indent,
//             // node.utf8_text(self.source.as_bytes()).unwrap(),
//             node.kind(),
//             node.start_position(),
//             node.end_position(),
//         );

//         // match node.kind() {
//         //     "variable_declaration" => {
//         //         println!(
//         //             "variable_declaration: {:#?}",
//         //             node.utf8_text(self.source.as_bytes())
//         //         );
//         //     }
//         //     &_ => {}
//         // }

//         for child in node.children(&mut node.walk()) {
//             self.walk(&child, depth + 1);
//         }
//     }
// }
