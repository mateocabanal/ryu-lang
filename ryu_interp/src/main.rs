use ryu_core::ast::{print_ast, AST};
use ryu_core::interpreter::Interpreter;
use ryu_core::lexer::Lexer;
use ryu_core::parser::Parser;
use ryu_core::token::print_tokens;

struct Args {
    path: Option<String>,
    print_ast: bool,
    print_tokens: bool,
    dry_run: bool,
}

fn main() {
    let mut args = Args {
        path: None,
        print_ast: false,
        print_tokens: false,
        dry_run: false,
    };

    for arg in std::env::args().skip(1) {
        match arg.as_str() {
            "--dry-run" | "-n" => args.dry_run = true,
            "--print-ast" | "-a" => args.print_ast = true,
            "--print-tokens" | "-t" => args.print_tokens = true,
            path => args.path = Some(path.to_string()),
        }
    }

    let Some(file_path) = args.path else {
        panic!("No file was passed!");
    };

    let lexer = Lexer::from_file(&file_path);
    let Ok(mut lexer) = lexer else {
        panic!("File could not be opened!");
    };

    let tokens = lexer.lex();
    let Ok(tokens) = tokens else {
        panic!("Lexer failed: {tokens:?}");
    };

    if args.print_tokens {
        print_tokens(&tokens);
    }

    let prog_node = Parser::new(tokens).parse_program();
    let Ok(prog_node) = prog_node else {
        panic!("Parser failed: {prog_node:?}");
    };

    let ast = AST::new(prog_node);

    if args.print_ast {
        println!("{}", print_ast(&ast));
    }

    if !args.dry_run {
        let mut interpreter = Interpreter::new();
        interpreter.run(&ast);
    }
}
