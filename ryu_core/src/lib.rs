#![recursion_limit = "256"]

pub mod ast;
pub mod interpreter;
pub mod lexer;
pub mod parser;
pub mod token;

#[cfg(test)]
mod tests {
    use ast::{print_ast, AstNode, AST};
    use interpreter::Interpreter;
    use lexer::Lexer;
    use parser::Parser;

    use super::*;

    #[test]
    fn lexer_string_literals() {
        let chars = "\"Hello, world!\"".chars().collect::<Vec<char>>();
        let mut lexer = Lexer::from_chars(chars);
        dbg!(lexer.lex().unwrap());
    }

    #[test]
    fn lexer_numbers() {
        let chars = "\"Hello, world!\"5.32 5 -1".chars().collect::<Vec<char>>();
        let mut lexer = Lexer::from_chars(chars);
        dbg!(lexer.lex().unwrap());
    }

    #[test]
    fn lexer_variables() {
        let chars = "let name = 5\nlet i\ni += 5\ni *= 65"
            .chars()
            .collect::<Vec<char>>();
        let mut lexer = Lexer::from_chars(chars);
        dbg!(lexer.lex().unwrap());
    }

    #[test]
    fn lexer_functions() {
        let chars = "fn test() {\nlet hi = \"hello\"\n}\nfn with_args(msg: string, num: int) {\nprint(msg)\nexit()\n}"
            .chars()
            .collect::<Vec<char>>();
        let mut lexer = Lexer::from_chars(chars);
        dbg!(lexer.lex().unwrap());
    }

    #[test]
    fn lexer_f_hello_world() {
        let mut lexer = Lexer::from_file("../tests/hello_world.ryu").unwrap();
        dbg!(lexer.lex().unwrap());
    }

    #[test]
    fn parse_f_hello_world() {
        let mut lexer = Lexer::from_file("../tests/hello_world.ryu").unwrap();
        let tokens = lexer.lex().unwrap();
        dbg!(&tokens);
        let mut parser = Parser::new(tokens);
        let program_node = parser.parse_program().unwrap();
        let ast = AST::new(program_node);
        dbg!(&ast);
    }

    #[test]
    fn parse_f_if() {
        let mut lexer = Lexer::from_file("../tests/if.ryu").unwrap();
        let tokens = lexer.lex();

        let Ok(tokens) = tokens else {
            panic!("{tokens:?}");
        };
        dbg!(&tokens);
        let mut parser = Parser::new(tokens);
        let program_node = parser.parse_program().unwrap();
        let ast = AST::new(program_node);
        dbg!(&ast);
    }

    #[test]
    fn interpret_f_hello_world() {
        let mut lexer = Lexer::from_file("../tests/hello_world.ryu").unwrap();
        let tokens = lexer.lex().unwrap();
        let mut parser = Parser::new(tokens);
        let program_node = parser.parse_program().unwrap();
        let ast = AST::new(program_node);
        let mut interpreter = Interpreter::new();

        let ast_node: Box<dyn AstNode> = Box::new(ast.program.clone());
        print_ast(&ast_node);
        interpreter.run(&ast);
    }

    #[test]
    fn interpret_f_if() {
        let mut lexer = Lexer::from_file("../tests/if.ryu").unwrap();
        let tokens = lexer.lex();

        let Ok(tokens) = tokens else {
            panic!("{tokens:?}");
        };
        let mut parser = Parser::new(tokens);
        let program_node = parser.parse_program().unwrap();
        let ast = AST::new(program_node);
        let mut interpreter = Interpreter::new();

        let ast_node: Box<dyn AstNode> = Box::new(ast.program.clone());
        print_ast(&ast_node);
        interpreter.run(&ast);
    }
}
