use crate::{
    ast::*,
    lexer::Lexer,
    token::{FnData, FnInvocation, Token},
};
use std::fmt::{self, write};
use std::{collections::HashMap, error::Error};

#[derive(Debug)]
pub struct ParseError {
    pub message: String,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ParseError: {}", self.message)
    }
}

#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct IdentInfo {
    val: Vec<u8>,
    ident_type: String,
}

impl Error for ParseError {}

/// **Summary of How the Parser Works:**
///
/// The `Parser` is responsible for converting a flat sequence of `Token`s (produced by the lexer)
/// into a structured Abstract Syntax Tree (AST). The parser enforces the grammar of the language,
/// ensuring that tokens appear in a valid order and form valid constructs like functions,
/// statements, and expressions.
///
/// **Workflow:**
/// 1. **Initialization:** The parser is initialized with a vector of tokens and a position index.
/// 2. **Top-Level Parsing (`parse_program`):** Reads multiple top-level constructs (e.g., function
///    declarations) until the end of the token stream.
/// 3. **Function Declarations (`parse_function_decl`):** When a function token is encountered,
///    the parser consumes it, extracts arguments and return types, and then reads a block `{ ... }`
///    containing statements.
/// 4. **Statements (`parse_statement`):** Within a function body, the parser expects statements:
///    - Assignments (e.g., `x += 5`)
///    - Return statements (e.g., `return x`)
///    - Function calls (e.g., `print("Hello")`)
///    - Possibly expressions or other statement forms.
/// 5. **Expressions (`parse_expression` and `parse_expression_from`):** The parser reduces tokens
///    like identifiers, integers, strings, and operators into expression AST nodes (`IntLiteralNode`,
///    `BinaryOpNode`, etc.).
/// 6. **Error Handling:** If unexpected tokens appear or the token stream ends prematurely, the
///    parser returns a `ParseError`.
///
/// In short, the parser reads tokens in a linear fashion, making decisions based on the current
/// token, and builds a tree-like AST structure representing the syntactic structure of the code.
pub struct Parser {
    idents: HashMap<String, IdentInfo>,
    tokens: Vec<Token>,
    pos: usize,
}

impl Parser {
    /// Creates a new Parser with a provided vector of tokens.
    ///
    /// # Arguments
    /// * `tokens` - A vector of tokens produced by the lexer.
    ///
    /// # Returns
    /// A `Parser` instance ready to parse the given tokens.
    pub fn new(tokens: Vec<Token>) -> Self {
        Parser {
            tokens,
            pos: 0,
            idents: HashMap::new(),
        }
    }

    /// Parses the entire program, which consists of zero or more top-level declarations,
    /// typically function definitions.
    ///
    /// # Returns
    /// * `Ok(ProgramNode)` if parsing completes successfully.
    /// * `Err(ParseError)` if it encounters unexpected tokens or incomplete constructs.
    pub fn parse_program(&mut self) -> Result<ProgramNode, Box<dyn Error>> {
        let mut classes = HashMap::new();
        let mut functions = Vec::new();

        // Loop until we run out of tokens or hit an error.
        while !self.is_at_end() {
            match self.peek_token() {
                Some(Token::Import) => {
                    let (extern_fns, extern_classes) = match self.parse_import() {
                        Ok((a, b)) => (a, b),
                        Err(e) => {
                            return Err(Box::new(ParseError {
                                message: format!("Import Error: {e:?}"),
                            }))
                        }
                    };
                    functions.extend(extern_fns);
                    classes.extend(extern_classes);
                }

                Some(Token::Class) => {
                    let class = match self.parse_class_decl() {
                        Ok(c) => c,
                        Err(e) => {
                            return Err(Box::new(ParseError {
                                message: format!("Class Error: {e:?}"),
                            }))
                        }
                    };
                    let class_as_any = class.clone_box();
                    classes.insert(class.name, class_as_any);
                }

                Some(Token::Function(_)) => {
                    // Found a function declaration token, parse it fully.
                    let func = match self.parse_function_decl() {
                        Ok(f) => f,
                        Err(e) => {
                            dbg!(&self.idents);
                            return Err(Box::new(ParseError {
                                message: format!("Function Error: {e:?}"),
                            }));
                        }
                    };
                    functions.push(func);
                }
                Some(Token::NewLine) => {
                    // Newlines at the top-level can be safely ignored.
                    self.next_token();
                }
                Some(other) => {
                    // Encountered a token that doesn't fit top-level constructs.
                    return Err(Box::new(ParseError {
                        message: format!("Unexpected token at top-level: {:?}", other),
                    }));
                }
                None => break, // End of token stream.
            }
        }

        // Return a ProgramNode containing all parsed functions.
        Ok(ProgramNode { functions, classes })
    }

    /// Parses a single function declaration, including its name, arguments, optional return type,
    /// and body enclosed in `{ ... }`.
    ///
    /// # Returns
    /// * `Ok(Box<dyn AstNode>)` containing a `FunctionDeclNode` if successful.
    /// * `Err(ParseError)` if the function structure is incomplete or incorrect.
    fn parse_function_decl(&mut self) -> Result<Box<dyn AstNode>, Box<dyn Error>> {
        // Expect a Function token
        let fn_data = match self.next_token().cloned() {
            Some(Token::Function(data)) => data,
            _ => {
                return Err(Box::new(ParseError {
                    message: "Expected a Function token".to_string(),
                }))
            }
        };

        // After function keyword and info, we expect a left brace to start the body
        self.expect_token(&Token::LeftBrace, "Expected '{' after function declaration")?;

        // Convert FnData arguments into FunctionArgNodes
        let args = self.convert_fn_data_args(&fn_data)?;
        // Parse the statements inside the function body
        let body = self.parse_statements()?;

        // Expect a right brace to close the function body
        self.expect_token(&Token::RightBrace, "Expected '}' at end of function body")?;

        // Construct and return the FunctionDeclNode
        Ok(Box::new(FunctionDeclNode {
            name: fn_data.fn_name.to_string(),
            args,
            return_type: fn_data.return_type.clone(),
            body,
        }))
    }

    /// Parses multiple statements until a `}` token or the end of the file is encountered.
    /// Used for parsing function bodies or other block-like structures.
    ///
    /// # Returns
    /// * `Ok(Vec<Box<dyn AstNode>>)` representing a list of statements.
    /// * `Err(ParseError)` if a statement is malformed.
    fn parse_statements(&mut self) -> Result<Vec<Box<dyn AstNode>>, Box<dyn Error>> {
        let mut stmts = Vec::new();

        // Read statements until we reach a closing brace or run out of tokens.
        while !self.check_token(&Token::RightBrace) && !self.is_at_end() {
            // Skip over newline tokens, which typically don't have semantic value here.
            if self.check_token(&Token::NewLine) {
                self.next_token();
                continue;
            }

            let stmt = self.parse_statement()?;
            stmts.push(stmt);
        }

        Ok(stmts)
    }

    /// Parses a single statement. Statements can include:
    /// - `return` statements
    /// - Assignments (e.g., `x += 5`)
    /// - Standalone function calls (e.g., `print("Hello")`)
    /// - Simple expressions that stand alone as statements (if allowed by the language)
    ///
    /// The parser decides which kind of statement it is based on the next token(s).
    ///
    /// # Returns
    /// * `Ok(Box<dyn AstNode>)` if a valid statement is parsed.
    /// * `Err(ParseError)` if tokens don't form a valid statement.
    fn parse_statement(&mut self) -> Result<Box<dyn AstNode>, Box<dyn Error>> {
        // Check for a return statement first
        if self.check_token(&Token::Return) {
            return self.parse_return();
        }

        if self.check_token(&Token::If) {
            return self.parse_if();
        }

        if self.check_token(&Token::While) {
            return self.parse_while();
        }

        // Check if the next token is a function invocation
        if let Some(Token::FunctionInvocation(inv)) = self.peek_token().cloned() {
            self.next_token(); // consume the invocation token
            let call_node = self.parse_function_invocation(&inv)?;
            return Ok(call_node);
        }

        if let Some(Token::Variable(var_name)) = self.peek_token().cloned() {
            self.next_token();
            let assign_node = self.parse_ident_initialization(&var_name)?;
            return Ok(assign_node);
        }

        // Otherwise, we might have an identifier leading to an assignment or expression
        if let Some(Token::Ident(name)) = self.peek_token().cloned() {
            let ident_name = name.to_string();

            // Look at the next token to determine if it's an assignment operator or a binary operator
            match self.peek_token_n(1) {
                Some(Token::MulAssign) => {
                    self.next_token(); // consume ident
                    self.next_token(); // consume '*='
                    let right_expr = self.parse_expression()?;
                    let node = AssignmentNode {
                        operator: AssignOperator::MulAssign,
                        left: Box::new(IdentNode { name: ident_name }),
                        right: right_expr,
                    };
                    Ok(Box::new(node))
                }
                Some(Token::AddAssign) => {
                    self.next_token(); // consume ident
                    self.next_token(); // consume '+='
                    let right_expr = self.parse_expression()?;
                    let node = AssignmentNode {
                        operator: AssignOperator::AddAssign,
                        left: Box::new(IdentNode { name: ident_name }),
                        right: right_expr,
                    };
                    Ok(Box::new(node))
                }
                Some(Token::SubAssign) => {
                    self.next_token(); // consume ident
                    self.next_token(); // consume '-='
                    let right_expr = self.parse_expression()?;
                    let node = AssignmentNode {
                        operator: AssignOperator::SubAssign,
                        left: Box::new(IdentNode { name: ident_name }),
                        right: right_expr,
                    };
                    Ok(Box::new(node))
                }
                Some(Token::Period) => self.parse_class_member_access(),
                Some(Token::Assign) => {
                    self.next_token(); // consume ident
                    self.next_token(); // consume '='

                    let right_expr = self.parse_expression()?;
                    let node = AssignmentNode {
                        operator: AssignOperator::Assign,
                        left: Box::new(IdentNode { name: ident_name }),
                        right: right_expr,
                    };
                    Ok(Box::new(node))
                }
                Some(Token::Add) | Some(Token::Sub) | Some(Token::Mul) | Some(Token::Div) => {
                    // We have something like `x + y` or `x * y`, etc.
                    // Treat it as an expression statement.
                    self.next_token(); // consume ident
                    let left_node = Box::new(IdentNode { name: ident_name });
                    let expr_node = self.parse_expression_from(left_node)?;
                    Ok(expr_node)
                }
                // TODO: Fill out scope operators
                Some(Token::ScopeOperator) => {
                    self.next_token();
                    let right = self.parse_equality()?;
                    dbg!(&right);

                    let r_as_any = right.as_any();

                    if let Some(function) = r_as_any.downcast_ref::<FunctionCallNode>().cloned() {
                        let method = Box::new(IdentNode {
                            name: function.name,
                        });
                        let args = function.args;
                        Ok(Box::new(ClassMethodCall {
                            object: Box::new(IdentNode { name: ident_name }),
                            method,
                            args,
                        }))
                    } else {
                        Err(Box::new(ParseError {
                            message:
                                "Expected either a Ident or FunctionCall after scoped operator"
                                    .to_string(),
                        }))
                    }
                }

                Some(Token::LeftSquareBracket) => {
                    self.next_token().unwrap();
                    self.next_token().unwrap();
                    let index = self.parse_expression()?;
                    dbg!(&index);
                    self.expect_token(
                        &Token::RightSquareBracket,
                        "Expected ']' before assignment",
                    )?;

                    let operator = match self.next_token().cloned() {
                        Some(Token::Assign) => AssignOperator::Assign,
                        Some(_) => {
                            return Err(Box::new(ParseError {
                                message: "Expected assignment operation".to_string(),
                            }))
                        }

                        None => {
                            return Err(Box::new(ParseError {
                                message: "Expected assignment operation".to_string(),
                            }))
                        }
                    };

                    let array_access_node = Box::new(ArrayAccessNode {
                        arr_name: Box::new(IdentNode { name: ident_name }),
                        index,
                    });

                    Ok(Box::new(ArrayAssignmentNode {
                        operator,
                        left: array_access_node,
                        right: self.parse_expression()?,
                    }))
                }
                _ => Err(Box::new(ParseError {
                    message: format!(
                        "Expected operator or statement continuation after {name:?}, got {:?}",
                        self.peek_token()
                    ),
                })),
            }
        } else {
            Err(Box::new(ParseError {
                message: format!("Unknown statement type: {:?}", self.peek_token().unwrap()),
            }))
        }
    }

    fn parse_class_member_assign(&mut self) -> Result<Box<dyn AstNode>, Box<dyn Error>> {
        let lhs = self.parse_class_member_access()?;

        let operator = match self.next_token() {
            Some(Token::Assign) => AssignOperator::Assign,
            Some(Token::AddAssign) => AssignOperator::AddAssign,
            Some(Token::SubAssign) => AssignOperator::SubAssign,
            Some(Token::MulAssign) => AssignOperator::MulAssign,
            Some(Token::DivAssign) => AssignOperator::DivAssign,
            _ => {
                return Err(Box::new(ParseError {
                    message: "Operator does not assign!".to_string(),
                }))
            }
        };

        let expr = self.parse_expression()?;

        Ok(Box::new(AssignmentNode {
            operator,
            left: lhs,
            right: expr,
        }))
    }

    /// Parse and instantiate a class type
    fn parse_class_decl(&mut self) -> Result<Box<ClassDeclNode>, Box<dyn Error>> {
        self.next_token(); // Consume class token
        let Some(Token::Ident(class_name)) = self.next_token().cloned() else {
            return Err(Box::new(ParseError {
                message: "Expected Ident after Class".to_string(),
            }));
        };
        self.expect_token(
            &Token::LeftBrace,
            "Expected a Left Brace following the declaration of a class",
        )?;

        let mut members = Vec::new();

        while !self.check_token(&Token::RightBrace) && !self.is_at_end() {
            if self.check_token(&Token::NewLine) {
                self.next_token();
                continue;
            }

            match self.parse_class_member() {
                Ok(t) => members.push(t),
                Err(e) => {
                    println!("Failed parsing {class_name:?} class");
                    return Err(e);
                }
            }
        }

        self.next_token(); // Consume Right Brace

        Ok(Box::new(ClassDeclNode {
            name: Box::new(IdentNode { name: class_name }),
            tokens: members,
        }))
    }

    fn parse_class_member(&mut self) -> Result<Box<dyn AstNode>, Box<dyn Error>> {
        match self.peek_token() {
            Some(Token::Variable(_)) => self.parse_class_field(),
            Some(Token::Function(_)) => self.parse_class_method(),

            Some(e) => Err(Box::new(ParseError {
                message: format!("Unexpected token: {e:?}"),
            })),

            None => panic!("No token found!"),
        }
    }

    fn parse_class_field(&mut self) -> Result<Box<dyn AstNode>, Box<dyn Error>> {
        let Some(Token::Variable(var_name)) = self.next_token().cloned() else {
            return Err(Box::new(ParseError {
                message: "Expected field definition".to_string(),
            }));
        };

        self.expect_token(&Token::Colon, "Expected colon after field name")?;

        let var_type = match self.next_token() {
            Some(Token::Ident(var_type)) => Box::new(IdentNode {
                name: var_type.to_string(),
            }),

            Some(Token::LeftSquareBracket) => {
                let Some(Token::Ident(arr_type)) = self.next_token().cloned() else {
                    return Err(Box::new(ParseError {
                        message: "Expected type inside of array".to_string(),
                    }));
                };

                self.expect_token(
                    &Token::RightSquareBracket,
                    "Expected RightSquareBracket after array declaration",
                )?;

                Box::new(IdentNode {
                    name: format!("[{arr_type}]"),
                })
            }

            _ => {
                return Err(Box::new(ParseError {
                    message: "Expected field type".to_string(),
                }))
            }
        };

        Ok(Box::new(ClassFieldNode {
            var_type: Box::new(IdentNode {
                name: var_type.name,
            }),
            left: Box::new(IdentNode {
                name: var_name.to_string(),
            }),
            right: Vec::new(),
        }))
    }

    fn parse_class_method(&mut self) -> Result<Box<dyn AstNode>, Box<dyn Error>> {
        let Some(Token::Function(fn_data)) = self.next_token().cloned() else {
            return Err(Box::new(ParseError {
                message: "Expected method definition".to_string(),
            }));
        };

        self.expect_token(
            &Token::LeftBrace,
            "Expected Left Brace after method declaration",
        )?;

        // Convert FnData arguments into FunctionArgNodes
        let args = self.convert_method_data_args(&fn_data)?;
        // Parse the statements inside the function body
        let body = self.parse_statements()?;

        self.expect_token(
            &Token::RightBrace,
            "Expected Right Brace after method definition",
        )?;

        Ok(Box::new(ClassMethodNode {
            name: Box::new(IdentNode {
                name: fn_data.fn_name,
            }),
            return_type: Box::new(IdentNode {
                name: fn_data.return_type.unwrap_or("unit".to_string()),
            }),
            is_static: args.is_empty(),
            args,
            body,
        }))
    }

    /// Converts `FnData` from a `Function` token into a vector of `FunctionArgNode`.
    /// This extracts argument names and types from the `arguments` field of `FnData`.
    ///
    /// # Arguments
    /// * `fn_data` - The `FnData` structure containing arguments info.
    ///
    /// # Returns
    /// * `Ok(Vec<FunctionArgNode>)` if arguments are successfully converted.
    fn convert_method_data_args(
        &self,
        fn_data: &FnData,
    ) -> Result<Vec<ClassMethodArgNode>, Box<dyn Error>> {
        let mut args = Vec::new();
        if let Some(map) = &fn_data.arguments {
            for (name, ty) in map {
                if name == "self" {
                    args.push(ClassMethodArgNode {
                        name: Box::new(IdentNode {
                            name: String::from("self"),
                        }),
                        arg_type: Box::new(IdentNode {
                            name: "Self".to_string(),
                        }),
                    });
                } else {
                    args.push(ClassMethodArgNode {
                        name: Box::new(IdentNode {
                            name: name.to_string(),
                        }),
                        arg_type: Box::new(IdentNode {
                            name: ty.to_string(),
                        }),
                    });
                }
            }
        }
        Ok(args)
    }

    /// Load external source file
    #[allow(clippy::type_complexity)]
    fn parse_import(
        &mut self,
    ) -> Result<
        (
            Vec<Box<dyn AstNode>>,
            HashMap<Box<IdentNode>, Box<dyn AstNode>>,
        ),
        Box<dyn Error>,
    > {
        self.next_token(); // Consumes Import token
        let Some(Token::Ident(file_path)) = self.next_token() else {
            return Err(Box::new(ParseError {
                message: "Import syntax error".to_string(),
            }));
        };

        let file_source = if let Ok(c) = std::fs::read_to_string(file_path.to_owned() + ".ryu") {
            c
        } else if let Ok(c) = std::fs::read_to_string(format!(
            "{}/stdlib/{file_path}.ryu",
            std::env::current_dir().unwrap().to_str().unwrap()
        )) {
            c
        } else {
            return Err(Box::new(ParseError {
                message: "Import file not found!".to_string(),
            }));
        };

        let mut sub_lexer = Lexer::from_chars(file_source.chars().collect());
        let Ok(tokens) = sub_lexer.lex() else {
            return Err(Box::new(ParseError {
                message: "Lexicial error in import".to_string(),
            }));
        };
        let mut sub_parser = Parser::new(tokens);
        let sub_prog = sub_parser.parse_program()?;

        Ok((sub_prog.functions, sub_prog.classes))
    }

    /// Parses a return statement. A return statement may be followed by an optional expression,
    /// or it might be just `return` on its own.
    ///
    /// # Returns
    /// * `Ok(Box<ReturnNode>)` if a valid return statement is parsed.
    /// * `Err(ParseError)` if there's a syntactic error.
    fn parse_return(&mut self) -> Result<Box<dyn AstNode>, Box<dyn Error>> {
        self.next_token(); // consume the 'return' keyword

        if let Some(Token::NewLine) = self.peek_token() {
            Ok(Box::new(ReturnNode { value: None }))
        } else {
            let value = self.parse_expression()?;
            Ok(Box::new(ReturnNode { value: Some(value) }))
        }
    }

    /// parse_expression:
    ///
    /// Handles the lowest-precedence binary operators (+ and -).
    /// It first parses a `term`, then repeatedly checks if the next token is `+` or `-`.
    /// If so, it consumes that token, parses another term, and wraps them in a BinaryOpNode.
    pub fn parse_expression(&mut self) -> Result<Box<dyn AstNode>, Box<dyn Error>> {
        self.parse_scope_opers()
    }

    fn parse_scope_opers(&mut self) -> Result<Box<dyn AstNode>, Box<dyn Error>> {
        let mut node = self.parse_equality()?;

        loop {
            if self.check_token(&Token::Period) {
                dbg!(&node);
                self.next_token(); // Consume the '.'

                // Parse the right-hand side (could be a field or a function call)
                let right = self.parse_equality()?;

                // Now we need to check the type of 'node' (the left-hand side)
                node = match node.as_any().downcast_ref::<IdentNode>() {
                    Some(ident_node) if ident_node.name == "self" => {
                        // Special handling for 'self.field'
                        if let Some(field_name) = right.as_any().downcast_ref::<IdentNode>() {
                            Box::new(SelfFieldAccessNode {
                                field: Box::new(field_name.clone()),
                            })
                        } else {
                            return Err(Box::new(ParseError {
                                message: "Invalid expression after 'self.'".to_string(),
                            }));
                        }
                    }
                    _ => {
                        // 'node' is not 'self', so proceed as before
                        match right.as_any().downcast_ref::<FunctionCallNode>() {
                            Some(function) => {
                                // Method call
                                Box::new(MethodCallNode {
                                    object: node.clone_box(),
                                    method: Box::new(IdentNode {
                                        name: function.name.clone(),
                                    }),
                                    args: function.args.clone(),
                                })
                            }
                            None => {
                                // Not a function call, so it must be a field access
                                match right.as_any().downcast_ref::<IdentNode>() {
                                    Some(field_name) => Box::new(ClassFieldAccess {
                                        member: node.clone_box(),
                                        field: Box::new(field_name.clone()),
                                    }),
                                    None => {
                                        return Err(Box::new(ParseError {
                                            message: "Invalid expression after '.'".to_string(),
                                        }));
                                    }
                                }
                            }
                        }
                    }
                };
            } else if self.check_token(&Token::ScopeOperator) {
                self.next_token(); // Consume the '::'
                let right = self.parse_equality()?;

                let r_as_any = right.as_any();

                if let Some(function) = r_as_any.downcast_ref::<FunctionCallNode>().cloned() {
                    // Static method call
                    // Ensure the left-hand side is an IdentNode (class name)
                    if let Some(class_name) = node.as_any().downcast_ref::<IdentNode>() {
                        node = Box::new(StaticMethodCallNode {
                            class: Box::new(class_name.clone()), // Correctly store IdentNode
                            method: Box::new(IdentNode {
                                name: function.name,
                            }),
                            args: function.args,
                        });
                    } else {
                        return Err(Box::new(ParseError {
                            message: "Expected a class name before '::'".to_string(),
                        }));
                    }
                } else {
                    return Err(Box::new(ParseError {
                        message: "Expected a function call after '::'".to_string(),
                    }));
                }
            } else {
                break;
            }
        }

        Ok(node)
    }

    pub fn parse_equality(&mut self) -> Result<Box<dyn AstNode>, Box<dyn Error>> {
        let mut node = self.parse_add_sub()?;

        loop {
            if self.check_token(&Token::Equal) {
                self.next_token();
                let right = self.parse_add_sub()?;
                node = Box::new(BinaryOpNode {
                    operator: BinaryOperator::Equal,
                    left: node,
                    right,
                });
            } else if self.check_token(&Token::LessEqual) {
                self.next_token();
                println!("next: {:?}", self.peek_token());
                let right = self.parse_add_sub()?;
                node = Box::new(BinaryOpNode {
                    operator: BinaryOperator::LessEqual,
                    left: node,
                    right,
                });
            } else if self.check_token(&Token::Less) {
                self.next_token();
                let right = self.parse_add_sub()?;
                node = Box::new(BinaryOpNode {
                    operator: BinaryOperator::Less,
                    left: node,
                    right,
                });
            } else {
                break;
            }
        }

        Ok(node)
    }

    pub fn parse_add_sub(&mut self) -> Result<Box<dyn AstNode>, Box<dyn Error>> {
        let mut node = self.parse_term()?;

        loop {
            if self.check_token(&Token::Add) {
                self.next_token(); // consume '+'
                let right = self.parse_term()?;
                node = Box::new(BinaryOpNode {
                    operator: BinaryOperator::Add,
                    left: node,
                    right,
                });
            } else if self.check_token(&Token::Sub) {
                self.next_token(); // consume '-'
                let right = self.parse_term()?;
                node = Box::new(BinaryOpNode {
                    operator: BinaryOperator::Sub,
                    left: node,
                    right,
                });
            } else {
                break; // No more + or -
            }
        }

        Ok(node)
    }

    /// parse_term:
    ///
    /// Handles the next level of precedence: `*` and `/`.
    /// It first parses a `factor`, then checks if the next token is `*` or `/`.
    /// If so, it consumes that token, parses another factor, and forms a BinaryOpNode.
    fn parse_term(&mut self) -> Result<Box<dyn AstNode>, Box<dyn Error>> {
        let mut node = self.parse_factor()?;

        loop {
            if self.check_token(&Token::Mul) {
                self.next_token(); // consume '*'
                let right = self.parse_factor()?;
                node = Box::new(BinaryOpNode {
                    operator: BinaryOperator::Mul,
                    left: node,
                    right,
                });
            } else if self.check_token(&Token::Div) {
                self.next_token(); // consume '/'
                let right = self.parse_factor()?;
                node = Box::new(BinaryOpNode {
                    operator: BinaryOperator::Div,
                    left: node,
                    right,
                });
            } else {
                break; // No more * or /
            }
        }

        Ok(node)
    }

    /// parse_factor:
    ///
    /// Handles the "atoms" of expressions: integers, strings, identifiers,
    /// parentheses, and function invocations.
    ///
    /// For the given token sequence:
    /// - `Integer(val)` -> IntLiteralNode
    /// - `String(val)` -> StringLiteralNode
    /// - `Ident(name)` -> IdentNode
    /// - `FunctionInvocation(inv)` -> parse_function_invocation(inv)
    /// - `(` -> parse_expression() then expect `)`
    fn parse_factor(&mut self) -> Result<Box<dyn AstNode>, Box<dyn Error>> {
        match self.peek_token().cloned() {
            Some(Token::Integer(val)) => {
                self.next_token();
                Ok(Box::new(IntLiteralNode { value: val as i64 }))
            }
            Some(Token::String(s)) => {
                self.next_token();
                Ok(Box::new(StringLiteralNode {
                    value: s.to_string(),
                }))
            }
            Some(Token::Char(c)) => {
                self.next_token();
                Ok(Box::new(CharLiteralNode { value: c }))
            }
            Some(Token::True) => {
                self.next_token();
                Ok(Box::new(BoolLiteralNode { value: true }))
            }
            Some(Token::False) => {
                self.next_token();
                Ok(Box::new(BoolLiteralNode { value: false }))
            }
            // This will try to match a ArrayLiteral
            Some(Token::LeftSquareBracket) => {
                self.next_token();
                match self.peek_token().cloned() {
                    Some(Token::Ident(_)) => self.parse_array_literal(),

                    Some(_) => Err(Box::new(ParseError {
                        message: format!(
                            "Expected array access or array literal, got: {:?}",
                            self.peek_token()
                        ),
                    })),
                    None => Err(Box::new(ParseError {
                        message: "Could not get next token".to_string(),
                    })),
                }
            }
            Some(Token::Ident(name)) => {
                match self.peek_token_n(1) {
                    Some(&Token::ScopeOperator) => {
                        let Some(Token::FunctionInvocation(member_method)) =
                            self.peek_token_n(2).cloned()
                        else {
                            return Err(Box::new(ParseError {
                                message: "Expected member after ScopeOperator".to_string(),
                            }));
                        };

                        self.next_token();
                        self.next_token();
                        self.next_token();

                        let parsed_fn_invoke = self
                            .parse_function_invocation(&member_method)?
                            .as_any()
                            .downcast_ref::<FunctionCallNode>()
                            .cloned()
                            .unwrap();

                        Ok(Box::new(StaticMethodCallNode {
                            class: Box::new(IdentNode { name }),
                            method: Box::new(IdentNode {
                                name: parsed_fn_invoke.name,
                            }),
                            args: parsed_fn_invoke.args,
                        }))
                    }

                    Some(&Token::LeftBrace) => self.parse_class_member_initialization(),

                    Some(&Token::LeftSquareBracket) => self.parse_array_access(),

                    Some(&Token::Period) => {
                        // Identifier followed by a Period (.)
                        // self.next_token(); // Consume the identifier
                        // self.next_token(); // Consume the '.'

                        if name == "self" {
                            self.parse_self_field_access()
                        } else {
                            self.parse_class_member_access()
                        }
                    }

                    // Return value of Ident otherwise
                    _ => {
                        self.next_token();
                        Ok(Box::new(IdentNode { name }))
                    }
                }
            }

            Some(Token::FunctionInvocation(inv)) => {
                // Direct function invocation token
                if let Some(Token::Period) = self.peek_token_n(1).cloned() {
                    return self.parse_class_member_access();
                }
                self.next_token();
                self.parse_function_invocation(&inv)
            }
            Some(Token::LeftBracket) => {
                // Parenthesized expression
                self.next_token(); // consume '('
                let node = self.parse_expression()?;
                self.expect_token(&Token::RightBracket, "Expected ')' after expression")?;
                Ok(node)
            }
            Some(Token::If) => {
                self.next_token(); // consume `if`
                let condition = self.parse_expression()?;
                dbg!(&condition);

                panic!();
            }
            other => Err(Box::new(ParseError {
                message: format!("Expected factor, got {:?}", other),
            })),
        }
    }

    // Helper function to parse 'self.field' accesses
    fn parse_self_field_access(&mut self) -> Result<Box<dyn AstNode>, Box<dyn Error>> {
        self.next_token(); // Consume 'self'
        self.next_token(); // Consume '.'
        if let Some(Token::Ident(field_name)) = self.next_token() {
            Ok(Box::new(SelfFieldAccessNode {
                field: Box::new(IdentNode {
                    name: field_name.to_string(),
                }),
            }))
        } else {
            Err(Box::new(ParseError {
                message: "Expected field name after 'self.'".to_string(),
            }))
        }
    }

    fn parse_array_literal(&mut self) -> Result<Box<dyn AstNode>, Box<dyn Error>> {
        let Some(Token::Ident(arr_type)) = self.next_token().cloned() else {
            return Err(Box::new(ParseError {
                message: "Expected Ident for array type".to_string(),
            }));
        };

        self.expect_token(&Token::Colon, "Expected Colon after array type")?;

        let mut values: Vec<Box<dyn AstNode>> = Vec::new();
        while !matches!(self.peek_token(), Some(&Token::RightSquareBracket)) {
            let Some(tok) = self.peek_token() else {
                return Err(Box::new(ParseError {
                    message:
                        "Failed to get next token, when right square bracket has not yet been seen"
                            .to_string(),
                }));
            };
            if let Token::Comma = tok {
                self.next_token();
                continue;
            }

            values.push(self.parse_expression()?);
        }

        self.next_token(); // Consume Right Square Bracket

        let arr_type = Box::new(IdentNode {
            name: arr_type.to_string(),
        });

        Ok(Box::new(ArrayLiteralNode { arr_type, values }))
    }

    /// Parse indexing operator
    fn parse_array_access(&mut self) -> Result<Box<dyn AstNode>, Box<dyn Error>> {
        let Some(Token::Ident(var_name)) = self.next_token().cloned() else {
            return Err(Box::new(ParseError {
                message: "Expected Ident for array access".to_string(),
            }));
        };

        self.expect_token(&Token::LeftSquareBracket, "Expected Left Square Bracket")?;

        let index = self.parse_expression()?;

        self.expect_token(&Token::RightSquareBracket, "Expected Right Square Bracket")?;

        Ok(Box::new(ArrayAccessNode {
            arr_name: Box::new(IdentNode { name: var_name }),
            index,
        }))
    }

    fn parse_class_member_access(&mut self) -> Result<Box<dyn AstNode>, Box<dyn Error>> {
        let Some(Token::Ident(var_name)) = self.peek_token().cloned() else {
            return Err(Box::new(ParseError {
                message: format!(
                    "Expected Ident for member access, got {:?}",
                    self.peek_token()
                ),
            }));
        };

        self.next_token(); // Actually consume the Ident token

        self.expect_token(&Token::Period, "Expected Period")?;

        let field: Box<dyn AstNode> = match self.next_token().cloned() {
            Some(Token::Ident(var_name)) => Box::new(IdentNode { name: var_name }),

            Some(Token::FunctionInvocation(fn_invoke)) => {
                let fn_decl_as_any = self.parse_function_invocation(&fn_invoke)?;

                let fn_decl = fn_decl_as_any
                    .as_any()
                    .downcast_ref::<FunctionCallNode>()
                    .unwrap();

                Box::new(ClassMethodCall {
                    object: Box::new(IdentNode {
                        name: var_name.clone(),
                    }),
                    method: Box::new(IdentNode {
                        name: fn_decl.name.clone(),
                    }),
                    args: fn_decl.args.clone(),
                })
            }

            Some(tok) => {
                return Err(Box::new(ParseError {
                    message: format!(
                        "Expected either an Ident or FnInvoke as class field, got {:?}",
                        tok
                    ),
                }));
            }

            None => {
                return Err(Box::new(ParseError {
                    message: "Expected either an Ident or FnInvoke as class field, but no more tokens left?!".to_string()
                }));
            }
        };

        // Parse as a regular field access
        let class_field_node = Box::new(ClassFieldAccess {
            member: Box::new(IdentNode { name: var_name }),
            field,
        });

        if let Some(Token::Assign) = self.peek_token().cloned() {
            self.next_token(); // Consume '='

            let right = self.parse_expression()?;

            Ok(Box::new(AssignmentNode {
                operator: AssignOperator::Assign,
                left: class_field_node,
                right,
            }))
        } else {
            Ok(class_field_node)
        }
    }

    /// Parse initialization of class via Left Brace
    fn parse_class_member_initialization(&mut self) -> Result<Box<dyn AstNode>, Box<dyn Error>> {
        let Some(Token::Ident(class_name)) = self.next_token().cloned() else {
            return Err(Box::new(ParseError {
                message: "Expected Ident for class name".to_string(),
            }));
        };

        self.expect_token(
            &Token::LeftBrace,
            "Expected Left Brace to initialize member",
        )?;

        while let Some(&Token::NewLine) = self.peek_token() {
            self.next_token();
        }

        let mut args = HashMap::new();
        while !matches!(self.peek_token(), Some(&Token::RightBrace)) {
            if let Some(&Token::NewLine) = self.peek_token() {
                self.next_token();
                continue;
            }

            let arg_name = match self.next_token().cloned() {
                Some(Token::Ident(n)) => n,
                Some(e) => {
                    return Err(Box::new(ParseError {
                        message: format!("Expected Ident in member init, but got {e:?}"),
                    }));
                }

                None => {
                    return Err(Box::new(ParseError {
                        message: "Expected a token".to_string(),
                    }));
                }
            };

            self.expect_token(&Token::Colon, "Expected Colon after class field")?;

            let right = self.parse_argument_value()?;

            if let Some(&Token::Comma) = self.peek_token() {
                self.next_token();
            }

            args.insert(
                Box::new(IdentNode {
                    name: arg_name.to_string(),
                }),
                right,
            );
        }

        self.next_token();

        Ok(Box::new(ClassMemberInit {
            class: Box::new(IdentNode {
                name: class_name.to_string(),
            }),
            args,
        }))
    }

    // Add a new helper function to parse argument values
    fn parse_argument_value(&mut self) -> Result<Box<dyn AstNode>, Box<dyn Error>> {
        let mut tokens = Vec::new();
        let mut nested_parens = 0;

        while let Some(token) = self.peek_token() {
            match token {
                Token::LeftSquareBracket | Token::LeftBrace | Token::LeftBracket => {
                    nested_parens += 1;
                    tokens.push(token.clone());
                    self.next_token();
                }

                Token::RightSquareBracket | Token::RightBracket => {
                    nested_parens -= 1;
                    tokens.push(token.clone());
                    self.next_token();
                }

                Token::Comma => {
                    if nested_parens == 0 {
                        break;
                    } else {
                        tokens.push(token.clone());
                        self.next_token();
                    }
                }

                Token::RightBrace => {
                    if nested_parens == 0 {
                        break;
                    } else {
                        tokens.push(token.clone());
                        self.next_token();
                    }
                }
                _ => {
                    tokens.push(token.clone());
                    self.next_token();
                }
            }
        }

        if tokens.is_empty() {
            return Err(Box::new(ParseError {
                message: "Expected argument value".to_string(),
            }));
        }

        if *tokens.last().unwrap() == Token::Comma {
            tokens.remove(tokens.len() - 1);
        }

        // Parse the collected tokens as an expression
        let mut parser = Parser::new(tokens);
        parser.parse_expression()
    }

    /// Parse a while block
    fn parse_while(&mut self) -> Result<Box<dyn AstNode>, Box<dyn Error>> {
        self.expect_token(&Token::While, "Expected `while`")?;
        let condition = self.parse_expression()?;

        let then_block = self.parse_block()?;

        Ok(Box::new(WhileNode {
            condition,
            then_block,
        }))
    }

    /// Parse a stream of tokens inside a if block
    fn parse_if(&mut self) -> Result<Box<dyn AstNode>, Box<dyn Error>> {
        self.expect_token(&Token::If, "Expected `if`")?;
        let condition = self.parse_expression()?;

        let then_block = self.parse_block()?;

        let else_block = if self.check_token(&Token::Else) {
            self.next_token();
            Some(self.parse_block()?)
        } else {
            None
        };

        Ok(Box::new(IfNode {
            condition,
            then_block,
            else_block,
        }))
    }

    fn parse_block(&mut self) -> Result<Vec<Box<dyn AstNode>>, Box<dyn std::error::Error>> {
        // Expect a left brace
        self.expect_token(&Token::LeftBrace, "Expected '{' at start of block")?;

        let mut statements = Vec::new();

        // Continue until we find a RightBrace or run out of tokens
        while !self.check_token(&Token::RightBrace) && !self.is_at_end() {
            // You might want to ignore NewLine tokens here
            if self.check_token(&Token::NewLine) {
                self.next_token(); // skip newlines
                continue;
            }

            let stmt = self.parse_statement()?;
            statements.push(stmt);
        }

        // Expect a closing brace '}'
        self.expect_token(&Token::RightBrace, "Expected '}' at end of block")?;
        Ok(statements)
    }

    /// parse_function_invocation:
    ///
    /// Given a `FnInvocation` from a `FunctionInvocation` token, parse its arguments and produce a `FunctionCallNode`.
    /// The arguments array may contain tokens that represent integers, strings, identifiers, or even nested `FunctionInvocation` tokens.
    /// We assume each argument can be parsed as a full expression. If arguments are only single tokens, simplify accordingly.
    fn parse_function_invocation(
        &mut self,
        inv: &FnInvocation,
    ) -> Result<Box<dyn AstNode>, Box<dyn Error>> {
        let mut arg_nodes = Vec::new();

        if let Some(args) = &inv.arguments {
            for arg_token in args {
                // If arguments can be full expressions, you may need a mini-parser or integrate here.
                // If arguments are single tokens, a simple match is enough.
                // Let's assume arguments can be expressions. Then we’d need logic to parse them:

                // One approach: Turn `arg_token` into a temporary token stream and call `parse_expression`.
                // But we only have one token. If arguments themselves can be `FunctionInvocation`, `Integer`, `String`, or `Ident`,
                // we can do something like:

                let mut parser = Parser::new(arg_token.clone());
                let arg_node = parser.parse_expression()?;
                arg_nodes.push(arg_node);
            }
        }

        Ok(Box::new(FunctionCallNode {
            name: inv.fn_name.to_string(),
            args: arg_nodes,
        }))
    }

    /// Parses an expression starting from an already-known left-hand side node (`left_node`)
    /// followed by a binary operator and a right-hand side expression.
    ///
    /// This method is a stand-in for a proper expression parser. It assumes one binary operator
    /// and one operand follow.
    ///
    /// # Arguments
    /// * `left_node` - The already parsed left-hand side AST node.
    ///
    /// # Returns
    /// * `Ok(Box<BinaryOpNode>)` representing a binary operation.
    /// * `Err(ParseError)` if the expected operator or right-hand expression is missing or invalid.
    fn parse_expression_from(
        &mut self,
        left_node: Box<dyn AstNode>,
    ) -> Result<Box<dyn AstNode>, Box<dyn Error>> {
        // Identify the next token as a binary operator
        let operator = match self.peek_token().cloned() {
            Some(Token::Add) => {
                self.next_token();
                BinaryOperator::Add
            }
            Some(Token::Sub) => {
                self.next_token();
                BinaryOperator::Sub
            }
            Some(Token::Mul) => {
                self.next_token();
                BinaryOperator::Mul
            }
            Some(Token::Div) => {
                self.next_token();
                BinaryOperator::Div
            }
            other => {
                return Err(Box::new(ParseError {
                    message: format!("Expected binary operator, got {:?}", other),
                }))
            }
        };

        // Parse the right-hand side of the binary expression
        let right_expr = self.parse_expression()?;

        // Return a BinaryOpNode representing the entire expression
        Ok(Box::new(BinaryOpNode {
            operator,
            left: left_node,
            right: right_expr,
        }))
    }

    /// Parses and initializes variables with their respective types
    fn parse_ident_initialization(
        &mut self,
        var_name: &str,
    ) -> Result<Box<dyn AstNode>, Box<dyn Error>> {
        let left = Box::new(IdentNode {
            name: var_name.to_string(),
        });

        self.expect_token(&Token::Colon, "Expected colon after variable declaration")?;

        let ident_type = match self.next_token().cloned() {
            Some(Token::Ident(i)) => i,
            Some(Token::LeftSquareBracket) => {
                let Some(Token::Ident(i)) = self.next_token().cloned() else {
                    return Err(Box::new(ParseError {
                        message: "Expected type after Left Square Bracket".to_string(),
                    }));
                };

                self.expect_token(
                    &Token::RightSquareBracket,
                    "Expected Right Square Bracket to close out type",
                )?;

                i
            }

            _ => {
                return Err(Box::new(ParseError {
                    message: "Expected type after variable declaration".to_string(),
                }));
            }
        };

        // Record defined ident
        self.idents.insert(
            var_name.to_string(),
            IdentInfo {
                val: vec![],
                ident_type,
            },
        );

        if *self.peek_token().unwrap() != Token::Assign {
            return Ok(Box::new(VariableInitNode {
                left,
                right: Box::new(IntLiteralNode { value: 0 }),
            }));
        } else {
            self.next_token();
        }

        let right = self.parse_expression()?;

        Ok(Box::new(VariableInitNode { left, right }))
    }

    /// Converts `FnData` from a `Function` token into a vector of `FunctionArgNode`.
    /// This extracts argument names and types from the `arguments` field of `FnData`.
    ///
    /// # Arguments
    /// * `fn_data` - The `FnData` structure containing arguments info.
    ///
    /// # Returns
    /// * `Ok(Vec<FunctionArgNode>)` if arguments are successfully converted.
    fn convert_fn_data_args(
        &self,
        fn_data: &FnData,
    ) -> Result<Vec<FunctionArgNode>, Box<dyn Error>> {
        let mut args = Vec::new();
        if let Some(map) = &fn_data.arguments {
            for (name, ty) in map {
                args.push(FunctionArgNode {
                    name: name.to_string(),
                    arg_type: ty.to_string(),
                });
            }
        }
        Ok(args)
    }

    /// Peeks at the current token without consuming it.
    ///
    /// # Returns
    /// * `Some(&Token)` if a token is available at the current position.
    /// * `None` if we have reached the end of the token stream.
    fn peek_token(&self) -> Option<&Token> {
        self.tokens.get(self.pos)
    }

    fn peek_token_n(&self, n: usize) -> Option<&Token> {
        self.tokens.get(self.pos + n)
    }
    /// Consumes and returns the current token, then advances to the next one.
    ///
    /// # Returns
    /// * `Some(&Token)` for the consumed token.
    /// * `None` if at end of token stream.
    fn next_token(&mut self) -> Option<&Token> {
        let tok = self.tokens.get(self.pos);
        if tok.is_some() {
            self.pos += 1;
        }
        tok
    }

    /// Checks if the current token matches an expected token.
    ///
    /// # Arguments
    /// * `expected` - A reference to the token we expect at the current position.
    ///
    /// # Returns
    /// * `true` if the current token equals the expected token.
    /// * `false` otherwise.
    fn check_token(&self, expected: &Token) -> bool {
        matches!(self.peek_token(), Some(tok) if tok == expected)
    }

    /// Consumes a token if it matches the expected token. Returns an error if not.
    ///
    /// # Arguments
    /// * `expected` - The token we expect.
    /// * `err_msg` - A custom error message if the token doesn't match.
    ///
    /// # Returns
    /// * `Ok(())` if the expected token was found.
    /// * `Err(ParseError)` if a different token or end of tokens is encountered.
    fn expect_token(&mut self, expected: &Token, err_msg: &str) -> Result<(), Box<dyn Error>> {
        match self.peek_token() {
            Some(tok) if tok == expected => {
                self.next_token();
                Ok(())
            }
            Some(tok) => Err(Box::new(ParseError {
                message: format!("{}: got {:?}", err_msg, tok),
            })),
            None => Err(Box::new(ParseError {
                message: format!("{}: reached end of tokens", err_msg),
            })),
        }
    }

    /// Checks if we have reached the end of the token stream.
    ///
    /// # Returns
    /// * `true` if no more tokens are available.
    /// * `false` otherwise.
    fn is_at_end(&self) -> bool {
        self.pos >= self.tokens.len()
    }

    /// A helper method used to decide if there's something after `return` or not.
    /// If the next token is a right brace or we're at the end of file, we consider that
    /// there's no expression following the return.
    ///
    /// # Returns
    /// * `true` if we can parse another token (like an expression).
    /// * `false` if the next token ends a block or is none.
    fn check_not_end_or_brace(&self) -> bool {
        if self.is_at_end() {
            return false;
        }
        !matches!(self.peek_token(), Some(Token::RightBrace) | None)
    }
}
