use std::{collections::HashMap, fs::File, io::Read};

use crate::token::{FnData, FnInvocation, Token};

#[derive(Debug, thiserror::Error)]
pub enum SyntaxError {
    #[error("Invalid function definition")]
    FunctionDefinition,

    #[error("Unterminated string literal")]
    UnterminatedStringLiteral,

    #[error("Invalid function call")]
    InvocationError,
}

#[derive(Debug, thiserror::Error)]
pub enum ErrorLexer {
    #[error("{0} not found")]
    FileNotFound(String),

    #[error("Generic syntax error")]
    GenericSyntaxError,

    #[error("Syntax Error: {0}")]
    SyntaxError(SyntaxError),

    #[error("EOF")]
    EOF,
}

#[derive(Debug)]
pub enum Started {
    Equal,
    Exclamation,
    LessThan,
    GreaterThan,
    DoubleQuote(String),
    Variable(String),
}

impl Started {
    pub fn to_token(self) -> Option<Token> {
        if let Started::DoubleQuote(_) = self {
            return None;
        }

        Some(match self {
            Started::Equal => Token::Assign,
            Started::Exclamation => Token::Inverse,
            Started::LessThan => Token::Less,
            Started::GreaterThan => Token::Greater,
            _ => unreachable!(),
        })
    }
}

#[derive(Debug)]
pub struct Lexer {
    file: Vec<char>,
    next: usize,
    tokens: Vec<Token>,
}

impl Lexer {
    pub fn from_chars(chars: Vec<char>) -> Lexer {
        Lexer {
            file: chars,
            next: 0,
            tokens: Vec::new(),
        }
    }

    pub fn from_file(path: &str) -> Result<Lexer, ErrorLexer> {
        let mut buf = String::new();

        let Ok(mut file) = File::open(path) else {
            return Err(ErrorLexer::FileNotFound(path.to_string()));
        };

        file.read_to_string(&mut buf).unwrap();

        Ok(Lexer {
            file: buf.into_bytes().iter().map(|&u| u as char).collect(),
            next: 0,
            tokens: Vec::new(),
        })
    }

    pub fn lex(&mut self) -> Result<Vec<Token>, ErrorLexer> {
        loop {
            let tok = self.next_token();
            if let Err(e) = &tok {
                if let ErrorLexer::EOF = e {
                    break;
                }

                eprintln!("token dump: {:?}", self.tokens);
            }

            if let Some(t) = tok? {
                self.tokens.push(t);
            }
        }

        Ok(self.tokens.clone())
    }

    pub fn next_token(&mut self) -> Result<Option<Token>, ErrorLexer> {
        let Some(&tok) = self.file.get(self.next) else {
            return Err(ErrorLexer::EOF);
        };

        match tok {
            '<' | '>' | '=' | '!' | '+' | '-' | '*' | '/' | ':' => {
                let &next_tok = self.file.get(self.next + 1).unwrap();

                match next_tok {
                    '=' => {
                        let double_tok = match tok {
                            '<' => Token::LessEqual,
                            '>' => Token::GreaterEqual,
                            '!' => Token::NotEqual,
                            '+' => Token::AddAssign,
                            '-' => Token::SubAssign,
                            '*' => Token::MulAssign,
                            '/' => Token::DivAssign,
                            '=' => Token::Equal,
                            _ => return Err(ErrorLexer::GenericSyntaxError),
                        };

                        self.next += 2;
                        Ok(Some(double_tok))
                    }

                    '>' => {
                        if tok != '>' {
                            Err(ErrorLexer::GenericSyntaxError)
                        } else {
                            self.next += 2;
                            Ok(Some(Token::RightShift))
                        }
                    }

                    '<' => {
                        if tok != '<' {
                            Err(ErrorLexer::GenericSyntaxError)
                        } else {
                            self.next += 2;
                            Ok(Some(Token::LeftShift))
                        }
                    }

                    ':' => {
                        if tok == ':' {
                            self.next += 2;
                            Ok(Some(Token::ScopeOperator))
                        } else {
                            Err(ErrorLexer::GenericSyntaxError)
                        }
                    }

                    '/' => {
                        if tok == '/' {
                            self.next += 2;
                            while let Some(c) = self.file.get(self.next) {
                                self.next += 1;
                                if *c == '\n' {
                                    break;
                                }
                            }
                            Ok(None)
                        } else {
                            Ok(Some(Token::Div))
                        }
                    }

                    _ => {
                        let res = match tok {
                            '<' => Token::Less,
                            '>' => Token::Greater,
                            '!' => Token::Inverse,
                            '=' => Token::Assign,
                            '+' => Token::Add,
                            '-' => Token::Sub,
                            '*' => Token::Mul,
                            '/' => Token::Div,
                            ':' => Token::Colon,
                            _ => unreachable!(),
                        };

                        self.next += 1;
                        Ok(Some(res))
                    }
                }
            }

            '\'' => {
                let mut cnt = 1;
                let Some(c_val) = self.file.get(self.next + cnt) else {
                    return Err(ErrorLexer::GenericSyntaxError);
                };
                cnt += 1;
                let Some(r_quote) = self.file.get(self.next + cnt) else {
                    return Err(ErrorLexer::GenericSyntaxError);
                };

                if *r_quote != '\'' {
                    return Err(ErrorLexer::GenericSyntaxError);
                }

                self.next += cnt + 1;
                Ok(Some(Token::Char(*c_val)))
            }

            '.' => {
                self.next += 1;
                Ok(Some(Token::Period))
            }

            ',' => {
                self.next += 1;
                Ok(Some(Token::Comma))
            }

            '{' => {
                self.next += 1;
                Ok(Some(Token::LeftBrace))
            }

            '}' => {
                self.next += 1;
                Ok(Some(Token::RightBrace))
            }

            '(' => {
                self.next += 1;
                Ok(Some(Token::LeftBracket))
            }

            ')' => {
                self.next += 1;
                Ok(Some(Token::RightBracket))
            }

            '[' => {
                self.next += 1;
                Ok(Some(Token::LeftSquareBracket))
            }

            ']' => {
                self.next += 1;
                Ok(Some(Token::RightSquareBracket))
            }

            '"' => {
                let mut buf = String::new();
                let mut cnt = 1;
                while let Some(&c) = self.file.get(self.next + cnt) {
                    if c == '"' {
                        break;
                    }

                    buf.push(c);
                    cnt += 1;
                }

                self.next += cnt + 1;
                Ok(Some(Token::String(buf)))
            }

            x if x.is_ascii_digit() => {
                let mut buf = String::new();
                buf.push(x);
                let mut cnt = 1;
                while let Some(&c) = self.file.get(self.next + cnt) {
                    if !c.is_ascii_digit() {
                        break;
                    }

                    buf.push(c);
                    cnt += 1;
                }

                self.next += cnt;

                if buf.contains('.') {
                    Ok(Some(Token::Double(buf.parse::<f64>().unwrap().to_bits())))
                } else {
                    Ok(Some(Token::Integer(buf.parse::<i64>().unwrap() as u64)))
                }
            }

            '\n' => {
                self.next += 1;
                Ok(Some(Token::NewLine))
            }

            x if x.is_ascii_whitespace() => {
                self.next += 1;
                Ok(None)
            }

            // Multi-character tokens
            x => {
                let mut buf = String::new();
                buf.push(x);
                let mut cnt = 1;
                let mut str_lit = false;
                let mut is_fn_invocation = false;
                while let Some(&c) = self.file.get(self.next + cnt) {
                    if c == '"' {
                        str_lit = !str_lit;
                    }

                    if !str_lit {
                        if c == '(' {
                            is_fn_invocation = true;
                            break;
                        }

                        if c.is_ascii_whitespace()
                            || c == '{'
                            || c == '}'
                            || c == '='
                            || c == '.'
                            || c == ','
                            || c == ':'
                            || c == '['
                            || c == ']'
                            || c == '-'
                            || c == '+'
                        {
                            break;
                        }
                    }

                    if c == ')' {
                        break;
                    }

                    buf.push(c);
                    cnt += 1;
                }

                self.next += cnt;

                if is_fn_invocation {
                    let mut cnt = 1;
                    let mut args_raw = String::new();
                    let mut str_lit = false;
                    let mut bracket_cnt = 0;
                    while let Some(&c) = self.file.get(self.next + cnt) {
                        if c == '"' {
                            str_lit = !str_lit;
                        }

                        if !str_lit {
                            if c == '(' {
                                bracket_cnt += 1;
                            }

                            if c == ')' {
                                if bracket_cnt == 0 {
                                    cnt += 1;
                                    break;
                                }
                                bracket_cnt -= 1;
                            }
                        }

                        args_raw.push(c);
                        cnt += 1;
                    }

                    self.next += cnt;
                    let mut fn_data = FnInvocation {
                        arguments: None,
                        fn_name: buf.to_string(),
                    };

                    if args_raw.trim() != "" {
                        let mut tokens = Vec::new();
                        let mut str_lit = false;
                        let mut args = Vec::new();
                        let mut arg_buf = String::new();
                        for c in args_raw.chars() {
                            if c == '"' {
                                str_lit = !str_lit;
                            }

                            if !str_lit && c == ',' {
                                args.push(arg_buf.clone());
                                arg_buf.clear();
                                continue;
                            }

                            if !str_lit && c.is_ascii_whitespace() {
                                continue;
                            }

                            arg_buf.push(c);
                        }

                        if str_lit {
                            return Err(ErrorLexer::SyntaxError(
                                SyntaxError::UnterminatedStringLiteral,
                            ));
                        }

                        args.push(arg_buf);

                        for arg in &args {
                            let mut buf = Vec::new();
                            let mut internal_lexer =
                                Lexer::from_chars(arg.chars().collect::<Vec<char>>());

                            while let Ok(token) = internal_lexer.next_token() {
                                if let Some(t) = token {
                                    buf.push(t);
                                }
                            }

                            tokens.push(buf);
                        }

                        fn_data.arguments = Some(tokens);
                    }

                    return Ok(Some(Token::FunctionInvocation(fn_data)));
                }

                // NOTE: Match keywords
                match buf.as_str() {
                    "let" => {
                        let Some(&c) = self.file.get(self.next) else {
                            return Err(ErrorLexer::GenericSyntaxError);
                        };

                        if c != ' ' {
                            println!("{c}");
                            return Err(ErrorLexer::GenericSyntaxError);
                        }

                        let mut var_name = String::new();
                        let mut cnt = 1;
                        while let Some(&c) = self.file.get(self.next + cnt) {
                            if !c.is_ascii_alphanumeric() && c != '_' {
                                break;
                            }

                            var_name.push(c);
                            cnt += 1;
                        }

                        self.next += cnt;
                        Ok(Some(Token::Variable(var_name)))
                    }

                    "true" => Ok(Some(Token::True)),

                    "false" => Ok(Some(Token::False)),

                    "if" => Ok(Some(Token::If)),

                    "else" => Ok(Some(Token::Else)),

                    "while" => Ok(Some(Token::While)),

                    "return" => Ok(Some(Token::Return)),

                    "import" => Ok(Some(Token::Import)),

                    "class" => Ok(Some(Token::Class)),

                    "fn" => {
                        let Some(&c) = self.file.get(self.next) else {
                            return Err(ErrorLexer::SyntaxError(SyntaxError::FunctionDefinition));
                        };

                        if c != ' ' {
                            return Err(ErrorLexer::SyntaxError(SyntaxError::FunctionDefinition));
                        }

                        let mut fn_name = String::new();
                        let mut cnt = 1;
                        while let Some(&c) = self.file.get(self.next + cnt) {
                            if c.is_ascii_whitespace() || c == '(' {
                                break;
                            }

                            fn_name.push(c);
                            cnt += 1;
                        }

                        let mut fn_data = FnData {
                            arguments: None,
                            return_type: None,
                            fn_name,
                        };

                        cnt += 1;
                        let mut arguments_raw = String::new();
                        while let Some(&c) = self.file.get(self.next + cnt) {
                            if c == '\n' {
                                return Err(ErrorLexer::SyntaxError(
                                    SyntaxError::FunctionDefinition,
                                ));
                            }

                            if c == ')' {
                                cnt += 1;
                                break;
                            }

                            arguments_raw.push(c);
                            cnt += 1;
                        }

                        // Checks the argument list of the declared function
                        if arguments_raw.trim() != "" {
                            let arg_iter = arguments_raw.split(',');
                            let mut arg_map = HashMap::new();
                            for arg in arg_iter {
                                let mut split = arg.split(':');

                                let Some(arg_name) = split.next() else {
                                    return Err(ErrorLexer::SyntaxError(
                                        SyntaxError::FunctionDefinition,
                                    ));
                                };

                                if arg_name == "self" {
                                    arg_map.insert("self".to_string(), "Self".to_string());
                                    continue;
                                }

                                let Some(arg_type) = split.next() else {
                                    return Err(ErrorLexer::SyntaxError(
                                        SyntaxError::FunctionDefinition,
                                    ));
                                };

                                arg_map.insert(
                                    arg_name.trim().to_string(),
                                    arg_type.trim().to_string(),
                                );
                            }

                            fn_data.arguments = Some(arg_map);
                        }

                        let mut return_type = String::new();
                        while let Some(&c) = self.file.get(self.next + cnt) {
                            // Don't move the cursor, in order to record LEFT_BRACE next
                            if c == '{' {
                                break;
                            }

                            cnt += 1;
                            if c == ' ' {
                                continue;
                            }

                            return_type.push(c);
                        }

                        let trimmed_ret = return_type.trim();
                        if trimmed_ret.contains("=>") {
                            let mut split = trimmed_ret.split("=>");
                            let Some(ret_type) = split.nth(1) else {
                                return Err(ErrorLexer::SyntaxError(
                                    SyntaxError::FunctionDefinition,
                                ));
                            };

                            fn_data.return_type = Some(ret_type.to_string());
                        }

                        self.next += cnt;
                        Ok(Some(Token::Function(fn_data)))
                    }

                    _ => Ok(Some(Token::Ident(buf))),
                }
            }
        }
    }
}
