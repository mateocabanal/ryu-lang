use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    Import,
    True,
    False,
    If,
    Else,
    While,
    LeftSquareBracket,
    RightSquareBracket,
    LeftBrace,
    RightBrace,
    LeftBracket,
    RightBracket,
    Return,
    Assign,
    AddAssign,
    SubAssign,
    MulAssign,
    DivAssign,
    Colon,
    Period,
    Comma,
    Add,
    Sub,
    Mul,
    Div,
    Equal,
    LessEqual,
    GreaterEqual,
    Less,
    Greater,
    NotEqual,
    RightShift,
    LeftShift,
    Inverse,
    Whitespace,
    NewLine,
    ScopeOperator,
    Variable(String),
    Function(FnData),
    FunctionInvocation(FnInvocation),
    Ident(String),
    Char(char),
    String(String),
    Integer(u64),
    Double(u64),
    Class,
}

pub fn print_tokens(tokens: &[Token]) {
    let mut tab_cnt = 0;
    let mut is_new_line = false;
    let output_tabs = |tab_cnt: i32, cond: &mut bool| {
        if *cond {
            for _ in 0..tab_cnt {
                print!(" ");
            }
            *cond = false;
        }
    };

    for tok in tokens {
        match tok {
            Token::NewLine => {
                is_new_line = true;
                println!();
            }
            Token::LeftBrace => {
                output_tabs(tab_cnt, &mut is_new_line);
                tab_cnt += 4;
                print!("{:?} ", Token::LeftBrace);
            }
            Token::RightBrace => {
                tab_cnt -= 4;
                output_tabs(tab_cnt, &mut is_new_line);
                print!("{:?} ", Token::RightBrace);
            }
            t => {
                output_tabs(tab_cnt, &mut is_new_line);
                print!("{t:?} ");
            }
        }
    }
}

#[derive(Debug, Clone)]
pub enum Type {
    Int,
    String,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FnInvocation {
    /// Each argument is a Vec<Token>
    pub arguments: Option<Vec<Vec<Token>>>,
    pub fn_name: String,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FnData {
    pub arguments: Option<HashMap<String, String>>,
    pub fn_name: String,
    pub return_type: Option<String>,
}
