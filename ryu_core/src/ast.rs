use std::{any::Any, borrow::Borrow, collections::HashMap, fmt::Debug};

pub trait AstNode: Downcastable + Debug {
    fn clone_box(&self) -> Box<dyn AstNode>;
}

// This allows us to use downcasting on trait objects.
pub trait Downcastable {
    fn as_any(&self) -> &dyn Any;
}

impl<T: 'static + AstNode> Downcastable for T {
    fn as_any(&self) -> &dyn Any {
        self
    }
}

// Implement Clone for Box<dyn AstNode> using the clone_box method.
impl Clone for Box<dyn AstNode> {
    fn clone(&self) -> Box<dyn AstNode> {
        self.clone_box()
    }
}

/// The top-level AST structure containing the entire program.
#[derive(Clone, Debug)]
pub struct AST {
    pub program: ProgramNode,
}

impl AST {
    pub fn new(program: ProgramNode) -> Self {
        AST { program }
    }
}

impl AstNode for AST {
    fn clone_box(&self) -> Box<dyn AstNode> {
        Box::new(self.clone())
    }
}

#[derive(Clone, Debug)]
pub struct ProgramNode {
    pub functions: Vec<Box<dyn AstNode>>,
    pub classes: HashMap<Box<IdentNode>, Box<dyn AstNode>>,
}

impl AstNode for ProgramNode {
    fn clone_box(&self) -> Box<dyn AstNode> {
        Box::new(self.clone())
    }
}

#[derive(Clone, Debug)]
pub struct FunctionArgNode {
    pub name: String,
    pub arg_type: String,
}

#[derive(Clone, Debug)]
pub struct FunctionDeclNode {
    pub name: String,
    pub args: Vec<FunctionArgNode>,
    pub return_type: Option<String>,
    pub body: Vec<Box<dyn AstNode>>,
}

impl AstNode for FunctionDeclNode {
    fn clone_box(&self) -> Box<dyn AstNode> {
        Box::new(self.clone())
    }
}

#[derive(Clone, Debug)]
pub struct FunctionCallNode {
    pub name: String,
    pub args: Vec<Box<dyn AstNode>>,
}

impl AstNode for FunctionCallNode {
    fn clone_box(&self) -> Box<dyn AstNode> {
        Box::new(self.clone())
    }
}

#[derive(Clone, Debug)]
pub enum AssignOperator {
    DivAssign,
    MulAssign,
    SubAssign,
    AddAssign,
    Assign,
}

#[derive(Clone, Debug)]
pub struct AssignmentNode {
    pub operator: AssignOperator,
    pub left: Box<dyn AstNode>,
    pub right: Box<dyn AstNode>,
}

impl AstNode for AssignmentNode {
    fn clone_box(&self) -> Box<dyn AstNode> {
        Box::new(self.clone())
    }
}

#[derive(Clone, Debug)]
pub struct VariableInitNode {
    pub left: Box<IdentNode>,
    pub right: Box<dyn AstNode>,
}

impl AstNode for VariableInitNode {
    fn clone_box(&self) -> Box<dyn AstNode> {
        Box::new(self.clone())
    }
}

#[derive(Clone, Hash, Eq, PartialEq, Debug)]
pub struct IdentNode {
    pub name: String,
}

impl AstNode for IdentNode {
    fn clone_box(&self) -> Box<dyn AstNode> {
        Box::new(self.clone())
    }
}

#[derive(Clone, Debug)]
pub struct StringLiteralNode {
    pub value: String,
}

impl AstNode for StringLiteralNode {
    fn clone_box(&self) -> Box<dyn AstNode> {
        Box::new(self.clone())
    }
}

#[derive(Clone, Debug)]
pub struct CharLiteralNode {
    pub value: char,
}

impl AstNode for CharLiteralNode {
    fn clone_box(&self) -> Box<dyn AstNode> {
        Box::new(self.clone())
    }
}

#[derive(Clone, Debug)]
pub struct IntLiteralNode {
    pub value: i64,
}

impl AstNode for IntLiteralNode {
    fn clone_box(&self) -> Box<dyn AstNode> {
        Box::new(self.clone())
    }
}

#[derive(Clone, Debug)]
pub struct BoolLiteralNode {
    pub value: bool,
}

impl AstNode for BoolLiteralNode {
    fn clone_box(&self) -> Box<dyn AstNode> {
        Box::new(self.clone())
    }
}

#[derive(Clone, Debug)]
pub struct ArrayTypeNode {
    pub arr_type: Box<IdentNode>,
}

impl AstNode for ArrayTypeNode {
    fn clone_box(&self) -> Box<dyn AstNode> {
        Box::new(self.clone())
    }
}

#[derive(Clone, Debug)]
pub struct ArrayLiteralNode {
    pub arr_type: Box<IdentNode>,
    pub values: Vec<Box<dyn AstNode>>,
}

impl AstNode for ArrayLiteralNode {
    fn clone_box(&self) -> Box<dyn AstNode> {
        Box::new(self.clone())
    }
}

#[derive(Clone, Debug)]
pub struct ArrayAccessNode {
    pub arr_name: Box<IdentNode>,
    pub index: Box<dyn AstNode>,
}

impl AstNode for ArrayAccessNode {
    fn clone_box(&self) -> Box<dyn AstNode> {
        Box::new(self.clone())
    }
}

#[derive(Clone, Debug)]
pub struct ArrayAssignmentNode {
    pub operator: AssignOperator,
    pub left: Box<ArrayAccessNode>,
    pub right: Box<dyn AstNode>,
}

impl AstNode for ArrayAssignmentNode {
    fn clone_box(&self) -> Box<dyn AstNode> {
        Box::new(self.clone())
    }
}

/// `BinaryOperator` is an enum representing different kinds of binary operations
/// your language supports. For example, `Add` corresponds to the `+` operator,
/// `Sub` to `-`, `Mul` to `*`, and `Div` to `/`. You can extend this enum with
/// more operators (like `%`, `==`, etc.) as your language evolves.
#[derive(Clone, Debug)]
pub enum BinaryOperator {
    Add,
    Sub,
    Mul,
    Div,
    // Add more operators if needed, like:
    // Mod,
    Equal,
    NotEqual,
    LessEqual,
    Less, // etc.
}

/// `BinaryOpNode` represents an expression with a left-hand side (LHS) node, a
/// right-hand side (RHS) node, and a binary operator between them. For example,
/// if you have an expression like `x + 5`, then:
///
/// - `operator` would be `BinaryOperator::Add`
/// - `left` would be an `IdentNode` representing `x`
/// - `right` would be an `IntLiteralNode` representing `5`
///
/// The interpreter or compiler will evaluate `BinaryOpNode` by evaluating both
/// children and then applying the operator.
#[derive(Clone, Debug)]
pub struct BinaryOpNode {
    /// The binary operator, such as `BinaryOperator::Add` for `+`.
    pub operator: BinaryOperator,
    /// The left-hand side expression node.
    pub left: Box<dyn AstNode>,
    /// The right-hand side expression node.
    pub right: Box<dyn AstNode>,
}

impl AstNode for BinaryOpNode {
    fn clone_box(&self) -> Box<dyn AstNode> {
        Box::new(self.clone())
    }
}

/// A `ReturnNode` represents a `return` statement in the language.
///
/// In many languages, a return statement can optionally return a value. If
/// the `value` field is `Some(...)`, it contains the expression’s AST node
/// that produces the return value. If `None`, it means `return` was used
/// without a value (effectively `return;`).
#[derive(Clone, Debug)]
pub struct ReturnNode {
    /// The expression being returned, if any. If this is `None`, the return
    /// statement returns no value.
    pub value: Option<Box<dyn AstNode>>,
}

impl AstNode for ReturnNode {
    fn clone_box(&self) -> Box<dyn AstNode> {
        Box::new(self.clone())
    }
}

/// A `WhileNode` represents a conditional loop
#[derive(Clone, Debug)]
pub struct WhileNode {
    pub condition: Box<dyn AstNode>,
    pub then_block: Vec<Box<dyn AstNode>>,
}

impl AstNode for WhileNode {
    fn clone_box(&self) -> Box<dyn AstNode> {
        Box::new(self.clone())
    }
}

/// A `IfNode` represents a conditional jump
#[derive(Clone, Debug)]
pub struct IfNode {
    pub condition: Box<dyn AstNode>,
    pub then_block: Vec<Box<dyn AstNode>>,
    pub else_block: Option<Vec<Box<dyn AstNode>>>,
}

impl AstNode for IfNode {
    fn clone_box(&self) -> Box<dyn AstNode> {
        Box::new(self.clone())
    }
}

/// A `ClassDeclNode` holds all relevent tokens to a class defintion
#[derive(Clone, Debug)]
pub struct ClassDeclNode {
    pub name: Box<IdentNode>,
    pub tokens: Vec<Box<dyn AstNode>>,
}

impl AstNode for ClassDeclNode {
    fn clone_box(&self) -> Box<dyn AstNode> {
        Box::new(self.clone())
    }
}

/// A `ClassFieldNode` represents a class field
#[derive(Clone, Debug)]
pub struct ClassFieldNode {
    pub var_type: Box<IdentNode>,
    pub left: Box<IdentNode>,
    pub right: Vec<u8>,
}

impl AstNode for ClassFieldNode {
    fn clone_box(&self) -> Box<dyn AstNode> {
        Box::new(self.clone())
    }
}

#[derive(Clone, Debug)]
pub struct ClassMethodArgNode {
    pub name: Box<IdentNode>,
    pub arg_type: Box<IdentNode>,
}

impl AstNode for ClassMethodArgNode {
    fn clone_box(&self) -> Box<dyn AstNode> {
        Box::new(self.clone())
    }
}

#[derive(Clone, Debug)]
pub struct ClassMethodNode {
    pub name: Box<IdentNode>,
    pub args: Vec<ClassMethodArgNode>,
    pub return_type: Box<IdentNode>,
    pub body: Vec<Box<dyn AstNode>>,
    pub is_static: bool,
}

impl AstNode for ClassMethodNode {
    fn clone_box(&self) -> Box<dyn AstNode> {
        Box::new(self.clone())
    }
}

#[derive(Clone, Debug)]
pub struct MethodCallNode {
    pub object: Box<dyn AstNode>,
    pub method: Box<IdentNode>,
    pub args: Vec<Box<dyn AstNode>>,
}

impl AstNode for MethodCallNode {
    fn clone_box(&self) -> Box<dyn AstNode> {
        Box::new(self.clone())
    }
}

#[derive(Clone, Debug)]
pub struct StaticMethodCallNode {
    pub class: Box<IdentNode>,
    pub method: Box<IdentNode>,
    pub args: Vec<Box<dyn AstNode>>,
}

impl AstNode for StaticMethodCallNode {
    fn clone_box(&self) -> Box<dyn AstNode> {
        Box::new(self.clone())
    }
}

#[derive(Clone, Debug)]
pub struct SelfFieldAccessNode {
    pub field: Box<IdentNode>,
}

impl AstNode for SelfFieldAccessNode {
    fn clone_box(&self) -> Box<dyn AstNode> {
        Box::new(self.clone())
    }
}

#[derive(Clone, Debug)]
pub struct ClassFieldAssignmentNode {
    pub assign_operator: Box<AssignOperator>,
    pub field: Box<IdentNode>,
    pub member: Box<dyn AstNode>,
    pub value: Box<dyn AstNode>,
}

impl AstNode for ClassFieldAssignmentNode {
    fn clone_box(&self) -> Box<dyn AstNode> {
        Box::new(self.clone())
    }
}

#[derive(Clone, Debug)]
pub struct ClassFieldAccess {
    pub field: Box<dyn AstNode>,
    pub member: Box<dyn AstNode>,
}

impl AstNode for ClassFieldAccess {
    fn clone_box(&self) -> Box<dyn AstNode> {
        Box::new(self.clone())
    }
}

#[derive(Clone, Debug)]
pub struct ClassMethodCall {
    pub object: Box<dyn AstNode>,
    pub method: Box<IdentNode>,
    pub args: Vec<Box<dyn AstNode>>,
}

impl AstNode for ClassMethodCall {
    fn clone_box(&self) -> Box<dyn AstNode> {
        Box::new(self.clone())
    }
}

#[derive(Clone, Debug)]
pub struct ClassMemberInit {
    pub class: Box<IdentNode>,
    pub args: HashMap<Box<IdentNode>, Box<dyn AstNode>>,
}

impl AstNode for ClassMemberInit {
    fn clone_box(&self) -> Box<dyn AstNode> {
        Box::new(self.clone())
    }
}

/// Print the AST starting from the given node.
pub fn print_ast(node: &dyn AstNode) -> String {
    let mut output = String::new();
    print_ast_with_indent(node, &mut output, 0);
    output
}

/// A helper function that prints the AST node with a given indentation level.
fn print_ast_with_indent(node: &dyn AstNode, writer: &mut String, indent: usize) {
    use std::fmt::Write;

    let indentation = "  ".repeat(indent);

    // Identify the concrete node type by downcasting
    let any_node = node.as_any();

    if let Some(ast) = any_node.downcast_ref::<AST>() {
        writeln!(writer, "{}AST", indentation).unwrap();
        print_ast_with_indent(&ast.program, writer, indent + 1);
    } else if let Some(program) = any_node.downcast_ref::<ProgramNode>() {
        writeln!(writer, "{}ProgramNode", indentation).unwrap();
        for func in &program.functions {
            print_ast_with_indent(func.borrow(), writer, indent + 1);
        }
        for class in &program.classes {
            print_ast_with_indent(class.1.borrow(), writer, indent + 1);
        }
    } else if let Some(fdecl) = any_node.downcast_ref::<FunctionDeclNode>() {
        writeln!(
            writer,
            "{}FunctionDeclNode name={} return={:?}",
            indentation, fdecl.name, fdecl.return_type
        )
        .unwrap();

        if !fdecl.args.is_empty() {
            writeln!(writer, "{}  Arguments:", indentation).unwrap();
            for arg in &fdecl.args {
                writeln!(writer, "{}    {}: {}", indentation, arg.name, arg.arg_type).unwrap();
            }
        }
        writeln!(writer, "{}  Body:", indentation).unwrap();
        for stmt in &fdecl.body {
            print_ast_with_indent(stmt.borrow(), writer, indent + 2);
        }
    } else if let Some(class_decl_node) = any_node.downcast_ref::<ClassDeclNode>() {
        writeln!(
            writer,
            "{}ClassDeclNode name={}",
            indentation, class_decl_node.name.name
        )
        .unwrap();

        for member in &class_decl_node.tokens {
            print_ast_with_indent(member.borrow(), writer, indent + 1);
        }
    } else if let Some(class_field) = any_node.downcast_ref::<ClassFieldNode>() {
        writeln!(
            writer,
            "{}ClassFieldNode name={} type={}",
            indentation, class_field.left.name, class_field.var_type.name
        )
        .unwrap();
    } else if let Some(self_class_field) = any_node.downcast_ref::<SelfFieldAccessNode>() {
        writeln!(
            writer,
            "{}SelfFieldAccessNode field={}",
            indentation, self_class_field.field.name
        )
        .unwrap();
    } else if let Some(static_method_call) = any_node.downcast_ref::<StaticMethodCallNode>() {
        writeln!(
            writer,
            "{}StaticMethodCallNode class={} method={}",
            indentation, static_method_call.class.name, static_method_call.method.name
        )
        .unwrap();
        if !static_method_call.args.is_empty() {
            writeln!(writer, "{}  Arguments:", indentation).unwrap();
            for arg in &static_method_call.args {
                print_ast_with_indent(arg.borrow(), writer, indent + 2);
            }
        }
    } else if let Some(class_method) = any_node.downcast_ref::<ClassMethodNode>() {
        writeln!(
            writer,
            "{}ClassMethodNode name={} return={}",
            indentation, class_method.name.name, class_method.return_type.name
        )
        .unwrap();

        if !class_method.args.is_empty() {
            writeln!(writer, "{}  Arguments:", indentation).unwrap();
            for arg in &class_method.args {
                writeln!(
                    writer,
                    "{}    {}: {}",
                    indentation, arg.name.name, arg.arg_type.name
                )
                .unwrap();
            }
        }
        writeln!(writer, "{}  Body:", indentation).unwrap();
        for stmt in &class_method.body {
            print_ast_with_indent(stmt.borrow(), writer, indent + 2);
        }
    } else if let Some(method_call) = any_node.downcast_ref::<ClassMethodCall>() {
        writeln!(
            writer,
            "{}ClassMethodCallNode member={} method={}",
            indentation,
            method_call
                .object
                .as_any()
                .downcast_ref::<IdentNode>()
                .unwrap()
                .name,
            method_call.method.name,
        )
        .unwrap();

        if !method_call.args.is_empty() {
            writeln!(writer, "{}  Arguments:", indentation).unwrap();
            for arg in &method_call.args {
                print_ast_with_indent(arg.borrow(), writer, indent + 2);
            }
        }
    } else if let Some(class_init) = any_node.downcast_ref::<ClassMemberInit>() {
        writeln!(
            writer,
            "{}ClassMemberInitNode class={}",
            indentation, class_init.class.name
        )
        .unwrap();

        writeln!(writer, "{}  Arguments:", indentation).unwrap();
        for (arg_name, arg_tok) in &class_init.args {
            // let mut arg_output = String::new();
            writeln!(writer, "{}    {}:", indentation, arg_name.name).unwrap();
            print_ast_with_indent(arg_tok.borrow(), writer, indent + 3);
            // write!(
            //     writer,
            //     "{}    {}: {}",
            //     indentation, arg_name.name, arg_output
            // )
            // .unwrap();
        }
    } else if let Some(class_access) = any_node.downcast_ref::<ClassFieldAccess>() {
        writeln!(writer, "{}ClassFieldAccessNode", indentation).unwrap();

        writeln!(writer, "{}  Member:", indentation).unwrap();
        print_ast_with_indent(class_access.member.borrow(), writer, indent + 2);

        writeln!(writer, "{}  Field:", indentation).unwrap();
        print_ast_with_indent(class_access.field.borrow(), writer, indent + 2);
    } else if let Some(if_node) = any_node.downcast_ref::<IfNode>() {
        writeln!(writer, "{}IfNode", indentation).unwrap();
        writeln!(writer, "{}  Condition:", indentation).unwrap();
        print_ast_with_indent(if_node.condition.borrow(), writer, indent + 2);

        writeln!(writer, "{}  ThenBlock:", indentation).unwrap();
        for stmt in &if_node.then_block {
            print_ast_with_indent(stmt.borrow(), writer, indent + 2);
        }

        if let Some(else_blk) = &if_node.else_block {
            writeln!(writer, "{}  ElseBlock:", indentation).unwrap();
            for stmt in else_blk {
                print_ast_with_indent(stmt.borrow(), writer, indent + 2);
            }
        }
    } else if let Some(while_node) = any_node.downcast_ref::<WhileNode>() {
        writeln!(writer, "{}WhileNode", indentation).unwrap();
        writeln!(writer, "{}  Condition:", indentation).unwrap();
        print_ast_with_indent(while_node.condition.borrow(), writer, indent + 2);

        writeln!(writer, "{}  ThenBlock:", indentation).unwrap();
        for stmt in &while_node.then_block {
            print_ast_with_indent(stmt.borrow(), writer, indent + 2);
        }
    } else if let Some(ret) = any_node.downcast_ref::<ReturnNode>() {
        writeln!(writer, "{}ReturnNode", indentation).unwrap();
        if let Some(val) = &ret.value {
            print_ast_with_indent(val.borrow(), writer, indent + 1);
        } else {
            writeln!(writer, "{}  (no value)", indentation).unwrap();
        }
    } else if let Some(binop) = any_node.downcast_ref::<BinaryOpNode>() {
        writeln!(
            writer,
            "{}BinaryOpNode operator={:?}",
            indentation, binop.operator
        )
        .unwrap();
        writeln!(writer, "{}  Left:", indentation).unwrap();
        print_ast_with_indent(binop.left.borrow(), writer, indent + 2);
        writeln!(writer, "{}  Right:", indentation).unwrap();
        print_ast_with_indent(binop.right.borrow(), writer, indent + 2);
    } else if let Some(call) = any_node.downcast_ref::<FunctionCallNode>() {
        writeln!(writer, "{}FunctionCallNode name={}", indentation, call.name).unwrap();
        for (i, arg) in call.args.iter().enumerate() {
            writeln!(writer, "{}  Arg {}:", indentation, i).unwrap();
            print_ast_with_indent(arg.borrow(), writer, indent + 2);
        }
    } else if let Some(ilit) = any_node.downcast_ref::<IntLiteralNode>() {
        writeln!(writer, "{}IntLiteralNode {}", indentation, ilit.value).unwrap();
    } else if let Some(slit) = any_node.downcast_ref::<StringLiteralNode>() {
        writeln!(writer, "{}StringLiteralNode {:?}", indentation, slit.value).unwrap();
    } else if let Some(clit) = any_node.downcast_ref::<CharLiteralNode>() {
        writeln!(writer, "{}CharLiteralNode \'{}\'", indentation, clit.value).unwrap();
    } else if let Some(alit) = any_node.downcast_ref::<ArrayLiteralNode>() {
        writeln!(
            writer,
            "{}ArrayLiteralNode type={}",
            indentation, alit.arr_type.name
        )
        .unwrap();
        writeln!(writer, "{}  Values:", indentation).unwrap();
        for value in &alit.values {
            print_ast_with_indent(value.borrow(), writer, indent + 2);
        }
    } else if let Some(arr_acc) = any_node.downcast_ref::<ArrayAccessNode>() {
        writeln!(writer, "{}ArrayAccessNode", indentation).unwrap();
        writeln!(writer, "{}  Ident:", indentation).unwrap();
        print_ast_with_indent(arr_acc.arr_name.clone_box().borrow(), writer, indent + 2);
        writeln!(writer, "{}  Index:", indentation).unwrap();
        print_ast_with_indent(arr_acc.index.borrow(), writer, indent + 2);
    } else if let Some(arr_ass) = any_node.downcast_ref::<ArrayAssignmentNode>() {
        writeln!(writer, "{}ArrayAssignmentNode", indentation).unwrap();
        writeln!(writer, "{}  ArrayAccess:", indentation).unwrap();
        print_ast_with_indent(arr_ass.left.clone_box().borrow(), writer, indent + 2);
        writeln!(writer, "{}  Assignment:", indentation).unwrap();
        print_ast_with_indent(arr_ass.right.borrow(), writer, indent + 2);
    } else if let Some(ident) = any_node.downcast_ref::<IdentNode>() {
        writeln!(writer, "{}IdentNode {}", indentation, ident.name).unwrap();
    } else if let Some(assign) = any_node.downcast_ref::<AssignmentNode>() {
        writeln!(
            writer,
            "{}AssignmentNode op={:?}",
            indentation, assign.operator
        )
        .unwrap();
        writeln!(writer, "{}  Left:", indentation).unwrap();
        print_ast_with_indent(assign.left.borrow(), writer, indent + 2);
        writeln!(writer, "{}  Right:", indentation).unwrap();
        print_ast_with_indent(assign.right.borrow(), writer, indent + 2);
    } else if let Some(var_init) = any_node.downcast_ref::<VariableInitNode>() {
        writeln!(writer, "{}VaraibleInitNode", indentation).unwrap();
        writeln!(writer, "{}  Left:", indentation).unwrap();
        let ast_node: Box<dyn AstNode> = var_init.left.clone();
        print_ast_with_indent(ast_node.borrow(), writer, indent + 2);
        writeln!(writer, "{}  Right:", indentation).unwrap();
        print_ast_with_indent(var_init.right.borrow(), writer, indent + 2);
    } else {
        // If a new node type appears, just print a fallback
        writeln!(writer, "{}Unknown node type: {node:?}", indentation).unwrap();
    }
}
