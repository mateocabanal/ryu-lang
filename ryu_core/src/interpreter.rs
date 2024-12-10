#[derive(Clone, Debug)]
pub struct Class {
    name: String,
    members: HashMap<String, Value>,
}

#[derive(Clone, Debug)]
pub enum Value {
    Int(i64),
    Bool(bool),
    Char(char),
    Str(String),
    Array(Vec<Value>),
    Object(Box<Class>),
    Unit, // Like a void or no value
}

#[allow(clippy::to_string_trait_impl)]
impl ToString for Value {
    fn to_string(&self) -> String {
        let res = match self {
            Self::Int(a) => a.to_string(),
            Self::Bool(b) => b.to_string(),
            Self::Str(s) => s.to_string(),
            Self::Object(s) => format!("{s:?}"),
            Self::Array(v) => format!("{v:?}"),
            Self::Char(c) => c.to_string(),
            Self::Unit => String::new(),
        };

        String::from(res)
    }
}

use crate::ast::*;
use std::{collections::HashMap, fmt::write};

/// Represents control flow changes like `return` that need to unwind the call stack.
#[derive(Debug)]
enum ControlFlow {
    Return(Value),
}

/// The interpreter executes the AST. It uses an environment (`env`) to store variables and
/// a function map (`functions`) to store function definitions. Evaluating the program means:
/// 1. Storing top-level functions in `functions`.
/// 2. Calling `main`.
/// 3. Executing statements until completion or until `return` is encountered.
pub struct Interpreter {
    pub classes: HashMap<Box<IdentNode>, ClassDeclNode>,
    pub functions: HashMap<String, FunctionDeclNode>,
    pub env: HashMap<String, Value>,
}

impl Default for Interpreter {
    fn default() -> Self {
        Self::new()
    }
}

impl Interpreter {
    /// Creates a new `Interpreter` with empty environment and function map.
    pub fn new() -> Self {
        Interpreter {
            classes: HashMap::new(),
            functions: HashMap::new(),
            env: HashMap::new(),
        }
    }

    /// Runs the entire program AST by:
    /// - Extracting all top-level functions (like `main`) into `self.functions`.
    /// - Calling `main()` with no arguments.
    /// - Returning the result of `main()` or Value::Unit if none.
    pub fn run(&mut self, ast: &AST) -> Value {
        // Collect functions from the program node
        for func_node in &ast.program.functions {
            let any_node = func_node.as_any();
            if let Some(fdecl) = any_node.downcast_ref::<FunctionDeclNode>() {
                self.functions.insert(fdecl.name.clone(), fdecl.clone());
            } else {
                panic!("Top-level node is not a function declaration!");
            }
        }

        // TODO: Check for duplicate class definitions
        for (class_name, class_decl) in &ast.program.classes {
            if let Some(fdecl) = class_decl.as_any().downcast_ref::<ClassDeclNode>() {
                let Some(class_name) = class_name.as_any().downcast_ref::<IdentNode>() else {
                    panic!("Class name is not an ident!");
                };
                self.classes
                    .insert(Box::new(class_name.clone()), fdecl.clone());
            }
        }

        // Invoke main
        self.eval_function_call("main", vec![])
    }

    /// Evaluates a function call by:
    /// 1. Finding the function in `self.functions`.
    /// 2. Setting up a new environment with the arguments.
    /// 3. Evaluating the function body statements until completion or a `return` is encountered.
    /// 4. Restoring the old environment and returning the final value.
    fn eval_function_call(&mut self, name: &str, args: Vec<Value>) -> Value {
        let func = match self.functions.get(name).cloned() {
            Some(f) => f,
            None => panic!("Function '{}' not defined", name),
        };

        if func.args.len() != args.len() {
            panic!(
                "Function '{}' expected {} args, got {}",
                name,
                func.args.len(),
                args.len()
            );
        }

        let old_env = self.env.clone();
        self.env.clear();

        // Assign arguments to parameters
        for (i, arg_def) in func.args.iter().enumerate() {
            self.env.insert(arg_def.name.clone(), args[i].clone());
        }

        let mut last_value = Value::Unit;
        for stmt in &func.body {
            match self.eval_node(stmt) {
                Ok(val) => last_value = val,
                Err(ControlFlow::Return(rv)) => {
                    // On return, restore old env and return immediately
                    self.env = old_env;
                    return rv;
                }
            }
        }

        self.env = old_env;
        last_value
    }

    /// Evaluates a generic AST node by downcasting it to the appropriate node type
    /// and calling the corresponding evaluation method.
    ///
    /// Returns `Ok(Value)` for normal evaluation or `Err(ControlFlow)` if control flow changes.
    #[allow(clippy::borrowed_box)]
    fn eval_node(&mut self, node: &Box<dyn AstNode>) -> Result<Value, ControlFlow> {
        let any_node = node.as_any();

        if let Some(call) = any_node.downcast_ref::<FunctionCallNode>() {
            self.eval_function_call_node(call)
        } else if let Some(method_call) = any_node.downcast_ref::<ClassMethodCall>() {
            self.eval_class_method_node(method_call)
        } else if let Some(member_field_access) = any_node.downcast_ref::<ClassFieldAccess>() {
            self.eval_class_member_access(member_field_access)
        } else if let Some(member_init) = any_node.downcast_ref::<ClassMemberInit>() {
            self.eval_class_member_init_node(member_init)
        } else if let Some(variable_init) = any_node.downcast_ref::<VariableInitNode>() {
            self.eval_variable_init(variable_init)
        } else if let Some(assign) = any_node.downcast_ref::<AssignmentNode>() {
            self.eval_assignment_node(assign)
        } else if let Some(ident) = any_node.downcast_ref::<IdentNode>() {
            Ok(self.eval_ident_node(ident))
        } else if let Some(slit) = any_node.downcast_ref::<StringLiteralNode>() {
            Ok(self.eval_string_literal_node(slit))
        } else if let Some(ilit) = any_node.downcast_ref::<IntLiteralNode>() {
            Ok(self.eval_int_literal_node(ilit))
        } else if let Some(blit) = any_node.downcast_ref::<BoolLiteralNode>() {
            Ok(self.eval_bool_literal_node(blit))
        } else if let Some(clit) = any_node.downcast_ref::<CharLiteralNode>() {
            Ok(self.eval_char_literal_node(clit))
        } else if let Some(alit) = any_node.downcast_ref::<ArrayLiteralNode>() {
            self.eval_array_literal_node(alit)
        } else if let Some(arr_acc) = any_node.downcast_ref::<ArrayAccessNode>() {
            self.eval_array_access_node(arr_acc)
        } else if let Some(binop) = any_node.downcast_ref::<BinaryOpNode>() {
            self.eval_binary_op_node(binop)
        } else if let Some(if_node) = any_node.downcast_ref::<IfNode>() {
            self.eval_if_node(if_node)
        } else if let Some(while_node) = any_node.downcast_ref::<WhileNode>() {
            self.eval_while_node(while_node)
        } else if let Some(ret) = any_node.downcast_ref::<ReturnNode>() {
            self.eval_return_node(ret)
        } else {
            panic!("Unhandled AST node type in eval_node: {node:?}");
        }
    }

    // TODO: Review this code from o1
    fn eval_class_member_access(
        &mut self,
        member_access: &ClassFieldAccess,
    ) -> Result<Value, ControlFlow> {
        // Collect the field names recursively
        let mut field_names = Vec::new();
        self.collect_field_names(member_access, &mut field_names)?;

        // Now 'field_names' should have the list of names starting from the base object

        // Evaluate the base object
        let base_name = field_names.first().unwrap().clone();
        let mut current_value = self.env.get(&base_name).cloned().unwrap_or(Value::Unit);

        // Traverse the fields
        for field_name in field_names.iter().skip(1) {
            if let Value::Object(obj) = &current_value {
                if let Some(val) = obj.members.get(field_name) {
                    current_value = val.clone();
                } else {
                    panic!("Field '{}' not found in object '{}'", field_name, obj.name);
                }
            } else {
                panic!("Cannot access field '{}' on non-object value", field_name);
            }
        }

        Ok(current_value)
    }

    fn collect_field_names(
        &mut self,
        node: &dyn AstNode,
        field_names: &mut Vec<String>,
    ) -> Result<(), ControlFlow> {
        if let Some(class_field_access) = node.as_any().downcast_ref::<ClassFieldAccess>() {
            // Process 'member' first
            self.collect_field_names(&*class_field_access.member, field_names)?;
            // Then process 'field'
            self.collect_field_names(&*class_field_access.field, field_names)?;
        } else if let Some(ident_node) = node.as_any().downcast_ref::<IdentNode>() {
            field_names.push(ident_node.name.clone());
        // } else if let Some(function_node) = node.as_any().downcast_ref::<FunctionCallNode>() {
        //     field_names.push(
        } else {
            panic!("Expected IdentNode or ClassFieldAccess, got {:?}", node);
        }

        Ok(())
    }

    fn eval_class_member_init_node(
        &mut self,
        member: &ClassMemberInit,
    ) -> Result<Value, ControlFlow> {
        let name = &member.class;
        let Some(class_definition) = self.classes.get(name).cloned() else {
            panic!("{name:?} class is not defined!");
        };

        let class_fields = class_definition
            .tokens
            .iter()
            .filter_map(|i| i.as_any().downcast_ref::<ClassFieldNode>())
            .collect::<Vec<_>>();

        let mut args = HashMap::new();

        // TODO: Args is a terrible name for members...
        for (arg_name, arg_expr) in member.args.clone() {
            let left = arg_name.name;
            let right = self.eval_node(&arg_expr)?;
            args.insert(left, right);
        }

        for field in class_fields {
            let arg_name = &field.left.name;
            if !args.contains_key(arg_name) {
                panic!("{name:?} initialization is missing {arg_name} field");
            }
        }

        Ok(Value::Object(Box::new(Class {
            name: name.name.clone(),
            members: args,
        })))
    }

    fn eval_class_method_node(&mut self, call: &ClassMethodCall) -> Result<Value, ControlFlow> {
        let class_name = call.member.clone();
        let method_name = call.method.clone();

        let Some(class_name) = class_name.as_any().downcast_ref::<IdentNode>() else {
            panic!(
                "member field of ClassMethodCall is not an IdentNode, got: {:?}",
                call.member
            );
        };

        let Some(class_lookup) = self.classes.get(class_name) else {
            panic!("Class could not be looked up!");
        };

        let mut class_method: Option<ClassMethodNode> = None;
        for member in class_lookup.tokens.iter() {
            let as_any = member.as_any();
            if let Some(m) = as_any.downcast_ref::<ClassMethodNode>() {
                if m.name == method_name {
                    class_method = Some(m.clone())
                }
            }
        }

        let Some(class_method) = class_method else {
            panic!("Could not find method: {method_name:?}");
        };

        let arg_values: Vec<Value> = call
            .args
            .iter()
            .map(|a| self.eval_node(a).unwrap())
            .collect();

        if class_method.args.len() != arg_values.len() {
            panic!(
                "Function '{}' expected {} args, got {}",
                method_name.name,
                class_method.args.len(),
                arg_values.len()
            );
        }

        let old_env = self.env.clone();
        self.env.clear();

        // Assign arguments to parameters
        for (i, arg_def) in class_method.args.iter().enumerate() {
            self.env
                .insert(arg_def.name.name.clone(), arg_values[i].clone());
        }

        let mut last_value = Value::Unit;
        for stmt in &class_method.body {
            match self.eval_node(stmt) {
                Ok(val) => last_value = val,
                Err(ControlFlow::Return(rv)) => {
                    // On return, restore old env and return immediately
                    self.env = old_env;
                    return Ok(rv);
                }
            }
        }

        if last_value.to_string() != class_method.return_type.name {
            panic!(
                "Expected {} return type, got: {}",
                class_method.return_type.name,
                last_value.to_string()
            );
        }

        self.env = old_env;
        Ok(last_value)
    }

    fn eval_array_literal_node(&mut self, array: &ArrayLiteralNode) -> Result<Value, ControlFlow> {
        let arr_type = &array.arr_type.name;
        let mut array_internal: Vec<Value> = Vec::new();

        for arg in &array.values {
            let value = self.eval_node(arg)?;

            array_internal.push(value);
        }

        Ok(Value::Array(array_internal))
    }

    fn eval_array_access_node(&mut self, array: &ArrayAccessNode) -> Result<Value, ControlFlow> {
        let variable = self.eval_node(&array.arr_name.clone_box())?;
        let Value::Array(var) = variable else {
            panic!("Tried indexing into something that isn't an array");
        };

        let Value::Int(index) = self.eval_node(&array.index)? else {
            panic!("Index does not evaluate to an Int");
        };

        let Some(indexed_val) = var.get(index as usize).cloned() else {
            panic!("Index is out of bounds");
        };

        Ok(indexed_val)
    }

    /// Evaluate While node
    fn eval_while_node(&mut self, node: &WhileNode) -> Result<Value, ControlFlow> {
        let mut last_value = Value::Unit;

        let old_env = self.env.clone();
        loop {
            let condition = self.eval_node(&node.condition)?;

            let Value::Bool(condition) = condition else {
                panic!("Condition evaluated is not a boolean!, {condition:?}");
            };

            if condition {
                for stmt in &node.then_block {
                    last_value = self.eval_node(stmt)?;
                }
            } else {
                break;
            }
        }
        self.env = old_env;
        Ok(last_value)
    }

    /// Evaluate if node
    fn eval_if_node(&mut self, node: &IfNode) -> Result<Value, ControlFlow> {
        let condition = self.eval_node(&node.condition)?;

        let Value::Bool(condition) = condition else {
            panic!("Condition evaluated is not a boolean!, {condition:?}");
        };

        if condition {
            let mut last_value: Result<Value, ControlFlow> = Ok(Value::Unit);
            for stmt in &node.then_block {
                last_value = self.eval_node(stmt);
            }

            last_value
        } else if let Some(block) = &node.else_block {
            let mut last_value: Result<Value, ControlFlow> = Ok(Value::Unit);
            for stmt in block {
                last_value = self.eval_node(stmt);
            }

            last_value
        } else {
            Ok(Value::Unit)
        }
    }

    /// Creates and inserts a new variable into the interpreters environment
    fn eval_variable_init(&mut self, node: &VariableInitNode) -> Result<Value, ControlFlow> {
        let var_name = node.left.name.clone();
        let right = self.eval_node(&node.right)?;
        self.env.insert(var_name, right);

        Ok(Value::Unit)
    }

    /// Evaluates a `FunctionCallNode`, distinguishing between built-in functions and user-defined functions.
    /// Built-ins:
    /// - `print(...)` prints arguments to stdout and returns Value::Unit.
    /// - `exit` terminates the process.
    ///
    /// User-defined:
    /// - Calls `eval_function_call` with the resolved arguments.
    fn eval_function_call_node(&mut self, call: &FunctionCallNode) -> Result<Value, ControlFlow> {
        let arg_values: Vec<Value> = call
            .args
            .iter()
            .map(|a| self.eval_node(a).unwrap())
            .collect();

        match call.name.as_str() {
            "__native_print" => {
                for val in arg_values {
                    match val {
                        Value::Int(i) => print!("{}", i),
                        Value::Str(s) => {
                            let s = s
                                .replace("\\n", "\n")
                                .replace("\\t", "\t")
                                .replace("\\r", "\r");

                            print!("{s}")
                        }
                        Value::Bool(b) => print!("{b}"),
                        Value::Object(c) => print!("{c:?}"),
                        Value::Array(v) => print!("{v:?}"),
                        Value::Char(c) => print!("\'{c}\'"),
                        Value::Unit => print!("()"),
                    }
                }
                Ok(Value::Unit)
            }
            "exit" => {
                std::process::exit(0);
            }
            _ => {
                // Call a user-defined function
                let rv = self.eval_function_call(&call.name, arg_values);
                Ok(rv)
            }
        }
    }

    /// Evaluates an `AssignmentNode`. The `operator` might be `MulAssign`, `AddAssign`, or `SubAssign`.
    /// We:
    /// 1. Evaluate the left and right sides.
    /// 2. Apply the operator.
    /// 3. Store the result back into the variable.
    fn eval_assignment_node(&mut self, assign: &AssignmentNode) -> Result<Value, ControlFlow> {
        let left_val = self.eval_node(&assign.left)?;
        let right_val = self.eval_node(&assign.right)?;

        if assign
            .left
            .as_any()
            .downcast_ref::<ClassFieldAccess>()
            .is_some()
        {
            return self.assign_to_class_member(assign);
        }

        let lvar = if let Some(id) = assign.left.as_any().downcast_ref::<IdentNode>() {
            &id.name
        } else {
            panic!("Left side of assignment must be ident");
        };

        let result: Value = match left_val {
            Value::Int(l_i) => {
                let r_i = match right_val {
                    Value::Int(i) => i,
                    _ => panic!("Non-integer on right side of assignment"),
                };

                let result = match assign.operator {
                    AssignOperator::MulAssign => Value::Int(l_i * r_i),
                    AssignOperator::DivAssign => Value::Int(l_i / r_i),
                    AssignOperator::AddAssign => Value::Int(l_i + r_i),
                    AssignOperator::SubAssign => Value::Int(l_i - r_i),
                    AssignOperator::Assign => Value::Int(r_i),
                };

                self.env.insert(lvar.clone(), result.clone());
                result
            }

            _ => {
                let result = match assign.operator {
                    AssignOperator::Assign => right_val,
                    _ => panic!("Operator not defined"),
                };
                self.env.insert(lvar.clone(), result.clone());
                result
            }
        };

        Ok(result)
    }

    fn assign_to_class_member(&mut self, operator: &AssignmentNode) -> Result<Value, ControlFlow> {
        // Similar to eval_class_member_access, but we modify the field instead of reading it
        let Some(member_access) = operator.left.as_any().downcast_ref::<ClassFieldAccess>() else {
            panic!("LHS is not a class field!");
        };

        let value = self.eval_node(&operator.right)?;

        // Collect the field names
        let mut field_names = Vec::new();
        self.collect_field_names(member_access, &mut field_names)?;

        // Evaluate the base object
        let base_name = field_names.first().unwrap().clone();
        let mut current_value = self.env.get_mut(&base_name).unwrap();

        // Traverse to the last object
        for field_name in field_names.iter().skip(1).take(field_names.len() - 2) {
            if let Value::Object(obj) = current_value {
                current_value = obj.members.get_mut(field_name).unwrap();
            } else {
                panic!("Cannot access field '{}' on non-object value", field_name);
            }
        }

        // Now current_value is a reference to the object containing the field to assign
        let last_field_name = field_names.last().unwrap();

        if let Value::Object(obj) = current_value {
            match operator.operator {
                AssignOperator::Assign => {
                    obj.members.insert(last_field_name.clone(), value);
                }
                _ => {}
            }
            Ok(Value::Unit)
        } else {
            panic!("Cannot assign to non-object");
        }
    }

    /// Evaluates a `BinaryOpNode` by evaluating both sides and applying the operator.
    /// We assume both sides produce integers for simplicity.
    fn eval_binary_op_node(&mut self, binop: &BinaryOpNode) -> Result<Value, ControlFlow> {
        let left_val = self.eval_node(&binop.left)?;
        let right_val = self.eval_node(&binop.right)?;

        let oper = match left_val {
            Value::Int(l_i) => {
                let Value::Int(r_i) = right_val else {
                    panic!("Right val does not match type of left val!");
                };
                match binop.operator {
                    BinaryOperator::Add => Value::Int(l_i + r_i),
                    BinaryOperator::Sub => Value::Int(l_i - r_i),
                    BinaryOperator::Mul => Value::Int(l_i * r_i),
                    BinaryOperator::Div => Value::Int(l_i / r_i),
                    BinaryOperator::Equal => Value::Bool(l_i == r_i),
                    BinaryOperator::LessEqual => Value::Bool(l_i <= r_i),
                    BinaryOperator::Less => Value::Bool(l_i < r_i),
                    BinaryOperator::NotEqual => Value::Bool(l_i == r_i),
                }
            }

            Value::Str(l_s) => match binop.operator {
                BinaryOperator::Add => Value::Str(l_s + &right_val.to_string()),
                BinaryOperator::Equal => Value::Bool(l_s == right_val.to_string()),
                _ => panic!("Invalid operators on a string type!"),
            },

            Value::Bool(l_b) => {
                let Value::Bool(r_b) = right_val else {
                    panic!("Right val does not match type of left val!");
                };

                match binop.operator {
                    BinaryOperator::NotEqual => Value::Bool(l_b != r_b),
                    BinaryOperator::Equal => Value::Bool(l_b == r_b),
                    _ => panic!("Invalid operator on a bool type!"),
                }
            }
            _ => panic!("Unknown left hand type!"),
        };

        Ok(oper)
    }

    /// Evaluates a `ReturnNode`. If the node has a value expression, evaluate it.
    /// Then return `Err(ControlFlow::Return(val))` to unwind.
    fn eval_return_node(&mut self, ret: &ReturnNode) -> Result<Value, ControlFlow> {
        if let Some(value_expr) = &ret.value {
            let val = self.eval_node(value_expr)?;
            Err(ControlFlow::Return(val))
        } else {
            // return with no value
            Err(ControlFlow::Return(Value::Unit))
        }
    }

    /// Evaluates an identifier by looking it up in the environment.
    fn eval_ident_node(&mut self, ident: &IdentNode) -> Value {
        self.env.get(&ident.name).cloned().unwrap_or(Value::Unit)
    }

    /// Evaluates a string literal node.
    fn eval_string_literal_node(&self, slit: &StringLiteralNode) -> Value {
        Value::Str(slit.value.clone())
    }

    /// Evaluates an integer literal node.
    fn eval_int_literal_node(&self, ilit: &IntLiteralNode) -> Value {
        Value::Int(ilit.value)
    }

    /// Evaluates an integer literal node.
    fn eval_bool_literal_node(&self, blit: &BoolLiteralNode) -> Value {
        Value::Bool(blit.value)
    }

    /// Evaluates a Char literal
    fn eval_char_literal_node(&self, clit: &CharLiteralNode) -> Value {
        Value::Char(clit.value)
    }
}
