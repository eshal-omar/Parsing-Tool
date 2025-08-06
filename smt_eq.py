from parser import *
from ssa_eq import *
from typing import Dict, List, Set, Tuple, Optional
import re
from ssa_eq import WhileLoop,SSAAssignment,SSAIfStatement,SSANode,SSAPhiFunction,SSAProgram,SSAWhileLoop
def ssa_to_smt(ssa_ast: SSAProgram, output_file: str, result_var: str = "result", prefix: str = ""):
    """
    Convert SSA program to SMT constraints
    
    Args:
        ssa_ast: The SSA Program
        output_file: Path to output SMT file
        result_var: Name of the result variable
        prefix: Prefix for all variables (useful for combining multiple programs)
    """
    smt_lines = []
    variable_types = {}  # Maps variable name to its SMT type
    variable_declarations = []
    assertions = []
    
    # Add SMT-LIB header
    smt_lines.append("; SMT-LIB2 encoding of the program")
    smt_lines.append("(set-logic QF_LIA)")  # Quantifier-free linear integer arithmetic
    
    def determine_type(expr) -> str:
        """Determine the SMT type of an expression"""
        if isinstance(expr, Number):
            return "Int"
        elif isinstance(expr, Boolean):
            return "Bool"
        elif isinstance(expr, Variable):
            return variable_types.get(expr.name, "Int")  # Default to Int if unknown
        elif isinstance(expr, BinaryOp):
            op = expr.op
            # Comparison operations return Bool
            if op in ["==", "!=", "<", ">", "<=", ">=", "&&", "||"]:
                return "Bool"
            # Conditional operations return the type of their branches
            elif op in ["?", ":"]:
                return determine_type(expr.right)
            # Arithmetic operations return Int
            else:
                return "Int"
        elif isinstance(expr, UnaryOp):
            if expr.op == "!":
                return "Bool"
            else:
                return "Int"
        else:
            return "Int"  # Default to Int
    
    def translate_expression(expr) -> str:
        """Translate an expression to SMT-LIB2 format"""
        if isinstance(expr, Number):
            return str(expr.value)
        
        elif isinstance(expr, Boolean):
            return "true" if expr.value else "false"
        
        elif isinstance(expr, Variable):
            var_name = expr.name
            return var_name
        
        elif isinstance(expr, ArrayAccess):
            # Arrays are modeled as functions in SMT
            array_name = expr.array if isinstance(expr.array, str) else expr.array.name
            index_smt = translate_expression(expr.index)
            return f"(select {array_name} {index_smt})"
        
        elif isinstance(expr, BinaryOp):
            left_smt = translate_expression(expr.left)
            right_smt = translate_expression(expr.right)
            op = expr.op
            
            # Map operators to SMT-LIB2 operators
            op_map = {
                "+": "+",
                "-": "-",
                "*": "*",
                "/": "div",
                "%": "mod",
                "==": "=",
                "!=": "distinct",
                "<": "<",
                ">": ">",
                "<=": "<=",
                ">=": ">=",
                "&&": "and",
                "||": "or",
                "?": "ite"  # if-then-else for phi functions
            }
            
            if op in op_map:
                if op == "?":
                    if hasattr(expr.right, 'op') and expr.right.op == ':':
                        then_expr = translate_expression(expr.right.left)
                        else_expr = translate_expression(expr.right.right)
                        return f"(ite {left_smt} {then_expr} {else_expr})"
                    else:
                        middle_smt = right_smt
                        else_smt = "0"  # Using a default value as fallback
                        return f"(ite {left_smt} {middle_smt} {else_smt})"
                else:
                    return f"({op_map[op]} {left_smt} {right_smt})"
            
            # Handle the ":" operator as part of ternary expressions
            elif op == ":":
                return left_smt
            
            elif op == "with":
                # Array update operation
                # left is the array, right is a BinaryOp with index = value
                index_smt = translate_expression(expr.right.left)
                value_smt = translate_expression(expr.right.right)
                return f"(store {left_smt} {index_smt} {value_smt})"
            
            else:
                raise ValueError(f"Unsupported binary operator: {op}")
        
        elif isinstance(expr, UnaryOp):
            sub_expr = translate_expression(expr.expr)
            op = expr.op
            
            if op == "!":
                return f"(not {sub_expr})"
            elif op == "-":
                return f"(- {sub_expr})"
            elif op == "+":
                return sub_expr  # Unary plus does nothing
            else:
                raise ValueError(f"Unsupported unary operator: {op}")
        
        else:
            raise ValueError(f"Unsupported expression type: {type(expr)}")
    
    def process_assignment(stmt: SSAAssignment):
        """Process an assignment statement"""
        nonlocal variable_declarations, assertions
        
        # Get variable name
        var_name = stmt.variable.name if isinstance(stmt.variable, Variable) else str(stmt.variable)
        
        # Determine variable type
        var_type = determine_type(stmt.expression)
        variable_types[var_name] = var_type
        
        # Declare the variable
        
        variable_declarations.append(f"(declare-const {var_name} {var_type})")
        
        # Create assertion for the assignment
        expr_smt = translate_expression(stmt.expression)
        assertions.append(f"(assert (= {var_name} {expr_smt}))")
    
    def process_statement(stmt):
        """Process a statement and add corresponding SMT constraints"""
        if isinstance(stmt, SSAAssignment):
            process_assignment(stmt)
        
        elif isinstance(stmt, SSAIfStatement):
            # Process condition
            cond_smt = translate_expression(stmt.condition)
            
            # Process then branch
            for s in stmt.then_branch:
                process_statement(s)
            
            # Process else branch if it exists
            if stmt.else_branch:
                for s in stmt.else_branch:
                    process_statement(s)
            
            
        
        elif isinstance(stmt, SSAWhileLoop):
            # Process phi nodes
            for phi in stmt.phi_nodes:
                if isinstance(phi, SSAAssignment):
                    process_assignment(phi)
            
            # Process condition
            cond_smt = translate_expression(stmt.condition)
            
            # Process loop body
            for s in stmt.body:
                process_statement(s)
            
            
        
        else:
            pass
    
    # Process all statements
    for stmt in ssa_ast.statements:
        process_statement(stmt)
    
    # Combine all parts into the final SMT file
    smt_lines.extend(variable_declarations)
    smt_lines.extend(assertions)
    
    # Rename and define result variable if needed
    if f"{prefix}result" in variable_types:
        var_type = variable_types[f"{prefix}result"]
        smt_lines.append(f"(declare-const {prefix}{result_var} {var_type})")
        smt_lines.append(f"(assert (= {prefix}{result_var} {prefix}result))")
    
    # Write to output file
    with open(output_file, 'w') as f:
        f.write("\n".join(smt_lines))
    
    return smt_lines

def parse_smt_model(model_str: str) -> Dict[str, str]:
    """Parse a Z3 model string and return variable assignments"""
    result = {}
    
    # Match variable definitions in the form: (define-fun var_name () type value)
    var_pattern = r'\(define-fun\s+(\S+)\s+\(\)\s+(\S+)\s+(.+?)\)'
    matches = re.findall(var_pattern, model_str, re.DOTALL)
    
    for var_name, var_type, var_value in matches:
        # Clean up the value
        var_value = var_value.strip()
        if var_value.endswith(')'):
            var_value = var_value[:-1].strip()
        
        result[var_name] = var_value
    
    return result

def extract_variables_from_model(model: Dict[str, str]) -> Dict[str, Dict[str, str]]:
    """
    Extract original program variables from the model
    Groups variables by their base name (before underscore)
    """
    variables = {}
    
    for var_name, var_value in model.items():
        # Parse variable name to extract original name and version
        match = re.match(r'([^_]+)_(\d+)', var_name)
        if match:
            base_name = match.group(1)
            version = int(match.group(2))
            
            if base_name not in variables:
                variables[base_name] = {}
            
            variables[base_name][version] = var_value
    
    return variables