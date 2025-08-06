from parser import *
from typing import Dict, List, Set, Tuple
import copy
from parser_eq import IfStatement,Program,WhileLoop,Variable,BinaryOp,Boolean,Number,UnaryOp,ArrayAccess,Assignment,ForLoop,AssertStatement

class SSANode(ASTNode):
    """Base class for all SSA nodes"""
    pass

class SSAProgram(SSANode):
    def __init__(self, statements, phi_functions=None):
        self.statements = statements
        self.phi_functions = phi_functions or {}  # Map from var to list of (block, var) tuples

class SSAAssignment(SSANode):
    def __init__(self, variable, expression):
        self.variable = variable
        self.expression = expression

class SSAIfStatement(SSANode):
    def __init__(self, condition, then_branch, else_branch=None):
        self.condition = condition
        self.then_branch = then_branch
        self.else_branch = else_branch

class SSAWhileLoop(SSANode):
    def __init__(self, condition, body, phi_nodes=None):
        self.condition = condition
        self.body = body
        self.phi_nodes = phi_nodes or []  # Phi nodes at loop entry

class SSAPhiFunction(SSANode):
    def __init__(self, variable, sources):
        self.variable = variable
        self.sources = sources  # List of (block_id, variable) tuples

def convert_to_ssa(ast_node, prefix=""):
    """Convert AST to SSA form"""
    # Keep track of variable versions
    var_versions = {}  # Maps var_name -> current_version
    var_defs = {}  # Maps var_name -> list of defined SSA vars
    
    def get_new_var(var_name):
        """Get a new SSA variable name"""
        if var_name not in var_versions:
            var_versions[var_name] = 0
        else:
            var_versions[var_name] += 1
        
        ssa_name = f"{prefix}{var_name}_{var_versions[var_name]}"
        
        if var_name not in var_defs:
            var_defs[var_name] = []
        var_defs[var_name].append(ssa_name)
        
        return ssa_name
    
    def get_current_var(var_name):
        """Get the current SSA variable name"""
        if var_name not in var_versions:
            # If variable is used before definition, give it an initial version
            return get_new_var(var_name)
        
        return f"{prefix}{var_name}_{var_versions[var_name]}"
    
    def transform_expression(expr):
        """Transform expression to SSA form"""
        if isinstance(expr, Variable):
            # Replace variable references with their current SSA version
            return Variable(get_current_var(expr.name))
        
        elif isinstance(expr, Number) or isinstance(expr, Boolean):
            # Constants remain unchanged
            return copy.deepcopy(expr)
        
        elif isinstance(expr, BinaryOp):
            # Recursively transform operands
            return BinaryOp(
                transform_expression(expr.left),
                expr.op,
                transform_expression(expr.right)
            )
        
        elif isinstance(expr, UnaryOp):
            # Recursively transform operand
            return UnaryOp(
                expr.op,
                transform_expression(expr.expr)
            )
        
        elif isinstance(expr, ArrayAccess):
            # Transform array access (both array name and index)
            array_var = get_current_var(expr.array)
            index_expr = transform_expression(expr.index)
            return ArrayAccess(array_var, index_expr)
        
        else:
            # For other expressions, make a deep copy
            return copy.deepcopy(expr)
    
    def transform_assignment(stmt):
        """Transform assignment to SSA form"""
        if isinstance(stmt.variable, Variable):
            # Regular variable assignment
            var_name = stmt.variable.name
            new_var = get_new_var(var_name)
            return SSAAssignment(
                Variable(new_var),
                transform_expression(stmt.expression)
            )
        elif isinstance(stmt.variable, ArrayAccess):
            # Array assignment is more complex in SSA
            # We need to create a new version of the array
            array_name = stmt.variable.array
            new_array = get_new_var(array_name)
            return SSAAssignment(
                Variable(new_array),
                BinaryOp(
                    Variable(get_current_var(array_name)),
                    "with",
                    BinaryOp(
                        transform_expression(stmt.variable.index),
                        "=",
                        transform_expression(stmt.expression)
                    )
                )
            )
        else:
            raise ValueError(f"Unsupported assignment target: {stmt.variable}")
    
    def transform_if_statement(stmt):
        """Transform if statement to SSA form"""
        # Save variable versions before the if statement
        before_vars = var_versions.copy()
        
        # Transform condition and store it in a new variable
        ssa_condition = transform_expression(stmt.condition)
        condition_var_name = get_new_var("phi")
        condition_var = Variable(condition_var_name)
        condition_assignment = SSAAssignment(condition_var, ssa_condition)
        
        # Transform then branch
        ssa_then = [transform_statement(s) for s in stmt.then_branch]
        
        # Save variable versions after then branch
        then_vars = var_versions.copy()
        
        # Restore variable versions to before the if
        var_versions.update(before_vars)
        
        # Transform else branch
        ssa_else = []
        if stmt.else_branch:
            ssa_else = [transform_statement(s) for s in stmt.else_branch]
        
        # Save variable versions after else branch
        else_vars = var_versions.copy()
        
        # Create phi nodes for variables modified in either branch
        phi_nodes = []
        modified_vars = set()
        
        for var in set(then_vars.keys()) | set(else_vars.keys()):
            # If variable version changed in either branch
            if (var in then_vars and before_vars.get(var, -1) != then_vars[var]) or \
               (var in else_vars and before_vars.get(var, -1) != else_vars[var]):
                modified_vars.add(var)
                
                # Create a new version for after the if
                new_var = get_new_var(var)
                
                # Create sources for phi function
                then_source = f"{prefix}{var}_{then_vars.get(var, before_vars.get(var, 0))}"
                else_source = f"{prefix}{var}_{else_vars.get(var, before_vars.get(var, 0))}"
                
                # Create phi assignment using the ternary operator as in the example
                phi_nodes.append(
                    SSAAssignment(
                        Variable(new_var),
                        BinaryOp(
                            condition_var,
                            "?",
                            BinaryOp(
                                Variable(then_source),
                                ":",
                                Variable(else_source)
                            )
                        )
                    )
                )
        
        # We'll now return the condition assignment followed by both branches (without if statement)
        # and then the phi nodes
        result = [condition_assignment]
        result.extend(ssa_then)
        result.extend(ssa_else)
        result.extend(phi_nodes)
        
        return result
    
    def transform_while_loop(stmt):
        """Transform while loop to SSA form"""
        # Save variable versions before the loop
        before_vars = var_versions.copy()
        
        # Create phi nodes for all variables that might be modified in the loop
        # This is conservative - we create phi nodes for all variables defined so far
        phi_nodes = []
        for var in var_versions:
            new_var = get_new_var(var)
            # The phi function has two sources: the entry value and the loop back value
            phi_nodes.append(
                SSAAssignment(
                    Variable(new_var),
                    Variable(f"{prefix}{var}_{before_vars.get(var, 0)}")  # Initially from before loop
                )
            )
        
        # Transform condition with the phi node versions
        ssa_condition = transform_expression(stmt.condition)
        
        # Transform loop body
        ssa_body = [transform_statement(s) for s in stmt.body]
        
        # After loop, create new versions for all variables modified in the loop
        after_vars = var_versions.copy()
        for var in after_vars:
            if before_vars.get(var, -1) != after_vars.get(var, -1):
                # Only create a new version if the variable was modified in the loop
                new_var = get_new_var(var)
                # No need to add an explicit phi function here, as control flow is linear
        
        return SSAWhileLoop(ssa_condition, ssa_body, phi_nodes)
    
    def transform_for_loop(stmt):
        """Transform for loop to SSA form"""
        # A for loop is transformed into:
        # 1. Initialization
        # 2. While loop with condition and body (followed by update)
        
        # Transform initialization
        ssa_init = transform_statement(stmt.init) if stmt.init else None
        
        # Save variable versions after initialization
        after_init_vars = var_versions.copy()
        
        # Create phi nodes for all variables that might be modified in the loop
        phi_nodes = []
        for var in var_versions:
            new_var = get_new_var(var)
            phi_nodes.append(
                SSAAssignment(
                    Variable(new_var),
                    Variable(f"{prefix}{var}_{after_init_vars.get(var, 0)}")
                )
            )
        
        # Transform condition with the phi node versions
        ssa_condition = transform_expression(stmt.condition) if stmt.condition else Boolean(True)
        
        # Transform loop body
        ssa_body = [transform_statement(s) for s in stmt.body]
        
        # Transform update and add to the end of the body
        if stmt.update:
            ssa_update = transform_statement(stmt.update)
            ssa_body.append(ssa_update)
        
        # Create while loop with the transformed components
        result = []
        if ssa_init:
            if isinstance(ssa_init, list):
                result.extend(ssa_init)
            else:
                result.append(ssa_init)
        
        result.append(SSAWhileLoop(ssa_condition, ssa_body, phi_nodes))
        return result
    
    def transform_statement(stmt):
        """Transform a statement to SSA form"""
        if isinstance(stmt, Assignment):
            return transform_assignment(stmt)
        
        elif isinstance(stmt, IfStatement):
            return transform_if_statement(stmt)
        
        elif isinstance(stmt, WhileLoop):
            return transform_while_loop(stmt)
        
        elif isinstance(stmt, ForLoop):
            return transform_for_loop(stmt)
        
        else:
            # For other statements, make a deep copy
            return copy.deepcopy(stmt)
    
    if isinstance(ast_node, Program):
        ssa_statements = []
        for stmt in ast_node.statements:
            result = transform_statement(stmt)
            # Handle case where transform_statement returns a list
            if isinstance(result, list):
                ssa_statements.extend(result)
            else:
                ssa_statements.append(result)
        
        return SSAProgram(ssa_statements)
    
    else:
        result = transform_statement(ast_node)
        # Handle case where transform_statement returns a list
        if isinstance(result, list):
            return SSAProgram(result)
        else:
            return SSAProgram([result])


def ssa_to_string(node, indent=0):
    """Convert an SSA AST to a readable string representation"""
    if isinstance(node, SSAProgram):
        result = ""
        for stmt in node.statements:
            stmt_str = ssa_to_string(stmt, indent)
            if stmt_str:  # Skip empty strings
                result += stmt_str + "\n"
        return result
    
    elif isinstance(node, SSAAssignment):
        var_str = node.variable.name if isinstance(node.variable, Variable) else str(node.variable)
        expr_str = ssa_to_string(node.expression)
        
        # Check if this is a phi function (ternary operation with ? and :)
        is_phi = False
        if isinstance(node.expression, BinaryOp) and node.expression.op == "?":
            left_part = node.expression.left
            if isinstance(left_part, Variable) and left_part.name.startswith("phi"):
                is_phi = True
                phi_var = left_part.name
                
                # Format as shown in the example with a comment explaining the phi function
                if isinstance(node.expression.right, BinaryOp) and node.expression.right.op == ":":
                    then_val = ssa_to_string(node.expression.right.left)
                    else_val = ssa_to_string(node.expression.right.right)
                    
                    # Extract variable name without subscript for comment
                    base_var = var_str.split('_')[0]
                    
                    return " " * indent + f"{var_str} = {phi_var}?{then_val}:{else_val}; // ({phi_var}->{base_var}={then_val})V(~{phi_var}->{base_var}={else_val})"
        
        return " " * indent + f"{var_str} = {expr_str}"
    
    elif isinstance(node, SSAIfStatement):
        result = " " * indent + f"if ({ssa_to_string(node.condition)}) {{\n"
        for stmt in node.then_branch:
            stmt_str = ssa_to_string(stmt, indent + 2)
            if stmt_str:  # Skip empty strings
                result += stmt_str + "\n"
        result += " " * indent + "}"
        
        if node.else_branch:
            result += " else {\n"
            for stmt in node.else_branch:
                stmt_str = ssa_to_string(stmt, indent + 2)
                if stmt_str:  # Skip empty strings
                    result += stmt_str + "\n"
            result += " " * indent + "}"
        
        return result
    
    elif isinstance(node, SSAWhileLoop):
        result = ""
        # Print phi nodes
        for phi in node.phi_nodes:
            result += " " * indent + ssa_to_string(phi) + " // phi function\n"
        
        result += " " * indent + f"while ({ssa_to_string(node.condition)}) {{\n"
        for stmt in node.body:
            stmt_str = ssa_to_string(stmt, indent + 2)
            if stmt_str:  # Skip empty strings
                result += stmt_str + "\n"
        result += " " * indent + "}"
        return result
    
    elif isinstance(node, SSAPhiFunction):
        var_str = node.variable.name if isinstance(node.variable, Variable) else str(node.variable)
        sources_str = ", ".join([f"{src[0]}: {src[1]}" for src in node.sources])
        return f"{var_str} = phi({sources_str})"
    
    elif isinstance(node, BinaryOp):
        left_str = ssa_to_string(node.left)
        right_str = ssa_to_string(node.right)
        return f"({left_str} {node.op} {right_str})"
    
    elif isinstance(node, UnaryOp):
        expr_str = ssa_to_string(node.expr)
        return f"{node.op}{expr_str}"
    
    elif isinstance(node, Variable):
        return node.name
    
    elif isinstance(node, ArrayAccess):
        array_str = ssa_to_string(node.array) if isinstance(node.array, ASTNode) else str(node.array)
        index_str = ssa_to_string(node.index)
        return f"{array_str}[{index_str}]"
    
    elif isinstance(node, Number):
        return str(node.value)
    
    elif isinstance(node, Boolean):
        return str(node.value).lower()
    
    else:
        return str(node)