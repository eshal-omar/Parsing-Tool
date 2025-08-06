import re
from typing import Dict, List, Tuple, Any, Optional, Union
import ast

class ASTNode:
    """Base class for all AST nodes"""
    pass

class Program(ASTNode):
    def __init__(self, statements):
        self.statements = statements

class Statement(ASTNode):
    """Base class for all statements"""
    pass

class Assignment(Statement):
    def __init__(self, variable, expression):
        self.variable = variable
        self.expression = expression

class IfStatement(Statement):
    def __init__(self, condition, then_branch, else_branch=None):
        self.condition = condition
        self.then_branch = then_branch
        self.else_branch = else_branch

class WhileLoop(Statement):
    def __init__(self, condition, body):
        self.condition = condition
        self.body = body

class ForLoop(Statement):
    def __init__(self, init, condition, update, body):
        self.init = init
        self.condition = condition
        self.update = update
        self.body = body

class AssertStatement(Statement):
    def __init__(self, condition):
        self.condition = condition

class Expression(ASTNode):
    """Base class for all expressions"""
    pass

class BinaryOp(Expression):
    def __init__(self, left, op, right):
        self.left = left
        self.op = op
        self.right = right

class UnaryOp(Expression):
    def __init__(self, op, expr):
        self.op = op
        self.expr = expr

class Variable(Expression):
    def __init__(self, name):
        self.name = name

class ArrayAccess(Expression):
    def __init__(self, array, index):
        self.array = array
        self.index = index

class Number(Expression):
    def __init__(self, value):
        self.value = value

class Boolean(Expression):
    def __init__(self, value):
        self.value = value


def tokenize(program: str) -> List[str]:
    """Tokenize the input program"""
    # Replace common symbols with space-padded versions for easier tokenization
    program = program.replace(";", " ; ")
    program = program.replace("(", " ( ")
    program = program.replace(")", " ) ")
    program = program.replace("{", " { ")
    program = program.replace("}", " } ")
    program = program.replace("[", " [ ")
    program = program.replace("]", " ] ")
    program = program.replace(":=", " := ")
    program = program.replace("==", " == ")
    program = program.replace("!=", " != ")
    program = program.replace("<=", " <= ")
    program = program.replace(">=", " >= ")
    program = program.replace("<", " < ")
    program = program.replace(">", " > ")
    program = program.replace("+", " + ")
    program = program.replace("-", " - ")
    program = program.replace("*", " * ")
    program = program.replace("/", " / ")
    program = program.replace("%", " % ")
    program = program.replace("&&", " && ")
    program = program.replace("||", " || ")
    program = program.replace("!", " ! ")
    
    # Split by whitespace and filter out empty tokens
    tokens = [token for token in program.split() if token.strip()]
    return tokens


def parse_program(program: str) -> Program:
    """Parse the input program into an AST"""
    tokens = tokenize(program)
    idx = [0]  # Use list to pass by reference

    def parse_statements() -> List[Statement]:
        """Parse a list of statements"""
        statements = []
        while idx[0] < len(tokens) and tokens[idx[0]] != "}":
            statement = parse_statement()
            if statement:  # Skip None statements (like standalone semicolons)
                statements.append(statement)
        return statements

    def parse_statement() -> Optional[Statement]:
        """Parse a single statement"""
        if idx[0] >= len(tokens):
            return None

        token = tokens[idx[0]]
        
        # Assignment: x := expr;
        if is_identifier(token) and idx[0] + 1 < len(tokens) and tokens[idx[0] + 1] == ":=":
            return parse_assignment()
        
        # If statement: if (condition) { ... } else { ... }
        elif token == "if":
            return parse_if_statement()
        
        # While loop: while (condition) { ... }
        elif token == "while":
            return parse_while_loop()
        
        # For loop: for (init; condition; update) { ... }
        elif token == "for":
            return parse_for_loop()
        
        # Assert statement: assert(condition);
        elif token == "assert":
            return parse_assert_statement()
        
        # Skip semicolons
        elif token == ";":
            idx[0] += 1
            return None
        
        # Unknown statement
        else:
            raise SyntaxError(f"Unexpected token '{token}' at position {idx[0]}")

    def parse_assignment() -> Assignment:
        """Parse an assignment statement: var := expr;"""
        variable = parse_variable()
        
        # Handle array assignment: arr[idx] := expr;
        if idx[0] < len(tokens) and tokens[idx[0]] == "[":
            idx[0] += 1  # Skip [
            index_expr = parse_expression()
            consume("]")
            consume(":=")
            expr = parse_expression()
            consume(";")
            return Assignment(ArrayAccess(variable.name, index_expr), expr)
        
        # Regular variable assignment
        consume(":=")
        expr = parse_expression()
        consume(";")
        return Assignment(variable, expr)

    def parse_if_statement() -> IfStatement:
        """Parse an if statement: if (condition) { then_branch } else { else_branch }"""
        consume("if")
        consume("(")
        condition = parse_expression()
        consume(")")
        consume("{")
        then_branch = parse_statements()
        consume("}")
        
        # Check for else clause
        else_branch = None
        if idx[0] < len(tokens) and tokens[idx[0]] == "else":
            idx[0] += 1  # Skip 'else'
            consume("{")
            else_branch = parse_statements()
            consume("}")
        
        return IfStatement(condition, then_branch, else_branch)

    def parse_while_loop() -> WhileLoop:
        """Parse a while loop: while (condition) { body }"""
        consume("while")
        consume("(")
        condition = parse_expression()
        consume(")")
        consume("{")
        body = parse_statements()
        consume("}")
        return WhileLoop(condition, body)

    def parse_for_loop() -> ForLoop:
        """Parse a for loop: for (init; condition; update) { body }"""
        consume("for")
        consume("(")
        
        # Parse initialization
        init = parse_assignment() if not tokens[idx[0]] == ";" else None
        if not init:
            consume(";")
        
        # Parse condition
        condition = parse_expression() if not tokens[idx[0]] == ";" else None
        consume(";")
        
        # Parse update
        if tokens[idx[0]] == ")":
            update = None
        else:
            # Update might be a special case that doesn't end with semicolon
            var = parse_variable()
            consume(":=")
            expr = parse_expression()
            update = Assignment(var, expr)
        
        consume(")")
        consume("{")
        body = parse_statements()
        consume("}")
        
        return ForLoop(init, condition, update, body)

    def parse_assert_statement() -> AssertStatement:
        """Parse an assert statement: assert(condition);"""
        consume("assert")
        consume("(")
        condition = parse_expression()
        consume(")")
        consume(";")
        return AssertStatement(condition)

    def parse_expression() -> Expression:
        """Parse an expression"""
        return parse_logical_expression()

    def parse_logical_expression() -> Expression:
        """Parse logical operations (&&, ||)"""
        expr = parse_comparison_expression()
        
        while idx[0] < len(tokens) and tokens[idx[0]] in ["&&", "||"]:
            op = tokens[idx[0]]
            idx[0] += 1
            right = parse_comparison_expression()
            expr = BinaryOp(expr, op, right)
        
        return expr

    def parse_comparison_expression() -> Expression:
        """Parse comparison operations (==, !=, <, >, <=, >=)"""
        expr = parse_arithmetic_expression()
        
        while idx[0] < len(tokens) and tokens[idx[0]] in ["==", "!=", "<", ">", "<=", ">="]:
            op = tokens[idx[0]]
            idx[0] += 1
            right = parse_arithmetic_expression()
            expr = BinaryOp(expr, op, right)
        
        return expr

    def parse_arithmetic_expression() -> Expression:
        """Parse arithmetic operations (+, -)"""
        expr = parse_term()
        
        while idx[0] < len(tokens) and tokens[idx[0]] in ["+", "-"]:
            op = tokens[idx[0]]
            idx[0] += 1
            right = parse_term()
            expr = BinaryOp(expr, op, right)
        
        return expr

    def parse_term() -> Expression:
        """Parse term operations (*, /, %)"""
        expr = parse_factor()
        
        while idx[0] < len(tokens) and tokens[idx[0]] in ["*", "/", "%"]:
            op = tokens[idx[0]]
            idx[0] += 1
            right = parse_factor()
            expr = BinaryOp(expr, op, right)
        
        return expr

    def parse_factor() -> Expression:
        """Parse a factor (number, variable, parenthesized expression)"""
        if idx[0] >= len(tokens):
            raise SyntaxError("Unexpected end of input")
        
        token = tokens[idx[0]]
        
        # Unary operators
        if token in ["+", "-", "!"]:
            idx[0] += 1
            expr = parse_factor()
            return UnaryOp(token, expr)
        
        # Parenthesized expression
        elif token == "(":
            idx[0] += 1
            expr = parse_expression()
            consume(")")
            return expr
        
        # Number
        elif is_number(token):
            idx[0] += 1
            return Number(int(token) if token.isdigit() else float(token))
        
        # Boolean literals
        elif token.lower() in ["true", "false"]:
            idx[0] += 1
            return Boolean(token.lower() == "true")
        
        # Array access or variable
        elif is_identifier(token):
            return parse_variable_or_array_access()
        
        else:
            raise SyntaxError(f"Unexpected token '{token}' at position {idx[0]}")

    def parse_variable_or_array_access() -> Expression:
        """Parse a variable or array access"""
        var_name = tokens[idx[0]]
        idx[0] += 1
        
        # Array access: arr[index]
        if idx[0] < len(tokens) and tokens[idx[0]] == "[":
            idx[0] += 1  # Skip [
            index_expr = parse_expression()
            consume("]")
            return ArrayAccess(var_name, index_expr)
        
        # Simple variable
        return Variable(var_name)

    def parse_variable() -> Variable:
        """Parse a variable"""
        if not is_identifier(tokens[idx[0]]):
            raise SyntaxError(f"Expected identifier, got '{tokens[idx[0]]}'")
        
        var_name = tokens[idx[0]]
        idx[0] += 1
        return Variable(var_name)

    def consume(expected: str):
        """Consume an expected token"""
        if idx[0] >= len(tokens):
            raise SyntaxError(f"Unexpected end of input, expected '{expected}'")
        
        if tokens[idx[0]] != expected:
            raise SyntaxError(f"Expected '{expected}', got '{tokens[idx[0]]}'")
        
        idx[0] += 1

    def is_identifier(token: str) -> bool:
        """Check if a token is a valid identifier"""
        return re.match(r'^[a-zA-Z_][a-zA-Z0-9_]*$', token) is not None

    def is_number(token: str) -> bool:
        """Check if a token is a valid number"""
        try:
            float(token)
            return True
        except ValueError:
            return False

    # Start parsing
    statements = parse_statements()
    return Program(statements)


def ast_to_string(node, indent=0):
    """Convert an AST to a readable string representation for debugging"""
    if isinstance(node, Program):
        return "\n".join([ast_to_string(stmt, indent) for stmt in node.statements])
    
    elif isinstance(node, Assignment):
        if isinstance(node.variable, ArrayAccess):
            var_str = f"{node.variable.array}[{ast_to_string(node.variable.index)}]"
        else:
            var_str = node.variable.name if hasattr(node.variable, 'name') else str(node.variable)
        return " " * indent + f"{var_str} := {ast_to_string(node.expression)}"
    
    elif isinstance(node, IfStatement):
        result = " " * indent + f"if ({ast_to_string(node.condition)}) {{\n"
        for stmt in node.then_branch:
            result += ast_to_string(stmt, indent + 2) + "\n"
        result += " " * indent + "}"
        
        if node.else_branch:
            result += " else {\n"
            for stmt in node.else_branch:
                result += ast_to_string(stmt, indent + 2) + "\n"
            result += " " * indent + "}"
        
        return result
    
    elif isinstance(node, WhileLoop):
        result = " " * indent + f"while ({ast_to_string(node.condition)}) {{\n"
        for stmt in node.body:
            result += ast_to_string(stmt, indent + 2) + "\n"
        result += " " * indent + "}"
        return result
    
    elif isinstance(node, ForLoop):
        init_str = ast_to_string(node.init) if node.init else ""
        cond_str = ast_to_string(node.condition) if node.condition else ""
        update_str = ast_to_string(node.update) if node.update else ""
        
        result = " " * indent + f"for ({init_str}; {cond_str}; {update_str}) {{\n"
        for stmt in node.body:
            result += ast_to_string(stmt, indent + 2) + "\n"
        result += " " * indent + "}"
        return result
    
    elif isinstance(node, AssertStatement):
        return " " * indent + f"assert({ast_to_string(node.condition)})"
    
    elif isinstance(node, BinaryOp):
        return f"({ast_to_string(node.left)} {node.op} {ast_to_string(node.right)})"
    
    elif isinstance(node, UnaryOp):
        return f"{node.op}{ast_to_string(node.expr)}"
    
    elif isinstance(node, Variable):
        return node.name
    
    elif isinstance(node, ArrayAccess):
        return f"{node.array}[{ast_to_string(node.index)}]"
    
    elif isinstance(node, Number):
        return str(node.value)
    
    elif isinstance(node, Boolean):
        return str(node.value).lower()
    
    else:
        return str(node)


