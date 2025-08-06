from parser import ASTNode

class SSAConverter:
    def __init__(self):
        self.var_counters = {}  # Keep track of variable versions
        self.array_counters = {}  # Keep track of array versions
        self.ssa_code = []  # Store the SSA representation
        self.phi_nodes = {}  # Store phi nodes for each variable
        self.phi_counter = 1  # Counter for phi node labels
    
    def reset(self):
        """Reset the state of the converter."""
        self.var_counters = {}
        self.array_counters = {}
        self.ssa_code = []
        self.phi_nodes = {}
        self.phi_counter = 1
    
    def get_var_version(self, var):
        """Get the current version of a variable."""
        if var not in self.var_counters:
            self.var_counters[var] = 0
        return self.var_counters[var]
    
    def get_array_version(self, arrayname):
        """Get the current version of an array."""
        if arrayname not in self.var_counters:
            self.var_counters[arrayname] = 0
        return self.var_counters[arrayname]
    
    def increment_var(self, var):
        """Increment the version of a variable."""
        if var not in self.var_counters:
            self.var_counters[var] = 0
        self.var_counters[var] += 1
        return self.var_counters[var]
    
    def increment_array(self, arrayname):
        """Increment the version of an array."""
        if arrayname not in self.var_counters:
            self.var_counters[arrayname] = 0
        self.var_counters[arrayname] += 1
        return self.var_counters[arrayname]
    
    def convert_to_ssa(self, ast):
        """Convert the AST to SSA form."""
        self.reset()
        ssa_ast = []
        
        for node in ast:
            if node.type == "assign":
                ssa_node = self._convert_assignment(node)
                self.ssa_code.append(ssa_node)
                ssa_ast.append(ssa_node)
            
            elif node.type == "if":
                if_ssa = self._convert_if_statement(node)
                self.ssa_code.extend(if_ssa)
                ssa_ast.extend(if_ssa)
            
            elif node.type == "while":
                while_ssa = self._convert_while_loop(node)
                self.ssa_code.extend(while_ssa)
                ssa_ast.extend(while_ssa)
            
            elif node.type == "for":
                for_ssa = self._convert_for_loop(node)
                self.ssa_code.extend(for_ssa)
                ssa_ast.extend(for_ssa)
            
            elif node.type == "assert":
                assert_ssa = self._convert_assert(node)
                self.ssa_code.append(assert_ssa)
                ssa_ast.append(assert_ssa)
            
            else:
                # Just pass through nodes we don't specifically handle
                self.ssa_code.append(node)
                ssa_ast.append(node)
        
        return ssa_ast
    
    def _convert_assignment(self, node):
        """Convert an assignment node to SSA form."""
        var = node.value["var"]
        expr = node.value["expr"]
        
        # Replace variables in the expression with their current versions
        ssa_expr = self._replace_vars_in_expr(expr)
        
        # Check if this is an array assignment
        if "[" in var:
            # Handle array assignment (e.g., arr[j] := value)
            array_parts = var.split("[", 1)
            arrayname = array_parts[0].strip()
            index_expr = array_parts[1].rstrip("]").strip()
            
            # Replace variables in the index expression
            ssa_index = self._replace_vars_in_expr(index_expr)
            
            # Get the current array version
            array_ver = self.get_array_version(arrayname)
            
            # Create a new array version
            new_array_ver = self.increment_array(arrayname)
            
            # Create an SSA array assignment node with proper formatting
            ssa_node = ASTNode("assign", value={
                "var": f"{arrayname}_{new_array_ver}[{ssa_index}]",
                "expr": ssa_expr
            })
        else:
            # Regular variable assignment
            new_version = self.increment_var(var)
            
            # Create an SSA assignment node
            ssa_node = ASTNode("assign", value={
                "var": f"{var}_{new_version}",
                "expr": ssa_expr
            })
        
        return ssa_node
    
    def _create_phi_node(self, var, condition, then_ver, else_ver, is_loop=False):
        """Create a phi node for a variable."""
        phi_id = self.phi_counter
        self.phi_counter += 1
        
        # Find or create the next version for this variable
        next_ver = max(then_ver, else_ver) + 1
        self.var_counters[var] = next_ver
        
        if is_loop:
            ssa_node = ASTNode("phi", value={
                "id": phi_id,
                "var": f"{var}_{next_ver}",
                "condition": condition,
                "entry": f"{var}_{else_ver}",
                "loop": f"{var}_{then_ver}"
            })
        else:
            ssa_node = ASTNode("phi", value={
                "id": phi_id,
                "var": f"{var}_{next_ver}",
                "condition": condition,
                "then": f"{var}_{then_ver}",
                "else": f"{var}_{else_ver}"
            })
        
        return ssa_node
    
    def _convert_if_statement(self, node):
        """Convert an if statement to SSA form."""
        # Convert condition to SSA form
        condition = node.value
        ssa_condition = self._replace_vars_in_expr(condition)
        
        # Create a condition variable to store the if condition result
        cond_var = f"φ{self.phi_counter}"
        self.phi_counter += 1
        
        cond_node = ASTNode("condition", value={
            "var": cond_var,
            "expr": f"({ssa_condition})"
        })
        
        # Save the current variable versions before the branches
        pre_if_vars = self.var_counters.copy()
        
        # Convert the then branch
        then_branch = node.children[0].children
        then_converter = SSAConverter()
        then_converter.var_counters = pre_if_vars.copy()
        then_converter.phi_counter = self.phi_counter
        then_ssa = then_converter.convert_to_ssa(then_branch)
        
        # Update our phi counter with any that were created in the then branch
        self.phi_counter = then_converter.phi_counter
        
        # Save the then branch variable versions
        then_vars = then_converter.var_counters
        
        # Convert the else branch
        else_branch = node.children[1].children
        else_converter = SSAConverter()
        else_converter.var_counters = pre_if_vars.copy()
        else_converter.phi_counter = self.phi_counter
        else_ssa = else_converter.convert_to_ssa(else_branch)
        
        # Update our phi counter
        self.phi_counter = else_converter.phi_counter
        
        # Save the else branch variable versions
        else_vars = else_converter.var_counters
        
        # Create the if node with its branches
        then_block = ASTNode("then", children=then_ssa)
        else_block = ASTNode("else", children=else_ssa)
        
        if_node = ASTNode("if", children=[then_block, else_block], value=cond_var)
        
        # Create phi nodes for variables modified in either branch
        phi_nodes = []
        all_vars = set(then_vars.keys()) | set(else_vars.keys()) | set(pre_if_vars.keys())
        
        for var in all_vars:
            pre_ver = pre_if_vars.get(var, 0)
            then_ver = then_vars.get(var, pre_ver)
            else_ver = else_vars.get(var, pre_ver)
            
            # Only create phi nodes for variables that were modified
            if then_ver != pre_ver or else_ver != pre_ver:
                # Increment to a new version
                new_ver = max(then_ver, else_ver) + 1
                self.var_counters[var] = new_ver
                
                phi_node = ASTNode("phi", value={
                    "id": self.phi_counter,
                    "var": f"{var}_{new_ver}",
                    "condition": cond_var,
                    "then": f"{var}_{then_ver}",
                    "else": f"{var}_{else_ver}"
                })
                self.phi_counter += 1
                phi_nodes.append(phi_node)
        
        # Final result: condition node + if node + phi nodes
        result = [cond_node, if_node] + phi_nodes
        return result
    
    def _convert_while_loop(self, node):
        """Convert a while loop to SSA form using phi nodes."""
        # Save the current variable versions before the loop
        pre_loop_vars = self.var_counters.copy()
        
        # Create entry phi nodes for all variables that might be modified in the loop
        entry_phi_nodes = []
        
        # Convert condition to SSA form
        original_condition = node.value
        ssa_condition = self._replace_vars_in_expr(original_condition)
        
        # Create a condition variable to store the while condition result
        cond_var = f"φ{self.phi_counter}"
        self.phi_counter += 1
        
        cond_node = ASTNode("condition", value={
            "var": cond_var,
            "expr": f"({ssa_condition})"
        })
        
        # Create a separate converter for the loop body to preserve variable versions
        body_converter = SSAConverter()
        body_converter.var_counters = self.var_counters.copy()
        body_converter.phi_counter = self.phi_counter
        
        # Process the loop body
        body = node.children
        body_ssa = body_converter.convert_to_ssa(body)
        
        # Update phi counter
        self.phi_counter = body_converter.phi_counter
        
        # Post-loop variable versions
        body_vars = body_converter.var_counters
        
        # Create the while loop node
        while_node = ASTNode("while", children=body_ssa, value=cond_var)
        
        # Create phi nodes for all variables modified inside the loop
        all_vars = set(body_vars.keys()) | set(pre_loop_vars.keys())
        
        for var in all_vars:
            pre_ver = pre_loop_vars.get(var, 0)
            body_ver = body_vars.get(var, pre_ver)
            
            # Only create phi nodes for variables that were modified
            if body_ver != pre_ver:
                # Create new version for loop phi node
                new_ver = body_ver + 1
                self.var_counters[var] = new_ver
                
                # Create phi node for loop entry
                phi_node = ASTNode("phi", value={
                    "id": self.phi_counter,
                    "var": f"{var}_{new_ver}",
                    "condition": cond_var,
                    "entry": f"{var}_{pre_ver}",
                    "loop": f"{var}_{body_ver}"
                })
                self.phi_counter += 1
                entry_phi_nodes.append(phi_node)
        
        # Final result: condition + phi nodes + while loop
        result = [cond_node] + entry_phi_nodes + [while_node]
        return result
    
    def _convert_for_loop(self, node):
        """Convert a for loop to SSA form with phi nodes."""
        # Handle loop initialization
        init = node.value["init"]
        init_var = init["var"]
        init_expr = init["expr"]
        ssa_init_expr = self._replace_vars_in_expr(init_expr)
        
        # Create initialization assignment
        init_ver = self.increment_var(init_var)
        init_node = ASTNode("assign", value={
            "var": f"{init_var}_{init_ver}",
            "expr": ssa_init_expr
        })
        
        # Save the current variable versions after initialization
        pre_loop_vars = self.var_counters.copy()
        
        # Convert condition to SSA form
        cond = node.value["cond"]
        ssa_cond = self._replace_vars_in_expr(cond)
        
        # Create a condition variable
        cond_var = f"φ{self.phi_counter}"
        self.phi_counter += 1
        
        cond_node = ASTNode("condition", value={
            "var": cond_var,
            "expr": f"({ssa_cond})"
        })
        
        # Create a separate converter for the loop body
        body_converter = SSAConverter()
        body_converter.var_counters = pre_loop_vars.copy()
        body_converter.phi_counter = self.phi_counter
        
        # Convert the loop body
        body = node.children
        body_ssa = body_converter.convert_to_ssa(body)
        
        # Update phi counter
        self.phi_counter = body_converter.phi_counter
        
        # Get the post-body variable versions
        post_body_vars = body_converter.var_counters
        
        # Handle the increment
        incr = node.value["incr"]
        incr_var = incr["var"]
        incr_expr = incr["expr"]
        
        # Convert increment expression to SSA using the body converter's state
        incr_ssa_expr = body_converter._replace_vars_in_expr(incr_expr)
        
        # Create increment assignment using the body converter to get proper versions
        incr_ver = body_converter.increment_var(incr_var)
        incr_node = ASTNode("assign", value={
            "var": f"{incr_var}_{incr_ver}",
            "expr": incr_ssa_expr
        })
        
        # Add increment to the end of the body
        body_ssa.append(incr_node)
        
        # Final body variable versions (including increment)
        body_vars = body_converter.var_counters
        
        # Create the for loop node with updated init and incr variables
        for_node = ASTNode("for", value={
            "init": {"var": f"{init_var}_{init_ver}", "expr": ssa_init_expr},
            "cond": cond_var,
            "incr": {"var": f"{incr_var}_{incr_ver}", "expr": incr_ssa_expr}
        }, children=body_ssa)
        
        # Create phi nodes for all modified variables
        entry_phi_nodes = []
        all_vars = set(body_vars.keys()) | set(pre_loop_vars.keys())
        
        for var in all_vars:
            pre_ver = pre_loop_vars.get(var, 0)
            loop_ver = body_vars.get(var, pre_ver)
            
            # Only create phi nodes for variables that were modified
            if loop_ver != pre_ver:
                # Create new version for the loop phi node
                new_ver = loop_ver + 1
                self.var_counters[var] = new_ver
                
                phi_node = ASTNode("phi", value={
                    "id": self.phi_counter,
                    "var": f"{var}_{new_ver}",
                    "condition": cond_var,
                    "entry": f"{var}_{pre_ver}",
                    "loop": f"{var}_{loop_ver}"
                })
                self.phi_counter += 1
                entry_phi_nodes.append(phi_node)
        
        # Final result: Init + condition + phi nodes + for loop
        result = [init_node, cond_node] + entry_phi_nodes + [for_node]
        return result
    
    def _convert_assert(self, node):
        """Convert an assert statement to SSA form."""
        condition = node.value
        
        # Replace variables in the condition with their current versions
        ssa_condition = self._replace_vars_in_expr(condition)
        
        # Create an SSA assert node
        ssa_node = ASTNode("assert", value=ssa_condition)
        
        return ssa_node
    
    def _replace_vars_in_expr(self, expr):
        """Replace variables in an expression with their SSA versions."""
        if not expr or not isinstance(expr, str):
            return expr
        
        # Handle variable names and array accesses
        tokens = self._tokenize_expression(expr)
        result = []
        
        i = 0
        while i < len(tokens):
            token = tokens[i]
            
            # Check if this is an array access
            if i + 2 < len(tokens) and tokens[i+1] == '[' and ']' in tokens[i+3:]:
                #found array access pattern: arrayname [ index ]
                arrayname = token
                index_start = i + 2
                
                #find the matching closing bracket
                bracket_depth = 1
                index_end = index_start
                while index_end < len(tokens) and bracket_depth > 0:
                    index_end += 1
                    if index_end < len(tokens):
                        if tokens[index_end] == '[':
                            bracket_depth += 1
                        elif tokens[index_end] == ']':
                            bracket_depth -= 1
                
                if index_end < len(tokens):
                    #extract & convert the index expression
                    index_tokens = tokens[index_start:index_end]
                    index_expr = ''.join(index_tokens)
                    ssa_index = self._replace_vars_in_expr(index_expr)
                    
                    #gets current array version
                    array_ver = self.get_array_version(arrayname)
                    
                    #sdd SSA array access
                    result.append(f"{arrayname}_{array_ver}[{ssa_index}]")
                    
                    #kip past the processed tokens
                    i = index_end + 1
                else:
                    #corrupt expression, just add the token
                    result.append(token)
                    i += 1
            elif token.isalnum() and token[0].isalpha() and token not in ["and", "or", "not", "true", "false"]:
                # Regular variable - check if it's a valid identifier
                var = token
                # Exclude keywords and common operators
                keywords = ["if", "else", "while", "for", "return", "true", "false", "and", "or", "not"]
                if var not in keywords and not var.isdigit():
                    ver = self.get_var_version(var)
                    result.append(f"{var}_{ver}")
                else:
                    result.append(token)
                i += 1
            else:
                # Other tokens (operators, literals, etc.)
                result.append(token)
                i += 1
        
        return ''.join(result)
    
    def _tokenize_expression(self, expr):
        """Tokenize an expression for SSA conversion."""
        tokens = []
        current_token = ""
        
        i = 0
        while i < len(expr):
            char = expr[i]
            
            if char.isalnum() or char == '_':
                # Part of a variable name or number
                current_token += char
            elif char in "+-*/()[]=<>!&|^%":
                # Operator or delimiter
                if current_token:
                    tokens.append(current_token)
                    current_token = ""
                
                # Check for two-character operators
                if i + 1 < len(expr) and expr[i:i+2] in ["==", "!=", "<=", ">=", "&&", "||"]:
                    tokens.append(expr[i:i+2])
                    i += 1
                else:
                    tokens.append(char)
            elif char.isspace():
                # Whitespace
                if current_token:
                    tokens.append(current_token)
                    current_token = ""
            else:
                # Other character, treat as part of current token
                current_token += char
            
            i += 1
        
        # Add any remaining token
        if current_token:
            tokens.append(current_token)
        
        return tokens


class LoopUnroller:
    def __init__(self):
        pass
    
    def unroll_loops(self, code, depth):
        """Unroll loops in the given code to the specified depth."""
        if depth <= 0:
            return code
        
        # Parse the code into an AST
        from parser import parse_program
        ast = parse_program(code)
        
        # Create unrolled code by duplicating the entire program 'depth' times
        unrolled_ast = []
        for _ in range(depth):
            unrolled_ast.extend(self._process_ast_nodes(ast))
        
        # Convert back to code
        unrolled_code = self._ast_to_code(unrolled_ast)
        
        return unrolled_code
    
    def _process_ast_nodes(self, ast):
        """Process each node in the AST, handling loop structures appropriately."""
        processed_ast = []
        
        for node in ast:
            if node.type == "for":
                #add the for loop w/o unrolling
                processed_ast.append(node)
            elif node.type == "while":
                #add the while loop w/o unrolling
                processed_ast.append(node)
            elif node.type == "if":
                # Process if statements recursively
                then_processed = self._process_ast_nodes(node.children[0].children)
                else_processed = self._process_ast_nodes(node.children[1].children)
                
                if_node = ASTNode("if", children=[
                    ASTNode("then", children=then_processed),
                    ASTNode("else", children=else_processed)
                ], value=node.value)
                
                processed_ast.append(if_node)
            else:
                processed_ast.append(node)
        
        return processed_ast
    
    def _ast_to_code(self, ast):
        """Convert an AST back to code."""
        code_lines = []
        
        for node in ast:
            if node.type == "assign":
                var = node.value["var"]
                expr = node.value["expr"]
                code_lines.append(f"{var} := {expr};")
            
            elif node.type == "if":
                condition = node.value
                then_body = self._ast_to_code(node.children[0].children)
                else_body = self._ast_to_code(node.children[1].children)
                
                code_lines.append(f"if ({condition}) {{")
                code_lines.extend([f"  {line}" for line in then_body.split("\n")])
                
                if else_body:
                    code_lines.append("} else {")
                    code_lines.extend([f"  {line}" for line in else_body.split("\n")])
                
                code_lines.append("}")
            
            elif node.type == "while":
                condition = node.value
                body = self._ast_to_code(node.children)
                
                code_lines.append(f"while ({condition}) {{")
                code_lines.extend([f"  {line}" for line in body.split("\n")])
                code_lines.append("}")
            
            elif node.type == "for":
                init = node.value["init"]
                cond = node.value["cond"]
                incr = node.value["incr"]
                body = self._ast_to_code(node.children)
                
                init_str = f"{init['var']} := {init['expr']}"
                incr_str = f"{incr['var']} := {incr['expr']}"
                
                code_lines.append(f"for ({init_str}; {cond}; {incr_str}) {{")
                code_lines.extend([f"  {line}" for line in body.split("\n")])
                code_lines.append("}")
            
            elif node.type == "assert":
                code_lines.append(f"assert({node.value});")
            
            elif node.type == "phi":
                var = node.value["var"]
                if "then" in node.value and "else" in node.value:
                    then_var = node.value["then"]
                    else_var = node.value["else"]
                    condition = node.value["condition"]
                    code_lines.append(f"{var} = φ({condition} ? {then_var} : {else_var});")
                elif "entry" in node.value and "loop" in node.value:
                    entry_var = node.value["entry"]
                    loop_var = node.value["loop"]
                    condition = node.value["condition"]
                    code_lines.append(f"{var} = φ({condition} ? {entry_var} : {loop_var});")
            
            else:
                code_lines.append(f"// Unrecognized node: {node}")
        
        return "\n".join(code_lines)


def convert_to_ssa(code):
    """Convert the given code to SSA form."""
    # Parse the code into an AST
    from parser import parse_program
    ast = parse_program(code)
    
    # Convert to SSA
    converter = SSAConverter()
    ssa_ast = converter.convert_to_ssa(ast)
    
    # Format the SSA code
    ssa_code = format_ssa(ssa_ast)
    
    return ssa_code

def format_ssa(ssa_ast):
    """Format the SSA AST as readable code."""
    lines = []
    
    for node in ssa_ast:
        if node.type == "assign":
            var = node.value["var"]
            expr = node.value["expr"]
            lines.append(f"{var} := {expr}")
        
        elif node.type == "condition":
            var = node.value["var"]
            expr = node.value["expr"]
            lines.append(f"{var} := {expr}")
        
        elif node.type == "if":
            condition = node.value
            then_body = format_ssa(node.children[0].children)
            else_body = format_ssa(node.children[1].children)
            
            if then_body:
                for line in then_body.split("\n"):
                    if line.strip():
                        lines.append(line)
            
            if else_body:
                for line in else_body.split("\n"):
                    if line.strip():
                        lines.append(line)
        
        elif node.type == "while":
            condition = node.value
            body = format_ssa(node.children)
            
            if body:
                for line in body.split("\n"):
                    if line.strip():
                        lines.append(line)
        
        elif node.type == "for":
            init = node.value["init"]
            cond = node.value["cond"]
            incr = node.value["incr"]
            body = format_ssa(node.children)
            
            if body:
                for line in body.split("\n"):
                    if line.strip():
                        lines.append(line)
        
        elif node.type == "assert":
            lines.append(f"assert({node.value})")
        
        elif node.type == "phi":
            var = node.value["var"]
            phi_id = node.value.get("id", "")
            
            if "then" in node.value and "else" in node.value:
                then_var = node.value["then"]
                else_var = node.value["else"]
                condition = node.value["condition"]
                lines.append(f"{var} := φ{phi_id}({condition} ? {then_var} : {else_var})")
            elif "entry" in node.value and "loop" in node.value:
                entry_var = node.value["entry"]
                loop_var = node.value["loop"]
                condition = node.value["condition"]
                lines.append(f"{var} := φ{phi_id}({condition} ? {entry_var} : {loop_var})")
        
        else:
            lines.append(f"// Unrecognized node: {node}")
    
    return "\n".join(lines)

def unroll_and_convert_to_ssa(code, depth):
    """Unroll loops and convert to SSA form."""
    # First unroll the loops
    unroller = LoopUnroller()
    unrolled_code = unroller.unroll_loops(code, depth)
    
    # Then convert to SSA
    ssa_code = convert_to_ssa(unrolled_code)
    
    return unrolled_code, ssa_code

from parser import ASTNode, parse_program

# def extract_assertions(ast):
#     """
#     Extract all assertions from the AST and return them as a list.
    
#     Args:
#         ast: The Abstract Syntax Tree to analyze
        
#     Returns:
#         A list of assertion expressions
#     """
#     assertions = []
    
#     def traverse_ast(nodes):
#         for node in nodes:
#             if node.type == "assert":
#                 assertions.append(node.value)
            
#             # Recursively process child nodes
#             if node.children:
#                 if node.type == "if":
#                     # If statement has 'then' and 'else' blocks as children
#                     traverse_ast(node.children[0].children)  # Then block
#                     traverse_ast(node.children[1].children)  # Else block
#                 else:
#                     traverse_ast(node.children)
    
#     traverse_ast(ast)
#     return assertions

# def extract_assertions_from_code(code):
#     """
#     Extract all assertions from the given code and return them as a list.
    
#     Args:
#         code: Source code as a string
        
#     Returns:
#         A list of assertion expressions
#     """
#     ast = parse_program(code)
#     return extract_assertions(ast)

# def extract_assertions_from_ssa(ssa_code):
#     """
#     Extract all assertions from the SSA code and return them as a list.
#     This is useful to get assertions after SSA conversion.
    
#     Args:
#         ssa_code: SSA code as a string
        
#     Returns:
#         A list of assertion expressions in SSA form
#     """
#     # Parse the SSA code (this assumes the parser can handle SSA code format)
#     try:
#         ast = parse_program(ssa_code)
#         return extract_assertions(ast)
#     except:
#         # If parsing fails, use a simple regex-based approach
#         import re
#         assertions = []
#         # Match assert statements like "assert(condition)"
#         matches = re.findall(r'assert\((.*?)\)', ssa_code)
#         for match in matches:
#             assertions.append(match)
#         return assertions

