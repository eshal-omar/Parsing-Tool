class ASTNode:
    def __init__(self, type_, children=None, value=None):
        self.type = type_
        self.children = children if children else []
        self.value = value
    
    def __repr__(self):
        return f"{self.type}({self.value}) -> {self.children}"

class Parser:
    def __init__(self):
        self.tokens = []
        self.current = 0
    
    def parse_program(self, code):
        """Parse the input code into an AST structure."""
        lines = code.strip().splitlines()
        ast = []
        
        i = 0
        while i < len(lines):
            line = lines[i].strip()
            
            #skip empty lines and comments
            if not line or line.startswith("//"):
                i += 1
                continue
                
            #extract line number if present
            if line[0].isdigit():
                parts = line.split(" ", 1)
                if len(parts) > 1:
                    line = parts[1].strip()
            
            #for loop
            if line.startswith("for"):
                node, new_i = self._parse_for_loop(i, lines)
                ast.append(node)
                i = new_i
            
            #while loop
            elif line.startswith("while"):
                node, new_i = self._parse_while_loop(i, lines)
                ast.append(node)
                i = new_i
            
            #if statement
            elif line.startswith("if"):
                node, new_i = self._parse_if_statement(i, lines)
                ast.append(node)
                i = new_i
            
            #Assignment
            elif ":=" in line:
                var, expr = [part.strip() for part in line.split(":=", 1)]
                #remove any trailing semicolon
                if expr.endswith(";"):
                    expr = expr[:-1].strip()
                ast.append(ASTNode("assign", value={"var": var, "expr": expr}))
                i += 1
            
            #for assert statement
            elif line.startswith("assert"):
                cond = line[len("assert("):]                  #checks which condition
                if cond.endswith(");"):
                    cond = cond[:-2].strip()
                elif cond.endswith(")"):
                    cond = cond[:-1].strip()
                ast.append(ASTNode("assert", value=cond))
                i += 1
            
            else:
                i += 1  #skip lines 
        
        return ast
    
    def _find_matching_brace(self, start_idx, lines):
        """Find the matching closing brace starting from start_idx."""
        open_count = 0
        i = start_idx
        
        while i < len(lines):
            line = lines[i].strip()
            
            #extract line number if present
            if line[0].isdigit():
                parts = line.split(" ", 1)
                if len(parts) > 1:
                    line = parts[1].strip()
            
            #count opening braces
            if line == "{" or line.endswith("{"):
                open_count += 1
            
            #count closing braces
            if line == "}" or line.startswith("}"):
                open_count -= 1
                if open_count == 0:
                    return i
            
            i += 1
        
        return len(lines) - 1  #return the last line if no matching brace found
    
    def _parse_for_loop(self, start_idx, lines):
        """Parse a for loop starting at the given index."""
        line = lines[start_idx].strip()
        
        #extract line number if present
        if line[0].isdigit():
            parts = line.split(" ", 1)
            if len(parts) > 1:
                line = parts[1].strip()
        
        #extract the for loop components
        for_part = line[line.index("for")+3:].strip()
        if for_part.startswith("("):
            inner = for_part[for_part.index("(")+1:]
            if inner.endswith("{"):
                inner = inner[:-1].strip()
            if inner.endswith(")"):
                inner = inner[:-1].strip()
            
            components = inner.split(";")
            if len(components) == 3:
                init, cond, incr = [c.strip() for c in components]
                
                #parse init
                if ":=" in init:
                    init_var, init_expr = [p.strip() for p in init.split(":=", 1)]
                else:
                    init_var, init_expr = "", init
                
                #parse incr
                if ":=" in incr:
                    incr_var, incr_expr = [p.strip() for p in incr.split(":=", 1)]
                else:
                    incr_var, incr_expr = "", incr
                
                #ind the loop body
                end_idx = self._find_matching_brace(start_idx + 1, lines)
                body = []
                for i in range(start_idx + 1, end_idx):
                    if lines[i].strip() and lines[i].strip() != "{":
                        body.append(lines[i])
                
                body_ast = Parser().parse_program("\n".join(body))
                
                #craate the for loop node
                loop_node = ASTNode("for", children=body_ast, value={
                    "init": {"var": init_var, "expr": init_expr},
                    "cond": cond,
                    "incr": {"var": incr_var, "expr": incr_expr}
                })
                
                return loop_node, end_idx + 1
        
        
        return ASTNode("unknown", value=line), start_idx + 1
    
    def _parse_while_loop(self, start_idx, lines):
        """Parse a while loop starting at the given index."""
        line = lines[start_idx].strip()
        
        
        if line[0].isdigit():
            parts = line.split(" ", 1)
            if len(parts) > 1:
                line = parts[1].strip()
        
        #extract the while cond
        while_part = line[line.index("while")+5:].strip()
        if while_part.startswith("("):
            cond = while_part[1:]
            if cond.endswith("{"):
                cond = cond[:-1].strip()
            if cond.endswith(")"):
                cond = cond[:-1].strip()
            
            #looks for the loop body
            end_idx = self._find_matching_brace(start_idx + 1, lines)
            body = []
            for i in range(start_idx + 1, end_idx):
                if lines[i].strip() and lines[i].strip() != "{":
                    body.append(lines[i])
            
            body_ast = Parser().parse_program("\n".join(body))
            
            #create the while loop node
            loop_node = ASTNode("while", children=body_ast, value=cond)
            
            return loop_node, end_idx + 1
        
        #if parsing fails
        return ASTNode("unknown", value=line), start_idx + 1
    
    def _parse_if_statement(self, start_idx, lines):
        """Parse an if statement starting at the given index."""
        line = lines[start_idx].strip()
        
        #extract line number if present
        if line[0].isdigit():
            parts = line.split(" ", 1)
            if len(parts) > 1:
                line = parts[1].strip()
        
        
        if_part = line[line.index("if")+2:].strip()
        if if_part.startswith("("):
            cond = if_part[1:]
            if cond.endswith("{"):
                cond = cond[:-1].strip()
            if cond.endswith(")"):
                cond = cond[:-1].strip()
            
            
            end_idx = self._find_matching_brace(start_idx + 1, lines)
            
            if_body = []
            for i in range(start_idx + 1, end_idx):
                if lines[i].strip() and lines[i].strip() != "{":
                    if_body.append(lines[i])
            
            if_body_ast = Parser().parse_program("\n".join(if_body))
            
            #check if there's an else branch
            else_body_ast = []
            new_end_idx = end_idx
            
            if end_idx + 1 < len(lines) and "else" in lines[end_idx + 1].strip():
                #Found an else branch
                else_start_idx = end_idx + 1
                else_end_idx = self._find_matching_brace(else_start_idx + 1, lines)
                
                else_body = []
                for i in range(else_start_idx + 1, else_end_idx):
                    if lines[i].strip() and lines[i].strip() != "{":
                        else_body.append(lines[i])
                
                else_body_ast = Parser().parse_program("\n".join(else_body))
                new_end_idx = else_end_idx
            
            #Create the if-else node
            if_node = ASTNode("if", children=[
                ASTNode("then", children=if_body_ast),
                ASTNode("else", children=else_body_ast)
            ], value=cond)
            
            return if_node, new_end_idx + 1
        
        #Fallback if parsing fails
        return ASTNode("unknown", value=line), start_idx + 1

def parse_program(code):
    """Parse the input code into an AST structure."""
    parser = Parser()
    return parser.parse_program(code)
def convert_to_unified_ast(ast_list):
    """
    Convert a list of AST nodes into a unified AST object with a single root node.
    
    Args:
        ast_list: List of ASTNode objects from parse_program
        
    Returns:
        A single ASTNode that represents the entire program with a root node
    """
    #Create a Program root node that contains all other nodes as children
    root_node = ASTNode("program", children=ast_list)
    return root_node

def parse_to_unified_ast(code):
    """
    Parse the input code and convert it directly to a unified AST with a root node.
    
    Args:
        code: String containing the source code to parse
        
    Returns:
        A single ASTNode that represents the entire program with a root node
    """
    ast_list = parse_program(code)
    return convert_to_unified_ast(ast_list)