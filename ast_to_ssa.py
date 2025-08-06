#!/usr/bin/env python3
"""
Convert Python AST to Static Single Assignment (SSA) form.

This module provides functionality to transform a Python Abstract Syntax Tree (AST)
into a Static Single Assignment (SSA) form program object.
"""

import ast
import sys
from typing import Dict, List, Set, Optional, Union, Any
from dataclasses import dataclass, field


@dataclass
class BasicBlock:
    """A basic block of code in SSA form."""
    label: str
    instructions: List[Any] = field(default_factory=list)
    predecessors: List[str] = field(default_factory=list)
    successors: List[str] = field(default_factory=list)


@dataclass
class PhiNode:
    """Represents a phi function in SSA."""
    target: str
    sources: Dict[str, str]  # Maps block labels to variable names

    def __str__(self):
        sources_str = ", ".join([f"{src}:{var}" for src, var in self.sources.items()])
        return f"{self.target} = φ({sources_str})"


@dataclass
class Instruction:
    """Base class for SSA instructions."""
    result: Optional[str] = None

    def __str__(self):
        return f"{self.__class__.__name__}"


@dataclass
class AssignmentInst(Instruction):
    """Assignment instruction in SSA."""
    expr: Any = None

    def __str__(self):
        return f"{self.result} = {self.expr}"


@dataclass
class BinaryOpInst(Instruction):
    """Binary operation instruction in SSA."""
    op: str = None
    left: str = None
    right: str = None

    def __str__(self):
        return f"{self.result} = {self.left} {self.op} {self.right}"


@dataclass
class UnaryOpInst(Instruction):
    """Unary operation instruction in SSA."""
    op: str = None
    operand: str = None

    def __str__(self):
        return f"{self.result} = {self.op}{self.operand}"


@dataclass
class CallInst(Instruction):
    """Function call instruction in SSA."""
    func: str = None
    args: List[str] = field(default_factory=list)

    def __str__(self):
        args_str = ", ".join(self.args)
        return f"{self.result} = {self.func}({args_str})"


@dataclass
class ReturnInst(Instruction):
    """Return instruction in SSA."""
    value: Optional[str] = None

    def __str__(self):
        if self.value:
            return f"return {self.value}"
        return "return"


@dataclass
class BranchInst(Instruction):
    """Branch instruction in SSA."""
    condition: Optional[str] = None
    true_label: Optional[str] = None
    false_label: Optional[str] = None

    def __str__(self):
        if self.condition:
            return f"if {self.condition} goto {self.true_label} else goto {self.false_label}"
        return f"goto {self.true_label}"


@dataclass
class SSAProgram:
    """Represents a program in SSA form."""
    blocks: Dict[str, BasicBlock] = field(default_factory=dict)
    entry_block: str = "entry"
    exit_blocks: List[str] = field(default_factory=list)
    var_counter: Dict[str, int] = field(default_factory=dict)

    def new_temp(self, base="t"):
        """Generate a new temporary variable name."""
        if base not in self.var_counter:
            self.var_counter[base] = 0
        self.var_counter[base] += 1
        return f"{base}_{self.var_counter[base]}"

    def add_block(self, label=None):
        """Add a new basic block to the program."""
        if label is None:
            label = f"block_{len(self.blocks)}"
        if label not in self.blocks:
            self.blocks[label] = BasicBlock(label=label)
        return label

    def add_instruction(self, block_label, instruction):
        """Add an instruction to a block."""
        if block_label not in self.blocks:
            self.add_block(block_label)
        self.blocks[block_label].instructions.append(instruction)

    def add_edge(self, from_label, to_label):
        """Add an edge between two blocks."""
        if from_label not in self.blocks:
            self.add_block(from_label)
        if to_label not in self.blocks:
            self.add_block(to_label)

        from_block = self.blocks[from_label]
        to_block = self.blocks[to_label]

        if to_label not in from_block.successors:
            from_block.successors.append(to_label)
        if from_label not in to_block.predecessors:
            to_block.predecessors.append(from_label)


class SSAConverter(ast.NodeVisitor):
    """Converts a Python AST to SSA form."""

    def __init__(self):
        self.program = SSAProgram()
        self.current_block = self.program.entry_block
        self.program.add_block(self.current_block)
        self.variables = {}  # Maps variable names to their current SSA version
        self.scopes = [{}]  # Stack of scopes for variable lookups
        self.recursion_depth = 0
        self.max_recursion_depth = 1000  # Safeguard against excessive recursion
        
    def visit(self, node):
        """Override visit to add recursion depth tracking."""
        self.recursion_depth += 1
        if self.recursion_depth > self.max_recursion_depth:
            raise RecursionError(f"Maximum recursion depth exceeded while processing {type(node).__name__}")
        
        try:
            result = super().visit(node)
            return result
        finally:
            self.recursion_depth -= 1

    def visit_Module(self, node):
        """Visit a module node."""
        for stmt in node.body:
            try:
                self.visit(stmt)
            except RecursionError as e:
                print(f"Recursion error processing: {ast.dump(stmt, annotate_fields=False)}")
                raise
        # Add return if not already present
        if not self.program.exit_blocks:
            self.program.exit_blocks.append(self.current_block)
        return self.program

    def visit_Assign(self, node):
        """Visit an assignment node."""
        # Process the right-hand side
        rhs = self.visit(node.value)
        
        # Process the left-hand side (targets)
        for target in node.targets:
            if isinstance(target, ast.Name):
                # Simple variable assignment
                var_name = target.id
                ssa_name = self.program.new_temp(var_name)
                self.define_variable(var_name, ssa_name)
                
                # Create assignment instruction
                inst = AssignmentInst(result=ssa_name, expr=rhs)
                self.program.add_instruction(self.current_block, inst)
            else:
                # Handle more complex assignments (e.g., a.b = c, a[i] = v)
                # This would require more complex SSA handling
                pass

    def visit_Name(self, node):
        """Visit a name node."""
        if isinstance(node.ctx, ast.Load):
            # Variable reference
            return self.lookup_variable(node.id)
        # For ast.Store and ast.Del, handled by their parent nodes
        return node.id

    def visit_Constant(self, node):
        """Visit a constant node."""
        # Create a temporary for the constant
        temp = self.program.new_temp("const")
        inst = AssignmentInst(result=temp, expr=repr(node.value))
        self.program.add_instruction(self.current_block, inst)
        return temp
        
    def visit_Attribute(self, node):
        """Visit an attribute node (like a.b)."""
        # Visit the value part (a)
        value = self.visit(node.value)
        
        # Create a temporary for the attribute access
        temp = self.program.new_temp("attr")
        # In real implementation, this would need more complex handling
        inst = AssignmentInst(result=temp, expr=f"{value}.{node.attr}")
        self.program.add_instruction(self.current_block, inst)
        return temp
        
    def visit_Subscript(self, node):
        """Visit a subscript node (like a[b])."""
        # Visit the value and slice parts
        value = self.visit(node.value)
        slice_value = self.visit(node.slice)
        
        # Create a temporary for the subscript
        temp = self.program.new_temp("subscript")
        inst = AssignmentInst(result=temp, expr=f"{value}[{slice_value}]")
        self.program.add_instruction(self.current_block, inst)
        return temp

    def visit_BinOp(self, node):
        """Visit a binary operation node."""
        left = self.visit(node.left)
        right = self.visit(node.right)
        
        # Determine the operator
        op_map = {
            ast.Add: "+", ast.Sub: "-", ast.Mult: "*", ast.Div: "/",
            ast.FloorDiv: "//", ast.Mod: "%", ast.Pow: "**",
            ast.LShift: "<<", ast.RShift: ">>", ast.BitOr: "|",
            ast.BitXor: "^", ast.BitAnd: "&"
        }
        op = op_map.get(type(node.op), "?")
        
        # Create a new temporary for the result
        result = self.program.new_temp("bin")
        inst = BinaryOpInst(result=result, op=op, left=left, right=right)
        self.program.add_instruction(self.current_block, inst)
        return result

    def visit_UnaryOp(self, node):
        """Visit a unary operation node."""
        operand = self.visit(node.operand)
        
        # Determine the operator
        op_map = {
            ast.UAdd: "+", ast.USub: "-", ast.Not: "not", ast.Invert: "~"
        }
        op = op_map.get(type(node.op), "?")
        
        # Create a new temporary for the result
        result = self.program.new_temp("unary")
        inst = UnaryOpInst(result=result, op=op, operand=operand)
        self.program.add_instruction(self.current_block, inst)
        return result

    def visit_Call(self, node):
        """Visit a function call node."""
        # Visit the function
        func = self.visit(node.func)
        
        # Visit the arguments
        args = []
        for arg in node.args:
            args.append(self.visit(arg))
        
        # Create a temporary for the result
        result = self.program.new_temp("call")
        inst = CallInst(result=result, func=func, args=args)
        self.program.add_instruction(self.current_block, inst)
        return result

    def visit_If(self, node):
        """Visit an if statement node."""
        try:
            # Visit the test condition
            condition = self.visit(node.test)
            
            # Create blocks for the true branch, false branch, and continuation
            if_block = self.program.new_temp("if_true")
            else_block = self.program.new_temp("if_false")
            cont_block = self.program.new_temp("if_cont")
            
            # Add a branch instruction
            branch = BranchInst(condition=condition, true_label=if_block, false_label=else_block)
            self.program.add_instruction(self.current_block, branch)
            
            # Add edges
            self.program.add_edge(self.current_block, if_block)
            self.program.add_edge(self.current_block, else_block)
            
            # Save the current variable state
            old_vars = self.variables.copy()
            
            # Process the true branch
            prev_block = self.current_block
            self.current_block = if_block
            
            for stmt in node.body:
                self.visit(stmt)
            if_end_block = self.current_block
            
            # Add jump to continuation if needed
            if not self.current_block in self.program.exit_blocks:
                jump = BranchInst(true_label=cont_block)
                self.program.add_instruction(self.current_block, jump)
                self.program.add_edge(self.current_block, cont_block)
            
            # Save the true branch variables
            if_vars = self.variables.copy()
            
            # Restore original variables and process the false branch
            self.variables = old_vars.copy()
            self.current_block = else_block
            
            if node.orelse:
                for stmt in node.orelse:
                    self.visit(stmt)
            
            else_end_block = self.current_block
            
            # Add jump to continuation if needed
            if not self.current_block in self.program.exit_blocks:
                jump = BranchInst(true_label=cont_block)
                self.program.add_instruction(self.current_block, jump)
                self.program.add_edge(self.current_block, cont_block)
            
            # Save the false branch variables
            else_vars = self.variables.copy()
            
            # Merge variables at the continuation point using phi functions
            self.current_block = cont_block
            all_vars = set(if_vars.keys()) | set(else_vars.keys())
            for var in all_vars:
                if var in if_vars and var in else_vars and if_vars[var] != else_vars[var]:
                    # We need a phi function for this variable
                    phi_target = self.program.new_temp(var)
                    phi_sources = {
                        if_end_block: if_vars.get(var, "undefined"),
                        else_end_block: else_vars.get(var, "undefined")
                    }
                    phi = PhiNode(target=phi_target, sources=phi_sources)
                    self.program.add_instruction(self.current_block, phi)
                    self.variables[var] = phi_target
        except RecursionError:
            # If recursion error occurs during if statement processing,
            # revert to a simpler implementation
            print(f"Recursion error in If node, using simplified processing")
            self.current_block = prev_block  # Restore to block before if statement
            # Create a simple result for the if condition
            result = self.program.new_temp("if_result")
            inst = AssignmentInst(result=result, expr="<if-condition-simplified>")
            self.program.add_instruction(self.current_block, inst)

    def visit_While(self, node):
        """Visit a while statement node."""
        # Create blocks for the loop header, body, and exit
        header_block = self.program.new_temp("while_header")
        body_block = self.program.new_temp("while_body")
        exit_block = self.program.new_temp("while_exit")
        
        # Add jump to the header
        jump = BranchInst(true_label=header_block)
        self.program.add_instruction(self.current_block, jump)
        self.program.add_edge(self.current_block, header_block)
        
        # Process the header
        self.current_block = header_block
        
        # Visit the condition
        condition = self.visit(node.test)
        
        # Add conditional branch to body or exit
        branch = BranchInst(condition=condition, true_label=body_block, false_label=exit_block)
        self.program.add_instruction(self.current_block, branch)
        self.program.add_edge(self.current_block, body_block)
        self.program.add_edge(self.current_block, exit_block)
        
        # Process the body
        self.current_block = body_block
        for stmt in node.body:
            self.visit(stmt)
        
        # Jump back to header
        jump = BranchInst(true_label=header_block)
        self.program.add_instruction(self.current_block, jump)
        self.program.add_edge(self.current_block, header_block)
        
        # Continue from the exit block
        self.current_block = exit_block

    def visit_For(self, node):
        """Visit a for statement node (simplified)."""
        # This is a simplified implementation that doesn't handle all Python for semantics
        
        # Create blocks for the loop header, body, and exit
        init_block = self.program.new_temp("for_init")
        header_block = self.program.new_temp("for_header")
        body_block = self.program.new_temp("for_body")
        exit_block = self.program.new_temp("for_exit")
        
        # Add jump to the initialization
        jump = BranchInst(true_label=init_block)
        self.program.add_instruction(self.current_block, jump)
        self.program.add_edge(self.current_block, init_block)
        
        # Process the initialization
        self.current_block = init_block
        iterable = self.visit(node.iter)
        
        # Create a temporary for the iterator
        iter_temp = self.program.new_temp("iter")
        inst = CallInst(result=iter_temp, func="iter", args=[iterable])
        self.program.add_instruction(self.current_block, inst)
        
        # Jump to header
        jump = BranchInst(true_label=header_block)
        self.program.add_instruction(self.current_block, jump)
        self.program.add_edge(self.current_block, header_block)
        
        # Process the header
        self.current_block = header_block
        
        # Try to get the next element
        item_temp = self.program.new_temp("next")
        try_next = CallInst(result=item_temp, func="next", args=[iter_temp])
        self.program.add_instruction(self.current_block, try_next)
        
        # Check if we got StopIteration
        has_next = self.program.new_temp("has_next")
        check_next = BinaryOpInst(result=has_next, op="is not", left=item_temp, right="StopIteration")
        self.program.add_instruction(self.current_block, check_next)
        
        # Branch based on has_next
        branch = BranchInst(condition=has_next, true_label=body_block, false_label=exit_block)
        self.program.add_instruction(self.current_block, branch)
        self.program.add_edge(self.current_block, body_block)
        self.program.add_edge(self.current_block, exit_block)
        
        # Process the body
        self.current_block = body_block
        
        # Assign the iterator value to the target
        if isinstance(node.target, ast.Name):
            var_name = node.target.id
            ssa_name = self.program.new_temp(var_name)
            self.define_variable(var_name, ssa_name)
            inst = AssignmentInst(result=ssa_name, expr=item_temp)
            self.program.add_instruction(self.current_block, inst)
        
        # Process the loop body
        for stmt in node.body:
            self.visit(stmt)
        
        # Jump back to header
        jump = BranchInst(true_label=header_block)
        self.program.add_instruction(self.current_block, jump)
        self.program.add_edge(self.current_block, header_block)
        
        # Continue from the exit block
        self.current_block = exit_block

    def visit_Return(self, node):
        """Visit a return statement node."""
        value = None
        if node.value:
            value = self.visit(node.value)
        
        # Add the return instruction
        ret = ReturnInst(value=value)
        self.program.add_instruction(self.current_block, ret)
        
        # Mark this block as an exit block
        if self.current_block not in self.program.exit_blocks:
            self.program.exit_blocks.append(self.current_block)

    def define_variable(self, name, ssa_name):
        """Define a variable in the current scope."""
        self.variables[name] = ssa_name
        self.scopes[-1][name] = ssa_name

    def lookup_variable(self, name):
        """Look up a variable in the scopes."""
        if name in self.variables:
            return self.variables[name]
        # If the variable is not defined, create a new one
        # This is a simplification - in a real compiler, undefined variables would be an error
        ssa_name = self.program.new_temp(f"undef_{name}")
        self.define_variable(name, ssa_name)
        return ssa_name

    def push_scope(self):
        """Push a new scope onto the stack."""
        self.scopes.append({})

    def pop_scope(self):
        """Pop the current scope from the stack."""
        old_scope = self.scopes.pop()
        # Restore the variables from the previous scope
        for name, value in old_scope.items():
            if name in self.variables and self.variables[name] == value:
                # If this variable was defined in this scope and hasn't changed, remove it
                # Otherwise, try to find it in a parent scope
                for scope in reversed(self.scopes):
                    if name in scope:
                        self.variables[name] = scope[name]
                        break
                else:
                    del self.variables[name]


def ast_to_ssa(source_code):
    """Convert Python source code to SSA form."""
    # Increase recursion limit to handle larger ASTs
    import sys
    original_limit = sys.getrecursionlimit()
    try:
        sys.setrecursionlimit(10000)  # Increase limit - adjust as needed
        tree = ast.parse(source_code)
        converter = SSAConverter()
        return converter.visit(tree)
    finally:
        sys.setrecursionlimit(original_limit)  # Restore original limit


def print_ssa_program(program):
    """Print an SSA program in a readable format."""
    print("SSA Program:")
    for label, block in program.blocks.items():
        print(f"\n{label}:")
        if block.predecessors:
            print(f"  Predecessors: {', '.join(block.predecessors)}")
        
        for inst in block.instructions:
            print(f"  {inst}")
        
        if block.successors:
            print(f"  Successors: {', '.join(block.successors)}")


# Example usage
