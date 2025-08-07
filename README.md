## Parsing Tool
A tool that parses input algorithm and converts to Static Single Assignment (SSA) form. This tool helps analyze the correctness and equivalence of programs.

# Key Features
The tool does the following 
1. Parse simple programs input
2. Convert them into SSA (Static Single Assignment) form
3. Generate the corresponding SMT constraints
4. Use an SMT solver (e.g., Z3) to:
o Verify correctness (assert statements hold)
o Check whether two programs are semantically equivalent
5. Display all intermediate steps (SSA form, SMT code, result) in the GUI
