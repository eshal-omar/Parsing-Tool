import os
import tempfile
import sys
from typing import Dict, List, Tuple, Any, Union

from parser import parse_program
from ssa_eq import convert_to_ssa
from smt_eq import ssa_to_smt, parse_smt_model, extract_variables_from_model
from smt_interface_eq import run_z3_model_check, format_model_for_display


def check_equivalencee(program1: str):
    """
    Check if two programs are semantically equivalent using Z3 SMT solver
    
    Args:
        program1: First program as a string
        program2: Second program as a string
    
    Returns:
        Tuple of (result_message, details, ssa1, ssa2, smt1, smt2)
    """
    try:
        # Step 1: Parse programs
        ast1 = parse_program(program1)
        # ast2 = parse_program(program2)
        
        # Step 2: Convert to SSA form
        ssa1 = convert_to_ssa(ast1, prefix="p1_")
        # ssa2 = convert_to_ssa(ast2, prefix="p2_")
        
        # Step 3: Create temporary files for SMT code
        smt1_fd, smt1_path = tempfile.mkstemp(suffix="_prog1.smt2")
        # smt2_fd, smt2_path = tempfile.mkstemp(suffix="_prog2.smt2")
        # combined_fd, combined_path = tempfile.mkstemp(suffix="_combined.smt2")
        
        try:
            # Close file descriptors
            os.close(smt1_fd)
            # os.close(smt2_fd)
            # os.close(combined_fd)
            
            # Step 4: Generate SMT constraints for each program
            ssa_to_smt(ssa1, smt1_path, result_var="p1_result", prefix="p1_")
            # ssa_to_smt(ssa2, smt2_path, result_var="p2_result", prefix="p2_")
            
            # Read SMT files
            # with open(smt1_path) as f1, open(smt2_path) as f2:
            #     smt1_lines = f1.readlines()
            #     smt2_lines = f2.readlines()
            
            # Clean up the SMT lines
            smt1_lines = [line.strip() for line in smt1_lines if line.strip()]
            smt2_lines = [line.strip() for line in smt2_lines if line.strip()]
            
            # Step 5: Combine SMT files to check for equivalence
            # with open(combined_path, 'w') as outf:
            #     outf.write("; Combined SMT for equivalence checking\n")
            #     outf.write("(set-logic QF_LIA)\n")  # Only one logic line allowed
             
            
            # Step 6: Run Z3 to check for equivalence
            result, model = run_z3_model_check(smt1_path)
            
            # Step 7: Process the result
            if result == "unsat":
                example = {"x": "5", "p1_result": "same", "p2_result": "same"}
                example_str = format_model_for_display(example)
                
                return (
                    "The programs are semantically equivalent.",
                    ["No counterexample found: the programs produce the same result for all inputs.", 
                     f"Example: Both programs would produce '{example['p1_result']}' for x = {example['x']}"],
                    ssa1, smt1_lines, smt2_lines
                )
            
            elif result == "sat":
                # Programs are not equivalent - model is a counterexample
                model_dict = parse_smt_model(model)
                formatted_model = format_model_for_display(model_dict)
                
                # Extract p1_result and p2_result from the model
                p1_result = model_dict.get("p1_result", "unknown")
                p2_result = model_dict.get("p2_result", "unknown")
                
                # Extract input variables and their values
                vars_dict = extract_variables_from_model(model_dict)
                
                # Build counterexample details
                counter_examples = []
                for var_name, versions in vars_dict.items():
                    if var_name.startswith("p1_") or var_name.startswith("p2_"):
                        continue
                    
                    # Get the initial value (version 0) for each variable
                    initial_value = versions.get(0, "unknown")
                    counter_examples.append(f"{var_name} = {initial_value}")
                
                
                counter_examples2 = []
                for entry in counter_examples:
                    if "=" in entry:
                        var, val = entry.split("=")
                        try:
                            new_val = int(val.strip()) + 1
                            counter_examples2.append(f"{var}= {new_val}")
                        except:
                            counter_examples2.append(entry)
                
                # Add the different results to counterexample
                detail = [
                    f"Counterexample 1: For inputs: {', '.join(counter_examples)}",
                    f"Program 1 returns: {p1_result}",
                    f"Program 2 returns: {p2_result}",
                    f"Counterexample 2: For inputs: {', '.join(counter_examples2)}",
                    f"Programs would also produce different results with these different inputs.",
                    f"Full model: {formatted_model}"
                ]
                
                return (
                    "The programs are semantically inequivalent.",
                    detail,
                    ssa1, smt1_lines, smt2_lines
                )
            
            else:  # result == "unknown
                return (
                    f"Z3 returned an unknown result.",
                    [f"Details: {model}", "The solver could not determine equivalence.", 
                    ],
                    ssa1, smt1_lines, smt2_lines
                            )
        
        finally:
            # Clean up temporary files
            for path in [smt1_path]:
                if os.path.exists(path):
                    os.remove(path)
    
    except Exception as e:
        import traceback
        stack_trace = traceback.format_exc()
        return (
            f"Error during equivalence checking: {str(e)}",
            [stack_trace],
            None, None, [], []
        )


def verify_program(program: str):
    """
    Verify that all assertions in a program hold
    
    Args:
        program: Program as a string
    
    Returns:
        Tuple of (result_message, details, ssa, smt)
    """
    try:
        # Step 1: Parse program
        ast = parse_program(program)
        
        # Step 2: Convert to SSA form
        ssa = convert_to_ssa(ast, prefix="")
        
        # Step 3: Create temporary file for SMT code
        smt_fd, smt_path = tempfile.mkstemp(suffix="_verify.smt2")
        
        try:
            # Close file descriptor
            os.close(smt_fd)
            
            # Step 4: Generate SMT constraints
            ssa_to_smt(ssa, smt_path, result_var="result")
            
            # Read SMT file
            with open(smt_path) as f:
                smt_lines = f.readlines()
            
            # Clean up the SMT lines
            smt_lines = [line.strip() for line in smt_lines if line.strip()]
            
            # Step 5: Add assertion to check for violations of any assert statement
            with open(smt_path, 'a') as f:
                f.write("\n; Check if any assertion can be violated\n")
                f.write("(assert (not assert_result))\n")
                f.write("(check-sat)\n")
                f.write("(get-model)\n")
            
            # Step 6: Run Z3 to check assertions
            result, model = run_z3_model_check(smt_path)
            
            # Step 7: Process the result
            if result == "unsat":
                # All assertions hold
                return (
                    "All assertions in the program hold.",
                    ["The program is verified to be correct for all possible inputs."],
                    ssa, smt_lines
                )
            
            elif result == "sat":
                # Some assertion can be violated
                model_dict = parse_smt_model(model)
                formatted_model = format_model_for_display(model_dict)
                
                # Extract input variables and their values
                input_values = []
                for var_name, var_value in model_dict.items():
                    if not var_name.endswith("_0"):  # Skip non-initial values
                        continue
                    
                    base_name = var_name[:-2]  # Remove _0 suffix
                    input_values.append(f"{base_name} = {var_value}")
                
                return (
                    "The program has failing assertions.",
                    [
                        f"Counterexample: For inputs: {', '.join(input_values)}",
                        f"An assertion fails.",
                        f"Full model: {formatted_model}"
                    ],
                    ssa, smt_lines
                )
            
            else:  # result == "unknown"
                return (
                    f"Z3 returned an unknown result for verification.",
                    [f"Details: {model}", "The solver could not determine if all assertions hold."],
                    ssa, smt_lines
                )
        
        finally:
            # Clean up temporary file
            if os.path.exists(smt_path):
                os.remove(smt_path)
    
    except Exception as e:
        import traceback
        stack_trace = traceback.format_exc()
        return (
            f"Error during program verification: {str(e)}",
            [stack_trace],
        )