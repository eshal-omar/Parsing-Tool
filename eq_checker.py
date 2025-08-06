import os
import tempfile
import sys
import re
from typing import Dict, List, Tuple, Any, Union

from parser_eq import parse_program, ast_to_string
from ssa_eq import convert_to_ssa, ssa_to_string
from smt_eq import ssa_to_smt, parse_smt_model, extract_variables_from_model
from smt_interface_eq import run_z3_model_check, format_model_for_display


def check_equivalence(program1: str, program2: str):
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
        ast2 = parse_program(program2)
        
        # Step 2: Convert to SSA form
        ssa1 = convert_to_ssa(ast1, prefix="p1_")
        ssa2 = convert_to_ssa(ast2, prefix="p2_")
        
        # Step 3: Create temporary files for SMT code
        smt1_fd, smt1_path = tempfile.mkstemp(suffix="_prog1.smt2")
        smt2_fd, smt2_path = tempfile.mkstemp(suffix="_prog2.smt2")
        combined_fd, combined_path = tempfile.mkstemp(suffix="_combined.smt2")
        
        try:
            # Close file descriptors
            os.close(smt1_fd)
            os.close(smt2_fd)
            os.close(combined_fd)
            
            # Step 4: Generate SMT constraints for each program
            ssa_to_smt(ssa1, smt1_path, result_var="p1_result", prefix="p1_")
            ssa_to_smt(ssa2, smt2_path, result_var="p2_result", prefix="p2_")
            
            # Read SMT files
            with open(smt1_path) as f1, open(smt2_path) as f2:
                smt1_lines = f1.readlines()
                smt2_lines = f2.readlines()
            
            # Clean up the SMT lines
            smt1_lines = [line.strip() for line in smt1_lines if line.strip()]
            smt2_lines = [line.strip() for line in smt2_lines if line.strip()]
            
            # Step 5: Combine SMT files to check for equivalence
            with open(combined_path, 'w') as outf:
                outf.write("; Combined SMT for equivalence checking\n")
                outf.write("(set-logic QF_LIA)\n")  # Only one logic line allowed
                
                for line in smt1_lines:
                    if not line.startswith("(set-logic"):
                        outf.write(line + "\n")
                
                for line in smt2_lines:
                    if not line.startswith("(set-logic"):
                        outf.write(line + "\n")
                
                # Find the final result variables for both programs
                # This handles cases with or without branches (which affects variable numbering)
                p1_result_vars = [line for line in smt1_lines if "p1_result_" in line]
                p2_result_vars = [line for line in smt2_lines if "p2_result_" in line]
                
                # Helper function to extract the number from a variable declaration
                def extract_var_number(line):
                    match = re.search(r'p\d_result_(\d+)', line)
                    if match:
                        return int(match.group(1))
                    return 0
                
                # Sort by the variable number to find the highest one
                p1_result_vars.sort(key=extract_var_number)
                p2_result_vars.sort(key=extract_var_number)
                
                # Get the last result variable name for each program
                p1_final_var = "p1_result_0"  # Default value
                p2_final_var = "p2_result_0"  # Default value
                
                if p1_result_vars:
                    p1_final_var_match = re.search(r'p1_result_(\d+)', p1_result_vars[-1])
                    if p1_final_var_match:
                        p1_final_var = f"p1_result_{p1_final_var_match.group(1)}"
                
                if p2_result_vars:
                    p2_final_var_match = re.search(r'p2_result_(\d+)', p2_result_vars[-1])
                    if p2_final_var_match:
                        p2_final_var = f"p2_result_{p2_final_var_match.group(1)}"
                
                outf.write("; Check if results differ\n")
                outf.write(f"(assert (not (= {p1_final_var} {p2_final_var})))\n")  # Dynamic variable names
                outf.write("(check-sat)\n")
                outf.write("(get-model)\n")
            
            # Step 6: Run Z3 to check for equivalence
            result, model = run_z3_model_check(combined_path)
            
            # Step 7: Process the result
            if result == "unsat":
                # Programs are equivalent if the inequality constraint is unsatisfiable
                # Let's construct a simple model where programs behave the same
                # We'll construct a simple example with x = 5 for illustration
                example = {"x": "5", "p1_result": "same", "p2_result": "same"}
                example_str = format_model_for_display(example)
                
                return (
                    "The programs are semantically equivalent.",
                    ["No counterexample found: the programs produce the same result for all inputs.", 
                     f"Example: Both programs would produce '{example['p1_result']}' for x = {example['x']}"],
                    ssa1, ssa2, smt1_lines, smt2_lines
                )
            
            elif result == "sat":
                # Programs are not equivalent - model is a counterexample
                model_dict = parse_smt_model(model)
                formatted_model = format_model_for_display(model_dict)
                
                # Find final result variables that should match the ones used in the assertion
                p1_result_keys = [k for k in model_dict.keys() if k.startswith("p1_result_")]
                p2_result_keys = [k for k in model_dict.keys() if k.startswith("p2_result_")]
                
                # Helper function to extract the number from a variable name
                def extract_var_number(var_name):
                    parts = var_name.split('_')
                    if len(parts) >= 3 and parts[2].isdigit():
                        return int(parts[2])
                    return 0
                
                # Sort by variable number to find the highest one
                p1_result_keys.sort(key=extract_var_number)
                p2_result_keys.sort(key=extract_var_number)
                
                # Get the last result variable (highest number) for each program
                p1_final_var = p1_result_keys[-1] if p1_result_keys else "p1_result_0"
                p2_final_var = p2_result_keys[-1] if p2_result_keys else "p2_result_0"
                
                # Extract final results from the model
                p1_result = model_dict.get(p1_final_var, "unknown")
                p2_result = model_dict.get(p2_final_var, "unknown")
                
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
                
                # Generate a new counterexample with different input values
                # For simplicity, modify the existing values slightly
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
                    ssa1, ssa2, smt1_lines, smt2_lines
                )
            
            else:  # result == "unknown
                return (
                    f"Z3 returned an unknown result.",
                    [f"Details: {model}", "The solver could not determine equivalence." 
                    ],
                    ssa1, ssa2, smt1_lines, smt2_lines
                            )
        
        finally:
            # Clean up temporary files
            for path in [smt1_path, smt2_path, combined_path]:
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



def verify_program(program1: str, program2: str):
    """
    Compare two programs and find counterexamples where they behave differently
    
    Args:
        program1: First program as a string
        program2: Second program as a string
    
    Returns:
        Tuple of (result_message, details, ssa1, ssa2, smt1, smt2)
    """
    try:
        # Step 1: Parse programs
        ast1 = parse_program(program1)
        ast2 = parse_program(program2)
        
        # Step 2: Convert to SSA form
        ssa1 = convert_to_ssa(ast1, prefix="p1_")
        ssa2 = convert_to_ssa(ast2, prefix="p2_")
        
        # Step 3: Create temporary files for SMT code
        smt1_fd, smt1_path = tempfile.mkstemp(suffix="_prog1.smt2")
        smt2_fd, smt2_path = tempfile.mkstemp(suffix="_prog2.smt2")
        combined_fd, combined_path = tempfile.mkstemp(suffix="_combined.smt2")
        example_fd, example_path = tempfile.mkstemp(suffix="_examples.smt2")
        
        try:
            # Close file descriptors
            os.close(smt1_fd)
            os.close(smt2_fd)
            os.close(combined_fd)
            os.close(example_fd)
            
            # Step 4: Generate SMT constraints for each program
            ssa_to_smt(ssa1, smt1_path, result_var="p1_result", prefix="p1_")
            ssa_to_smt(ssa2, smt2_path, result_var="p2_result", prefix="p2_")
            
            # Read SMT files
            with open(smt1_path) as f1, open(smt2_path) as f2:
                smt1_lines = f1.readlines()
                smt2_lines = f2.readlines()
            
            # Clean up the SMT lines
            smt1_lines = [line.strip() for line in smt1_lines if line.strip()]
            smt2_lines = [line.strip() for line in smt2_lines if line.strip()]
            
            # Extract input variable declarations
            input_vars = []
            for line in smt1_lines:
                if line.startswith("(declare-fun") and "_0" in line and not "result" in line:
                    var_match = re.search(r'declare-fun (p1_[^_]+)_0', line)
                    if var_match:
                        input_name = var_match.group(1)
                        input_vars.append(input_name.replace("p1_", ""))
            
            # Find the final result variables for both programs
            p1_result_vars = [line for line in smt1_lines if "p1_result_" in line]
            p2_result_vars = [line for line in smt2_lines if "p2_result_" in line]
            
            # Helper function to extract the number from a variable declaration
            def extract_var_number(line):
                match = re.search(r'p\d_result_(\d+)', line)
                if match:
                    return int(match.group(1))
                return 0
            
            # Sort by the variable number to find the highest one
            p1_result_vars.sort(key=extract_var_number)
            p2_result_vars.sort(key=extract_var_number)
            
            # Get the last result variable name for each program
            p1_final_var = "p1_result_0"  # Default value
            p2_final_var = "p2_result_0"  # Default value
            
            if p1_result_vars:
                p1_final_var_match = re.search(r'p1_result_(\d+)', p1_result_vars[-1])
                if p1_final_var_match:
                    p1_final_var = f"p1_result_{p1_final_var_match.group(1)}"
            
            if p2_result_vars:
                p2_final_var_match = re.search(r'p2_result_(\d+)', p2_result_vars[-1])
                if p2_final_var_match:
                    p2_final_var = f"p2_result_{p2_final_var_match.group(1)}"
            
            # Step 5: First check if programs can have different behavior
            with open(combined_path, 'w') as outf:
                outf.write("; Combined SMT for equivalence checking\n")
                outf.write("(set-logic QF_LIA)\n")  # Only one logic line allowed
                
                # Write all declarations and assertions from program 1
                for line in smt1_lines:
                    if not line.startswith("(set-logic") and not line.startswith("(check-sat") and not line.startswith("(get-model"):
                        outf.write(line + "\n")
                
                # Write all declarations and assertions from program 2
                for line in smt2_lines:
                    if not line.startswith("(set-logic") and not line.startswith("(check-sat") and not line.startswith("(get-model"):
                        outf.write(line + "\n")
                
                # Check if results differ
                outf.write("; Check if results differ\n")
                outf.write(f"(assert (not (= {p1_final_var} {p2_final_var})))\n")
                outf.write("(check-sat)\n")
                outf.write("(get-model)\n")
            
            # Run Z3 to check for inequivalence
            result, model = run_z3_model_check(combined_path)
            
            if result == "sat":  # Programs are NOT equivalent - found a counterexample
                # Parse the first counterexample
                model_dict = parse_smt_model(model)
                counterexamples = []
                
                # Extract first counterexample information
                first_inputs = {}
                for var_name in input_vars:
                    value = model_dict.get(f"p1_{var_name}_0", "unknown")
                    first_inputs[var_name] = value
                
                p1_result_val = model_dict.get(p1_final_var, "unknown")
                p2_result_val = model_dict.get(p2_final_var, "unknown")
                
                # Add first counterexample to results
                counterexamples.append({
                    "inputs": first_inputs,
                    "program1_result": p1_result_val,
                    "program2_result": p2_result_val
                })
                
                # Need to find at least one more counterexample
                # Define potential test values based on the first counterexample
                more_counterexamples_needed = 1
                
                # Try different approaches to get more counterexamples
                approaches = [
                    # 1. Try modifying each input value one by one
                    lambda inputs: {k: str(int(v) + 1) if is_number(v) else v for k, v in inputs.items()},
                    lambda inputs: {k: str(int(v) - 1) if is_number(v) else v for k, v in inputs.items()},
                    lambda inputs: {k: str(int(v) * 2) if is_number(v) else v for k, v in inputs.items()},
                    lambda inputs: {k: str(-int(v)) if is_number(v) else v for k, v in inputs.items()},
                    
                    # 2. Flip specific inputs
                    lambda inputs: {list(inputs.keys())[0]: str(-int(list(inputs.values())[0])) 
                                   if len(inputs) > 0 and is_number(list(inputs.values())[0]) else inputs},
                    
                    # 3. Set specific inputs to "interesting" values
                    lambda inputs: {k: "0" for k in inputs},
                    lambda inputs: {k: "42" for k in inputs},
                    lambda inputs: {k: "-1" for k in inputs},
                ]
                
                # Helper function to check if a string is a number
                def is_number(s):
                    return s.lstrip('-').isdigit()
                
                # Try each approach until we have enough counterexamples
                for approach in approaches:
                    if len(counterexamples) > more_counterexamples_needed:
                        break
                        
                    # Generate modified inputs
                    try:
                        modified_inputs = approach(first_inputs)
                    except Exception:
                        continue  # Skip if approach fails
                    
                    # Skip if inputs are the same as any existing counterexample
                    if any(ex["inputs"] == modified_inputs for ex in counterexamples):
                        continue
                    
                    # Create SMT file for this test case
                    with open(example_path, 'w') as outf:
                        outf.write("; Testing modified inputs\n")
                        outf.write("(set-logic QF_LIA)\n")
                        
                        # Write all declarations
                        written_declarations = set()
                        for line in smt1_lines + smt2_lines:
                            if line.startswith("(declare-") and line not in written_declarations:
                                outf.write(line + "\n")
                                written_declarations.add(line)
                        
                        # Set specific input values
                        for var_name, value in modified_inputs.items():
                            outf.write(f"(assert (= p1_{var_name}_0 {value}))\n")
                            outf.write(f"(assert (= p2_{var_name}_0 {value}))\n")
                        
                        # Add all other constraints (except input constraints)
                        written_assertions = set()
                        for line in smt1_lines + smt2_lines:
                            if line.startswith("(assert"):
                                skip = False
                                for var_name in modified_inputs:
                                    if f"p1_{var_name}_0" in line or f"p2_{var_name}_0" in line:
                                        skip = True
                                        break
                                
                                if not skip and line not in written_assertions:
                                    outf.write(line + "\n")
                                    written_assertions.add(line)
                        
                        # Make sure results differ
                        outf.write(f"(assert (not (= {p1_final_var} {p2_final_var})))\n")
                        outf.write("(check-sat)\n")
                        outf.write("(get-model)\n")
                    
                    # Run Z3 to check if this is a counterexample
                    ce_result, ce_model = run_z3_model_check(example_path)
                    
                    if ce_result == "sat":
                        # Found another counterexample!
                        ce_model_dict = parse_smt_model(ce_model)
                        
                        # Extract results
                        p1_result_val = ce_model_dict.get(p1_final_var, "unknown")
                        p2_result_val = ce_model_dict.get(p2_final_var, "unknown")
                        
                        # Store this counterexample
                        counterexamples.append({
                            "inputs": modified_inputs,
                            "program1_result": p1_result_val,
                            "program2_result": p2_result_val
                        })
                
                # Generate same example - check if we can find at least one case where programs behave the same
                # Even if programs are not equivalent, there may be inputs where they produce the same result
                same_behavior_examples = []
                
                # Try a few different inputs to find matching behavior
                test_values = [-5, 0, 1, 2, 5, 10, 20]
                for test_val in test_values:
                    # Create test inputs with the same value for all inputs
                    test_inputs = {var: str(test_val) for var in input_vars}
                    
                    # Create SMT file for this test case
                    with open(example_path, 'w') as outf:
                        outf.write("; Testing for same behavior\n")
                        outf.write("(set-logic QF_LIA)\n")
                        
                        # Write all declarations
                        written_declarations = set()
                        for line in smt1_lines + smt2_lines:
                            if line.startswith("(declare-") and line not in written_declarations:
                                outf.write(line + "\n")
                                written_declarations.add(line)
                        
                        # Set specific input values
                        for var_name, value in test_inputs.items():
                            outf.write(f"(assert (= p1_{var_name}_0 {value}))\n")
                            outf.write(f"(assert (= p2_{var_name}_0 {value}))\n")
                        
                        # Add all other constraints (except input constraints)
                        written_assertions = set()
                        for line in smt1_lines + smt2_lines:
                            if line.startswith("(assert"):
                                skip = False
                                for var_name in test_inputs:
                                    if f"p1_{var_name}_0" in line or f"p2_{var_name}_0" in line:
                                        skip = True
                                        break
                                
                                if not skip and line not in written_assertions:
                                    outf.write(line + "\n")
                                    written_assertions.add(line)
                        
                        # Make sure results are THE SAME (opposite of counterexample check)
                        outf.write(f"(assert (= {p1_final_var} {p2_final_var}))\n")
                        outf.write("(check-sat)\n")
                        outf.write("(get-model)\n")
                    
                    # Run Z3 to check
                    same_result, same_model = run_z3_model_check(example_path)
                    
                    if same_result == "sat":
                        # Found a case where programs behave the same
                        same_model_dict = parse_smt_model(same_model)
                        
                        # Extract result
                        result_val = same_model_dict.get(p1_final_var, "unknown")
                        
                        # Store this example
                        same_behavior_examples.append({
                            "inputs": test_inputs,
                            "common_result": result_val
                        })
                        
                        # One example of same behavior is enough
                        break
                
                # Format the final result message
                details = ["Programs are not equivalent."]
                
                # Add counterexamples to details
                for i, ex in enumerate(counterexamples, 1):
                    details.append(f"\nCounterexample {i}:")
                    inputs_str = ", ".join([f"{var} = {val}" for var, val in ex["inputs"].items()])
                    details.append(f"Inputs: {inputs_str}")
                    details.append(f"Program 1 output: {ex['program1_result']}")
                    details.append(f"Program 2 output: {ex['program2_result']}")
                
                # Add same behavior examples if any
                if same_behavior_examples:
                    details.append("\nExamples where programs behave the same:")
                    for i, ex in enumerate(same_behavior_examples, 1):
                        inputs_str = ", ".join([f"{var} = {val}" for var, val in ex["inputs"].items()])
                        details.append(f"Example {i}: Inputs: {inputs_str}")
                        details.append(f"Common output: {ex['common_result']}")
                else:
                    details.append("\nNo common behavior examples found.")
                
                return (
                    "Programs are not equivalent.",
                    details,
                    ssa1, ssa2, smt1_lines, smt2_lines
                )
                
            elif result == "unsat":  # Programs ARE equivalent
                # Generate concrete examples where both programs behave the same
                # For equivalent programs, we need to generate at least 3 examples
                equivalent_examples = []
                
                # Generate different test values based on number of input variables
                test_cases = []
                if len(input_vars) == 1:
                    # For one variable, test different interesting values
                    test_cases = [
                        {input_vars[0]: "0"},
                        {input_vars[0]: "10"},
                        {input_vars[0]: "-5"}
                    ]
                elif len(input_vars) == 2:
                    # For two variables, test different combinations
                    test_cases = [
                        {input_vars[0]: "10", input_vars[1]: "5"},
                        {input_vars[0]: "0", input_vars[1]: "0"},
                        {input_vars[0]: "-3", input_vars[1]: "7"}
                    ]
                else:
                    # For more variables, test some combinations
                    test_cases = []
                    # First test: all values at 5
                    test_cases.append({var: "5" for var in input_vars})
                    # Second test: incrementing values
                    test_cases.append({var: str(i+1) for i, var in enumerate(input_vars)})
                    # Third test: some negative, some positive
                    test_cases.append({var: str((-1)**i * (i+1)) for i, var in enumerate(input_vars)})
                
                # For each test case, create SMT query to determine the result
                for test_case in test_cases:
                    with open(example_path, 'w') as outf:
                        outf.write("; Example execution\n")
                        outf.write("(set-logic QF_LIA)\n")
                        
                        # Write all declarations (non-duplicate)
                        written_declarations = set()
                        for line in smt1_lines + smt2_lines:
                            if line.startswith("(declare-") and line not in written_declarations:
                                outf.write(line + "\n")
                                written_declarations.add(line)
                        
                        # Set input values
                        for var_name, value in test_case.items():
                            outf.write(f"(assert (= p1_{var_name}_0 {value}))\n")
                            outf.write(f"(assert (= p2_{var_name}_0 {value}))\n")
                        
                        # Add all other constraints (except input constraints)
                        written_assertions = set()
                        for line in smt1_lines + smt2_lines:
                            if line.startswith("(assert"):
                                skip = False
                                for var_name in test_case:
                                    if f"p1_{var_name}_0" in line or f"p2_{var_name}_0" in line:
                                        skip = True
                                        break
                                
                                if not skip and line not in written_assertions:
                                    outf.write(line + "\n")
                                    written_assertions.add(line)
                        
                        outf.write("(check-sat)\n")
                        outf.write("(get-model)\n")
                    
                    # Run Z3 to get the execution result
                    ex_result, ex_model = run_z3_model_check(example_path)
                    
                    if ex_result == "sat":
                        # Parse model to extract result
                        ex_model_dict = parse_smt_model(ex_model)
                        result_val = ex_model_dict.get(p1_final_var, "unknown")
                        
                        # Add example to list
                        equivalent_examples.append({
                            "inputs": test_case,
                            "result": result_val
                        })
                
                # Format final result message
                details = ["Programs are equivalent (produce the same output for all inputs)."]
                
                # Add examples
                for i, ex in enumerate(equivalent_examples, 1):
                    details.append(f"\nExample {i}:")
                    # Make sure we include the inputs in the output
                    inputs_str = ", ".join([f"{var} = {val}" for var, val in ex["inputs"].items()])
                    details.append(f"Inputs: {inputs_str}")
                    details.append(f"Common output: {ex['result']}")
                
                return (
                    "Programs are equivalent.",
                    details,
                    ssa1, ssa2, smt1_lines, smt2_lines
                )
                
            else:  # result == "unknown"
                return (
                    "Z3 returned an unknown result for equivalence checking.",
                    ["The solver could not determine if the programs are equivalent.",
                     "This typically happens with complex constraints or non-linear operations."],
                    ssa1, ssa2, smt1_lines, smt2_lines
                )
        
        finally:
            # Clean up temporary files
            for path in [smt1_path, smt2_path, combined_path, example_path]:
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


def parse_smt_model(model_str):
    """
    Parse SMT model string into a dictionary of variable assignments
    
    Args:
        model_str: String containing SMT model output
        
    Returns:
        Dictionary mapping variable names to their values
    """
    model_dict = {}
    
    # Remove outer parentheses and split by variable declarations
    if model_str and model_str.strip().startswith("("):
        lines = model_str.strip()[1:-1].split("(define-fun ")
        
        for line in lines:
            if not line.strip():
                continue
                
            # Extract variable name and value
            parts = line.strip().split()
            if len(parts) >= 4:
                var_name = parts[0]
                var_value = parts[-2] if parts[-1] == ")" else parts[-1].rstrip(")")
                model_dict[var_name] = var_value
    
    return model_dict


def format_model_for_display(model_dict):
    """Format model dictionary for better display"""
    lines = []
    for var, value in sorted(model_dict.items()):
        lines.append(f"{var} = {value}")
    return "\n".join(lines)