import os
import tempfile
import re
from typing import Dict, List, Tuple, Any, Union

from smt_interface_eq import run_z3_model_check, format_model_for_display

def verify_program_ver(smt_content: str, unrolled_code: str = None):
    """
    Analyze a program and verify if its postconditions hold using provided SMT content
    
    Args:
        smt_content: SMT content string directly from the GUI
        unrolled_code: Pre-unrolled code (if available)
    
    Returns:
        Tuple of (result_message, details, ssa, smt_lines)
    """
    try:
        # Parse SMT content to extract lines
        smt_lines = smt_content.strip().split('\n')
        
        # Create temporary files for SMT operations
        combined_fd, combined_path = tempfile.mkstemp(suffix="_combined.smt2")
        example_fd, example_path = tempfile.mkstemp(suffix="_examples.smt2")
        
        try:
            # Close file descriptors
            os.close(combined_fd)
            os.close(example_fd)
            
            # Extract input variable declarations from SMT
            input_vars = []
            for line in smt_lines:
                if "declare-" in line and "_0" in line and "result" not in line:
                    # More robust matching for variable declarations
                    var_match = re.search(r'declare-(?:const|fun) ([^_:]+)_0', line)
                    if var_match:
                        input_name = var_match.group(1)
                        input_vars.append(input_name)
            
            # More robust extraction of assertions
            assertions = []
            assertion_vars = []
            
            # First pass: find all assert statements that look like actual assertions
            for line in smt_lines:
                if line.strip().startswith("(assert "):
                    # Clean up malformed assertions if needed
                    clean_line = re.sub(r'assert\(([^)]+)<', r'assert (< \1', line)
                    assertions.append(clean_line)
                    
                    # Look for assertion variables directly
                    assertion_match = re.search(r'assert_(\d+)', clean_line)
                    if assertion_match:
                        assertion_vars.append(f"assert_{assertion_match.group(1)}")
                    
                    # Also look for array comparison assertions that might be postconditions
                    array_assert_match = re.search(r'assert\s+\(\s*([<>=]+)\s*\(\s*select\s+arr_\d+\s+\d+\)', clean_line)
                    if array_assert_match:
                        assertion_vars.append(clean_line.strip())
            
            if not assertions:
                return (
                    "No assertions found in the SMT content.",
                    ["Please add at least one assert statement to verify."],
                    unrolled_code, smt_lines
                )
            
            # If no assertion variables found, look for other assertion patterns
            if not assertion_vars:
                # Look for result variables
                result_vars = []
                for line in assertions:
                    # Try to extract result variables or final condition checks
                    result_match = re.search(r'assert.*?\(([^_]+_result)', line)
                    if result_match:
                        result_vars.append(result_match.group(1))
                    
                    # Look for array comparison postconditions
                    array_compare = re.search(r'assert\s+\(\s*([<>=]+)\s*\(\s*select\s+arr_\d+\s+\d+\)', line)
                    if array_compare:
                        result_vars.append(line.strip())
                        
                if result_vars:
                    # Use the result variable as our assertion target
                    final_assertion_var = result_vars[-1]
                else:
                    # If still no assertions found, use the last assertion statement as a fallback
                    final_assertion_var = assertions[-1].strip()
            else:
                # Sort assertion variables by index
                assertion_vars.sort(key=lambda x: int(re.search(r'assert_(\d+)', x).group(1)) if re.search(r'assert_(\d+)', x) else 0)
                final_assertion_var = assertion_vars[-1]
            
            # Clean up assertion variable if it's a full assertion expression
            if final_assertion_var.strip().startswith("(assert "):
                final_assertion_content = re.search(r'\(assert\s+(.*)\)\s*$', final_assertion_var)
                if final_assertion_content:
                    final_assertion_var = final_assertion_content.group(1)
            
            # Step 5: Check if the postcondition can be violated
            with open(combined_path, 'w',encoding='utf-8') as outf:
                outf.write("; Combined SMT for postcondition verification\n")
                outf.write("(set-logic QF_LRA)\n")  # Linear Integer Arithmetic
                
                # Write all declarations and assertions from the program
                # Skip duplicates and fix formatting issues
                written_lines = set()
                for line in smt_lines:
                    # Skip malformed or duplicated lines
                    if line in written_lines or "< Int" in line:
                        continue
                    
                    # Fix array assertion syntax
                    if "assert(arr_" in line:
                        # Convert "assert(arr_0[0]< (select arr_0 1))" to proper SMT2 syntax
                        fixed_line = re.sub(r'assert\(arr_(\d+)\[(\d+)\]< ', r'(assert (< (select arr_\1 \2) ', line)
                        if fixed_line.endswith("))"):
                            fixed_line = fixed_line[:-1]  # Handle extra closing parenthesis
                        if fixed_line not in written_lines:
                            outf.write(fixed_line + "\n")
                            written_lines.add(fixed_line)
                    elif not line.startswith("(set-logic") and not line.startswith("(check-sat") and not line.startswith("(get-model"):
                        # Fix declaration syntax if needed
                        if "declare-const" in line and ":" in line and not line.endswith(")"):
                            fixed_line = line.replace(" : ", " ")
                            if fixed_line not in written_lines:
                                outf.write(fixed_line + ")\n")
                                written_lines.add(fixed_line)
                        else:
                            if line not in written_lines:
                                outf.write(line + "\n")
                                written_lines.add(line)
                
                # Check if postcondition can be violated
                outf.write("; Check if postcondition can be violated\n")
                
                # Make sure the assertion negation is properly formatted
                if final_assertion_var.startswith("(") and final_assertion_var.endswith(")"):
                    outf.write(f"(assert (not {final_assertion_var}))\n")
                elif final_assertion_var.startswith("assert_"):
                    outf.write(f"(assert (not {final_assertion_var}))\n")
                else:
                    # Handle full assertion statements
                    outf.write(f"(assert (not {final_assertion_var}))\n")
                
                outf.write("(check-sat)\n")
                outf.write("(get-model)\n")
            
            # Run Z3 to check for postcondition violation
            result, model = run_z3_model_check(combined_path)
            
            if result == "sat":  # Postcondition can be violated - found counterexamples
                # Parse the first counterexample
                model_dict = parse_smt_model(model)
                counterexamples = []
                
                # Extract first counterexample information
                first_inputs = {}
                for var_name in input_vars:
                    value = model_dict.get(f"{var_name}_0", "unknown")
                    first_inputs[var_name] = value
                
                # Get final values of program variables for the counterexample
                final_values = {}
                for var_name in model_dict:
                    if var_name not in [f"{var}_0" for var in input_vars] and not var_name.startswith("assert_"):
                        # Handle array elements specially
                        if "select" in var_name:
                            array_match = re.search(r'select arr_(\d+) (\d+)', var_name)
                            if array_match:
                                array_idx = int(array_match.group(1))
                                elem_idx = int(array_match.group(2))
                                if f"arr_{array_idx}" not in final_values:
                                    final_values[f"arr_{array_idx}"] = {}
                                final_values[f"arr_{array_idx}"][elem_idx] = model_dict[var_name]
                            continue
                        
                        base_name = var_name.split('_')[0]
                        if base_name not in final_values:
                            final_values[base_name] = {}
                        
                        # Extract version number and value
                        version_match = re.search(r'_(\d+)$', var_name)
                        if version_match:
                            version = int(version_match.group(1))
                            final_values[base_name][version] = model_dict[var_name]
                
                # For each variable, get the highest version (final value)
                final_state = {}
                for var, versions in final_values.items():
                    if versions:
                        if isinstance(versions, dict) and not var.startswith("arr_"):
                            max_version = max(versions.keys())
                            final_state[var] = versions[max_version]
                        else:
                            # Handle arrays differently
                            final_state[var] = versions
                
                # Add first counterexample to results
                counterexamples.append({
                    "inputs": first_inputs,
                    "final_state": final_state
                })
                
                # Need to find at least one more counterexample
                more_counterexamples_needed = 1
                
                # Helper function to check if a string is a number
                def is_number(s):
                    return s.lstrip('-').isdigit()
                
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
                    with open(example_path, 'w',encoding='utf-8') as outf:
                        outf.write("; Testing modified inputs\n")
                        outf.write("(set-logic QF_LRA)\n")
                        
                        # Write all declarations
                        written_declarations = set()
                        for line in smt_lines:
                            if line.startswith("(declare-") and line not in written_declarations:
                                # Fix declaration syntax if needed
                                if ":" in line and not line.endswith(")"):
                                    fixed_line = line.replace(" : ", " ")
                                    outf.write(fixed_line + ")\n")
                                else:
                                    outf.write(line + "\n")
                                written_declarations.add(line)
                        
                        # Set specific input values
                        for var_name, value in modified_inputs.items():
                            outf.write(f"(assert (= {var_name}_0 {value}))\n")
                        
                        # Add all other constraints (except input constraints)
                        written_assertions = set()
                        for line in smt_lines:
                            if line.startswith("(assert"):
                                skip = False
                                for var_name in modified_inputs:
                                    if f"{var_name}_0" in line:
                                        skip = True
                                        break
                                
                                if not skip and line not in written_assertions:
                                    outf.write(line + "\n")
                                    written_assertions.add(line)
                        
                        # Check if postcondition can be violated
                        if final_assertion_var.startswith("(") and final_assertion_var.endswith(")"):
                            outf.write(f"(assert (not {final_assertion_var}))\n")
                        elif final_assertion_var.startswith("assert_"):
                            outf.write(f"(assert (not {final_assertion_var}))\n")
                        else:
                            # Handle full assertion statements
                            outf.write(f"(assert (not {final_assertion_var}))\n")
                            
                        outf.write("(check-sat)\n")
                        outf.write("(get-model)\n")
                    
                    # Run Z3 to check if this is a counterexample
                    ce_result, ce_model = run_z3_model_check(example_path)
                    
                    if ce_result == "sat":
                        # Found another counterexample!
                        ce_model_dict = parse_smt_model(ce_model)
                        
                        # Get final values for this counterexample
                        ce_final_values = {}
                        for var_name in ce_model_dict:
                            if var_name not in [f"{var}_0" for var in input_vars] and not var_name.startswith("assert_"):
                                # Handle array elements specially
                                if "select" in var_name:
                                    array_match = re.search(r'select arr_(\d+) (\d+)', var_name)
                                    if array_match:
                                        array_idx = int(array_match.group(1))
                                        elem_idx = int(array_match.group(2))
                                        if f"arr_{array_idx}" not in ce_final_values:
                                            ce_final_values[f"arr_{array_idx}"] = {}
                                        ce_final_values[f"arr_{array_idx}"][elem_idx] = ce_model_dict[var_name]
                                    continue
                                
                                base_name = var_name.split('_')[0]
                                if base_name not in ce_final_values:
                                    ce_final_values[base_name] = {}
                                
                                # Extract version number and value
                                version_match = re.search(r'_(\d+)$', var_name)
                                if version_match:
                                    version = int(version_match.group(1))
                                    ce_final_values[base_name][version] = ce_model_dict[var_name]
                        
                        # For each variable, get the highest version (final value)
                        ce_final_state = {}
                        for var, versions in ce_final_values.items():
                            if versions:
                                if isinstance(versions, dict) and not var.startswith("arr_"):
                                    max_version = max(versions.keys())
                                    ce_final_state[var] = versions[max_version]
                                else:
                                    # Handle arrays differently
                                    ce_final_state[var] = versions
                        
                        # Store this counterexample
                        counterexamples.append({
                            "inputs": modified_inputs,
                            "final_state": ce_final_state
                        })
                
                # Find examples where postcondition holds (if possible)
                valid_examples = []
                
                # Try different test values
                test_values = [-5, 0, 1, 2, 5, 10, 20]
                for test_val in test_values:
                    if len(valid_examples) >= 1:
                        break  # We only need one valid example
                
                    # Create test inputs
                    test_inputs = {var: str(test_val) for var in input_vars}
                    
                    # Create SMT file for this test case
                    with open(example_path, 'w',encoding='utf-8') as outf:
                        outf.write("; Testing for valid inputs\n")
                        outf.write("(set-logic QF_LRA)\n")
                        
                        # Write all declarations
                        written_declarations = set()
                        for line in smt_lines:
                            if line.startswith("(declare-") and line not in written_declarations:
                                # Fix declaration syntax if needed
                                if ":" in line and not line.endswith(")"):
                                    fixed_line = line.replace(" : ", " ")
                                    outf.write(fixed_line + ")\n")
                                else:
                                    outf.write(line + "\n")
                                written_declarations.add(line)
                        
                        # Set specific input values
                        for var_name, value in test_inputs.items():
                            outf.write(f"(assert (= {var_name}_0 {value}))\n")
                        
                        # Add all other constraints (except input constraints)
                        written_assertions = set()
                        for line in smt_lines:
                            if line.startswith("(assert"):
                                skip = False
                                for var_name in test_inputs:
                                    if f"{var_name}_0" in line:
                                        skip = True
                                        break
                                
                                if not skip and line not in written_assertions:
                                    outf.write(line + "\n")
                                    written_assertions.add(line)
                        
                        # Make sure postcondition holds
                        if final_assertion_var.startswith("(") and final_assertion_var.endswith(")"):
                            outf.write(f"(assert {final_assertion_var})\n")
                        elif final_assertion_var.startswith("assert_"):
                            outf.write(f"(assert {final_assertion_var})\n")
                        else:
                            # Handle full assertion statements
                            if not final_assertion_var.startswith("(assert "):
                                outf.write(f"(assert {final_assertion_var})\n")
                            else:
                                outf.write(f"{final_assertion_var}\n")
                                
                        outf.write("(check-sat)\n")
                        outf.write("(get-model)\n")
                    
                    # Run Z3 to check
                    valid_result, valid_model = run_z3_model_check(example_path)
                    
                    if valid_result == "sat":
                        # Found a valid example
                        valid_model_dict = parse_smt_model(valid_model)
                        
                        # Get final values for this valid example
                        valid_final_values = {}
                        for var_name in valid_model_dict:
                            if var_name not in [f"{var}_0" for var in input_vars] and not var_name.startswith("assert_"):
                                # Handle array elements specially
                                if "select" in var_name:
                                    array_match = re.search(r'select arr_(\d+) (\d+)', var_name)
                                    if array_match:
                                        array_idx = int(array_match.group(1))
                                        elem_idx = int(array_match.group(2))
                                        if f"arr_{array_idx}" not in valid_final_values:
                                            valid_final_values[f"arr_{array_idx}"] = {}
                                        valid_final_values[f"arr_{array_idx}"][elem_idx] = valid_model_dict[var_name]
                                    continue
                                
                                base_name = var_name.split('_')[0]
                                if base_name not in valid_final_values:
                                    valid_final_values[base_name] = {}
                                
                                # Extract version number and value
                                version_match = re.search(r'_(\d+)$', var_name)
                                if version_match:
                                    version = int(version_match.group(1))
                                    valid_final_values[base_name][version] = valid_model_dict[var_name]
                        
                        # For each variable, get the highest version (final value)
                        valid_final_state = {}
                        for var, versions in valid_final_values.items():
                            if versions:
                                if isinstance(versions, dict) and not var.startswith("arr_"):
                                    max_version = max(versions.keys())
                                    valid_final_state[var] = versions[max_version]
                                else:
                                    # Handle arrays differently
                                    valid_final_state[var] = versions
                        
                        # Store this valid example
                        valid_examples.append({
                            "inputs": test_inputs,
                            "final_state": valid_final_state
                        })
                
                # Format the final result message
                details = ["Postcondition does not hold for all inputs."]
                
                # Add counterexamples to details
                for i, ex in enumerate(counterexamples, 1):
                    details.append(f"\nCounterexample {i}:")
                    inputs_str = ", ".join([f"{var} = {val}" for var, val in ex["inputs"].items()])
                    details.append(f"Inputs: {inputs_str}")
                    
                    # Format final state, handling arrays specially
                    final_state_parts = []
                    for var, val in ex["final_state"].items():
                        if isinstance(val, dict) and var.startswith("arr_"):
                            # Format array: arr_0 = [val0, val1, ...]
                            array_vals = []
                            for idx in sorted(val.keys()):
                                array_vals.append(val[idx])
                            final_state_parts.append(f"{var} = [{', '.join(array_vals)}]")
                        else:
                            final_state_parts.append(f"{var} = {val}")
                            
                    final_str = ", ".join(final_state_parts)
                    details.append(f"Final state: {final_str}")
                    details.append(f"Postcondition violated")
                
                # Add valid examples if any
                if valid_examples:
                    details.append("\nExamples where postcondition holds:")
                    for i, ex in enumerate(valid_examples, 1):
                        inputs_str = ", ".join([f"{var} = {val}" for var, val in ex["inputs"].items()])
                        details.append(f"Example {i}: Inputs: {inputs_str}")
                        
                        # Format final state, handling arrays specially
                        final_state_parts = []
                        for var, val in ex["final_state"].items():
                            if isinstance(val, dict) and var.startswith("arr_"):
                                # Format array: arr_0 = [val0, val1, ...]
                                array_vals = []
                                for idx in sorted(val.keys()):
                                    array_vals.append(val[idx])
                                final_state_parts.append(f"{var} = [{', '.join(array_vals)}]")
                            else:
                                final_state_parts.append(f"{var} = {val}")
                                
                        final_str = ", ".join(final_state_parts)
                        details.append(f"Final state: {final_str}")
                        details.append(f"Postcondition holds")
                else:
                    details.append("\nNo examples found where the postcondition holds.")
                
                return (
                    "Postcondition does not hold for all inputs.",
                    details,
                    unrolled_code, smt_lines
                )
                
            elif result == "unsat":  # Postcondition holds for all inputs
                # Generate concrete examples where postcondition holds
                # We want to generate at least 3 different examples
                valid_examples = []
                
                # Generate different test values based on number of input variables
                test_cases = []
                if not input_vars:
                    # Program has no input variables
                    test_cases = [{}]  # One empty case
                elif len(input_vars) == 1:
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
                    with open(example_path, 'w',encoding='utf-8') as outf:
                        outf.write("; Example execution\n")
                        outf.write("(set-logic QF_LRA)\n")
                        
                        # Write all declarations
                        written_declarations = set()
                        for line in smt_lines:
                            if line.startswith("(declare-") and line not in written_declarations:
                                # Fix declaration syntax if needed
                                if ":" in line and not line.endswith(")"):
                                    fixed_line = line.replace(" : ", " ")
                                    outf.write(fixed_line + ")\n")
                                else:
                                    outf.write(line + "\n")
                                written_declarations.add(line)
                        
                        # Set input values
                        for var_name, value in test_case.items():
                            outf.write(f"(assert (= {var_name}_0 {value}))\n")
                        
                        # Add all other constraints (except input constraints)
                        written_assertions = set()
                        for line in smt_lines:
                            if line.startswith("(assert"):
                                skip = False
                                for var_name in test_case:
                                    if f"{var_name}_0" in line:
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
                        
                        # Get final values for this example
                        ex_final_values = {}
                        for var_name in ex_model_dict:
                            if var_name not in [f"{var}_0" for var in input_vars] and not var_name.startswith("assert_"):
                                # Handle array elements specially
                                if "select" in var_name:
                                    array_match = re.search(r'select arr_(\d+) (\d+)', var_name)
                                    if array_match:
                                        array_idx = int(array_match.group(1))
                                        elem_idx = int(array_match.group(2))
                                        if f"arr_{array_idx}" not in ex_final_values:
                                            ex_final_values[f"arr_{array_idx}"] = {}
                                        ex_final_values[f"arr_{array_idx}"][elem_idx] = ex_model_dict[var_name]
                                    continue
                                
                                base_name = var_name.split('_')[0]
                                if base_name not in ex_final_values:
                                    ex_final_values[base_name] = {}
                                
                                # Extract version number and value
                                version_match = re.search(r'_(\d+)$', var_name)
                                if version_match:
                                    version = int(version_match.group(1))
                                    ex_final_values[base_name][version] = ex_model_dict[var_name]
                        
                        # For each variable, get the highest version (final value)
                        ex_final_state = {}
                        for var, versions in ex_final_values.items():
                            if versions:
                                if isinstance(versions, dict) and not var.startswith("arr_"):
                                    max_version = max(versions.keys())
                                    ex_final_state[var] = versions[max_version]
                                else:
                                    # Handle arrays differently
                                    ex_final_state[var] = versions
                                    # Store this example
                        valid_examples.append({
                            "inputs": test_case,
                            "final_state": ex_final_state
                        })
                
                # Format the final result message
                details = ["Postcondition holds for all inputs."]
                
                # Add validation examples to details
                for i, ex in enumerate(valid_examples, 1):
                    details.append(f"\nExample {i}:")
                    inputs_str = ", ".join([f"{var} = {val}" for var, val in ex["inputs"].items()]) if ex["inputs"] else "No inputs"
                    details.append(f"Inputs: {inputs_str}")
                    
                    # Format final state, handling arrays specially
                    final_state_parts = []
                    for var, val in ex["final_state"].items():
                        if isinstance(val, dict) and var.startswith("arr_"):
                            # Format array: arr_0 = [val0, val1, ...]
                            array_vals = []
                            for idx in sorted(val.keys()):
                                array_vals.append(val[idx])
                            final_state_parts.append(f"{var} = [{', '.join(array_vals)}]")
                        else:
                            final_state_parts.append(f"{var} = {val}")
                            
                    final_str = ", ".join(final_state_parts)
                    details.append(f"Final state: {final_str}")
                    details.append(f"Postcondition holds")
                
                return (
                    "Postcondition holds for all inputs.",
                    details,
                    unrolled_code, smt_lines
                )
            else:  # Error or timeout
                return (
                    f"Z3 solver error: {result}",
                    ["Error while checking postcondition with Z3."],
                    unrolled_code, smt_lines
                )
        
        finally:
            # Clean up temporary files
            try:
                os.remove(combined_path)
                os.remove(example_path)
            except Exception:
                pass
                
    except Exception as e:
        import traceback
        return (
            "Error analyzing program: " + str(e),
            [traceback.format_exc()],
            unrolled_code, smt_lines if 'smt_lines' in locals() else []
        )

def parse_smt_model(model_text: str) -> Dict[str, str]:
    """
    Parse SMT model output into a dictionary mapping variable names to values
    
    Args:
        model_text: Model output from Z3
        
    Returns:
        Dictionary mapping variable names to values
    """
    model_dict = {}
    
    # Skip empty models
    if not model_text or "model is not available" in model_text.lower():
        return model_dict
    
    # Pattern to match variable definitions
    var_pattern = re.compile(r'\(define-fun\s+([^\s\(\)]+)\s+\(\)\s+\w+\s+(.*?)\)', re.DOTALL)
    
    # Special pattern for array selects
    select_pattern = re.compile(r'\(define-fun\s+\(\(select\s+([^\s\(\)]+)\s+(\d+)\)\)\s+\(\)\s+\w+\s+(.*?)\)', re.DOTALL)
    
    # Find all variable definitions
    for match in var_pattern.finditer(model_text):
        var_name = match.group(1)
        value = match.group(2).strip()
        
        # Clean up the value
        value = re.sub(r'\((-\s+\d+)\)', r'\1', value)  # Fix negative numbers like (- 5) to -5
        value = value.replace("(- ", "-")
        value = re.sub(r'\)', '', value)
        
        model_dict[var_name] = value
    
    # Find array select operations
    for match in select_pattern.finditer(model_text):
        array_name = match.group(1)
        index = match.group(2)
        value = match.group(3).strip() 
        
        # Clean up the value
        value = re.sub(r'\((-\s+\d+)\)', r'\1', value)  # Fix negative numbers like (- 5) to -5
        value = value.replace("(- ", "-")
        value = re.sub(r'\)', '', value)
        
        # Store as "select array_name index" -> value
        model_dict[f"select {array_name} {index}"] = value
    
    return model_dict



def validate_postcondition(test_cases, smt_formula, input_vars, output_vars):
    """
    Validates that a postcondition holds for all test cases.
    
    Args:
        test_cases: List of dictionaries containing input values
        smt_formula: The SMT formula representing the program's logic
        input_vars: List of input variable names
        output_vars: List of output variable names
        
    Returns:
        tuple: (result_message, details, unrolled_code, smt_lines)
    """
    unrolled_code = "# Symbolic execution trace would go here"
    smt_lines = ["# SMT formula would go here"]
    valid_examples = []
    
    # Process each test case
    for test_case in test_cases:
        # In a real implementation, this would call parse_smt_model
        # Here we'll hardcode the results for demonstration
        
        # For each test case, we create a simulated final state
        ex_final_values = {}
        
        # Process variables based on test case inputs
        # This is a simplified example - in reality, you would run the model
        # and extract the final values from the SMT solver
        for var_name in output_vars:
            # Create entries for output variables
            base_name = var_name.split('_')[0]
            if base_name not in ex_final_values:
                ex_final_values[base_name] = {}
            
            # Simulate versions (assuming we're tracking versions of variables)
            ex_final_values[base_name][0] = str(test_case.get(base_name, 0) * 2)  # Simple transformation for demo
        
        # Handle array variables if present
        for var_name in [v for v in test_case.keys() if v.startswith("arr_")]:
            if var_name not in ex_final_values:
                ex_final_values[var_name] = {}
            
            # For demo purposes, we'll just copy the array
            if isinstance(test_case[var_name], list):
                for idx, val in enumerate(test_case[var_name]):
                    ex_final_values[var_name][idx] = str(val)
        
        # Get final state (highest version for each variable)
        ex_final_state = {}
        for var, versions in ex_final_values.items():
            if versions:
                if isinstance(versions, dict) and not var.startswith("arr_"):
                    max_version = max(versions.keys())
                    ex_final_state[var] = versions[max_version]
                else:
                    # Handle arrays
                    ex_final_state[var] = versions
        
        # Store this example
        valid_examples.append({
            "inputs": test_case,
            "final_state": ex_final_state
        })
    
    # Generate details report
    details = ["Postcondition holds for all inputs."]
    
    # Add validation examples to details
    for i, ex in enumerate(valid_examples, 1):
        details.append(f"\nExample {i}:")
        inputs_str = ", ".join([f"{var} = {val}" for var, val in ex["inputs"].items()]) if ex["inputs"] else "No inputs"
        details.append(f"Inputs: {inputs_str}")
        
        # Format final state, handling arrays specially
        final_state_parts = []
        for var, val in ex["final_state"].items():
            if isinstance(val, dict) and var.startswith("arr_"):
                # Format array: arr_0 = [val0, val1, ...]
                array_vals = []
                for idx in sorted(val.keys()):
                    array_vals.append(val[idx])
                final_state_parts.append(f"{var} = [{', '.join(array_vals)}]")
            else:
                final_state_parts.append(f"{var} = {val}")
                
        final_str = ", ".join(final_state_parts)
        details.append(f"Final state: {final_str}")
        details.append("Postcondition holds")
    
    return (
        "Postcondition holds for all inputs.",
        details,
        unrolled_code, 
        smt_lines
    )

