import subprocess
import re
import os
import tempfile
from typing import Tuple, Dict, Optional

def run_z3_model_check(smt_file_path: str) -> Tuple[str, str]:
    """
    Run Z3 on an SMT file and return the res
    
    Args:
        smt_file_path: Path to the SMT file
        
    Returns:
        Tuple of (res, model) where:
            res: 'sat', 'unsat', or 'unknown'
            model: model string if sat, error message if unknown
    """
    try:
        # Call Z3 with the SMT file
        res = subprocess.run(
            ["C:\\Users\\eshal\\Downloads\\z3-4.14.1-x64-win\\z3-4.14.1-x64-win\\bin\\z3", smt_file_path],
            capture_output=True,
            text=True,
            check=False,
            timeout=30  # Timeout after 30 seconds
        )
        
        output = res.stdout.strip()
        error = res.stderr.strip()
        
        # Check for errors
        if error:
            return "unknown", f"Error: {error}"
        
        # Parse the output
        if output.startswith("sat"):
            # Extract the model
            model_str = output[3:].strip()  # Remove "sat" prefix
            return "sat", model_str
        elif output.startswith("unsat"):
            return "unsat", ""
        else:
            return "unknown", output
    
    except subprocess.TimeoutExpired:
        return "unknown", "Timeout expired"
    except subprocess.CalledProcessError as e:
        return "unknown", f"Error: {e}"
    except FileNotFoundError:
        return "unknown", "Z3 executable not found. Please install Z3."
    except Exception as e:
        return "unknown", f"Unexpected error: {e}"

def parse_z3_model(model_str: str) -> Dict[str, str]:
    """
    Parse a Z3 model output string and return a dictionary of variable assignments
    
    Args:
        model_str: Z3 model output
        
    Returns:
        Dictionary mapping variable names to values
    """
    modeldict = {}
    
    # Look for define-fun statements
    pattern = r'\(define-fun\s+(\S+)\s+\(\)\s+(\S+)\s+(.+?)\)'
    matches = re.findall(pattern, model_str, re.DOTALL)
    
    for var_name, var_type, var_value in matches:
        # Clean up the value
        var_value = var_value.strip()
        if var_value.endswith(')'):
            var_value = var_value[:-1].strip()
        
        modeldict[var_name] = var_value
    
    return modeldict

def format_model_for_display(modeldict: Dict[str, str]) -> str:
    """
    Format a model dictionary for display
    
    Args:
        modeldict: Dictionary of variable assignments
        
    Returns:
        Formatted string representation
    """
    res = []
    
    # Group variables by their base name (before underscore)
    grouped_vars = {}
    for var_name, var_value in modeldict.items():
        # Parse variable name to extract original name and version
        match = re.match(r'([^_]+)_(\d+)', var_name)
        if match:
            basename = match.group(1)
            version = int(match.group(2))
            
            if basename not in grouped_vars:
                grouped_vars[basename] = {}
            
            grouped_vars[basename][version] = var_value
    
    # Add special variables first (like res)
    for var_name in ["p1_res", "p2_res"]:
        if var_name in modeldict:
            res.append(f"{var_name} = {modeldict[var_name]}")
    
    # Format each variable group
    for basename, versions in sorted(grouped_vars.items()):
        if basename in ["p1_res", "p2_res", "res"]:
            continue  # Skip res variables as they were handled above
            
        values = []
        for version in sorted(versions.keys()):
            values.append(f"{basename}_{version} = {versions[version]}")
        
        res.append(", ".join(values))
    
    return "\n".join(res)

def check_smt_constraints(smt_file_path: str) -> Tuple[str, Optional[str]]:
    """
    Check SMT constraints and format the res
    
    Args:
        smt_file_path: Path to the SMT file
        
    Returns:
        Tuple of (status, model_str) where:
            status: 'sat', 'unsat', or 'unknown'
            model_str: Formatted model string if sat, None otherwise
    """
    res, model_output = run_z3_model_check(smt_file_path)
    
    if res == "sat":
        modeldict = parse_z3_model(model_output)
        formatted_model = format_model_for_display(modeldict)
        return "sat", formatted_model
    elif res == "unsat":
        return "unsat", None
    else:
        return "unknown", model_output

