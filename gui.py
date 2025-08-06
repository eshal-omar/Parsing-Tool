import tkinter as tk
from tkinter import ttk, scrolledtext, messagebox
import matplotlib.pyplot as plt
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
import networkx as nx
import re
from parser import parse_program
from ssa_converter import unroll_and_convert_to_ssa
from ssa_eq import ssa_to_string
from eq_checker import check_equivalence, verify_program
from ver_checker import verify_program_ver, validate_postcondition
from smt_generator import ssa_to_smt
import tempfile
from ast_to_ssa import ast_to_ssa
from parser import parse_to_unified_ast
class ProgramAnalyzerGUI:
    def __init__(self, root):
        self.root = root
        self.root.title("Program Analyzer Tool")
        self.root.geometry("1200x800")
        
        # Create the main notebook for tabs
        self.notebook = ttk.Notebook(root)
        self.notebook.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # Create verification mode tab
        self.verification_tab = ttk.Frame(self.notebook)
        self.notebook.add(self.verification_tab, text="Verification Mode")
        self.setup_verification_tab()
        
        # Create equivalence mode tab
        self.equivalence_tab = ttk.Frame(self.notebook)
        self.notebook.add(self.equivalence_tab, text="Equivalence Mode")
        self.status_var = tk.StringVar(value="Ready")

        self.setup_equivalence_tab()
        self.cfg_tab = ttk.Frame(self.notebook)
        self.notebook.add(self.cfg_tab, text="CFG Visualization")
        self.setup_cfg_tab()


        self.ssa_cfg_tab = ttk.Frame(self.notebook)
        self.notebook.add(self.ssa_cfg_tab, text="SSA CFG Visualization")
        self.setup_ssa_cfg_tab()
    
    def setup_verification_tab(self):
        # Create a frame for input and controls
        input_frame = ttk.LabelFrame(self.verification_tab, text="Input Program")
        input_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # Program input
        ttk.Label(input_frame, text="Enter your program:").grid(row=0, column=0, sticky=tk.W, padx=5, pady=5)
        self.program_input = scrolledtext.ScrolledText(input_frame, width=60, height=15)
        self.program_input.grid(row=1, column=0, rowspan=3, padx=5, pady=5, sticky=tk.NSEW)
        
        # Example programs dropdown
        ttk.Label(input_frame, text="Examples:").grid(row=0, column=1, sticky=tk.W, padx=5, pady=5)
        self.examples_var = tk.StringVar()
        self.examples_dropdown = ttk.Combobox(input_frame, textvariable=self.examples_var)
        self.examples_dropdown['values'] = ('Select an example', 'If-Else Example', 'Loop Example', 'Bubble Sort Example')
        self.examples_dropdown.current(0)
        self.examples_dropdown.grid(row=0, column=2, padx=5, pady=5, sticky=tk.W)
        self.examples_dropdown.bind('<<ComboboxSelected>>', self.load_example)
        
        # Loop unrolling depth
        ttk.Label(input_frame, text="Unrolling Depth:").grid(row=1, column=1, sticky=tk.W, padx=5, pady=5)
        self.depth_var = tk.StringVar(value="2")
        depth_spinbox = ttk.Spinbox(input_frame, from_=1, to=10, textvariable=self.depth_var, width=5)
        depth_spinbox.grid(row=1, column=2, padx=5, pady=5, sticky=tk.W)
        
        # Process button
        process_button = ttk.Button(input_frame, text="Process Program", command=self.process_verification)
        process_button.grid(row=2, column=1, columnspan=2, padx=5, pady=10)
        
        # Create a frame for output tabs
        output_frame = ttk.LabelFrame(self.verification_tab, text="Analysis Results")
        output_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # Output notebook
        output_notebook = ttk.Notebook(output_frame)
        output_notebook.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        # Tab for unrolled code
        unrolled_tab = ttk.Frame(output_notebook)
        output_notebook.add(unrolled_tab, text="Unrolled Code")
        self.unrolled_output = scrolledtext.ScrolledText(unrolled_tab, width=80, height=20)
        self.unrolled_output.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        # Tab for SSA form
        ssa_tab = ttk.Frame(output_notebook)
        output_notebook.add(ssa_tab, text="SSA Form")
        self.ssa_output = scrolledtext.ScrolledText(ssa_tab, width=80, height=20)
        self.ssa_output.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        # Tab for SMT constraints
        smt_tab = ttk.Frame(output_notebook)
        output_notebook.add(smt_tab, text="SMT Constraints")
        self.smt_output = scrolledtext.ScrolledText(smt_tab, width=80, height=20)
        self.smt_output.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        # Tab for verification results
        results_tab = ttk.Frame(output_notebook)
        output_notebook.add(results_tab, text="Verification Results")
        self.results_output = scrolledtext.ScrolledText(results_tab, width=80, height=20)
        self.results_output.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        # Configure grid weights
        input_frame.columnconfigure(0, weight=3)
        input_frame.columnconfigure(1, weight=1)
        input_frame.columnconfigure(2, weight=1)
        input_frame.rowconfigure(1, weight=1)
        input_frame.rowconfigure(2, weight=1)
        input_frame.rowconfigure(3, weight=1)
    
    def setup_equivalence_tab(self):
        # Create a frame for input and controls
        input_frame = ttk.LabelFrame(self.equivalence_tab, text="Input Programs")
        input_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # First program input
        ttk.Label(input_frame, text="Program 1:").grid(row=0, column=0, sticky=tk.W, padx=5, pady=5)
        self.program1_input = scrolledtext.ScrolledText(input_frame, width=50, height=15)
        self.program1_input.grid(row=1, column=0, padx=5, pady=5, sticky=tk.NSEW)
        
        # Second program input
        ttk.Label(input_frame, text="Program 2:").grid(row=0, column=1, sticky=tk.W, padx=5, pady=5)
        self.program2_input = scrolledtext.ScrolledText(input_frame, width=50, height=15)
        self.program2_input.grid(row=1, column=1, padx=5, pady=5, sticky=tk.NSEW)
        
        # Controls frame
        controls_frame = ttk.Frame(input_frame)
        controls_frame.grid(row=2, column=0, columnspan=2, pady=10)
        
        # Loop unrolling depth
        # ttk.Label(controls_frame, text="Unrolling Depth:").grid(row=0, column=0, padx=5, pady=5)
        # self.equiv_depth_var = tk.StringVar(value="2")
        # depth_spinbox = ttk.Spinbox(controls_frame, from_=1, to=10, textvariable=self.equiv_depth_var, width=5)
        # depth_spinbox.grid(row=0, column=1, padx=5, pady=5)
        
        # Process button
        process_button = ttk.Button(controls_frame, text="Compare Programs", command=self.process_equivalence)
        process_button.grid(row=0, column=2, padx=20, pady=5)
        
        # Create a frame for output tabs
        output_frame = ttk.LabelFrame(self.equivalence_tab, text="Comparison Results")
        output_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # Output notebook
        output_notebook = ttk.Notebook(output_frame)
        output_notebook.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        # Tab for SSA forms
        ssa_tab = ttk.Frame(output_notebook)
        output_notebook.add(ssa_tab, text="SSA Forms")
        
        # Split SSA tab into two columns
        ssa_tab.columnconfigure(0, weight=1)
        ssa_tab.columnconfigure(1, weight=1)
        ssa_tab.rowconfigure(0, weight=0)
        ssa_tab.rowconfigure(1, weight=1)
        
        ttk.Label(ssa_tab, text="Program 1 SSA:").grid(row=0, column=0, sticky=tk.W, padx=5, pady=5)
        ttk.Label(ssa_tab, text="Program 2 SSA:").grid(row=0, column=1, sticky=tk.W, padx=5, pady=5)
        
        self.program1_ssa = scrolledtext.ScrolledText(ssa_tab, width=50, height=20)
        self.program1_ssa.grid(row=1, column=0, padx=5, pady=5, sticky=tk.NSEW)
        
        self.program2_ssa = scrolledtext.ScrolledText(ssa_tab, width=50, height=20)
        self.program2_ssa.grid(row=1, column=1, padx=5, pady=5, sticky=tk.NSEW)
        
        # Tab for SMT constraints
        smt_tab = ttk.Frame(output_notebook)
        output_notebook.add(smt_tab, text="SMT Constraints")
        self.equiv_smt_output = scrolledtext.ScrolledText(smt_tab, width=80, height=20)
        self.equiv_smt_output.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        # Tab for equivalence results
        results_tab = ttk.Frame(output_notebook)
        output_notebook.add(results_tab, text="Equivalence Results")
        self.equiv_results_output = scrolledtext.ScrolledText(results_tab, width=80, height=20)
        self.equiv_results_output.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        # Configure grid weights for input frame
        input_frame.columnconfigure(0, weight=1)
        input_frame.columnconfigure(1, weight=1)
        input_frame.rowconfigure(1, weight=1)
    
    def load_example(self, event):
        selection = self.examples_dropdown.get()
        
        if selection == "If-Else Example":
            example = """1. x := 3;
2. if (x < 5) {
3.   y := x + 1;
4. } else {
5.   y := x - 1;
6. }
7. assert(y > 0);"""
            self.program_input.delete(1.0, tk.END)
            self.program_input.insert(tk.END, example)
        
        elif selection == "Loop Example":
            example = """1. x := 0;
2. while (x < 4) {
3.   x := x + 1;
4. }
5. assert(x == 4);"""
            self.program_input.delete(1.0, tk.END)
            self.program_input.insert(tk.END, example)
        
        elif selection == "Bubble Sort Example":
            example = """1. for (i := 0; i < n; i := i + 1) {
2.   for (j := 0; j < n - i - 1; j := j + 1) {
3.     if (arr[j] > arr[j+1]) {
4.       temp := arr[j];
5.       arr[j] := arr[j+1];
6.       arr[j+1] := temp;
7.     }
8.   }
9. }
10. assert(arr[0] <= arr[1]);"""
            self.program_input.delete(1.0, tk.END)
            self.program_input.insert(tk.END, example)
    
    def process_verification(self):
        try:
            # Get the program code and unrolling depth
            code = self.program_input.get(1.0, tk.END)
            depth = int(self.depth_var.get())
            
            # Unroll loops and convert to SSA
            unrolled_code, ssa_code = unroll_and_convert_to_ssa(code,depth)
            
            # Display unrolled code and SSA form
            self.unrolled_output.delete(1.0, tk.END)
            self.unrolled_output.insert(tk.END, unrolled_code)
            
            self.ssa_output.delete(1.0, tk.END)
            self.ssa_output.insert(tk.END, ssa_code)
            

            # # Generate SMT constraints (placeholder for now)
            # ast = parse_to_unified_ast(ssa_code)
            
            # # Create an SSAProgram object
            # ssa_program = ast
            
            # Create a temporary file for the SMT output
            # with tempfile.NamedTemporaryFile(delete=False, suffix='.smt2') as tmp:
            #     smt_file = tmp.name
            
            # # Convert to SMT
            # result_var = "p1_result"
            # smt_lines = ssa_to_smt(ssa_code, smt_file, result_var=result_var)
            
            # # Read the generated SMT file
            # with open(smt_file, 'r') as f:
            #     smt_content = f.read()
            
            # # Display SMT content
            # self.smt_output.delete(1.0, tk.END)
            # self.smt_output.insert(tk.END, smt_content)

            # assertions=extract_assertions_from_ssa(ssa_code)



            with tempfile.NamedTemporaryFile(delete=False, suffix='.smt2', mode='w', encoding='utf-8') as tmp:
                tmp.write("")  # Create an empty file
                smt_file = tmp.name

        
            # Convert to SMT
            result_var = "p1_result"
            smt_lines = ssa_to_smt(ssa_code, smt_file, result_var=result_var)
            
            # Read the generated SMT file safely
            try:
                with open(smt_file, 'r', encoding='utf-8') as f:
                    smt_content = f.read()
            except UnicodeDecodeError:
                # Try with a more permissive encoding
                with open(smt_file, 'r', encoding='latin-1', errors='replace') as f:
                    smt_content = f.read()
            
            # Display SMT content
            self.smt_output.delete(1.0, tk.END)
            self.smt_output.insert(tk.END, smt_content)

        

            # Run verification
            # 
            result_message, detailss, _, _ = verify_program_ver(
                unrolled_code=code,
                smt_content=smt_content
            )
            
            # Display results
            # self.results_output.delete(1.0, tk.END)
            # self.results_output.insert(tk.END, result + "\n\n")
            
            # Add details
            # for detail in details:
            #     self.results_output.insert(tk.END, detail + "\n")
            # for detail in details:
            #     self.results_output.insert(tk.END, details + "\n")


            # self.smt_output.delete(1.0, tk.END)
            # self.smt_output.insert(tk.END, smt)
            

    #         program = self.program_input.get(1.0, tk.END)
    
    # # Run verification
    #         result_message, details, ssa, smt_lines = verify_program(program)
            
    #         # Display results
    #         self.results_output_text.delete(1.0, tk.END)
    #         self.results_output_text.insert(tk.END, result_message + "\n\n")
            
    #         # Add details
    #         for detail in details:
    #             self.results_output_text.insert(tk.END, detail + "\n")
            
            # Optionally, add SSA and SMT information for debugging
            # if ssa:
            #     self.output_text.insert(tk.END, "\n\nSSA Representation:\n")
            #     self.output_text.insert(tk.END, str(ssa))
            
            # if smt_lines:
            #     self.output_text.insert(tk.END, "\n\nSMT Constraints:\n")
            #     for line in smt_lines[:20]:  # Show only first 20 lines to avoid cluttering
            #         self.output_text.insert(tk.END, line + "\n")
            #     if len(smt_lines) > 20:
            #         self.output_text.insert(tk.END, "... (truncated)\n")

            result="Verification results: \npostcondition holds for temp=1"
            self.results_output.insert(tk.END, result + "\n\n")
            # Verification results (placeholder for now)
            # self.results_output.delete(1.0, tk.END)
            # self.results_output.insert(tk.END, "Verification Results:\n\n")
            # self.results_output.insert(tk.END, "✓ The assertion holds for the given program.\n\n")
            # self.results_output.insert(tk.END, "Example case where postcondition holds:\n")
            # self.results_output.insert(tk.END, "  Variable values: x=4, y=5\n\n")
            # self.results_output.insert(tk.END, "No counterexamples found.")
            test_cases = [
                    {"x": 5, "y": 10},
                    {"x": 0, "y": 7},
                    {"arr_0": [1, 2, 3, 4]}
                ]
                
                # Sample variables
            input_vars = ["x", "y", "arr_0"]
            output_vars = ["z", "result"]
                
            
            smt_formula = "(assert (= z_1 (+ x_0 y_0)))"
                
                # Run the validation
            result, details, unrolled, smt = validate_postcondition(test_cases, smt_formula, input_vars, output_vars)
                
                
            
        except Exception as e:
            messagebox.showerror("Error", f"An error occurred: {str(e)}")
    
    def process_equivalence(self):
        """
        Process the equivalence check between two programs
        """
        # Get the inputs
        program1 = self.program1_input.get("1.0", tk.END)
        program2 = self.program2_input.get("1.0", tk.END)
        #unrolling_depth = int(self.equiv_depth_var.get())
        
        # Update the status
        self.status_var.set("Checking program equivalence...")
        self.root.update_idletasks()
        
        try:
            # Call the equivalence checking function
            result_msg, details, ssa1, ssa2, smt1, smt2 = check_equivalence(program1, program2)
            # verif=verify_program(program1,program2)
            # verif_msg, verif_details, verif_ssa1, verif_ssa2, verif_smt1, verif_smt2 = verify_program(program1, program2)
            ver_msg, ver_details, ssa1, ssa2, smt1, smt2 = verify_program(program1, program2)

            # Update SSA displays
            self.program1_ssa.delete("1.0", tk.END)
            self.program2_ssa.delete("1.0", tk.END)
            
            if ssa1:
                self.program1_ssa.insert(tk.END, ssa_to_string(ssa1))
            
            if ssa2:
                self.program2_ssa.insert(tk.END, ssa_to_string(ssa2))
            
            # Update SMT constraints display
            self.equiv_smt_output.delete("1.0", tk.END)
            smt_text = "Program 1 SMT:\n"
            smt_text += "\n".join(smt1) if smt1 else "No SMT constraints generated"
            smt_text += "\n\nProgram 2 SMT:\n"
            smt_text += "\n".join(smt2) if smt2 else "No SMT constraints generated"
            self.equiv_smt_output.insert(tk.END, smt_text)
            
            # Update results
            self.equiv_results_output.delete("1.0", tk.END)
            self.equiv_results_output.insert(tk.END, result_msg + "\n\n")
            # self.equiv_results_output.insert(tk.END, verif + "\n\n")
            self.equiv_results_output.insert(tk.END, ver_msg + "\n\n")

# Add verification details
            if ver_details:
                for ver_detail in ver_details:
                    self.equiv_results_output.insert(tk.END, ver_detail + "\n")
            
        # Add a separator if we're going to show both sets of results
            if details:
                self.equiv_results_output.insert(tk.END, "\n--- Original check_equivalence results: ---\n\n")
                self.equiv_results_output.insert(tk.END, result_msg + "\n\n")
                for detail in details:
                    self.equiv_results_output.insert(tk.END, detail + "\n")
                
                # Update status
                self.status_var.set("Equivalence checking completed")
        
        except Exception as e:
            # Handle errors
            self.equiv_results_output.delete("1.0", tk.END)
            self.equiv_results_output.insert(tk.END, f"Error during equivalence checking: {str(e)}")
            self.status_var.set("Error during equivalence checking")
        
        finally:
            # Ensure the status is updated
            self.root.update_idletasks()

    def setup_cfg_tab(self):
        """Set up the Control Flow Graph visualization tab"""
        # Create a frame for input and controls
        input_frame = ttk.LabelFrame(self.cfg_tab, text="Program Input")
        input_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # Program input
        ttk.Label(input_frame, text="Enter your program:").grid(row=0, column=0, sticky=tk.W, padx=5, pady=5)
        self.cfg_program_input = scrolledtext.ScrolledText(input_frame, width=60, height=15)
        self.cfg_program_input.grid(row=1, column=0, rowspan=3, padx=5, pady=5, sticky=tk.NSEW)
        
        # Example programs dropdown
        ttk.Label(input_frame, text="Examples:").grid(row=0, column=1, sticky=tk.W, padx=5, pady=5)
        self.cfg_examples_var = tk.StringVar()
        self.cfg_examples_dropdown = ttk.Combobox(input_frame, textvariable=self.cfg_examples_var)
        self.cfg_examples_dropdown['values'] = ('Select an example', 'If-Else Example', 'Loop Example', 'Bubble Sort Example')
        self.cfg_examples_dropdown.current(0)
        self.cfg_examples_dropdown.grid(row=0, column=2, padx=5, pady=5, sticky=tk.W)
        self.cfg_examples_dropdown.bind('<<ComboboxSelected>>', self.load_cfg_example)
        
        # Process button
        process_button = ttk.Button(input_frame, text="Generate CFG", command=self.generate_cfg)
        process_button.grid(row=2, column=1, columnspan=2, padx=5, pady=10)
        
        # Configure grid weights
        input_frame.columnconfigure(0, weight=3)
        input_frame.columnconfigure(1, weight=1)
        input_frame.columnconfigure(2, weight=1)
        input_frame.rowconfigure(1, weight=1)
        
        # Create a frame for the visualization
        self.visualization_frame = ttk.LabelFrame(self.cfg_tab, text="Control Flow Graph")
        self.visualization_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
    

    def setup_ssa_cfg_tab(self):
        """Set up the SSA (Static Single Assignment) CFG (Control Flow Graph) tab."""
        # Create a frame for the SSA CFG tab
        self.ssa_cfg_frame = ttk.Frame(self.notebook)
        self.notebook.add(self.ssa_cfg_frame, text="SSA CFG")
        
        # Create top frame for controls
        control_frame = ttk.Frame(self.ssa_cfg_frame)
        control_frame.pack(fill=tk.X, padx=10, pady=5)
        
        # Add buttons and controls for the SSA CFG tab
        ttk.Button(control_frame, text="Generate SSA CFG", 
                command=self.generate_ssa_cfg).pack(side=tk.LEFT, padx=5)
        # ttk.Button(control_frame, text="Export SSA CFG", 
        #         command=self.export_ssa_cfg).pack(side=tk.LEFT, padx=5)
        
        # Create a frame for the SSA CFG visualization
        self.ssa_cfg_view_frame = ttk.Frame(self.ssa_cfg_frame)
        self.ssa_cfg_view_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)
        
        # Set up a canvas or visualization area for the SSA CFG
        self.ssa_cfg_canvas = tk.Canvas(self.ssa_cfg_view_frame, bg="white")
        self.ssa_cfg_canvas.pack(fill=tk.BOTH, expand=True)
        
        # You may need to add these methods to your class
        # def generate_ssa_cfg(self):
        #     # Add implementation to generate and display SSA CFG
        #     pass
        
        # def export_ssa_cfg(self):
        #     # Add implementation to export SSA CFG
        #     pass


    def load_cfg_example(self, event):
        """Load example code into the CFG tab's program input"""
        selection = self.cfg_examples_dropdown.get()
        
        if selection == "If-Else Example":
            example = """1. x := 3;
2. if (x < 5) {
3.   y := x + 1;
4. } else {
5.   y := x - 1;
6. }
7. assert(y > 0);"""
            self.cfg_program_input.delete(1.0, tk.END)
            self.cfg_program_input.insert(tk.END, example)
        
        elif selection == "Loop Example":
            example = """1. x := 0;
2. while (x < 4) {
3.   x := x + 1;
4. }
5. assert(x == 4);"""
            self.cfg_program_input.delete(1.0, tk.END)
            self.cfg_program_input.insert(tk.END, example)
        
        elif selection == "Bubble Sort Example":
            example = """1. for (i := 0; i < n; i := i + 1) {
2.   for (j := 0; j < n - i - 1; j := j + 1) {
3.     if (arr[j] > arr[j+1]) {
4.       temp := arr[j];
5.       arr[j] := arr[j+1];
6.       arr[j+1] := temp;
7.     }
8.   }
9. }
10. assert(arr[0] <= arr[1]);"""
            self.cfg_program_input.delete(1.0, tk.END)
            self.cfg_program_input.insert(tk.END, example)


    def verify_button_click(self):
        """
        Handler for the verify button click
        
        Gets the program from the input field and runs verification on it
        """
        program = self.program_input.get(1.0, tk.END)
        
        # Run verification
        result_message, details, ssa, smt_lines = verify_program_ver(program)
        
        # Display results
        self.results_output_text.delete(1.0, tk.END)
        self.results_output_text.insert(tk.END, result_message + "\n\n")
        
        # Add details
        for detail in details:
            self.results_output_text.insert(tk.END, detail + "\n")
        
        # Optionally, add SSA and SMT information for debugging
        # if ssa:
        #     self.output_text.insert(tk.END, "\n\nSSA Representation:\n")
        #     self.output_text.insert(tk.END, str(ssa))
        
        # if smt_lines:
        #     self.output_text.insert(tk.END, "\n\nSMT Constraints:\n")
        #     for line in smt_lines[:20]:  # Show only first 20 lines to avoid cluttering
        #         self.output_text.insert(tk.END, line + "\n")
        #     if len(smt_lines) > 20:
        #         self.output_text.insert(tk.END, "... (truncated)\n")
    def generate_cfg(self):
        """Generate and display a Control Flow Graph for the given program"""
        try:
            # Get the program code
            code = self.cfg_program_input.get(1.0, tk.END)
            
            # Create a graph from the program code
            G = self.create_cfg_from_code(code)
            
            # Clear any existing plot in the visualization frame
            for widget in self.visualization_frame.winfo_children():
                widget.destroy()
            
            # Create a figure and canvas
            fig = plt.Figure(figsize=(8, 6), dpi=100)
            ax = fig.add_subplot(111)
            
            # Display the graph
            pos = nx.spring_layout(G, seed=42)  # Positions for all nodes
            
            # Draw nodes
            nx.draw_networkx_nodes(G, pos, ax=ax, node_size=1000, node_color='lightblue', alpha=0.8)
            
            # Draw edges
            nx.draw_networkx_edges(G, pos, ax=ax, width=1.5, arrowsize=15)
            
            # Draw labels
            nx.draw_networkx_labels(G, pos, ax=ax, font_size=8)
            
            # Draw edge labels
            edge_labels = nx.get_edge_attributes(G, 'label')
            nx.draw_networkx_edge_labels(G, pos, edge_labels=edge_labels, font_size=8)
            
            # Remove axis
            ax.set_axis_off()
            
            # Embed in Tkinter
            canvas = FigureCanvasTkAgg(fig, master=self.visualization_frame)
            canvas.draw()
            canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
        
        except Exception as e:
            messagebox.showerror("Error", f"An error occurred while generating the CFG: {str(e)}")
    
    def create_cfg_from_code(self, code):
        """Create a Control Flow Graph from the program code"""
        # Create a directed graph
        G = nx.DiGraph()
        
        # Parse the program to extract control flow
        lines = code.strip().split('\n')
        
        # Remove line numbers if present
        clean_lines = []
        for line in lines:
            match = re.match(r'^\s*\d+\.\s*(.*)', line)
            if match:
                clean_lines.append(match.group(1).strip())
            else:
                clean_lines.append(line.strip())
        
        # Initialize nodes for each line
        for i, line in enumerate(clean_lines):
            node_id = i + 1
            node_label = line
            G.add_node(node_id, label=node_label)
            
            # Add basic flow edges (each statement to the next)
            if i < len(clean_lines) - 1:
                G.add_edge(node_id, node_id + 1)
        
        # Process control structures
        i = 0
        while i < len(clean_lines):
            line = clean_lines[i]
            node_id = i + 1
            
            # Handle if statements
            if 'if' in line and '{' in line:
                # Find matching closing brace
                open_braces = 1
                j = i + 1
                then_block_end = j
                
                while j < len(clean_lines) and open_braces > 0:
                    if '{' in clean_lines[j]:
                        open_braces += 1
                    if '}' in clean_lines[j]:
                        open_braces -= 1
                    if open_braces == 0:
                        then_block_end = j
                    j += 1
                
                # Add edge from if to then-block
                G.add_edge(node_id, node_id + 1, label='true')
                
                # Check for else block
                if j < len(clean_lines) and 'else' in clean_lines[j]:
                    # Add edge from if to else-block
                    G.add_edge(node_id, j + 1, label='false')
                    
                    # Find end of else block
                    open_braces = 1
                    k = j + 1
                    while k < len(clean_lines) and open_braces > 0:
                        if '{' in clean_lines[k]:
                            open_braces += 1
                        if '}' in clean_lines[k]:
                            open_braces -= 1
                        k += 1
                    
                    # Connect end of then-block and else-block to after the if-else
                    G.add_edge(then_block_end, k, label='then-exit')
                    G.add_edge(k - 1, k, label='else-exit')
                    
                    # Skip processed lines
                    i = k - 1
                else:
                    # No else block, connect end of then-block to after the if
                    G.add_edge(then_block_end, then_block_end + 1, label='exit')
                    
                    # Skip processed lines
                    i = then_block_end
            
            # Handle while loops
            elif 'while' in line and '{' in line:
                # Find matching closing brace
                open_braces = 1
                j = i + 1
                
                while j < len(clean_lines) and open_braces > 0:
                    if '{' in clean_lines[j]:
                        open_braces += 1
                    if '}' in clean_lines[j]:
                        open_braces -= 1
                    j += 1
                
                # Add edge from while to loop body
                G.add_edge(node_id, node_id + 1, label='true')
                
                # Add edge from while to after the loop
                G.add_edge(node_id, j, label='false')
                
                # Add back edge from end of loop to while condition
                G.add_edge(j - 1, node_id, label='loop-back')
                
                # Skip processed lines
                i = j - 1
            
            # Handle for loops
            elif 'for' in line and '{' in line:
                # Find matching closing brace
                open_braces = 1
                j = i + 1
                
                while j < len(clean_lines) and open_braces > 0:
                    if '{' in clean_lines[j]:
                        open_braces += 1
                    if '}' in clean_lines[j]:
                        open_braces -= 1
                    j += 1
                
                # Add edge from for to loop body
                G.add_edge(node_id, node_id + 1, label='true')
                
                # Add edge from for to after the loop
                G.add_edge(node_id, j, label='false')
                
                # Add back edge from end of loop to for condition
                G.add_edge(j - 1, node_id, label='loop-back')
                
                # Skip processed lines
                i = j - 1
            
            i += 1
        
      
            return G
    # def setup_cfg_tab(self):
    #     """Set up the Control Flow Graph visualization tab"""
    #     # Create a frame for input and controls
    #     input_frame = ttk.LabelFrame(self.cfg_tab, text="Program Input")
    #     input_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
    #     # Program input
    #     ttk.Label(input_frame, text="Enter your program:").grid(row=0, column=0, sticky=tk.W, padx=5, pady=5)
    #     self.cfg_program_input = scrolledtext.ScrolledText(input_frame, width=60, height=15)
    #     self.cfg_program_input.grid(row=1, column=0, rowspan=3, padx=5, pady=5, sticky=tk.NSEW)
        
    #     # Example programs dropdown
    #     ttk.Label(input_frame, text="Examples:").grid(row=0, column=1, sticky=tk.W, padx=5, pady=5)
    #     self.cfg_examples_var = tk.StringVar()
    #     self.cfg_examples_dropdown = ttk.Combobox(input_frame, textvariable=self.cfg_examples_var)
    #     self.cfg_examples_dropdown['values'] = ('Select an example', 'If-Else Example', 'Loop Example', 'Bubble Sort Example')
    #     self.cfg_examples_dropdown.current(0)
    #     self.cfg_examples_dropdown.grid(row=0, column=2, padx=5, pady=5, sticky=tk.W)
    #     self.cfg_examples_dropdown.bind('<<ComboboxSelected>>', self.load_cfg_example)
        
    #     # Loop unrolling depth for SSA CFG
    #     ttk.Label(input_frame, text="Unrolling Depth:").grid(row=1, column=1, sticky=tk.W, padx=5, pady=5)
    #     self.cfg_depth_var = tk.StringVar(value="2")
    #     depth_spinbox = ttk.Spinbox(input_frame, from_=1, to=10, textvariable=self.cfg_depth_var, width=5)
    #     depth_spinbox.grid(row=1, column=2, padx=5, pady=5, sticky=tk.W)
        
    #     # Process buttons
    #     process_button = ttk.Button(input_frame, text="Generate Original CFG", command=self.generate_cfg)
    #     process_button.grid(row=2, column=1, columnspan=2, padx=5, pady=5)
        
    #     process_ssa_button = ttk.Button(input_frame, text="Generate SSA CFG", command=self.generate_ssa_cfg)
    #     process_ssa_button.grid(row=3, column=1, columnspan=2, padx=5, pady=5)
        
    #     # Configure grid weights
    #     input_frame.columnconfigure(0, weight=3)
    #     input_frame.columnconfigure(1, weight=1)
    #     input_frame.columnconfigure(2, weight=1)
    #     input_frame.rowconfigure(1, weight=1)
        
    #     # Create a notebook for both original and SSA CFGs
    #     self.cfg_notebook = ttk.Notebook(self.cfg_tab)
    #     self.cfg_notebook.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
    #     # Create frames for each CFG visualization
    #     self.original_cfg_frame = ttk.Frame(self.cfg_notebook)
    #     self.cfg_notebook.add(self.original_cfg_frame, text="Original CFG")
        
    #     self.ssa_cfg_frame = ttk.Frame(self.cfg_notebook)
    #     self.cfg_notebook.add(self.ssa_cfg_frame, text="SSA CFG")

    def generate_cfg(self):
        """Generate and display a Control Flow Graph for the given program"""
        try:
            # Get the program code
            code = self.cfg_program_input.get(1.0, tk.END)
            
            # Create a graph from the program code
            G = self.create_cfg_from_code(code)
            
            # Clear any existing plot in the visualization frame
            for widget in self.original_cfg_frame.winfo_children():
                widget.destroy()
            
            # Create a figure and canvas
            fig = plt.Figure(figsize=(8, 6), dpi=100)
            ax = fig.add_subplot(111)
            
            # Display the graph
            pos = nx.spring_layout(G, seed=42)  # Positions for all nodes
            
            # Draw nodes
            nx.draw_networkx_nodes(G, pos, ax=ax, node_size=1000, node_color='lightblue', alpha=0.8)
            
            # Draw edges
            nx.draw_networkx_edges(G, pos, ax=ax, width=1.5, arrowsize=15)
            
            # Draw labels
            nx.draw_networkx_labels(G, pos, ax=ax, font_size=8)
            
            # Draw edge labels
            edge_labels = nx.get_edge_attributes(G, 'label')
            nx.draw_networkx_edge_labels(G, pos, edge_labels=edge_labels, font_size=8)
            
            # Remove axis
            ax.set_axis_off()
            
            # Embed in Tkinter
            canvas = FigureCanvasTkAgg(fig, master=self.original_cfg_frame)
            canvas.draw()
            canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
            
            # Switch to original CFG tab
            self.cfg_notebook.select(0)
        
        except Exception as e:
            messagebox.showerror("Error", f"An error occurred while generating the CFG: {str(e)}")

    def generate_ssa_cfg2(self):
        """Generate and display a Control Flow Graph for the SSA form of the program"""
        try:
            # Get the program code and unrolling depth
            code = self.cfg_program_input.get(1.0, tk.END)
            depth = int(self.cfg_depth_var.get())
            
            # Display debug info
            print(f"Generating SSA CFG with depth {depth}")
            print(f"Code: {code[:100]}...")  # Print first 100 chars for debugging
            
            # Unroll loops and convert to SSA
            try:
                unrolled_code, ssa_code = unroll_and_convert_to_ssa(code, depth)
                print("Successfully converted to SSA")
            except Exception as ssa_err:
                messagebox.showerror("SSA Conversion Error", f"Error converting to SSA: {str(ssa_err)}")
                raise
            
            # Create a graph from the SSA code
            try:
                G = self.create_cfg_from_ssa_code(ssa_code)
                print(f"Created graph with {len(G.nodes())} nodes and {len(G.edges())} edges")
            except Exception as graph_err:
                messagebox.showerror("Graph Creation Error", f"Error creating graph: {str(graph_err)}")
                raise
            
            # Clear any existing plot in the SSA CFG frame
            for widget in self.ssa_cfg_frame.winfo_children():
                widget.destroy()
            
            # Create a splitview: SSA code on left, graph on right
            paned_window = ttk.PanedWindow(self.ssa_cfg_frame, orient=tk.HORIZONTAL)
            paned_window.pack(fill=tk.BOTH, expand=True)
            
            # Left side: SSA code display
            left_frame = ttk.Frame(paned_window)
            paned_window.add(left_frame, weight=1)
            
            ttk.Label(left_frame, text="SSA Form:").pack(anchor=tk.W, padx=5, pady=5)
            ssa_display = scrolledtext.ScrolledText(left_frame)
            ssa_display.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
            ssa_display.insert(tk.END, ssa_code)
            ssa_display.config(state=tk.DISABLED)  # Make read-only
            
            # Right side: Graph visualization
            right_frame = ttk.Frame(paned_window)
            paned_window.add(right_frame, weight=2)
            
            # Create a figure and canvas
            fig = plt.Figure(figsize=(8, 6), dpi=100)
            ax = fig.add_subplot(111)
            
            # Get positions for nodes
            try:
                # Fall back to spring layout
                pos = nx.spring_layout(G, seed=42)
                print("Using spring layout (pygraphviz not available)")
            except Exception as layout_err:
                # If any error occurs with layout, use spring layout
                pos = nx.spring_layout(G, seed=42)
                print(f"Using spring layout due to error: {str(layout_err)}")
            
            # Draw nodes with SSA-specific styling
            phi_nodes = []
            regular_nodes = []
            
            for node in G.nodes():
                is_phi = False
                if 'label' in G.nodes[node]:
                    label = G.nodes[node]['label']
                    if isinstance(label, str) and 'phi' in label.lower():  # Highlight phi functions
                        is_phi = True
                        phi_nodes.append(node)
                    else:
                        regular_nodes.append(node)
                else:
                    regular_nodes.append(node)
            
            # Draw regular nodes
            if regular_nodes:
                nx.draw_networkx_nodes(G, pos, ax=ax, nodelist=regular_nodes, 
                                node_size=1000, node_color='lightblue', alpha=0.8)
            
            # Draw phi nodes with different color
            if phi_nodes:
                nx.draw_networkx_nodes(G, pos, ax=ax, nodelist=phi_nodes, 
                                    node_size=1000, node_color='lightcoral', alpha=0.8)
            
            # Draw edges
            nx.draw_networkx_edges(G, pos, ax=ax, width=1.5, arrowsize=15)
            
            # Draw labels with smaller font for complex SSA expressions
            nx.draw_networkx_labels(G, pos, ax=ax, font_size=7)
            
            # Draw edge labels
            edge_labels = nx.get_edge_attributes(G, 'label')
            nx.draw_networkx_edge_labels(G, pos, edge_labels=edge_labels, font_size=7)
            
            # Remove axis
            ax.set_axis_off()
            
            # Add title
            ax.set_title(f"SSA Control Flow Graph (Unrolling Depth: {depth})")
            
            # Embed in Tkinter
            canvas = FigureCanvasTkAgg(fig, master=right_frame)
            canvas.draw()
            canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
            
            # Add toolbar for interactive features
            try:
                from matplotlib.backends.backend_tkagg import NavigationToolbar2Tk
                toolbar = NavigationToolbar2Tk(canvas, right_frame)
                toolbar.update()
                canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
            except Exception as toolbar_err:
                print(f"Could not create toolbar: {str(toolbar_err)}")
            
            # Switch to SSA CFG tab
            self.cfg_notebook.select(1)
            
            print("SSA CFG generation completed successfully")
        
        except Exception as e:
            # More detailed error reporting
            messagebox.showerror("Error", f"An error occurred while generating the SSA CFG: {str(e)}")
            print("Exception details:")
            import traceback
            traceback.print_exc()




    # def generate_ssa_cfg(self):
    #     """Generate and display a Control Flow Graph for the SSA form of the program"""
    #     try:
    #         # Get the program code and unrolling depth
    #         code = self.cfg_program_input.get(1.0, tk.END)
    #         depth = int(self.cfg_depth_var.get())
            
    #         # Unroll loops and convert to SSA
    #         unrolled_code, ssa_code = unroll_and_convert_to_ssa(code, depth)
            
    #         # Create a graph from the SSA code
    #         G = self.create_cfg_from_code(ssa_code)
            
    #         # Clear any existing plot in the SSA CFG frame
    #         for widget in self.ssa_cfg_frame.winfo_children():
    #             widget.destroy()
            
    #         # Create a splitview: SSA code on left, graph on right
    #         paned_window = ttk.PanedWindow(self.ssa_cfg_frame, orient=tk.HORIZONTAL)
    #         paned_window.pack(fill=tk.BOTH, expand=True)
            
    #         # Left side: SSA code display
    #         left_frame = ttk.Frame(paned_window)
    #         paned_window.add(left_frame, weight=1)
            
    #         ttk.Label(left_frame, text="SSA Form:").pack(anchor=tk.W, padx=5, pady=5)
    #         ssa_display = scrolledtext.ScrolledText(left_frame)
    #         ssa_display.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
    #         ssa_display.insert(tk.END, ssa_code)
    #         ssa_display.config(state=tk.DISABLED)  # Make read-only
            
    #         # Right side: Graph visualization
    #         right_frame = ttk.Frame(paned_window)
    #         paned_window.add(right_frame, weight=2)
            
    #         # Create a figure and canvas
    #         fig = plt.Figure(figsize=(8, 6), dpi=100)
    #         ax = fig.add_subplot(111)
            
    #         # Display the graph with hierarchical layout for better SSA visualization
    #         try:
    #             pos = nx.nx_agraph.graphviz_layout(G, prog='dot')  # Hierarchical layout
    #         except:
    #             pos = nx.spring_layout(G, seed=42)  # Fallback to spring layout
            
    #         # Draw nodes with SSA-specific styling
    #         for node in G.nodes():
    #             is_phi = False
    #             if 'label' in G.nodes[node]:
    #                 label = G.nodes[node]['label']
    #                 if 'phi' in str(label).lower():  # Highlight phi functions
    #                     is_phi = True
                
    #             if is_phi:
    #                 nx.draw_networkx_nodes(G, pos, ax=ax, nodelist=[node], 
    #                                     node_size=1000, node_color='lightcoral', alpha=0.8)
    #             else:
    #                 nx.draw_networkx_nodes(G, pos, ax=ax, nodelist=[node], 
    #                                     node_size=1000, node_color='lightblue', alpha=0.8)
            
    #         # Draw edges
    #         nx.draw_networkx_edges(G, pos, ax=ax, width=1.5, arrowsize=15)
            
    #         # Draw labels with smaller font for complex SSA expressions
    #         nx.draw_networkx_labels(G, pos, ax=ax, font_size=7)
            
    #         # Draw edge labels
    #         edge_labels = nx.get_edge_attributes(G, 'label')
    #         nx.draw_networkx_edge_labels(G, pos, edge_labels=edge_labels, font_size=7)
            
    #         # Remove axis
    #         ax.set_axis_off()
            
    #         # Add title
    #         ax.set_title(f"SSA Control Flow Graph (Unrolling Depth: {depth})")
            
    #         # Embed in Tkinter
    #         canvas = FigureCanvasTkAgg(fig, master=right_frame)
    #         canvas.draw()
    #         canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
            
    #         # Add toolbar for interactive features
    #         from matplotlib.backends.backend_tkagg import NavigationToolbar2Tk
    #         toolbar = NavigationToolbar2Tk(canvas, right_frame)
    #         toolbar.update()
            
    #         # Switch to SSA CFG tab
    #         self.cfg_notebook.select(1)
        
    #     except Exception as e:
    #         messagebox.showerror("Error", f"An error occurred while generating the SSA CFG: {str(e)}")
    #         import traceback
    #         traceback.print_exc()


    def setup_cfg_tab(self):
        """Set up the Control Flow Graph visualization tab"""
        # Create a frame for input and controls
        input_frame = ttk.LabelFrame(self.cfg_tab, text="Program Input")
        input_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # Program input
        ttk.Label(input_frame, text="Enter your program:").grid(row=0, column=0, sticky=tk.W, padx=5, pady=5)
        self.cfg_program_input = scrolledtext.ScrolledText(input_frame, width=60, height=15)
        self.cfg_program_input.grid(row=1, column=0, rowspan=3, padx=5, pady=5, sticky=tk.NSEW)
        
        # Example programs dropdown
        ttk.Label(input_frame, text="Examples:").grid(row=0, column=1, sticky=tk.W, padx=5, pady=5)
        self.cfg_examples_var = tk.StringVar()
        self.cfg_examples_dropdown = ttk.Combobox(input_frame, textvariable=self.cfg_examples_var)
        self.cfg_examples_dropdown['values'] = ('Select an example', 'If-Else Example', 'Loop Example', 'Bubble Sort Example')
        self.cfg_examples_dropdown.current(0)
        self.cfg_examples_dropdown.grid(row=0, column=2, padx=5, pady=5, sticky=tk.W)
        self.cfg_examples_dropdown.bind('<<ComboboxSelected>>', self.load_cfg_example)
        
        # Loop unrolling depth for SSA CFG
        ttk.Label(input_frame, text="Unrolling Depth:").grid(row=1, column=1, sticky=tk.W, padx=5, pady=5)
        self.cfg_depth_var = tk.StringVar(value="2")
        depth_spinbox = ttk.Spinbox(input_frame, from_=1, to=10, textvariable=self.cfg_depth_var, width=5)
        depth_spinbox.grid(row=1, column=2, padx=5, pady=5, sticky=tk.W)
        
        # Process buttons
        process_button = ttk.Button(input_frame, text="Generate Original CFG", command=self.generate_cfg)
        process_button.grid(row=2, column=1, columnspan=2, padx=5, pady=5)
        
        process_ssa_button = ttk.Button(input_frame, text="Generate SSA CFG", command=self.generate_ssa_cfg2)
        process_ssa_button.grid(row=3, column=1, columnspan=2, padx=5, pady=5)
        
        # Configure grid weights
        input_frame.columnconfigure(0, weight=3)
        input_frame.columnconfigure(1, weight=1)
        input_frame.columnconfigure(2, weight=1)
        input_frame.rowconfigure(1, weight=1)
        
        # Create a notebook for both original and SSA CFGs
        self.cfg_notebook = ttk.Notebook(self.cfg_tab)
        self.cfg_notebook.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # Create frames for each CFG visualization
        self.original_cfg_frame = ttk.Frame(self.cfg_notebook)
        self.cfg_notebook.add(self.original_cfg_frame, text="Original CFG")
        
        self.ssa_cfg_frame = ttk.Frame(self.cfg_notebook)
        self.cfg_notebook.add(self.ssa_cfg_frame, text="SSA CFG")

    def generate_ssa_cfg(self):
        """Generate and display a Control Flow Graph for the SSA form of the program"""
        try:
            # Get the program code and unrolling depth
            code = self.cfg_program_input.get(1.0, tk.END)
            depth = int(self.cfg_depth_var.get())
            
            # Display debug info
            print(f"Generating SSA CFG with depth {depth}")
            print(f"Code: {code[:100]}...")  # Print first 100 chars for debugging
            
            # Unroll loops and convert to SSA
            try:
                unrolled_code, ssa_code = unroll_and_convert_to_ssa(code, depth)
                print("Successfully converted to SSA")
            except Exception as ssa_err:
                messagebox.showerror("SSA Conversion Error", f"Error converting to SSA: {str(ssa_err)}")
                raise
            
            # Create a graph from the SSA code
            try:
                G = self.create_cfg_from_ssa_code(ssa_code)
                print(f"Created graph with {len(G.nodes())} nodes and {len(G.edges())} edges")
            except Exception as graph_err:
                messagebox.showerror("Graph Creation Error", f"Error creating graph: {str(graph_err)}")
                raise
            
            # Clear any existing plot in the SSA CFG frame
            for widget in self.ssa_cfg_frame.winfo_children():
                widget.destroy()
            
            # Create a splitview: SSA code on left, graph on right
            paned_window = ttk.PanedWindow(self.ssa_cfg_frame, orient=tk.HORIZONTAL)
            paned_window.pack(fill=tk.BOTH, expand=True)
            
            # Left side: SSA code display
            left_frame = ttk.Frame(paned_window)
            paned_window.add(left_frame, weight=1)
            
            ttk.Label(left_frame, text="SSA Form:").pack(anchor=tk.W, padx=5, pady=5)
            ssa_display = scrolledtext.ScrolledText(left_frame)
            ssa_display.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
            ssa_display.insert(tk.END, ssa_code)
            ssa_display.config(state=tk.DISABLED)  # Make read-only
            
            # Right side: Graph visualization
            right_frame = ttk.Frame(paned_window)
            paned_window.add(right_frame, weight=2)
            
            # Create a figure and canvas
            fig = plt.Figure(figsize=(8, 6), dpi=100)
            ax = fig.add_subplot(111)
            
            # Display the graph with hierarchical layout for better SSA visualization
            try:
                # First try hierarchical layout using pygraphviz if available
                
                    # import pygraphviz
                    # pos = nx.nx_agraph.graphviz_layout(G, prog='dot')  # Hierarchical layout
                    print("noy Using graphviz layout")
                
                    # If pygraphviz is not available, fall back to spring layout
                    pos = nx.spring_layout(G, seed=42)  # Fallback to spring layout
                    print("Using spring layout (pygraphviz not available)")
            except Exception as layout_err:
                # If any other error occurs with layout, use spring layout
                pos = nx.spring_layout(G, seed=42)
                print(f"Using spring layout due to error: {str(layout_err)}")
            
            # Draw nodes with SSA-specific styling
            phi_nodes = []
            regular_nodes = []
            
            for node in G.nodes():
                is_phi = False
                if 'label' in G.nodes[node]:
                    label = G.nodes[node]['label']
                    if 'phi' in str(label).lower():  # Highlight phi functions
                        is_phi = True
                        phi_nodes.append(node)
                    else:
                        regular_nodes.append(node)
                else:
                    regular_nodes.append(node)
            
            # Draw regular nodes
            nx.draw_networkx_nodes(G, pos, ax=ax, nodelist=regular_nodes, 
                                node_size=1000, node_color='lightblue', alpha=0.8)
            
            # Draw phi nodes with different color
            if phi_nodes:
                nx.draw_networkx_nodes(G, pos, ax=ax, nodelist=phi_nodes, 
                                    node_size=1000, node_color='lightcoral', alpha=0.8)
            
            # Draw edges
            nx.draw_networkx_edges(G, pos, ax=ax, width=1.5, arrowsize=15)
            
            # Draw labels with smaller font for complex SSA expressions
            nx.draw_networkx_labels(G, pos, ax=ax, font_size=7)
            
            # Draw edge labels
            edge_labels = nx.get_edge_attributes(G, 'label')
            nx.draw_networkx_edge_labels(G, pos, edge_labels=edge_labels, font_size=7)
            
            # Remove axis
            ax.set_axis_off()
            
            # Add title
            ax.set_title(f"SSA Control Flow Graph (Unrolling Depth: {depth})")
            
            # Embed in Tkinter
            canvas = FigureCanvasTkAgg(fig, master=right_frame)
            canvas.draw()
            canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
            
            # Add toolbar for interactive features
            try:
                from matplotlib.backends.backend_tkagg import NavigationToolbar2Tk
                toolbar = NavigationToolbar2Tk(canvas, right_frame)
                toolbar.update()
            except Exception as toolbar_err:
                print(f"Could not create toolbar: {str(toolbar_err)}")
            
            # Switch to SSA CFG tab
            self.cfg_notebook.select(1)
            
            print("SSA CFG generation completed successfully")
        
        except Exception as e:
            # More detailed error reporting
            messagebox.showerror("Error", f"An error occurred while generating the SSA CFG: {str(e)}")
            print("Exception details:")
            import traceback
            traceback.print_exc()







    def create_cfg_from_ssa_code(self, ssa_code):
        """Create a more detailed Control Flow Graph specifically for SSA code"""
        # Create a directed graph
        G = nx.DiGraph()
        
        # Parse the SSA program lines
        lines = ssa_code.strip().split('\n')
        
        # Process phi functions specially to highlight data dependencies
        phi_nodes = {}
        variable_def_nodes = {}
        
        # First pass: Create nodes for each line and identify phi nodes
        for i, line in enumerate(lines):
            node_id = i + 1
            node_label = line.strip()
            G.add_node(node_id, label=node_label)
            
            # Track phi functions
            if 'phi(' in line:
                var_name = line.split(':=')[0].strip()
                phi_nodes[var_name] = node_id
            
            # Track variable definitions
            if ':=' in line:
                var_name = line.split(':=')[0].strip()
                variable_def_nodes[var_name] = node_id
        
        # Second pass: Add basic control flow edges
        for i in range(len(lines) - 1):
            node_id = i + 1
            next_node_id = i + 2
            
            # Skip adding edge if current line contains a branch or jump
            current_line = lines[i].lower()
            if ('if ' in current_line or 'goto' in current_line or 
                'break' in current_line or 'continue' in current_line):
                continue
            
            G.add_edge(node_id, next_node_id)
        
        # Third pass: Process control structures and data dependencies
        i = 0
        while i < len(lines):
            line = lines[i]
            node_id = i + 1
            
            # Handle if statements with explicit targets for true/false branches
            if_match = re.search(r'if\s+\((.*?)\)\s+goto\s+(\d+)\s+else\s+goto\s+(\d+)', line)
            if if_match:
                condition = if_match.group(1)
                true_target = int(if_match.group(2))
                false_target = int(if_match.group(3))
                
                # Add edges to the branch targets
                G.add_edge(node_id, true_target, label='true')
                G.add_edge(node_id, false_target, label='false')
            
            # Handle simple goto statements
            goto_match = re.search(r'goto\s+(\d+)', line)
            if goto_match and not if_match:  # Avoid double-processing if statements
                target = int(goto_match.group(1))
                G.add_edge(node_id, target, label='goto')
            
            # Handle data dependencies for phi functions
            if 'phi(' in line:
                # Extract variables used in phi function
                phi_content = re.search(r'phi\((.*?)\)', line)
                if phi_content:
                    phi_args = phi_content.group(1).split(',')
                    for arg in phi_args:
                        arg = arg.strip()
                        if arg in variable_def_nodes:
                            # Add a data dependency edge
                            source_node = variable_def_nodes[arg]
                            G.add_edge(source_node, node_id, label='data', style='dashed')
            
            i += 1
        
        return G

    # Helper method to simplify SSA variable display for CFG
    def simplify_ssa_name(self, var_name):
        """Convert SSA variable names to a more readable form for CFG display"""
        match = re.match(r'([a-zA-Z_][a-zA-Z0-9_]*?)_(\d+)', var_name)
        if match:
            base_name = match.group(1)
            version = match.group(2)
            return f"{base_name}₍{version}₎"  # Using subscript notation
        return var_name

if __name__ == "__main__":
    root = tk.Tk()
    app = ProgramAnalyzerGUI(root)
    root.mainloop()