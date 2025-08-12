# Parsing Tool
A tool that parses input algorithm and converts to Static Single Assignment (SSA) form. This tool helps analyze the correctness and equivalence of programs.


## Key Feature
The tool does the following 
1. Parse simple programs input
2. Convert them into SSA (Static Single Assignment) form
3. Generate the corresponding SMT constraints
4. Use an SMT solver (e.g., Z3) to:
o Verify correctness (assert statements hold)
o Check whether two programs are semantically equivalent
5. Display all intermediate steps (SSA form, SMT code, result) in the GUI
   

## Tech Stack
Python


## Setup Instructions
Open command prompt

CD into the directory you wish to store the applications folder. Command is:  cd path\to\folder (replace path\to\folder with your own path)

then run this command : git clone https://github.com/eshal-omar/Parsing-Tool.git

Open vscode

Select terminal button at the top left toolbar and select new terminal

Run this command in the terminal: pip install matplotlib networkx

Then run: python gui.py

This will open the application window and is ready to be used.



# Video Demonstration

## Verification Mode

https://github.com/user-attachments/assets/f4aa5a5a-d08e-41af-83ae-984599d10881


## Equivalence Mode 
https://github.com/user-attachments/assets/c301e721-a2ae-46d5-8f32-549a0cf82913


