# MiniLang Verification Tool

A formal verification tool for MiniLang programs, implementing parsing, SSA transformation, loop unrolling, SMT-based reasoning with Z3, and equivalence checking.

---

## 📚 Overview

This tool verifies the correctness and equivalence of programs written in MiniLang, a minimalistic language for formal verification. It processes code through parsing, SSA conversion, loop unrolling, SMT formulation, and Z3 solving, with an interactive GUI for visualization and results.

Key features include:

- Parsing MiniLang syntax into AST.
- SSA translation with phi functions and array handling.
- User-specified loop unrolling.
- SMT-LIB generation for Z3-based verification.
- GUI for input, step-by-step views (AST, SSA, unrolled code, SMT), CFG visualization, and results (models/counterexamples).
- Equivalence checking between two programs.

---

## ⚙️ Implementation Details

**Language:** Python 3.x  

**Key Libraries:**

- Tkinter (GUI)
- Graphviz (CFG visualization)
- Z3 (SMT solver)

**Core Components:**

- `core/parser.py` – Parses MiniLang code into AST.
- `core/ssa.py` – Converts to SSA form.
- `core/unroller.py` – Handles loop unrolling.
- `core/smt_generator.py` – Generates SMT-LIB code.
- GUI – Supports Verification and Equivalence modes with interactive panels.

> MiniLang supports assignments (scalar/array), if-else, while/for loops, and assertions. Assumptions include well-formed input and single-dimensional arrays.

---

## 📊 Features and Examples

### Verification Mode

- Input MiniLang code, set unrolling depth, and verify assertions.
- Outputs: AST, SSA, unrolled code, SMT, Z3 results (sat/unsat with models/counterexamples).  
- **Example:** Simple loop verification shows assertions hold with sample models.

### Equivalence Mode

- Compare two programs by specifying output variables.
- Checks if final states are equivalent; provides counterexamples if not.

### CFG Visualization

- Generates original and optimized SSA control flow graphs using Graphviz.  
- Test cases (e.g., from `examples/`) demonstrate successful verification, assertion failures, and equivalence checks.

---

## 📂 Project Structure

```bash
├── core/ # Core logic modules
│ ├── parser.py # MiniLang parser
│ ├── ssa.py # SSA converter
│ ├── unroller.py # Loop unroller
│ ├── smt_generator.py # SMT-LIB generator
│ └── optimizer.py # Basic optimizations
├── gui/ # GUI components
│ └── main.py # Main GUI application
├── examples/ # Test files (e.g., Verification1.txt, Equivalence1_pair.txt)
├── README.md
└── requirements.txt # Dependencies

```

## 🚀 How to Run

Clone the repository:

```bash
git clone https://github.com/your-username/minilang-verification-tool.git
cd minilang-verification-tool
```

Install dependencies (including Z3 and Graphviz):

```bash
pip install -r requirements.txt
```
Ensure Graphviz is installed system-wide (e.g., brew install graphviz on macOS, apt install graphviz on Ubuntu).

Run the GUI:

```bash
python gui/main.py
```
---

## Usage

- Verification Tab: Enter code, set unrolling depth, click "Verify".

- Equivalence Tab: Enter two programs and output variables, click "Check Equivalence".

- Visualize CFGs: Use "Optimize and Visualize SSA" buttons.

---

## 👨‍💻 Contributors
- **Abdullah Daoud (22I-2626)**  
- **Usman Ali (22I-2725)**  
- **Faizan Rasheed (22I-2734)**

---

## ⚖️ License
This project is for **academic and personal skill development purposes only**.  
Reuse is allowed for **learning and research** with proper credit.

---


## ⚠️ Limitations

- Supports only single-dimensional arrays and fixed-depth loop unrolling.

- Basic optimizations; no advanced loop invariants or multi-dimensional arrays.

- GUI lacks interactivity in visualizations and export features.

- For improvements, see the project report (Tool Report.pdf).

---
