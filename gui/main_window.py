import tkinter as tk
from tkinter import scrolledtext, messagebox, ttk, Toplevel
from PIL import Image, ImageTk
import time
import os
from core.parser import Parser
from core.ssa import SSAConverter
from core.unroller import LoopUnroller
from core.smt_generator import SMTGenerator
from core.z3_interface import verify_program, check_equivalence
from core.optimizer import optimize_ssa, generate_ssa_cfg, get_live_vars_from_assertions, get_final_versions

def launch_app():
    root = tk.Tk()
    root.title("MiniLang Tool")
    root.geometry("1400x900")
    root.resizable(True, True)

    notebook = ttk.Notebook(root)
    notebook.pack(fill='both', expand=True)

    verification_frame = ttk.Frame(notebook)
    notebook.add(verification_frame, text="Verification")

    equivalence_frame = ttk.Frame(notebook)
    notebook.add(equivalence_frame, text="Equivalence")

    # --- Verification Tab ---
    v_input_frame = ttk.LabelFrame(verification_frame, text="Input")
    v_input_frame.grid(row=0, column=0, padx=10, pady=10, sticky="nsew")

    input_label_v = ttk.Label(v_input_frame, text="MiniLang Code:")
    input_label_v.grid(row=0, column=0, padx=5, pady=5, sticky="w")

    input_text_v = scrolledtext.ScrolledText(v_input_frame, height=10, width=80)
    input_text_v.grid(row=1, column=0, columnspan=2, padx=5, pady=5, sticky="we")

    depth_label_v = ttk.Label(v_input_frame, text="Unrolling Depth:")
    depth_label_v.grid(row=2, column=0, padx=5, pady=5, sticky="w")

    depth_entry_v = ttk.Entry(v_input_frame, width=5)
    depth_entry_v.grid(row=2, column=1, padx=5, pady=5, sticky="w")
    depth_entry_v.insert(0, "2")

    parse_button_v = ttk.Button(v_input_frame, text="Parse and Verify", command=lambda: on_parse_verification())
    parse_button_v.grid(row=3, column=0, columnspan=4, padx=5, pady=10, sticky="we")

    v_output_frame = ttk.LabelFrame(verification_frame, text="Outputs")
    v_output_frame.grid(row=1, column=0, padx=10, pady=10, sticky="nsew")

    ast_label_v = ttk.Label(v_output_frame, text="AST:")
    ast_label_v.grid(row=0, column=0, padx=5, pady=5, sticky="w")
    ast_text_v = scrolledtext.ScrolledText(v_output_frame, height=8, width=40, state='disabled')
    ast_text_v.grid(row=1, column=0, padx=5, pady=5, sticky="we")

    ssa_label_v = ttk.Label(v_output_frame, text="SSA:")
    ssa_label_v.grid(row=0, column=1, padx=5, pady=5, sticky="w")
    ssa_text_v = scrolledtext.ScrolledText(v_output_frame, height=8, width=40, state='disabled')
    ssa_text_v.grid(row=1, column=1, padx=5, pady=5, sticky="we")

    unrolled_label_v = ttk.Label(v_output_frame, text="Unrolled Code:")
    unrolled_label_v.grid(row=2, column=0, padx=5, pady=5, sticky="w")
    unrolled_text_v = scrolledtext.ScrolledText(v_output_frame, height=8, width=40, state='disabled')
    unrolled_text_v.grid(row=3, column=0, padx=5, pady=5, sticky="we")

    unrolled_ssa_label_v = ttk.Label(v_output_frame, text="Unrolled SSA:")
    unrolled_ssa_label_v.grid(row=2, column=1, padx=5, pady=5, sticky="w")
    unrolled_ssa_text_v = scrolledtext.ScrolledText(v_output_frame, height=8, width=40, state='disabled')
    unrolled_ssa_text_v.grid(row=3, column=1, padx=5, pady=5, sticky="we")

    smt_label_v = ttk.Label(v_output_frame, text="SMT Code:")
    smt_label_v.grid(row=4, column=0, padx=5, pady=5, sticky="w")
    smt_text_v = scrolledtext.ScrolledText(v_output_frame, height=8, width=40, state='disabled')
    smt_text_v.grid(row=5, column=0, padx=5, pady=5, sticky="we")

    z3_results_label_v = ttk.Label(v_output_frame, text="Z3 Results:")
    z3_results_label_v.grid(row=4, column=1, padx=5, pady=5, sticky="w")
    z3_results_text_v = scrolledtext.ScrolledText(v_output_frame, height=8, width=40, state='disabled')
    z3_results_text_v.grid(row=5, column=1, padx=5, pady=5, sticky="we")

    optimize_button_v = ttk.Button(v_output_frame, text="Optimize and Visualize SSA", command=lambda: optimize_verification())
    optimize_button_v.grid(row=6, column=0, columnspan=2, padx=5, pady=10, sticky="we")

    # --- Equivalence Tab ---
    e_input_frame = ttk.LabelFrame(equivalence_frame, text="Input")
    e_input_frame.grid(row=0, column=0, padx=10, pady=10, sticky="nsew")

    program1_label = ttk.Label(e_input_frame, text="Program 1 Code:")
    program1_label.grid(row=0, column=0, padx=5, pady=5, sticky="w")
    program1_text = scrolledtext.ScrolledText(e_input_frame, height=10, width=40)
    program1_text.grid(row=1, column=0, padx=5, pady=5, sticky="we")

    program2_label = ttk.Label(e_input_frame, text="Program 2 Code:")
    program2_label.grid(row=0, column=1, padx=5, pady=5, sticky="w")
    program2_text = scrolledtext.ScrolledText(e_input_frame, height=10, width=40)
    program2_text.grid(row=1, column=1, padx=5, pady=5, sticky="we")

    output_vars_label = ttk.Label(e_input_frame, text="Output Variables (Prog1, Prog2):")
    output_vars_label.grid(row=2, column=0, padx=5, pady=5, sticky="w")
    output_vars_entry = ttk.Entry(e_input_frame, width=30)
    output_vars_entry.grid(row=2, column=1, padx=5, pady=5, sticky="w")

    depth_label_e = ttk.Label(e_input_frame, text="Unrolling Depth:")
    depth_label_e.grid(row=3, column=0, padx=5, pady=5, sticky="w")
    depth_entry_e = ttk.Entry(e_input_frame, width=5)
    depth_entry_e.grid(row=3, column=1, padx=5, pady=5, sticky="w")
    depth_entry_e.insert(0, "2")

    parse_button_e = ttk.Button(e_input_frame, text="Parse and Check Equivalence", command=lambda: on_parse_equivalence())
    parse_button_e.grid(row=4, column=0, columnspan=2, padx=5, pady=10, sticky="we")

    e_output_frame = ttk.LabelFrame(equivalence_frame, text="Outputs")
    e_output_frame.grid(row=1, column=0, padx=10, pady=10, sticky="nsew")

    ssa1_label = ttk.Label(e_output_frame, text="Program 1 SSA:")
    ssa1_label.grid(row=0, column=0, padx=5, pady=5, sticky="w")
    ssa1_text = scrolledtext.ScrolledText(e_output_frame, height=8, width=40, state='disabled')
    ssa1_text.grid(row=1, column=0, padx=5, pady=5, sticky="we")

    ssa2_label = ttk.Label(e_output_frame, text="Program 2 SSA:")
    ssa2_label.grid(row=0, column=1, padx=5, pady=5, sticky="w")
    ssa2_text = scrolledtext.ScrolledText(e_output_frame, height=8, width=40, state='disabled')
    ssa2_text.grid(row=1, column=1, padx=5, pady=5, sticky="we")

    smt1_label = ttk.Label(e_output_frame, text="Program 1 SMT:")
    smt1_label.grid(row=2, column=0, padx=5, pady=5, sticky="w")
    smt1_text = scrolledtext.ScrolledText(e_output_frame, height=8, width=40, state='disabled')
    smt1_text.grid(row=3, column=0, padx=5, pady=5, sticky="we")

    smt2_label = ttk.Label(e_output_frame, text="Program 2 SMT:")
    smt2_label.grid(row=2, column=1, padx=5, pady=5, sticky="w")
    smt2_text = scrolledtext.ScrolledText(e_output_frame, height=8, width=40, state='disabled')
    smt2_text.grid(row=3, column=1, padx=5, pady=5, sticky="we")

    z3_results_label = ttk.Label(e_output_frame, text="Z3 Results:")
    z3_results_label.grid(row=4, column=0, columnspan=2, padx=5, pady=5, sticky="w")
    z3_results_text = scrolledtext.ScrolledText(e_output_frame, height=8, width=80, state='disabled')
    z3_results_text.grid(row=5, column=0, columnspan=2, padx=5, pady=5, sticky="we")

    optimize_button_e = ttk.Button(e_output_frame, text="Optimize and Visualize SSA", command=lambda: optimize_equivalence())
    optimize_button_e.grid(row=6, column=0, columnspan=2, padx=5, pady=10, sticky="we")

    # Configure grid weights for responsiveness
    verification_frame.grid_rowconfigure(1, weight=1)
    verification_frame.grid_columnconfigure(0, weight=1)
    v_input_frame.grid_columnconfigure(0, weight=1)
    v_output_frame.grid_columnconfigure((0, 1), weight=1)

    equivalence_frame.grid_rowconfigure(1, weight=1)
    equivalence_frame.grid_columnconfigure(0, weight=1)
    e_input_frame.grid_columnconfigure((0, 1), weight=1)
    e_output_frame.grid_columnconfigure((0, 1), weight=1)

    # --- Helper Functions ---
    def process_code(code, depth):
        parser = Parser(code)
        ast = parser.parse()
        ssa_converter = SSAConverter()
        ssa_result = ssa_converter.convert(ast)
        unroller = LoopUnroller(depth)
        unrolled_code = unroller.get_unrolled_code(ast)
        unrolled_ssa = unroller.get_ssa(ast)
        return parser, ast, ssa_result, unrolled_code, unrolled_ssa

    def show_cfg(ssa_instructions, title="SSA CFG", save_path=None):
        top = Toplevel()
        top.title(title)
        canvas = tk.Canvas(top, width=800, height=600)
        canvas.pack(fill="both", expand=True)
        temp_path = "ssa_cfg_temp" if save_path is None else save_path
        generate_ssa_cfg(ssa_instructions, temp_path)
        img = Image.open(f"{temp_path}.png")
        img = img.resize((800, 600), Image.Resampling.LANCZOS)
        img_tk = ImageTk.PhotoImage(img)
        canvas.create_image(0, 0, anchor=tk.NW, image=img_tk)
        canvas.image = img_tk
        if save_path and os.path.exists(f"{temp_path}.png"):
            os.rename(f"{temp_path}.png", f"{save_path}.png")

    def on_parse_verification():
        code = input_text_v.get("1.0", tk.END).strip()
        try:
            if not code:
                messagebox.showwarning("Warning", "Please enter MiniLang code.")
                return

            depth = int(depth_entry_v.get())
            if depth < 0:
                raise ValueError("Unrolling depth must be non-negative.")

            parser, ast, ssa_result, unrolled_code, unrolled_ssa = process_code(code, depth)
            smt_generator = SMTGenerator(unrolled_ssa)
            program_smt_code, assertion_conditions = smt_generator.generate_smt()

            ast_text_v.config(state='normal')
            ast_text_v.delete("1.0", tk.END)
            ast_text_v.insert(tk.END, str(ast))
            ast_text_v.config(state='disabled')

            ssa_text_v.config(state='normal')
            ssa_text_v.delete("1.0", tk.END)
            ssa_text_v.insert(tk.END, "\n".join(str(instr) for instr in ssa_result))
            ssa_text_v.config(state='disabled')

            unrolled_text_v.config(state='normal')
            unrolled_text_v.delete("1.0", tk.END)
            unrolled_text_v.insert(tk.END, unrolled_code)
            unrolled_text_v.config(state='disabled')

            unrolled_ssa_text_v.config(state='normal')
            unrolled_ssa_text_v.delete("1.0", tk.END)
            unrolled_ssa_text_v.insert(tk.END, "\n".join(str(instr) for instr in unrolled_ssa))
            unrolled_ssa_text_v.config(state='disabled')

            smt_text_v.config(state='normal')
            smt_text_v.delete("1.0", tk.END)
            smt_text_v.insert(tk.END, program_smt_code)
            smt_text_v.config(state='disabled')

            holds, examples = verify_program(program_smt_code, assertion_conditions)
            z3_results = "Assertions hold.\n" if holds else "Assertions do not hold.\n"
            z3_results += "\n".join(examples)
            z3_results_text_v.config(state='normal')
            z3_results_text_v.delete("1.0", tk.END)
            z3_results_text_v.insert(tk.END, z3_results)
            z3_results_text_v.config(state='disabled')

            ast_image_path = "ast_output.png"
            parser.save_ast_graph(ast, "ast_output")
            attempts = 0
            while not os.path.exists(ast_image_path) and attempts < 10:
                time.sleep(0.1)
                attempts += 1
            if os.path.exists(ast_image_path):
                img = Image.open(ast_image_path)
                img = img.resize((300, 300), Image.Resampling.LANCZOS)
                img_tk = ImageTk.PhotoImage(img)
            else:
                raise FileNotFoundError(f"File {ast_image_path} not found after rendering.")

        except Exception as e:
            messagebox.showerror("Error", f"Processing failed:\n{str(e)}")

    def optimize_verification():
        code = input_text_v.get("1.0", tk.END).strip()
        try:
            if not code:
                messagebox.showwarning("Warning", "Please enter MiniLang code.")
                return

            depth = int(depth_entry_v.get())
            if depth < 0:
                raise ValueError("Unrolling depth must be non-negative.")

            _, _, _, _, unrolled_ssa = process_code(code, depth)
            live_vars = get_live_vars_from_assertions(unrolled_ssa)
            optimized_ssa = optimize_ssa(unrolled_ssa, live_vars)

            opt_window = Toplevel()
            opt_window.title("Optimized SSA - Verification")
            opt_text = scrolledtext.ScrolledText(opt_window, height=20, width=80, state='normal')
            opt_text.insert(tk.END, "\n".join(str(instr) for instr in optimized_ssa))
            opt_text.config(state='disabled')
            opt_text.pack(padx=10, pady=10)
            cfg_button = tk.Button(opt_window, text="Visualize Optimized SSA CFG", command=lambda: show_cfg(optimized_ssa, "Verification Optimized SSA CFG", "optimized_ssa_cfg_verification"))
            cfg_button.pack(padx=10, pady=10)

        except Exception as e:
            messagebox.showerror("Error", f"Optimization failed:\n{str(e)}")

    def on_parse_equivalence():
        code1 = program1_text.get("1.0", tk.END).strip()
        code2 = program2_text.get("1.0", tk.END).strip()
        output_vars = [var.strip() for var in output_vars_entry.get().split(',') if var.strip()]
        try:
            if not code1 or not code2:
                messagebox.showwarning("Warning", "Please enter both MiniLang programs.")
                return
            if len(output_vars) != 2:
                messagebox.showwarning("Warning", "Please specify exactly two output variables (one for each program).")
                return

            depth = int(depth_entry_e.get())
            if depth < 0:
                raise ValueError("Unrolling depth must be non-negative.")

            parser1, ast1, ssa_result1, unrolled_code1, unrolled_ssa1 = process_code(code1, depth)
            smt_generator1 = SMTGenerator(unrolled_ssa1)
            program_smt_code1, _ = smt_generator1.generate_smt(suffix='_p1')

            parser2, ast2, ssa_result2, unrolled_code2, unrolled_ssa2 = process_code(code2, depth)
            smt_generator2 = SMTGenerator(unrolled_ssa2)
            program_smt_code2, _ = smt_generator2.generate_smt(suffix='_p2')

            ssa1_text.config(state='normal')
            ssa1_text.delete("1.0", tk.END)
            ssa1_text.insert(tk.END, "\n".join(str(instr) for instr in ssa_result1))
            ssa1_text.config(state='disabled')

            ssa2_text.config(state='normal')
            ssa2_text.delete("1.0", tk.END)
            ssa2_text.insert(tk.END, "\n".join(str(instr) for instr in ssa_result2))
            ssa2_text.config(state='disabled')

            smt1_text.config(state='normal')
            smt1_text.delete("1.0", tk.END)
            smt1_text.insert(tk.END, program_smt_code1)
            smt1_text.config(state='disabled')

            smt2_text.config(state='normal')
            smt2_text.delete("1.0", tk.END)
            smt2_text.insert(tk.END, program_smt_code2)
            smt2_text.config(state='disabled')

            equiv, examples = check_equivalence(program_smt_code1, program_smt_code2, output_vars)
            z3_results = "Programs are equivalent.\n" if equiv else "Programs are not equivalent.\n"
            z3_results += "\n".join(examples)
            z3_results_text.config(state='normal')
            z3_results_text.delete("1.0", tk.END)
            z3_results_text.insert(tk.END, z3_results)
            z3_results_text.config(state='disabled')

            # Save AST graphs (labeled as CFGs) for original code of both programs
            parser1.save_ast_graph(ast1, "cfg_original_prog1")
            parser2.save_ast_graph(ast2, "cfg_original_prog2")
            # Save SSA CFGs for both programs
            generate_ssa_cfg(ssa_result1, "ssa_cfg_prog1")
            generate_ssa_cfg(ssa_result2, "ssa_cfg_prog2")

        except Exception as e:
            messagebox.showerror("Error", f"Processing failed:\n{str(e)}")

    def optimize_equivalence():
        code1 = program1_text.get("1.0", tk.END).strip()
        code2 = program2_text.get("1.0", tk.END).strip()
        output_vars = [var.strip() for var in output_vars_entry.get().split(',') if var.strip()]
        try:
            if not code1 or not code2:
                messagebox.showwarning("Warning", "Please enter both MiniLang programs.")
                return
            if len(output_vars) != 2:
                messagebox.showwarning("Warning", "Please specify exactly two output variables (one for each program).")
                return

            depth = int(depth_entry_e.get())
            if depth < 0:
                raise ValueError("Unrolling depth must be non-negative.")

            _, _, _, _, unrolled_ssa1 = process_code(code1, depth)
            live_vars1 = get_final_versions(unrolled_ssa1, [output_vars[0]])
            optimized_ssa1 = optimize_ssa(unrolled_ssa1, live_vars1)

            _, _, _, _, unrolled_ssa2 = process_code(code2, depth)
            live_vars2 = get_final_versions(unrolled_ssa2, [output_vars[1]])
            optimized_ssa2 = optimize_ssa(unrolled_ssa2, live_vars2)

            opt_window = Toplevel()
            opt_window.title("Optimized SSA - Equivalence")
            opt_text1 = scrolledtext.ScrolledText(opt_window, height=10, width=80, state='normal')
            opt_text1.insert(tk.END, "Program 1 Optimized SSA:\n" + "\n".join(str(instr) for instr in optimized_ssa1))
            opt_text1.config(state='disabled')
            opt_text1.pack(padx=10, pady=5)
            cfg_button1 = tk.Button(opt_window, text="Visualize Program 1 Optimized SSA CFG", 
                                  command=lambda: show_cfg(optimized_ssa1, "Program 1 Optimized SSA CFG", "optimized_ssa_cfg_prog1"))
            cfg_button1.pack(padx=10, pady=5)
            opt_text2 = scrolledtext.ScrolledText(opt_window, height=10, width=80, state='normal')
            opt_text2.insert(tk.END, "Program 2 Optimized SSA:\n" + "\n".join(str(instr) for instr in optimized_ssa2))
            opt_text2.config(state='disabled')
            opt_text2.pack(padx=10, pady=5)
            cfg_button2 = tk.Button(opt_window, text="Visualize Program 2 Optimized SSA CFG", 
                                  command=lambda: show_cfg(optimized_ssa2, "Program 2 Optimized SSA CFG", "optimized_ssa_cfg_prog2"))
            cfg_button2.pack(padx=10, pady=5)

        except Exception as e:
            messagebox.showerror("Error", f"Optimization failed:\n{str(e)}")

    root.mainloop()