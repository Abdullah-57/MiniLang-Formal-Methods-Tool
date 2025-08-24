import re
from z3 import *

def verify_program(program_smt_code, assertion_conditions):
    """Verify assertions in the program using Z3, always returning (holds, examples)."""
    try:
        solver = Solver()
        solver.from_string(program_smt_code)

        decls = {}
        for match in re.finditer(r'\(declare-const (\w+) (\w+)\)', program_smt_code):
            var_name, var_type = match.group(1), match.group(2)
            if var_type == 'Int':
                decls[var_name] = Int(var_name)
            elif var_type == 'Bool':
                decls[var_name] = Bool(var_name)

        assigned_vars = set()
        for line in program_smt_code.split('\n'):
            match = re.match(r'\(assert \(= (\w+) .+\)\)', line.strip())
            if match:
                assigned_vars.add(match.group(1))
        all_vars = set(decls.keys())
        input_vars = all_vars - assigned_vars

        if not assertion_conditions:
            if solver.check() == sat:
                return True, ["unsat", str(solver.model())]
            return False, ["unsat", "No assertions provided and program is unsatisfiable"]

        assertion_exprs = []
        for cond in assertion_conditions:
            try:
                expr = parse_smt2_string(f"(assert {cond})", decls=decls)[0]
                assertion_exprs.append(expr)
            except Exception as e:
                return False, [f"Error parsing assertion '{cond}': {str(e)}"]

        solver.push()
        solver.add(Not(And(*assertion_exprs)))
        result = solver.check()

        if result == unsat:
            solver.pop()
            solver.check()
            model = solver.model()
            return True, ["unsat", f"Assertions hold. Example model: {str(model)}"]
        else:
            counterexamples = []
            max_counterexamples = 2
            while len(counterexamples) < max_counterexamples and result == sat:
                model = solver.model()
                counterexamples.append(str(model))
                if input_vars:
                    exclude = [decls[var] != model[decls[var]] for var in input_vars if var in decls and model[decls[var]] is not None]
                    if exclude:
                        solver.add(Or(exclude))
                result = solver.check()
            solver.pop()
            return False, ["sat"] + counterexamples

    except Exception as e:
        return False, [f"Verification failed: {str(e)}"]

def find_final_version(var, assigned_vars):
    """Find the final SSA version of a variable."""
    matches = [v for v in assigned_vars if v.startswith(var + '_') or v == var]
    return max(matches, key=lambda x: int(x.split('_')[1] if '_' in x else 0)) if matches else var

def check_equivalence(smt_code1, smt_code2, output_vars):
    """Check if two programs are equivalent by comparing output_vars[0] from prog1 with output_vars[1] from prog2."""
    if len(output_vars) != 2:
        return False, ["Error: Exactly two output variables must be provided (one per program)."]

    solver = Solver()

    decls1 = re.findall(r'\(declare-const (\w+) (\w+)\)', smt_code1)
    decls2 = re.findall(r'\(declare-const (\w+) (\w+)\)', smt_code2)
    constraints1 = re.findall(r'\(assert .+\)', smt_code1)
    constraints2 = re.findall(r'\(assert .+\)', smt_code2)

    input_vars = {var for var, typ in decls1 if (var, typ) in decls2}
    assigned_vars1 = {var for var, _ in decls1 if var not in input_vars}
    assigned_vars2 = {var for var, _ in decls2 if var not in input_vars}

    combined_decls = []
    for var in input_vars:
        typ = next((t for v, t in decls1 if v == var), 'Int')
        combined_decls.append(f"(declare-const {var} {typ})")
    for var, typ in decls1:
        if var in assigned_vars1:
            combined_decls.append(f"(declare-const {var} {typ})")
    for var, typ in decls2:
        if var in assigned_vars2:
            combined_decls.append(f"(declare-const {var} {typ})")

    combined_smt = "(set-logic QF_NIA)\n" + "\n".join(combined_decls) + "\n" + "\n".join(constraints1) + "\n" + "\n".join(constraints2)
    solver.from_string(combined_smt)

    z3_vars = {}
    for var, typ in decls1 + decls2:
        if typ == 'Int':
            z3_vars[var] = Int(var)
        elif typ == 'Bool':
            z3_vars[var] = Bool(var)

    var1, var2 = output_vars
    final_var1 = find_final_version(var1, assigned_vars1)
    final_var2 = find_final_version(var2, assigned_vars2)

    if final_var1 not in z3_vars or final_var2 not in z3_vars:
        return False, [f"Error: Final version of '{var1}' or '{var2}' not found in respective programs."]

    solver.push()
    solver.add(z3_vars[final_var1] != z3_vars[final_var2])
    result = solver.check()

    if result == unsat:
        solver.pop()
        solver.check()
        model = solver.model()
        return True, ["unsat", f"Programs are equivalent.\nExample model: {str(model)}"]
    else:
        counterexamples = []
        max_counterexamples = 2 if input_vars else 1
        while len(counterexamples) < max_counterexamples and result == sat:
            model = solver.model()
            counterexamples.append(str(model))
            if input_vars:
                exclude = [z3_vars[var] != model[z3_vars[var]] for var in input_vars if var in z3_vars and model[z3_vars[var]] is not None]
                if exclude:
                    solver.add(Or(exclude))
            result = solver.check()
        solver.pop()
        return False, ["sat"] + [f"Counterexample {i+1}: {ce}" for i, ce in enumerate(counterexamples)]