import ast
import re

class SMTGenerator:
    def __init__(self, ssa_instructions):
        """Initialize with a list of SSAInstruction objects."""
        self.ssa_instructions = ssa_instructions
        self.types = self.infer_types()

    def _extract_vars(self, expr):
        """Extract variable names from an expression string."""
        var_pattern = r'\b[a-zA-Z_]\w*(?:_\w+)?\b'
        return set(re.findall(var_pattern, expr))

    def infer_types(self):
        """Infer variable types (Int or Bool) from SSA instructions and expressions."""
        all_vars = set()
        for instr in self.ssa_instructions:
            if instr.target == 'assert':
                all_vars.update(self._extract_vars(instr.expression))
            else:
                all_vars.add(instr.target)
                all_vars.update(self._extract_vars(instr.expression))

        types = {}
        for var in all_vars:
            target_instr = next((instr for instr in self.ssa_instructions if instr.target == var), None)
            if target_instr:
                if target_instr.expression.startswith('φ('):
                    args = [arg.strip() for arg in target_instr.expression[2:-1].split(',')][1:]  # skip condition
                    for arg in args:
                        if arg in types:
                            types[var] = types[arg]
                            break
                    else:
                        types[var] = 'Int'  # default to Int
                else:
                    if self.is_comparison(target_instr.expression):
                        types[var] = 'Bool'
                    else:
                        types[var] = 'Int'
            else:
                types[var] = 'Int'
        return types

    def is_comparison(self, expr):
        """Check if an expression contains a comparison operator."""
        comparison_ops = ['<', '>', '==', '!=', '<=', '>=']
        return any(op in expr for op in comparison_ops)

    def parse_expr_to_smt(self, expr, target=None, assigned_vars=None, suffix=''):
        """Convert a MiniLang expression to SMT-LIB format with optional suffixing."""
        if assigned_vars is None:
            assigned_vars = set()
        if expr.startswith('φ('):
            args = [arg.strip() for arg in expr[2:-1].split(',')]
            if len(args) != 3:
                raise ValueError("Phi function expects three arguments: condition, true_ver, false_ver")
            cond, true_ver, false_ver = args
            if not target:
                raise ValueError("Target variable required for phi function")
            cond_suff = cond + suffix if cond in assigned_vars else cond
            true_ver_suff = true_ver + suffix if true_ver in assigned_vars else true_ver
            false_ver_suff = false_ver + suffix if false_ver in assigned_vars else false_ver
            target_suff = target + suffix if target in assigned_vars else target
            return f"(ite {cond_suff} (= {target_suff} {true_ver_suff}) (= {target_suff} {false_ver_suff}))"
        else:
            try:
                tree = ast.parse(expr, mode='eval')
                return self.ast_to_smt(tree.body, assigned_vars, suffix)
            except SyntaxError as e:
                raise ValueError(f"Invalid expression: {expr}\nError: {str(e)}")

    def ast_to_smt(self, node, assigned_vars=None, suffix=''):
        """Recursively convert an AST node to SMT-LIB string with optional suffixing."""
        if assigned_vars is None:
            assigned_vars = set()
        if isinstance(node, ast.Name):
            return node.id + suffix if node.id in assigned_vars else node.id
        elif isinstance(node, ast.Num):
            return str(node.n)
        elif isinstance(node, ast.BinOp):
            left = self.ast_to_smt(node.left, assigned_vars, suffix)
            op = self.op_to_smt(type(node.op))
            right = self.ast_to_smt(node.right, assigned_vars, suffix)
            return f"({op} {left} {right})"
        elif isinstance(node, ast.Compare):
            left = self.ast_to_smt(node.left, assigned_vars, suffix)
            ops = [self.op_to_smt(type(op)) for op in node.ops]
            comparators = [self.ast_to_smt(comp, assigned_vars, suffix) for comp in node.comparators]
            return f"({ops[0]} {left} {comparators[0]})"
        elif isinstance(node, ast.BoolOp):
            op = 'and' if isinstance(node.op, ast.And) else 'or'
            values = [self.ast_to_smt(val, assigned_vars, suffix) for val in node.values]
            return f"({op} {' '.join(values)})"
        elif isinstance(node, ast.UnaryOp):
            if isinstance(node.op, ast.Not):
                operand = self.ast_to_smt(node.operand, assigned_vars, suffix)
                return f"(not {operand})"
            elif isinstance(node.op, ast.USub):
                operand = self.ast_to_smt(node.operand, assigned_vars, suffix)
                return f"(- {operand})"
            raise ValueError(f"Unsupported unary operator: {type(node.op)}")
        else:
            raise ValueError(f"Unsupported AST node: {type(node)}")

    def op_to_smt(self, op_type):
        """Map Python AST operator types to SMT-LIB operators."""
        op_map = {
            ast.Add: '+',
            ast.Sub: '-',
            ast.Mult: '*',
            ast.Div: '/',
            ast.Lt: '<',
            ast.Gt: '>',
            ast.Eq: '=',
            ast.NotEq: '!=',
            ast.LtE: '<=',
            ast.GtE: '>=',
            ast.Mod: 'mod',
        }
        op = op_map.get(op_type)
        if op is None:
            raise ValueError(f"Unsupported operator type: {op_type}")
        return op

    def generate_smt(self, suffix=''):
        """Generate SMT-LIB code with optional suffix for assigned variables and separate assertions."""
        assigned_vars = {instr.target for instr in self.ssa_instructions if instr.target != 'assert'}
        all_vars = set(self.types.keys())
        input_vars = all_vars - assigned_vars

        program_constraints = ["(set-logic QF_NIA)"]
        assertion_conditions = []

        for var in sorted(input_vars):
            program_constraints.append(f"(declare-const {var} {self.types[var]})")
        for var in sorted(assigned_vars):
            var_suff = var + suffix if suffix else var
            program_constraints.append(f"(declare-const {var_suff} {self.types[var]})")

        for instr in self.ssa_instructions:
            if instr.target == 'assert':
                parsed_cond = self.parse_expr_to_smt(instr.expression, assigned_vars=assigned_vars, suffix=suffix)
                assertion_conditions.append(parsed_cond)
            else:
                if instr.expression.startswith('φ('):
                    parsed_expr = self.parse_expr_to_smt(instr.expression, instr.target, assigned_vars, suffix)
                    program_constraints.append(f"(assert {parsed_expr})")
                else:
                    parsed_expr = self.parse_expr_to_smt(instr.expression, assigned_vars=assigned_vars, suffix=suffix)
                    target_suff = instr.target + suffix if instr.target in assigned_vars else instr.target
                    program_constraints.append(f"(assert (= {target_suff} {parsed_expr}))")

        # Add check-sat and get-model at the end
        program_constraints.append("(check-sat)")
        program_constraints.append("(get-model)")
        program_smt_code = "\n".join(program_constraints)
        return program_smt_code, assertion_conditions