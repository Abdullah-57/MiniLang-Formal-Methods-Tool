from core.parser import Node
from core.ssa import SSAConverter

class LoopUnroller:
    def __init__(self, depth):
        self.depth = depth
        self.ssa_converter = SSAConverter()

    def unroll(self, ast):
        return self._unroll_node(ast)

    def _unroll_node(self, node):
        if node.type == "Block":
            new_statements = []
            for stmt in node.statements:
                unrolled_stmt = self._unroll_node(stmt)
                if isinstance(unrolled_stmt, list):
                    new_statements.extend(unrolled_stmt)
                else:
                    new_statements.append(unrolled_stmt)
            return Node("Block", statements=new_statements)

        elif node.type == "For":
            return self._unroll_for_loop(node)

        elif node.type == "While":
            return self._unroll_while_loop(node)

        elif node.type == "If":
            true_branch = self._unroll_node(node.true_branch)
            false_branch = self._unroll_node(node.false_branch) if node.false_branch else None
            return Node("If", condition=node.condition, true_branch=true_branch, false_branch=false_branch)

        elif node.type in ("Assign", "Assert", "ArrayAssign"):
            return node

        else:
            raise ValueError(f"Unsupported node type: {node.type}")

    def _unroll_for_loop(self, for_node):
        init = for_node.init
        condition = for_node.condition
        update = for_node.update
        body = for_node.body

        init_parts = init.split(":=")
        loop_var = init_parts[0].strip()
        init_expr = init_parts[1].strip()

        # Parse condition (e.g., i < n)
        cond_parts = condition.split("<")
        if len(cond_parts) != 2:
            raise ValueError("Unsupported loop condition format")
        bound = cond_parts[1].strip()  # Keep as symbolic (e.g., 'n')

        statements = []
        statements.append(Node("Assign", variable=loop_var, expression=init_expr))

        # Track loop variable symbolically
        current_i = init_expr  # Start with initial expression (e.g., '0')
        update_expr = update.split(":=")[1].strip()  # e.g., "i + 1"

        for k in range(self.depth):
            # Create condition for iteration (e.g., i < n)
            true_branch_statements = self._unroll_node(body).statements
            # Update loop variable after body
            true_branch_statements.append(Node("Assign", variable=loop_var, expression=update_expr))
            true_branch = Node("Block", statements=true_branch_statements)

            statements.append(
                Node(
                    "If",
                    condition=f"{loop_var} < {bound}",
                    true_branch=true_branch,
                    false_branch=None
                )
            )
            # Update symbolic value of loop_var for next iteration
            current_i = update_expr.replace("i", current_i)

        return statements

    def _unroll_while_loop(self, while_node):
        condition = while_node.condition
        body = while_node.body

        # Parse condition (e.g., i < n)
        cond_parts = condition.split("<")
        if len(cond_parts) != 2:
            raise ValueError("Unsupported loop condition format")
        loop_var = cond_parts[0].strip()
        bound = cond_parts[1].strip()

        statements = []
        # Assume loop variable is initialized before loop
        for k in range(self.depth):
            true_branch = Node("Block", statements=self._unroll_node(body).statements)
            statements.append(
                Node(
                    "If",
                    condition=f"{loop_var} < {bound}",
                    true_branch=true_branch,
                    false_branch=None
                )
            )

        return statements

    def get_ssa(self, ast):
        unrolled_ast = self.unroll(ast)
        return self.ssa_converter.convert(unrolled_ast)

    def ast_to_minilang(self, ast):
        if ast.type == "Block":
            return "\n".join(self.ast_to_minilang(stmt) for stmt in ast.statements)
        elif ast.type == "Assign":
            return f"{ast.variable} := {ast.expression};"
        elif ast.type == "ArrayAssign":
            return f"{ast.array}[{ast.index}] := {ast.expression};"
        elif ast.type == "Assert":
            return f"assert({ast.condition});"
        elif ast.type == "If":
            code = [f"if ({ast.condition}) {{"]
            code.append(self.ast_to_minilang(ast.true_branch))
            code.append("}")
            if ast.false_branch:
                code.append("else {")
                code.append(self.ast_to_minilang(ast.false_branch))
                code.append("}")
            return "\n".join(code)
        else:
            raise ValueError(f"Cannot convert node type to MiniLang: {ast.type}")

    def get_unrolled_code(self, ast):
        unrolled_ast = self.unroll(ast)
        return self.ast_to_minilang(unrolled_ast)