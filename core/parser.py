import os
import re
import graphviz

class Node:
    def __init__(self, node_type, **kwargs):
        self.type = node_type
        self.__dict__.update(kwargs)

    def __repr__(self):
        return f"{self.type}({{ {', '.join(f'{k}: {v}' for k, v in self.__dict__.items() if k != 'type')} }})"

class Parser:
    def __init__(self, code):
        self.lines = self._preprocess_lines(code)
        self.index = 0
        print("DEBUG lines:", self.lines)

    def _preprocess_lines(self, code):
        raw_lines = [line.strip() for line in code.split('\n') if line.strip()]
        processed_lines = []
        for line in raw_lines:
            while True:
                match = re.search(r'(.*?)}\s*(else\s*\{?)', line)
                if match:
                    before = match.group(1).strip()
                    closing = '}'
                    after = match.group(2).strip()
                    if before:
                        processed_lines.append(before)
                    processed_lines.append(closing)
                    processed_lines.append(after)
                    break
                else:
                    processed_lines.append(line)
                    break
        return processed_lines

    def parse(self):
        return self.parse_block()

    def parse_block(self):
        block = []
        while self.index < len(self.lines):
            line = self.lines[self.index]

            if line.startswith("if"):
                block.append(self.parse_if())
            elif line.startswith("while"):
                block.append(self.parse_while())
            elif line.startswith("for"):
                block.append(self.parse_for())
            elif line.startswith("}"):
                self.index += 1
                break
            else:
                stmt = self.parse_statement()
                if stmt:
                    block.append(stmt)
        return Node("Block", statements=block)

    def parse_if(self):
        line = self.lines[self.index]
        match = re.match(r"if\s*\((.*)\)\s*{", line)
        if not match:
            raise ValueError(f"Invalid if statement: {line}")
        condition = match.group(1).strip()
        self.index += 1
        true_branch = self.parse_block()

        false_branch = None
        if self.index < len(self.lines):
            next_line = self.lines[self.index]
            if next_line.startswith("else"):
                if re.match(r"else\s*{", next_line):
                    self.index += 1
                elif next_line == "else":
                    self.index += 1
                    if self.index < len(self.lines) and self.lines[self.index].startswith("{"):
                        self.index += 1
                false_branch = self.parse_block()

        return Node("If", condition=condition, true_branch=true_branch, false_branch=false_branch)

    def parse_while(self):
        line = self.lines[self.index]
        match = re.match(r"while\s*\((.*)\)\s*{", line)
        if not match:
            raise ValueError(f"Invalid while statement: {line}")
        condition = match.group(1).strip()
        self.index += 1
        body = self.parse_block()
        return Node("While", condition=condition, body=body)

    def parse_for(self):
        line = self.lines[self.index]
        match = re.match(r"for\s*\(\s*(.+?)\s*;\s*(.+?)\s*;\s*(.+?)\s*\)\s*\{", line)
        if not match:
            raise ValueError(f"Invalid for statement: {line}")
        init, cond, update = match.groups()
        self.index += 1
        body = self.parse_block()
        return Node("For", init=init.strip(), condition=cond.strip(), update=update.strip(), body=body)

    def parse_statement(self):
        line = self.lines[self.index]
        self.index += 1
        if line.startswith("assert"):
            match = re.match(r"assert\s*\((.*)\);?", line)
            if not match:
                raise ValueError(f"Invalid assert statement: {line}")
            condition = match.group(1).strip()
            if 'forall' in condition:
                raise ValueError("Forall assertions are not supported. Use a loop-based assertion instead.")
            return Node("Assert", condition=condition)
        elif re.match(r"[\w\[\]]+\s*:=\s*.+;", line):
            match = re.match(r"([\w\[\]]+)\s*:=\s*(.+);", line)
            if not match:
                raise ValueError(f"Invalid assignment statement: {line}")
            variable = match.group(1).strip()
            expression = match.group(2).strip()
            if '[' in variable:
                array_match = re.match(r"(\w+)\[(.+)\]", variable)
                if not array_match:
                    raise ValueError(f"Invalid array assignment: {variable}")
                array_name, index = array_match.groups()
                return Node("ArrayAssign", array=array_name, index=index.strip(), expression=expression)
            return Node("Assign", variable=variable, expression=expression)
        return None

    def generate_dot(self, ast):
        dot = graphviz.Digraph(format='png')

        def add_node(node, parent=None):
            node_name = str(id(node))
            label = f"{node.type}"

            if node.type == "If":
                label += f"\ncond: {node.condition}"
            elif node.type == "While":
                label += f"\ncond: {node.condition}"
            elif node.type == "For":
                label += f"\ninit: {node.init}\ncond: {node.condition}\nupdate: {node.update}"
            elif node.type == "Assert":
                label += f"\ncond: {node.condition}"
            elif node.type == "Assign":
                label += f"\n{node.variable} := {node.expression}"
            elif node.type == "ArrayAssign":
                label += f"\n{node.array}[{node.index}] := {node.expression}"

            dot.node(node_name, label=label)

            if parent:
                dot.edge(parent, node_name)

            if hasattr(node, 'true_branch') and node.true_branch:
                add_node(node.true_branch, node_name)
            if hasattr(node, 'false_branch') and node.false_branch:
                add_node(node.false_branch, node_name)
            if hasattr(node, 'body') and node.body:
                add_node(node.body, node_name)
            if hasattr(node, 'statements'):
                for stmt in node.statements:
                    add_node(stmt, node_name)

        add_node(ast)
        return dot

    def save_ast_graph(self, ast, output_path="ast_output"):
        dot = self.generate_dot(ast)
        dot.render(filename=output_path, format='png', cleanup=True)