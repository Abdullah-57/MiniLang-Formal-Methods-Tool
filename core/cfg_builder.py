import graphviz
from core.parser import Node

class BasicBlock:
    def __init__(self, id):
        self.id = id
        self.statements = []
        self.successors = []

    def add_statement(self, stmt):
        self.statements.append(stmt)

    def add_successor(self, block):
        self.successors.append(block)

class CFGBuilder:
    def __init__(self):
        self.block_id = 0
        self.entry = None
        self.exit = None
        self.blocks = []

    def new_block(self):
        block = BasicBlock(self.block_id)
        self.block_id += 1
        self.blocks.append(block)
        return block

    def build(self, ast):
        self.entry = self.new_block()
        self.exit = self.new_block()
        self.build_block(ast, self.entry, self.exit)
        return self.entry, self.exit, self.blocks

    def build_block(self, block_node, entry, exit):
        current_block = entry
        for stmt in block_node.statements:
            if stmt.type in ("Assign", "Assert"):
                current_block.add_statement(stmt)
            elif stmt.type == "If":
                cond_block = self.new_block()
                cond_block.add_statement(Node("Condition", condition=stmt.condition))
                current_block.add_successor(cond_block)
                true_entry = self.new_block()
                true_exit = self.new_block()
                self.build_block(stmt.true_branch, true_entry, true_exit)
                cond_block.add_successor(true_entry)
                if stmt.false_branch:
                    false_entry = self.new_block()
                    false_exit = self.new_block()
                    self.build_block(stmt.false_branch, false_entry, false_exit)
                    cond_block.add_successor(false_entry)
                    merge_block = self.new_block()
                    true_exit.add_successor(merge_block)
                    false_exit.add_successor(merge_block)
                else:
                    merge_block = self.new_block()
                    true_exit.add_successor(merge_block)
                    cond_block.add_successor(merge_block)
                current_block = merge_block
            elif stmt.type == "While":
                header_block = self.new_block()
                header_block.add_statement(Node("Condition", condition=stmt.condition))
                current_block.add_successor(header_block)
                body_entry = self.new_block()
                body_exit = self.new_block()
                self.build_block(stmt.body, body_entry, body_exit)
                header_block.add_successor(body_entry)
                body_exit.add_successor(header_block)
                loop_exit = self.new_block()
                header_block.add_successor(loop_exit)
                current_block = loop_exit
            elif stmt.type == "For":
                init_block = self.new_block()
                init_block.add_statement(Node("Assign", variable=stmt.init.split(":=")[0].strip(), expression=stmt.init.split(":=")[1].strip()))
                current_block.add_successor(init_block)
                header_block = self.new_block()
                header_block.add_statement(Node("Condition", condition=stmt.condition))
                init_block.add_successor(header_block)
                body_entry = self.new_block()
                body_exit = self.new_block()
                self.build_block(stmt.body, body_entry, body_exit)
                update_block = self.new_block()
                update_block.add_statement(Node("Assign", variable=stmt.update.split(":=")[0].strip(), expression=stmt.update.split(":=")[1].strip()))
                body_exit.add_successor(update_block)
                header_block.add_successor(body_entry)
                update_block.add_successor(header_block)
                loop_exit = self.new_block()
                header_block.add_successor(loop_exit)
                current_block = loop_exit
        current_block.add_successor(exit)

    def generate_dot(self, blocks):
        dot = graphviz.Digraph(format='png')
        for block in blocks:
            label = "\n".join(str(stmt) for stmt in block.statements)
            dot.node(str(block.id), label=label)
            for succ in block.successors:
                dot.edge(str(block.id), str(succ.id))
        return dot

    def save_cfg_graph(self, blocks, output_path="cfg_output"):
        dot = self.generate_dot(blocks)
        dot.render(filename=output_path, format='png', cleanup=True)