import re
from core.ssa import SSAInstruction
import graphviz

def extract_used_vars(instruction):
    """Extract variables used in an SSA instruction."""
    if instruction.target == 'assert':
        var_pattern = r'\b[a-zA-Z_]\w*_\d+\b'
        return set(re.findall(var_pattern, instruction.expression))
    elif instruction.expression.startswith('φ('):
        args = [arg.strip() for arg in instruction.expression[2:-1].split(',')]
        return set(arg for arg in args if arg not in ('True', 'False'))
    else:
        var_pattern = r'\b[a-zA-Z_]\w*_\d+\b'
        return set(re.findall(var_pattern, instruction.expression))

def propagate_constants(expr, constants):
    """Replace variables with their constant values if known."""
    var_pattern = r'\b[a-zA-Z_]\w*_\d+\b'
    def replace_var(match):
        var = match.group(0)
        return str(constants.get(var, var))
    return re.sub(var_pattern, replace_var, expr)

def evaluate_expression(expr):
    """Safely evaluate a simple arithmetic or boolean expression if all parts are constants."""
    try:
        expr = expr.replace('=', '==')
        allowed_chars = set('0123456789 +-*/()=<>!')
        if not all(c in allowed_chars or c.isspace() for c in expr):
            return None
        if re.search(r'\b[a-zA-Z_]\w*\b', expr):
            return None
        return eval(expr, {"__builtins__": {}}, {})
    except:
        return None

def optimize_ssa(ssa_instructions, live_vars):
    """Apply constant propagation and preserve dependencies for SSA instructions."""
    # Step 1: Perform live variable analysis on original SSA
    live = set(live_vars)
    phi_vars = set()  # Track variables used in φ-functions
    for instr in ssa_instructions:
        if instr.expression.startswith('φ('):
            phi_vars.update(extract_used_vars(instr))

    changed = True
    while changed:
        changed = False
        for instr in reversed(ssa_instructions):
            if instr.target in live or instr.target in phi_vars or instr.target == 'assert':
                used_vars = extract_used_vars(instr)
                if live.update(used_vars):
                    changed = True

    # Step 2: Compute constants with propagation
    constants = {}
    for instr in ssa_instructions:
        if instr.target != 'assert':
            new_expr = propagate_constants(instr.expression, constants)
            const_value = evaluate_expression(new_expr)
            if const_value is not None:
                constants[instr.target] = const_value

    # Step 3: Build optimized SSA with all necessary instructions
    optimized_instructions = []
    for instr in ssa_instructions:
        if instr.target in live or instr.target == 'assert':
            if instr.target == 'assert':
                new_expr = propagate_constants(instr.expression, constants)
                optimized_instructions.append(SSAInstruction('assert', new_expr))
            else:
                new_expr = propagate_constants(instr.expression, constants)
                const_value = evaluate_expression(new_expr)
                if const_value is not None:
                    optimized_instructions.append(SSAInstruction(instr.target, str(const_value)))
                else:
                    optimized_instructions.append(SSAInstruction(instr.target, new_expr))

    return optimized_instructions

def generate_ssa_cfg(ssa_instructions, output_path="ssa_cfg"):
    """Generate a CFG for SSA instructions with proper control flow."""
    dot = graphviz.Digraph(format='png')

    # Helper to create a unique block ID
    block_id_counter = 0
    def new_block_id():
        nonlocal block_id_counter
        block_id_counter += 1
        return f"block_{block_id_counter}"

    # Basic block structure
    class BasicBlock:
        def __init__(self, block_id):
            self.id = block_id
            self.instructions = []
            self.successors = []

    # List of basic blocks
    blocks = []
    current_block = BasicBlock(new_block_id())
    blocks.append(current_block)

    # Regex to identify conditional instructions (e.g., if_cond_1 := (x_0 < 5))
    cond_pattern = r'if_cond_\d+ := (.+)'

    for instr in ssa_instructions:
        if re.match(cond_pattern, str(instr)):
            # Start a new block for the true branch
            true_block = BasicBlock(new_block_id())
            blocks.append(true_block)
            current_block.successors.append(true_block.id)

            # Start a new block for the false branch
            false_block = BasicBlock(new_block_id())
            blocks.append(false_block)
            current_block.successors.append(false_block.id)

            # Add the conditional instruction to the current block
            current_block.instructions.append(instr)

            # Move to the true block for the next instructions
            current_block = true_block
        elif instr.expression.startswith('φ('):
            # Phi functions indicate the start of a merge block
            merge_block = BasicBlock(new_block_id())
            blocks.append(merge_block)
            # Connect previous blocks to this merge block safely
            if len(blocks) >= 3:
                blocks[-3].successors.append(merge_block.id)  # False branch predecessor
                blocks[-2].successors.append(merge_block.id)  # True branch predecessor
            elif len(blocks) == 2:
                blocks[-2].successors.append(merge_block.id)  # Only one predecessor available
            current_block = merge_block
            current_block.instructions.append(instr)
        else:
            current_block.instructions.append(instr)

    # Add edges for sequential flow
    for i in range(len(blocks) - 1):
        if not blocks[i].successors:
            blocks[i].successors.append(blocks[i+1].id)

    # Create Graphviz nodes and edges
    for block in blocks:
        label = f"Block {block.id}\n" + "\n".join(str(instr) for instr in block.instructions)
        dot.node(block.id, label=label)
        for succ_id in block.successors:
            dot.edge(block.id, succ_id)

    dot.render(filename=output_path, cleanup=True)

def get_live_vars_from_assertions(ssa_instructions):
    """Extract variables used in assertions as live variables."""
    live_vars = set()
    for instr in ssa_instructions:
        if instr.target == 'assert':
            live_vars.update(extract_used_vars(instr))
    return live_vars

def get_final_versions(ssa_instructions, base_vars):
    """Find the final SSA versions of base variables."""
    final_versions = {}
    for instr in ssa_instructions:
        if instr.target != 'assert':
            base = instr.target.split('_')[0]
            if base in base_vars:
                final_versions[base] = instr.target
    return set(final_versions.values())