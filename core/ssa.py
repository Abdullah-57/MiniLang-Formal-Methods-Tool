import re
from collections import defaultdict
import copy

class SSAInstruction:
    def __init__(self, target, expression):
        self.target = target
        self.expression = expression

    def __repr__(self):
        return f"{self.target} := {self.expression}"

class SSAConverter:
    def __init__(self):
        self.instructions = []
        self.current_versions = {}
        self.var_stack = defaultdict(list)
        self.seen_vars = set()
        self.cond_counter = 0

    def get_versioned_var(self, var):
        if self.var_stack[var]:
            return self.var_stack[var][-1]
        versioned = f"{var}_0"
        if var not in self.seen_vars:
            self.seen_vars.add(var)
            self.var_stack[var].append(versioned)
        return versioned

    def new_version(self, var):
        self.seen_vars.add(var)
        self.current_versions[var] = self.current_versions.get(var, 0) + 1
        versioned = f"{var}_{self.current_versions[var]}"
        self.var_stack[var].append(versioned)
        return versioned

    def new_cond_var(self):
        self.cond_counter += 1
        return f"if_cond_{self.cond_counter}"

    def _replace_vars(self, expr):
        # Handle array accesses first (e.g., arr[j], arr[j+1])
        def replace_array_access(match):
            array_name = match.group(1)
            index_expr = match.group(2)
            # Recursively replace variables in the index expression
            versioned_index = self._replace_vars(index_expr)
            # Replace any non-alphanumeric characters in index to '_'
            safe_index = re.sub(r'[^a-zA-Z0-9]', '_', versioned_index)
            return f"{array_name}_{safe_index}"

        # Replace array accesses (e.g., arr[j] -> arr_j_1)
        expr = re.sub(r'(\w+)\[([^\]]+)\]', replace_array_access, expr)

        # Now replace standalone variables
        var_pattern = r'\b[a-zA-Z_]\w*\b'

        def replace_var(match):
            var = match.group(0)
            if var in ('if', 'else', 'while', 'for', 'assert', 'True', 'False'):
                return var
            self.seen_vars.add(var)
            return self.get_versioned_var(var)

        return re.sub(var_pattern, replace_var, expr)

    def convert(self, ast, unroll_depth=0):
        self.instructions = []
        self.current_versions = {}
        self.var_stack.clear()
        self.seen_vars = set()
        self.cond_counter = 0
        
        if unroll_depth > 0 and any(stmt.type == "While" for stmt in ast.statements):
            self._convert_with_unrolling(ast, unroll_depth)
        else:
            self._convert_block(ast)
        
        return self.instructions

    def _convert_block(self, block, is_loop_body=False):
        for stmt in block.statements:
            if stmt.type == "Assign":
                expr = self._replace_vars(stmt.expression)
                target = self.new_version(stmt.variable)
                self.instructions.append(SSAInstruction(target, expr))

            elif stmt.type == "ArrayAssign":
                index_expr = self._replace_vars(stmt.index)
                safe_index = re.sub(r'[^a-zA-Z0-9]', '_', index_expr)
                target = self.new_version(f"{stmt.array}_{safe_index}")
                expr = self._replace_vars(stmt.expression)
                self.instructions.append(SSAInstruction(target, expr))

            elif stmt.type == "Assert":
                cond = self._replace_vars(stmt.condition)
                self.instructions.append(SSAInstruction("assert", cond))

            elif stmt.type == "If":
                cond = self._replace_vars(stmt.condition)
                cond_var = self.new_cond_var()
                self.instructions.append(SSAInstruction(cond_var, cond))
                
                before_if = copy.deepcopy(self.var_stack)
                
                self._convert_block(stmt.true_branch)
                after_true = copy.deepcopy(self.var_stack)
                
                if stmt.false_branch:
                    self.var_stack = copy.deepcopy(before_if)
                    self._convert_block(stmt.false_branch)
                    after_false = copy.deepcopy(self.var_stack)
                    
                    modified_vars = self._collect_modified_variables(stmt.true_branch) | self._collect_modified_variables(stmt.false_branch)
                    
                    for var in modified_vars:
                        true_ver = after_true[var][-1] if var in after_true and after_true[var] else before_if[var][-1] if var in before_if and before_if[var] else f"{var}_0"
                        false_ver = after_false[var][-1] if var in after_false and after_false[var] else before_if[var][-1] if var in before_if and before_if[var] else f"{var}_0"
                        
                        if true_ver != false_ver:
                            phi_var = self.new_version(var)
                            self.instructions.append(SSAInstruction(phi_var, f"φ({cond_var}, {true_ver}, {false_ver})"))
                            self.var_stack[var] = [phi_var]
                        else:
                            self.var_stack[var] = [true_ver]
                else:
                    modified_vars = self._collect_modified_variables(stmt.true_branch)
                    
                    for var in modified_vars:
                        var_before = before_if[var][-1] if var in before_if and before_if[var] else f"{var}_0"
                        var_true = after_true[var][-1] if var in after_true and after_true[var] else var_before
                        
                        phi_var = self.new_version(var)
                        self.instructions.append(SSAInstruction(phi_var, f"φ({cond_var}, {var_true}, {var_before})"))
                        self.var_stack[var] = [phi_var]
                    
                    for var in self.seen_vars:
                        if var not in modified_vars:
                            if var in before_if and before_if[var]:
                                self.var_stack[var] = before_if[var]
                            else:
                                self.var_stack[var] = [f"{var}_0"]

            elif stmt.type == "While" and not is_loop_body:
                before_loop = copy.deepcopy(self.var_stack)
                loop_vars = self._collect_variables_in_block(stmt.body) | self._extract_variables(stmt.condition)
                
                unconditional_mods = self._collect_unconditional_modifications(stmt.body)
                
                phi_nodes = {}
                for var in unconditional_mods:
                    if var in loop_vars:
                        entry_ver = before_loop[var][-1] if var in before_loop and before_loop[var] else f"{var}_0"
                        phi_var = self.new_version(var)
                        phi_nodes[var] = (phi_var, entry_ver)
                        self.instructions.append(SSAInstruction(phi_var, f"φ({entry_ver}, ?)"))

                cond = self._replace_vars(stmt.condition)
                self.instructions.append(SSAInstruction("while_cond", cond))
                
                self._convert_block(stmt.body, is_loop_body=True)
                after_body = copy.deepcopy(self.var_stack)
                
                for var, (phi_var, entry_ver) in phi_nodes.items():
                    back_edge = after_body[var][-1] if var in after_body and after_body[var] else entry_ver
                    for i, instr in enumerate(self.instructions):
                        if instr.target == phi_var and "?" in instr.expression:
                            self.instructions[i] = SSAInstruction(phi_var, f"φ({entry_ver}, {back_edge})")
                            break
                            
                for var in loop_vars:
                    if var not in phi_nodes:
                        self.var_stack[var] = before_loop[var] if var in before_loop and before_loop[var] else [f"{var}_0"]

            elif stmt.type == "For" and not is_loop_body:
                before_loop = copy.deepcopy(self.var_stack)
                
                init_parts = stmt.init.split(":=")
                var = init_parts[0].strip()
                init_expr = self._replace_vars(init_parts[1].strip())
                init_var = self.new_version(var)
                self.instructions.append(SSAInstruction(init_var, init_expr))
                
                loop_vars = self._collect_variables_in_block(stmt.body) | self._extract_variables(stmt.condition) | self._extract_variables(stmt.update)
                unconditional_mods = self._collect_unconditional_modifications(stmt.body) | {var}
                
                phi_nodes = {}
                for loop_var in unconditional_mods:
                    if loop_var in loop_vars or loop_var == var:
                        entry_ver = init_var if loop_var == var else before_loop[loop_var][-1] if loop_var in before_loop and before_loop[loop_var] else f"{loop_var}_0"
                        phi_var = self.new_version(loop_var)
                        phi_nodes[loop_var] = (phi_var, entry_ver)
                        self.instructions.append(SSAInstruction(phi_var, f"φ({entry_ver}, ?)"))
                
                cond = self._replace_vars(stmt.condition)
                self.instructions.append(SSAInstruction("for_cond", cond))
                
                self._convert_block(stmt.body, is_loop_body=True)
                
                update_parts = stmt.update.split(":=")
                update_expr = self._replace_vars(update_parts[1].strip())
                update_var = self.new_version(var)
                self.instructions.append(SSAInstruction(update_var, update_expr))
                
                after_body = copy.deepcopy(self.var_stack)
                for loop_var, (phi_var, entry_ver) in phi_nodes.items():
                    back_edge = update_var if loop_var == var else after_body[loop_var][-1] if loop_var in after_body and after_body[loop_var] else entry_ver
                    for i, instr in enumerate(self.instructions):
                        if instr.target == phi_var and "?" in instr.expression:
                            self.instructions[i] = SSAInstruction(phi_var, f"φ({entry_ver}, {back_edge})")
                            break
                            
                for loop_var in loop_vars:
                    if loop_var not in phi_nodes:
                        self.var_stack[loop_var] = before_loop[loop_var] if loop_var in before_loop and before_loop[loop_var] else [f"{var}_0"]

    def _convert_with_unrolling(self, ast, unroll_depth):
        for stmt in ast.statements:
            if stmt.type != "While":
                self._convert_block(StmtBlock([stmt]))
            else:
                before_loop = copy.deepcopy(self.var_stack)
                loop_vars = self._collect_variables_in_block(stmt.body) | self._extract_variables(stmt.condition)
                
                for var in loop_vars:
                    if var not in self.var_stack or not self.var_stack[var]:
                        self.var_stack[var].append(f"{var}_0")
                        self.seen_vars.add(var)
                
                for _ in range(unroll_depth):
                    cond = self._replace_vars(stmt.condition)
                    cond_var = self.new_cond_var()
                    self.instructions.append(SSAInstruction(cond_var, cond))
                    self._convert_block(stmt.body)
                
                after_loop = copy.deepcopy(self.var_stack)
                for var in loop_vars:
                    if var not in self._collect_modified_variables(stmt.body):
                        self.var_stack[var] = before_loop[var] if var in before_loop and before_loop[var] else [f"{var}_0"]
                    elif var not in after_loop or not after_loop[var]:
                        self.var_stack[var] = before_loop[var] if var in before_loop and before_loop[var] else [f"{var}_0"]

    def _collect_variables_in_block(self, block):
        variables = set()
        for stmt in block.statements:
            if stmt.type == "Assign":
                variables.add(stmt.variable)
                variables.update(self._extract_variables(stmt.expression))
            elif stmt.type == "ArrayAssign":
                variables.add(stmt.array)
                variables.update(self._extract_variables(stmt.index))
                variables.update(self._extract_variables(stmt.expression))
            elif stmt.type == "Assert":
                variables.update(self._extract_variables(stmt.condition))
            elif stmt.type == "If":
                variables.update(self._extract_variables(stmt.condition))
                variables.update(self._collect_variables_in_block(stmt.true_branch))
                if stmt.false_branch:
                    variables.update(self._collect_variables_in_block(stmt.false_branch))
            elif stmt.type == "While":
                variables.update(self._extract_variables(stmt.condition))
                variables.update(self._collect_variables_in_block(stmt.body))
            elif stmt.type == "For":
                init_parts = stmt.init.split(":=")
                variables.add(init_parts[0].strip())
                variables.update(self._extract_variables(init_parts[1].strip()))
                variables.update(self._extract_variables(stmt.condition))
                variables.update(self._collect_variables_in_block(stmt.body))
                update_parts = stmt.update.split(":=")
                variables.update(self._extract_variables(update_parts[1].strip()))
        return variables

    def _collect_modified_variables(self, block):
        modified = set()
        for stmt in block.statements:
            if stmt.type == "Assign":
                modified.add(stmt.variable)
            elif stmt.type == "ArrayAssign":
                modified.add(f"{stmt.array}_{stmt.index}")
            elif stmt.type == "If":
                true_mod = self._collect_modified_variables(stmt.true_branch)
                false_mod = self._collect_modified_variables(stmt.false_branch) if stmt.false_branch else set()
                modified.update(true_mod | false_mod)
            elif stmt.type == "While" or stmt.type == "For":
                modified.update(self._collect_modified_variables(stmt.body))
        return modified

    def _collect_unconditional_modifications(self, block):
        modified = set()
        for stmt in block.statements:
            if stmt.type == "Assign":
                modified.add(stmt.variable)
            elif stmt.type == "ArrayAssign":
                modified.add(f"{stmt.array}_{stmt.index}")
            elif stmt.type == "If":
                true_mod = self._collect_unconditional_modifications(stmt.true_branch)
                false_mod = self._collect_unconditional_modifications(stmt.false_branch) if stmt.false_branch else set()
                modified.update(true_mod & false_mod)
            elif stmt.type == "While" or stmt.type == "For":
                modified.update(self._collect_unconditional_modifications(stmt.body))
        return modified

    def _extract_variables(self, expr):
        var_pattern = r'\b[a-zA-Z_]\w*\b'
        keywords = ('if', 'else', 'while', 'for', 'assert', 'True', 'False')
        vars = set(re.findall(var_pattern, expr))
        return {v for v in vars if v not in keywords}

class StmtBlock:
    def __init__(self, statements):
        self.statements = statements