import ast
import astunparse


class Literal:
    def __init__(self, atom, pos):
        self.atom = atom
        self.pos = pos

    def negate(self):
        self.pos = not self.pos





class ENFDisjunctive:
    def __init__(self, left, right):
        self.left = left.clone()
        self.right = right.clone()

class Propagator:
    def __init__(self, left, middle, right):
        self.left = left.clone()
        self.middle = middle.clone()
        self.right = right.clone()



def derive_propagators(enf_rules):
    propagators = []
    for enf_rule in enf_rules:
        if type(enf_rule) == ENFDisjunctive and len(enf_rule.right) == 1:
            la = enf_rule.left.atom
            lv = enf_rule.left.pos
            ra = enf_rule.right[0].atom
            rv = enf_rule.right[0].pos

            propagators.append(Propagator(Literal(la, lv), [], Literal(ra, rv)))
            propagators.append(Propagator(Literal(ra, not rv), [], Literal(la, not lv)))
            propagators.append(Propagator(Literal(ra, rv), [], Literal(la, lv)))
            propagators.append(Propagator(Literal(la, not lv), [], Literal(ra, not rv)))




def generate_propagate(enf_rules):
    pass





def generate_feedback_loop():
    return ast.Module(
        body=[
            ast.Assign(
                targets=[
                    ast.Name(id='quit', ctx=ast.Store())],
                value=ast.Constant(value=False)),
            ast.While(
                test=ast.UnaryOp(
                    op=ast.Not(),
                    operand=ast.Name(id='quit', ctx=ast.Load())),
                body=[
                    ast.Assign(
                        targets=[
                            ast.Name(id='field', ctx=ast.Store())],
                        value=ast.Call(
                            func=ast.Name(id='input', ctx=ast.Load()),
                            args=[
                                ast.Constant(value='What field do you want to change\n')],
                            keywords=[])),
                    ast.Assign(
                        targets=[
                            ast.Name(id='value', ctx=ast.Store())],
                        value=ast.Call(
                            func=ast.Name(id='bool', ctx=ast.Load()),
                            args=[
                                ast.Call(
                                    func=ast.Name(id='int', ctx=ast.Load()),
                                    args=[
                                        ast.Call(
                                            func=ast.Name(id='input', ctx=ast.Load()),
                                            args=[
                                                ast.Constant(value='Do you want it to be True (1) or False (0)?\n')],
                                            keywords=[])],
                                    keywords=[])],
                            keywords=[])),
                    ast.If(
                        test=ast.BoolOp(
                            op=ast.Or(),
                            values=[
                                ast.Compare(
                                    left=ast.Name(id='field', ctx=ast.Load()),
                                    ops=[
                                        ast.Eq()],
                                    comparators=[
                                        ast.Constant(value='quit')]),
                                ast.Compare(
                                    left=ast.Name(id='value', ctx=ast.Load()),
                                    ops=[
                                        ast.Eq()],
                                    comparators=[
                                        ast.Constant(value='quit')])]),
                        body=[
                            ast.Assign(
                                targets=[
                                    ast.Name(id='quit', ctx=ast.Store())],
                                value=ast.Constant(value=True))],
                        orelse=[
                            ast.Assign(
                                targets=[
                                    ast.Name(id='changes', ctx=ast.Store())],
                                value=ast.Dict(
                                    keys=[
                                        ast.Name(id='field', ctx=ast.Load())],
                                    values=[
                                        ast.Name(id='value', ctx=ast.Load())])),
                            ast.While(
                                test=ast.Compare(
                                    left=ast.Call(
                                        func=ast.Name(id='len', ctx=ast.Load()),
                                        args=[
                                            ast.Name(id='changes', ctx=ast.Load())],
                                        keywords=[]),
                                    ops=[
                                        ast.NotEq()],
                                    comparators=[
                                        ast.Constant(value=0)]),
                                body=[
                                    ast.Assign(
                                        targets=[
                                            ast.Name(id='old_changes', ctx=ast.Store())],
                                        value=ast.Name(id='changes', ctx=ast.Load())),
                                    ast.Assign(
                                        targets=[
                                            ast.Name(id='changes', ctx=ast.Store())],
                                        value=ast.Call(
                                            func=ast.Name(id='propagate', ctx=ast.Load()),
                                            args=[
                                                ast.Name(id='changes', ctx=ast.Load())],
                                            keywords=[])),
                                    ast.Expr(
                                        value=ast.Call(
                                            func=ast.Name(id='update_structure', ctx=ast.Load()),
                                            args=[
                                                ast.Name(id='old_changes', ctx=ast.Load())],
                                            keywords=[]))],
                                orelse=[]),
                            ast.Expr(
                                value=ast.Call(
                                    func=ast.Name(id='print_structure', ctx=ast.Load()),
                                    args=[],
                                    keywords=[]))])],
                orelse=[])],
        type_ignores=[])


def generate(enf_rules):
    propagate_function = generate_propagate(enf_rules)
    feedback_loop = generate_feedback_loop()
    module = ast.Module(body=[propagate_function.body, feedback_loop.body], type_ignores=[])
    #print(ast.dump(module, indent=4))
    code = astunparse.unparse(module)
    with open("generated_code.py", "w") as file:
        file.write(code)


rules = ENFDisjunctive(Literal("A", True), [Literal("B", True), Literal("C", True)])
generate(rules)