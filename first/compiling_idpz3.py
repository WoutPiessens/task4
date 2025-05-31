import parsing_idpz3

import ast
import random
import time

import astunparse
from lark import Lark, Tree, Transformer, Token
from enum import Enum


class Integer(parsing_idpz3.Exp):
    def __init__(self, name):
        self.name = name
    def clone(self):
        return Integer(self.name)

    def equals(self, integer):
        return self.name == integer.name

class Operator(Enum):
    EQ = 1
    NEQ = 2
    LEQ = 3
    LT = 4
    GEQ = 5
    GT = 6


class Equation(parsing_idpz3.Exp):
    def __init__(self, operator, exp1, exp2):
        self.operator = operator
        self.exp1 = exp1
        self.exp2 = exp2

    def clone(self):
        return Equation(self.operator, self.exp1.clone(), self.exp2.clone())

    def negate(self):
        operation_negator = {Operator.EQ: Operator.NEQ, Operator.NEQ: Operator.EQ, Operator.GEQ: Operator.LT,
                             Operator.LT: Operator.GEQ, Operator.GT: Operator.LEQ, Operator.LEQ: Operator.GT}
        return Equation(operation_negator[self.operator], self.exp1.clone(), self.exp2.clone())

    def switch(self):
        operation_switcher = {Operator.EQ: Operator.EQ, Operator.NEQ: Operator.NEQ, Operator.GEQ: Operator.LEQ,
                             Operator.LEQ: Operator.GEQ, Operator.GT: Operator.LT, Operator.LT: Operator.GT}
        return Equation(operation_switcher[self.operator], self.exp2.clone(), self.exp1.clone())


    def equals(self, eq):
        return self.operator == eq.operator and self.exp1.equals(eq.exp1) and self.exp2.equals(eq.exp2)





class DerivedPropagator:
    def __init__(self, left, middle, right):
        if left == None:
            self.left = None
        else:
            self.left = left.clone()
        self.middle = [lit.clone() for lit in middle]
        self.right = right.clone()


class EquationPropagator:
    def __init__(self, left, middle, right):
        if left == None:
            self.left = None
        else:
            self.left = left.clone()
        self.middle = [lit.clone() for lit in middle]
        self.right = right.clone()

def derive_initial_propagators(enf_rule):
    initial_propagators = []
    if type(enf_rule) == parsing_idpz3.ENFDisjunctive:
        for literal in enf_rule.right:
            initial_propagators.append({literal,enf_rule.left.negate()})
        prop_set = {enf_rule.left}
        for literal in enf_rule.right[:-1]:
            prop_set.add(literal.negate())
        prop_set.add(enf_rule.right[-1].negate())
        initial_propagators.append(prop_set)
    elif type(enf_rule) == parsing_idpz3.ENFConjunctive:
        for literal in enf_rule.right:
            initial_propagators.append({enf_rule.left, literal.negate()})
        prop_set = set()
        for literal in enf_rule.right:
            prop_set.add(literal)
        prop_set.add(enf_rule.left.negate())
        initial_propagators.append(prop_set)
    #elif type(enf_rule) == Disjunctive:
    #    prop_set = set()
    #    for literal in enf_rule.literals:
    #        prop_set.add(literal.negate())
    #    initial_propagators.append(prop_set)
    elif type(enf_rule) == parsing_idpz3.Conjunctive:
        for literal in enf_rule.literals:
            initial_propagators.append({literal.negate()})

    return initial_propagators

def derive_derived_propagators(initial_propagator):
    derived_propagators = set()
    if len(initial_propagator) > 1:
        for start_literal in initial_propagator:
            for end_literal in initial_propagator:
                if (type(start_literal) != type(end_literal)) or not start_literal.equals(end_literal):
                    derived_propagators.add(DerivedPropagator(start_literal, initial_propagator - {start_literal, end_literal}, end_literal.negate()))
        if len(initial_propagator) == 2:
            initial_propagator_list = list(initial_propagator)
            first_elem = initial_propagator_list[0]
            second_elem = initial_propagator_list[1]
            if not (type(first_elem) == parsing_idpz3.Literal and type(second_elem) == parsing_idpz3.Literal):
                if type(first_elem) == Equation:
                    equation = first_elem
                    lit = second_elem
                elif type(second_elem) == Equation:
                    equation = second_elem
                    lit = first_elem
                if type(equation.exp1) == parsing_idpz3.Atom and type(equation.exp2) == parsing_idpz3.Atom:
                    derived_propagators.add(EquationPropagator(equation.exp1, [lit], equation.negate()))
                    derived_propagators.add(EquationPropagator(equation.exp2, [lit], equation.switch().negate()))

    else:
        literal = initial_propagator.pop()
        derived_propagators.add(DerivedPropagator(None, [], literal.negate()))
    return derived_propagators



def derive_derived_propagators_for_modifiable_set(initial_propagators, modifiable_set):
    derived_propagators = set()
    for modifiable_var in modifiable_set:
        inspected_literals = set()
        inspected_literals.add(parsing_idpz3.Literal(modifiable_var, True))
        inspected_literals.add(parsing_idpz3.Literal(modifiable_var, False))
        for initial_prop in initial_propagators:
            if len(initial_prop) == 1:
                for elem in initial_prop:
                    inspected_literals.add(elem.negate())
                    derived_propagators.add(DerivedPropagator(None, [], elem.negate()))
        changes = inspected_literals.copy()
        while len(changes) != 0:
            new_changes = set()
            new_inspected_literals = inspected_literals.copy()
            for initial_prop in initial_propagators:
                not_inspected = initial_prop.difference(inspected_literals)
                if len(not_inspected) == 1:
                    for elem in not_inspected:
                        new_conclusion = elem
                    new_inspected_literals.add(new_conclusion)
                    new_inspected_literals.add(new_conclusion.negate())
                    new_changes.add(new_conclusion)
                    new_changes.add(new_conclusion.negate())

                    newest_causes = initial_prop.intersection(changes)
                    for newest_cause in newest_causes:
                        derived_propagators.add(DerivedPropagator(newest_cause, initial_prop - {newest_cause, new_conclusion}, new_conclusion.negate()))
            changes = new_changes.copy()
            inspected_literals = new_inspected_literals.copy()
    return derived_propagators



def generate_dash_imports():
    return ast.ImportFrom(
         module='dash',
         names=[
            ast.alias(name='Dash'),
            ast.alias(name='html'),
            ast.alias(name='dcc'),
            ast.alias(name='State'),
            ast.alias(name='Input'),
            ast.alias(name='Output'),
            ast.alias(name='ALL'),
            ast.alias(name='callback_context')],
         level=0)


def derive_syntax_tree_for_set(set_of_values):
    elements = []
    for elem in set_of_values:
        elements.append(ast.Constant(value=elem))
    return elements

def generate_initial_structure(enf_rules, domain_rules, name='structure'):
    set_of_bool_var = set()

    for enf_rule in enf_rules:
        if type(enf_rule) == parsing_idpz3.ENFDisjunctive or type(enf_rule) == parsing_idpz3.ENFConjunctive:
            set_of_bool_var.add(enf_rule.left.atom)
            for exp in enf_rule.right:
                if type(exp) == parsing_idpz3.Literal:
                    set_of_bool_var.add(exp.atom)

        else:
            for exp in enf_rule.literals:
                if type(exp) == parsing_idpz3.Literal:
                    set_of_bool_var.add(exp.atom)

    list_of_atoms = []
    for atom in set_of_bool_var:
        list_of_atoms.append(ast.Constant(value=atom))
    list_of_values = []
    for i in range(len(set_of_bool_var)):
        list_of_values.append(ast.Set(
                  elts=[
                     ast.Constant(value=True),
                     ast.Constant(value=False)]))

    for key in domain_rules.keys():
        list_of_atoms.append(ast.Constant(value=key))
        list_of_values.append(ast.Set(elts=derive_syntax_tree_for_set(domain_rules[key])))




    return ast.Assign(
         targets=[
            ast.Name(id=name, ctx=ast.Store())],
         value=ast.Dict(
            keys=list_of_atoms,
            values=list_of_values))




def generate_update_structure():
    return ast.FunctionDef(
        name='update_structure',
        args=ast.arguments(
            posonlyargs=[],
            args=[
                ast.arg(arg='changes')],
            kwonlyargs=[],
            kw_defaults=[],
            defaults=[]),
        body=[
            ast.For(
                target=ast.Tuple(
                    elts=[
                        ast.Name(id='key', ctx=ast.Store()),
                        ast.Name(id='value', ctx=ast.Store())],
                    ctx=ast.Store()),
                iter=ast.Call(
                    func=ast.Attribute(
                        value=ast.Name(id='changes', ctx=ast.Load()),
                        attr='items',
                        ctx=ast.Load()),
                    args=[],
                    keywords=[]),
                body=[
                    ast.Assign(
                        targets=[
                            ast.Subscript(
                                value=ast.Name(id='structure', ctx=ast.Load()),
                                slice=ast.Name(id='key', ctx=ast.Load()),
                                ctx=ast.Store())],
                        value=ast.Name(id='value', ctx=ast.Load()))],
                orelse=[])],
        decorator_list=[])


def generate_handle_reset():
    return ast.FunctionDef(
         name='handle_reset',
         args=ast.arguments(
            posonlyargs=[],
            args=[],
            kwonlyargs=[],
            kw_defaults=[],
            defaults=[]),
         body=[
            ast.For(
               target=ast.Tuple(
                  elts=[
                     ast.Name(id='key', ctx=ast.Store()),
                     ast.Name(id='value', ctx=ast.Store())],
                  ctx=ast.Store()),
               iter=ast.Call(
                  func=ast.Attribute(
                     value=ast.Name(id='initial_structure', ctx=ast.Load()),
                     attr='items',
                     ctx=ast.Load()),
                  args=[],
                  keywords=[]),
               body=[
                  ast.Assign(
                     targets=[
                        ast.Subscript(
                           value=ast.Name(id='structure', ctx=ast.Load()),
                           slice=ast.Name(id='key', ctx=ast.Load()),
                           ctx=ast.Store())],
                     value=ast.Subscript(
                        value=ast.Name(id='initial_structure', ctx=ast.Load()),
                        slice=ast.Name(id='key', ctx=ast.Load()),
                        ctx=ast.Load()))],
               orelse=[])],
         decorator_list=[])
def generate_print_structure():
    return ast.FunctionDef(
         name='print_structure',
         args=ast.arguments(
            posonlyargs=[],
            args=[],
            kwonlyargs=[],
            kw_defaults=[],
            defaults=[]),
         body=[
            ast.For(
               target=ast.Name(id='key', ctx=ast.Store()),
               iter=ast.Call(
                  func=ast.Attribute(
                     value=ast.Name(id='structure', ctx=ast.Load()),
                     attr='keys',
                     ctx=ast.Load()),
                  args=[],
                  keywords=[]),
               body=[
                  ast.If(
                     test=ast.UnaryOp(
                        op=ast.Not(),
                        operand=ast.Call(
                           func=ast.Attribute(
                              value=ast.Name(id='key', ctx=ast.Load()),
                              attr='startswith',
                              ctx=ast.Load()),
                           args=[
                              ast.Constant(value='_')],
                           keywords=[])),
                     body=[
                        ast.Expr(
                           value=ast.Call(
                              func=ast.Name(id='print', ctx=ast.Load()),
                              args=[
                                 ast.Name(id='key', ctx=ast.Load())],
                              keywords=[
                                 ast.keyword(
                                    arg='end',
                                    value=ast.Constant(value=''))])),
                        ast.Expr(
                           value=ast.Call(
                              func=ast.Name(id='print', ctx=ast.Load()),
                              args=[
                                 ast.Constant(value=':  ')],
                              keywords=[
                                 ast.keyword(
                                    arg='end',
                                    value=ast.Constant(value=''))])),
                        ast.Expr(
                           value=ast.Call(
                              func=ast.Name(id='print', ctx=ast.Load()),
                              args=[
                                 ast.Subscript(
                                    value=ast.Name(id='structure', ctx=ast.Load()),
                                    slice=ast.Name(id='key', ctx=ast.Load()),
                                    ctx=ast.Load())],
                              keywords=[])),
                        ast.Expr(
                           value=ast.Call(
                              func=ast.Name(id='print', ctx=ast.Load()),
                              args=[],
                              keywords=[]))],
                     orelse=[])],
               orelse=[])],
         decorator_list=[])


def generate_check_unsat_fields():
    return ast.FunctionDef(
         name='check_unsat_fields',
         args=ast.arguments(
            posonlyargs=[],
            args=[
               ast.arg(arg='changes')],
            kwonlyargs=[],
            kw_defaults=[],
            defaults=[]),
         body=[
            ast.Assign(
               targets=[
                  ast.Name(id='unsat_fields', ctx=ast.Store())],
               value=ast.Call(
                  func=ast.Name(id='set', ctx=ast.Load()),
                  args=[],
                  keywords=[])),
            ast.For(
               target=ast.Name(id='key', ctx=ast.Store()),
               iter=ast.Call(
                  func=ast.Attribute(
                     value=ast.Name(id='changes', ctx=ast.Load()),
                     attr='keys',
                     ctx=ast.Load()),
                  args=[],
                  keywords=[]),
               body=[
                  ast.If(
                     test=ast.Compare(
                        left=ast.Call(
                           func=ast.Name(id='len', ctx=ast.Load()),
                           args=[
                              ast.Subscript(
                                 value=ast.Name(id='changes', ctx=ast.Load()),
                                 slice=ast.Name(id='key', ctx=ast.Load()),
                                 ctx=ast.Load())],
                           keywords=[]),
                        ops=[
                           ast.Eq()],
                        comparators=[
                           ast.Constant(value=0)]),
                     body=[
                        ast.Expr(
                           value=ast.Call(
                              func=ast.Attribute(
                                 value=ast.Name(id='unsat_fields', ctx=ast.Load()),
                                 attr='add',
                                 ctx=ast.Load()),
                              args=[
                                 ast.Name(id='key', ctx=ast.Load())],
                              keywords=[]))],
                     orelse=[])],
               orelse=[]),
            ast.Return(
               value=ast.Name(id='unsat_fields', ctx=ast.Load()))],
         decorator_list=[])


def generate_intersect_changes():
    return ast.FunctionDef(
         name='intersect_changes',
         args=ast.arguments(
            posonlyargs=[],
            args=[
               ast.arg(arg='changes')],
            kwonlyargs=[],
            kw_defaults=[],
            defaults=[]),
         body=[
            ast.Assign(
               targets=[
                  ast.Name(id='intersected_changes', ctx=ast.Store())],
               value=ast.Dict(keys=[], values=[])),
            ast.For(
               target=ast.Name(id='key', ctx=ast.Store()),
               iter=ast.Call(
                  func=ast.Attribute(
                     value=ast.Name(id='changes', ctx=ast.Load()),
                     attr='keys',
                     ctx=ast.Load()),
                  args=[],
                  keywords=[]),
               body=[
                  ast.If(
                     test=ast.Compare(
                        left=ast.Call(
                           func=ast.Name(id='len', ctx=ast.Load()),
                           args=[
                              ast.Subscript(
                                 value=ast.Name(id='changes', ctx=ast.Load()),
                                 slice=ast.Name(id='key', ctx=ast.Load()),
                                 ctx=ast.Load())],
                           keywords=[]),
                        ops=[
                           ast.Gt()],
                        comparators=[
                           ast.Constant(value=0)]),
                     body=[
                        ast.Assign(
                           targets=[
                              ast.Subscript(
                                 value=ast.Name(id='intersected_changes', ctx=ast.Load()),
                                 slice=ast.Name(id='key', ctx=ast.Load()),
                                 ctx=ast.Store())],
                           value=ast.Call(
                              func=ast.Attribute(
                                 value=ast.Subscript(
                                    value=ast.Name(id='changes', ctx=ast.Load()),
                                    slice=ast.Name(id='key', ctx=ast.Load()),
                                    ctx=ast.Load()),
                                 attr='pop',
                                 ctx=ast.Load()),
                              args=[],
                              keywords=[])),
                        ast.While(
                           test=ast.Compare(
                              left=ast.Call(
                                 func=ast.Name(id='len', ctx=ast.Load()),
                                 args=[
                                    ast.Subscript(
                                       value=ast.Name(id='changes', ctx=ast.Load()),
                                       slice=ast.Name(id='key', ctx=ast.Load()),
                                       ctx=ast.Load())],
                                 keywords=[]),
                              ops=[
                                 ast.Gt()],
                              comparators=[
                                 ast.Constant(value=0)]),
                           body=[
                              ast.Assign(
                                 targets=[
                                    ast.Subscript(
                                       value=ast.Name(id='intersected_changes', ctx=ast.Load()),
                                       slice=ast.Name(id='key', ctx=ast.Load()),
                                       ctx=ast.Store())],
                                 value=ast.Call(
                                    func=ast.Attribute(
                                       value=ast.Subscript(
                                          value=ast.Name(id='intersected_changes', ctx=ast.Load()),
                                          slice=ast.Name(id='key', ctx=ast.Load()),
                                          ctx=ast.Load()),
                                       attr='intersection',
                                       ctx=ast.Load()),
                                    args=[
                                       ast.Call(
                                          func=ast.Attribute(
                                             value=ast.Subscript(
                                                value=ast.Name(id='changes', ctx=ast.Load()),
                                                slice=ast.Name(id='key', ctx=ast.Load()),
                                                ctx=ast.Load()),
                                             attr='pop',
                                             ctx=ast.Load()),
                                          args=[],
                                          keywords=[])],
                                    keywords=[]))],
                           orelse=[]),
                        ast.If(
                           test=ast.Compare(
                              left=ast.Subscript(
                                 value=ast.Name(id='intersected_changes', ctx=ast.Load()),
                                 slice=ast.Name(id='key', ctx=ast.Load()),
                                 ctx=ast.Load()),
                              ops=[
                                 ast.Eq()],
                              comparators=[
                                 ast.Subscript(
                                    value=ast.Name(id='structure', ctx=ast.Load()),
                                    slice=ast.Name(id='key', ctx=ast.Load()),
                                    ctx=ast.Load())]),
                           body=[
                              ast.Delete(
                                 targets=[
                                    ast.Subscript(
                                       value=ast.Name(id='intersected_changes', ctx=ast.Load()),
                                       slice=ast.Name(id='key', ctx=ast.Load()),
                                       ctx=ast.Del())])],
                           orelse=[])],
                     orelse=[])],
               orelse=[]),
            ast.Return(
               value=ast.Name(id='intersected_changes', ctx=ast.Load()))],
         decorator_list=[])

def generate_feedback_loop_with_contradiction_check():
    return ast.Module(
   body=[
      ast.Assign(
         targets=[
            ast.Name(id='quit', ctx=ast.Store())],
         value=ast.Constant(value=False)),
      ast.Assign(
         targets=[
            ast.Name(id='unsat_fields', ctx=ast.Store())],
         value=ast.Call(
            func=ast.Name(id='propagation_loop', ctx=ast.Load()),
            args=[
               ast.Name(id='structure', ctx=ast.Load())],
            keywords=[])),
      ast.If(
         test=ast.Compare(
            left=ast.Call(
               func=ast.Name(id='len', ctx=ast.Load()),
               args=[
                  ast.Name(id='unsat_fields', ctx=ast.Load())],
               keywords=[]),
            ops=[
               ast.Gt()],
            comparators=[
               ast.Constant(value=0)]),
         body=[
            ast.Expr(
               value=ast.Call(
                  func=ast.Name(id='print', ctx=ast.Load()),
                  args=[
                     ast.Constant(value='The initial problem is unsatisfiable: in particular, the following fields are unsatisfiable')],
                  keywords=[])),
            ast.For(
               target=ast.Name(id='field', ctx=ast.Store()),
               iter=ast.Name(id='unsat_fields', ctx=ast.Load()),
               body=[
                  ast.Expr(
                     value=ast.Call(
                        func=ast.Name(id='print', ctx=ast.Load()),
                        args=[
                           ast.Name(id='field', ctx=ast.Load())],
                        keywords=[]))],
               orelse=[]),
            ast.Assign(
               targets=[
                  ast.Name(id='quit', ctx=ast.Store())],
               value=ast.Constant(value=True))],
         orelse=[
            ast.Expr(
               value=ast.Call(
                  func=ast.Name(id='print', ctx=ast.Load()),
                  args=[
                     ast.Constant(value='Initial domains')],
                  keywords=[])),
            ast.Expr(
               value=ast.Call(
                  func=ast.Name(id='print_structure', ctx=ast.Load()),
                  args=[],
                  keywords=[]))]),
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
                  func=ast.Name(id='input', ctx=ast.Load()),
                  args=[
                     ast.Constant(value='Enter the value\n')],
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
                  ast.If(
                     test=ast.Compare(
                        left=ast.Call(
                           func=ast.Attribute(
                              value=ast.Name(id='value', ctx=ast.Load()),
                              attr='lower',
                              ctx=ast.Load()),
                           args=[],
                           keywords=[]),
                        ops=[
                           ast.Eq()],
                        comparators=[
                           ast.Constant(value='true')]),
                     body=[
                        ast.Assign(
                           targets=[
                              ast.Name(id='value', ctx=ast.Store())],
                           value=ast.Call(
                              func=ast.Attribute(
                                 value=ast.Subscript(
                                    value=ast.Name(id='structure', ctx=ast.Load()),
                                    slice=ast.Name(id='field', ctx=ast.Load()),
                                    ctx=ast.Load()),
                                 attr='intersection',
                                 ctx=ast.Load()),
                              args=[
                                 ast.Set(
                                    elts=[
                                       ast.Constant(value=True)])],
                              keywords=[]))],
                     orelse=[
                        ast.If(
                           test=ast.Compare(
                              left=ast.Call(
                                 func=ast.Attribute(
                                    value=ast.Name(id='value', ctx=ast.Load()),
                                    attr='lower',
                                    ctx=ast.Load()),
                                 args=[],
                                 keywords=[]),
                              ops=[
                                 ast.Eq()],
                              comparators=[
                                 ast.Constant(value='false')]),
                           body=[
                              ast.Assign(
                                 targets=[
                                    ast.Name(id='value', ctx=ast.Store())],
                                 value=ast.Call(
                                    func=ast.Attribute(
                                       value=ast.Subscript(
                                          value=ast.Name(id='structure', ctx=ast.Load()),
                                          slice=ast.Name(id='field', ctx=ast.Load()),
                                          ctx=ast.Load()),
                                       attr='intersection',
                                       ctx=ast.Load()),
                                    args=[
                                       ast.Set(
                                          elts=[
                                             ast.Constant(value=False)])],
                                    keywords=[]))],
                           orelse=[
                              ast.Assign(
                                 targets=[
                                    ast.Name(id='value', ctx=ast.Store())],
                                 value=ast.Call(
                                    func=ast.Attribute(
                                       value=ast.Subscript(
                                          value=ast.Name(id='structure', ctx=ast.Load()),
                                          slice=ast.Name(id='field', ctx=ast.Load()),
                                          ctx=ast.Load()),
                                       attr='intersection',
                                       ctx=ast.Load()),
                                    args=[
                                       ast.Set(
                                          elts=[
                                             ast.Call(
                                                func=ast.Name(id='int', ctx=ast.Load()),
                                                args=[
                                                   ast.Name(id='value', ctx=ast.Load())],
                                                keywords=[])])],
                                    keywords=[]))])]),
                  ast.Assign(
                     targets=[
                        ast.Name(id='changes', ctx=ast.Store())],
                     value=ast.Dict(
                        keys=[
                           ast.Name(id='field', ctx=ast.Load())],
                        values=[
                           ast.Name(id='value', ctx=ast.Load())])),
                  ast.Assign(
                     targets=[
                        ast.Name(id='unsat_fields', ctx=ast.Store())],
                     value=ast.Call(
                        func=ast.Name(id='propagation_loop', ctx=ast.Load()),
                        args=[
                           ast.Name(id='changes', ctx=ast.Load())],
                        keywords=[])),
                  ast.If(
                     test=ast.Compare(
                        left=ast.Call(
                           func=ast.Name(id='len', ctx=ast.Load()),
                           args=[
                              ast.Name(id='unsat_fields', ctx=ast.Load())],
                           keywords=[]),
                        ops=[
                           ast.Gt()],
                        comparators=[
                           ast.Constant(value=0)]),
                     body=[
                        ast.Expr(
                           value=ast.Call(
                              func=ast.Name(id='print', ctx=ast.Load()),
                              args=[
                                 ast.Constant(value='The following fields have become unsatisfiable')],
                              keywords=[])),
                        ast.For(
                           target=ast.Name(id='field', ctx=ast.Store()),
                           iter=ast.Name(id='unsat_fields', ctx=ast.Load()),
                           body=[
                              ast.Expr(
                                 value=ast.Call(
                                    func=ast.Name(id='print', ctx=ast.Load()),
                                    args=[
                                       ast.Name(id='field', ctx=ast.Load())],
                                    keywords=[]))],
                           orelse=[]),
                        ast.Assign(
                           targets=[
                              ast.Name(id='quit', ctx=ast.Store())],
                           value=ast.Constant(value=True))],
                     orelse=[
                        ast.Expr(
                           value=ast.Call(
                              func=ast.Name(id='print_structure', ctx=ast.Load()),
                              args=[],
                              keywords=[]))])])],
         orelse=[])],
   type_ignores=[])

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
                  func=ast.Name(id='input', ctx=ast.Load()),
                  args=[
                     ast.Constant(value='Enter the value\n')],
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
                  ast.If(
                     test=ast.Compare(
                        left=ast.Call(
                           func=ast.Attribute(
                              value=ast.Name(id='value', ctx=ast.Load()),
                              attr='lower',
                              ctx=ast.Load()),
                           args=[],
                           keywords=[]),
                        ops=[
                           ast.Eq()],
                        comparators=[
                           ast.Constant(value='true')]),
                     body=[
                        ast.Assign(
                           targets=[
                              ast.Name(id='value', ctx=ast.Store())],
                           value=ast.Constant(value=True))],
                     orelse=[ast.If(
                     test=ast.Compare(
                        left=ast.Call(
                           func=ast.Attribute(
                              value=ast.Name(id='value', ctx=ast.Load()),
                              attr='lower',
                              ctx=ast.Load()),
                           args=[],
                           keywords=[]),
                        ops=[
                           ast.Eq()],
                        comparators=[
                           ast.Constant(value='false')]),
                     body=[
                        ast.Assign(
                           targets=[
                              ast.Name(id='value', ctx=ast.Store())],
                           value=ast.Constant(value=False))],
                     orelse=[
                        ast.Assign(
                           targets=[
                              ast.Name(id='value', ctx=ast.Store())],
                           value=ast.Set(
                              elts=[
                                 ast.Call(
                                    func=ast.Name(id='int', ctx=ast.Load()),
                                    args=[
                                       ast.Name(id='value', ctx=ast.Load())],
                                    keywords=[])]))])]),
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



def generate_equality_conditions(equation, variable, equation_var=False):
    operators_map = {Operator.LT : ast.Lt(), Operator.GT : ast.Gt(), Operator.LEQ : ast.LtE(), Operator.GEQ : ast.GtE(), Operator.EQ : ast.Eq(), Operator.NEQ : ast.NotEq()}
    ast_operator = operators_map[equation.operator]
    if not equation_var:
        if type(equation.exp1) == parsing_idpz3.Atom and equation.exp1.name == variable:
            if type(equation.exp2) == Integer:
                integer_value = equation.exp2.name
                return ast.Call(
                func=ast.Name(id='all', ctx=ast.Load()),
                args=[
                   ast.GeneratorExp(
                      elt=ast.Compare(
                         left=ast.Name(id='elem', ctx=ast.Load()),
                         ops=[ast_operator],
                         comparators=[
                            ast.Constant(value=integer_value)]),
                      generators=[
                         ast.comprehension(
                            target=ast.Name(id='elem', ctx=ast.Store()),
                            iter=ast.Name(id='value', ctx=ast.Load()),
                            ifs=[],
                            is_async=0)])],
                keywords=[])
            elif type(equation.exp2) == parsing_idpz3.Atom:
                atom_name = equation.exp2.name
                return ast.Call(
                func=ast.Name(id='all', ctx=ast.Load()),
                args=[
                   ast.GeneratorExp(
                      elt=ast.Compare(
                         left=ast.Name(id='elem', ctx=ast.Load()),
                         ops=[ast_operator],
                         comparators=[
                            ast.Name(id='other_elem', ctx=ast.Load())]),
                      generators=[
                         ast.comprehension(
                            target=ast.Name(id='elem', ctx=ast.Store()),
                            iter=ast.Name(id='value', ctx=ast.Load()),
                            ifs=[],
                            is_async=0),
                         ast.comprehension(
                            target=ast.Name(id='other_elem', ctx=ast.Store()),
                            iter=ast.Subscript(
                               value=ast.Name(id='structure', ctx=ast.Load()),
                               slice=ast.Constant(value=atom_name),
                               ctx=ast.Load()),
                            ifs=[],
                            is_async=0)])],
                keywords=[])
    else:
        if equation.exp1.name == variable:
            other_var = equation.exp2.name

        elif equation.exp2.name == variable:
            other_var = equation.exp1.name

        appropriate_comparison = get_appropriate_comparison(equation.operator, other_var, True)
        return ast.UnaryOp(
            op=ast.Not(),
            operand=ast.Call(
                func=ast.Name(id='all', ctx=ast.Load()),
                args=[
                    ast.GeneratorExp(
                        elt=appropriate_comparison,
                        generators=[
                            ast.comprehension(
                                target=ast.Name(id='elem', ctx=ast.Store()),
                                iter=ast.Subscript(
                                    value=ast.Name(id='structure', ctx=ast.Load()),
                                    slice=ast.Constant(value=other_var),
                                    ctx=ast.Load()),
                                ifs=[],
                                is_async=0)])],
                keywords=[]))





def get_appropriate_comparison(operator, other_variable, value=False):
    if value:
        args = ast.Name(id='value', ctx=ast.Load())
    else:
        args = ast.Subscript(
                        value=ast.Name(id='structure', ctx=ast.Load()),
                        slice=ast.Constant(value=other_variable),
                        ctx=ast.Load())
    if operator == Operator.GEQ:
        return ast.Compare(
            left=ast.Name(id='elem', ctx=ast.Load()),
            ops=[
               ast.GtE()],
            comparators=[
               ast.Call(
                  func=ast.Name(id='min', ctx=ast.Load()),
                  args=[args],
                  keywords=[])])
    elif operator == Operator.GT:
        return ast.Compare(
            left=ast.Name(id='elem', ctx=ast.Load()),
            ops=[
               ast.Gt()],
            comparators=[
               ast.Call(
                  func=ast.Name(id='min', ctx=ast.Load()),
                  args=[args],
                  keywords=[])])
    elif operator == Operator.LEQ:
        return ast.Compare(
                left=ast.Name(id='elem', ctx=ast.Load()),
                ops=[
                    ast.LtE()],
                comparators=[
                    ast.Call(
                        func=ast.Name(id='max', ctx=ast.Load()),
                        args=[args],
                        keywords=[])])
    elif operator == Operator.LT:
        return ast.Compare(
                left=ast.Name(id='elem', ctx=ast.Load()),
                ops=[
                    ast.Lt()],
                comparators=[
                    ast.Call(
                        func=ast.Name(id='max', ctx=ast.Load()),
                        args=[args],
                        keywords=[])])
    elif operator == Operator.EQ:
        return ast.Compare(
                left=ast.Name(id='elem', ctx=ast.Load()),
                ops=[
                    ast.In()],
                comparators=[args])
    elif operator == Operator.NEQ:
        return ast.Expr(
            value=ast.BoolOp(
                op=ast.Or(),
                values=[
                    ast.Compare(
                        left=ast.Name(id='elem', ctx=ast.Load()),
                        ops=[
                            ast.NotIn()],
                        comparators=[args]),
                    ast.Compare(
                        left=ast.Call(
                            func=ast.Name(id='len', ctx=ast.Load()),
                            args=[args],
                            keywords=[]),
                        ops=[
                            ast.Gt()],
                        comparators=[
                            ast.Constant(value=1)])]))





def generate_equality_consequences(equation, variable):
    operators_map = {Operator.LT: ast.Lt(), Operator.GT: ast.Gt(), Operator.LEQ: ast.LtE(), Operator.GEQ: ast.GtE(),
                     Operator.EQ: ast.Eq(), Operator.NEQ: ast.NotEq()}
    ast_operator = operators_map[equation.operator]
    if type(equation.exp1) == parsing_idpz3.Atom and equation.exp1.name == variable:
        if type(equation.exp2) == Integer:
            integer_value = equation.exp2.name
            return ast.If(
                test=ast.UnaryOp(
                    op=ast.Not(),
                    operand=ast.Call(
                        func=ast.Name(id='all', ctx=ast.Load()),
                        args=[
                            ast.GeneratorExp(
                                elt=ast.Compare(
                                    left=ast.Name(id='elem', ctx=ast.Load()),
                                    ops=[ast_operator],
                                    comparators=[
                                        ast.Constant(value=integer_value)]),
                                generators=[
                                    ast.comprehension(
                                        target=ast.Name(id='elem', ctx=ast.Store()),
                                        iter=ast.Subscript(
                                            value=ast.Name(id='structure', ctx=ast.Load()),
                                            slice=ast.Constant(value=variable),
                                            ctx=ast.Load()),
                                        ifs=[],
                                        is_async=0)])],
                        keywords=[])),
                body=[
                    ast.Expr(
                    value=ast.Call(
                        func=ast.Attribute(
                            value=ast.Subscript(
                                value=ast.Name(id='new_changes', ctx=ast.Load()),
                                slice=ast.Constant(value=variable),
                                ctx=ast.Load()),
                            attr='append',
                            ctx=ast.Load()),
                        args=[ast.SetComp(
                            elt=ast.Name(id='elem', ctx=ast.Load()),
                            generators=[
                                ast.comprehension(
                                    target=ast.Name(id='elem', ctx=ast.Store()),
                                    iter=ast.Subscript(
                                        value=ast.Name(id='structure', ctx=ast.Load()),
                                        slice=ast.Constant(value=variable),
                                        ctx=ast.Load()),
                                    ifs=[
                                        ast.Compare(
                                            left=ast.Name(id='elem', ctx=ast.Load()),
                                            ops=[ast_operator],
                                            comparators=[
                                                ast.Constant(value=integer_value)])],
                                    is_async=0)])],
                    keywords=[]))],
                orelse=[])
        elif type(equation.exp2) == parsing_idpz3.Atom:
            atom_name = equation.exp2.name

            return ast.If(
                    test=ast.UnaryOp(
                        op=ast.Not(),
                        operand=ast.Call(
                            func=ast.Name(id='all', ctx=ast.Load()),
                            args=[
                                ast.GeneratorExp(
                                    elt=ast.Compare(
                                        left=ast.Name(id='elem', ctx=ast.Load()),
                                        ops=[ast_operator],
                                        comparators=[
                                            ast.Name(id='other_elem', ctx=ast.Load())]),
                                    generators=[
                                        ast.comprehension(
                                            target=ast.Name(id='elem', ctx=ast.Store()),
                                            iter=ast.Subscript(
                                                value=ast.Name(id='structure', ctx=ast.Load()),
                                                slice=ast.Constant(value=variable),
                                                ctx=ast.Load()),
                                            ifs=[],
                                            is_async=0),
                                        ast.comprehension(
                                            target=ast.Name(id='other_elem', ctx=ast.Store()),
                                            iter=ast.Subscript(
                                                value=ast.Name(id='structure', ctx=ast.Load()),
                                                slice=ast.Constant(value=atom_name),
                                                ctx=ast.Load()),
                                            ifs=[],
                                            is_async=0)])],
                            keywords=[])),
                    body=[
                            ast.Expr(
                                value=ast.Call(
                                    func=ast.Attribute(
                                        value=ast.Subscript(
                                            value=ast.Name(id='new_changes', ctx=ast.Load()),
                                            slice=ast.Constant(value=variable),
                                            ctx=ast.Load()),
                                        attr='append',
                                        ctx=ast.Load()),
                                    args=[ast.SetComp(
                                elt=ast.Name(id='elem', ctx=ast.Load()),
                                generators=[
                                    ast.comprehension(
                                        target=ast.Name(id='elem', ctx=ast.Store()),
                                        iter=ast.Subscript(
                                            value=ast.Name(id='structure', ctx=ast.Load()),
                                            slice=ast.Constant(value=variable),
                                            ctx=ast.Load()),
                                        ifs=[get_appropriate_comparison(equation.operator, atom_name)],
                                        is_async=0)])],
                                    keywords=[]))],
                    orelse=[])

def generate_condition_equality_consequences(propagator, var):
    eq = propagator.right
    if eq.exp1.name == var:
        other_var = eq.exp2.name
    elif eq.exp2.name == var:
        other_var = eq.exp1.name

    return ast.If(
         test=ast.Call(
            func=ast.Name(id='all', ctx=ast.Load()),
            args=[
               ast.GeneratorExp(
                  elt=ast.Compare(
                     left=ast.Name(id='elem', ctx=ast.Load()),
                     ops=[
                        ast.Eq()],
                     comparators=[
                        ast.Constant(value=propagator.left.pos)]),
                  generators=[
                     ast.comprehension(
                        target=ast.Name(id='elem', ctx=ast.Store()),
                        iter=ast.Subscript(
                           value=ast.Name(id='structure', ctx=ast.Load()),
                           slice=ast.Constant(value=propagator.left.atom),
                           ctx=ast.Load()),
                        ifs=[],
                        is_async=0)])],
            keywords=[]),
         body=[

             ast.Expr(
                 value=ast.Call(
                     func=ast.Attribute(
                         value=ast.Subscript(
                             value=ast.Name(id='new_changes', ctx=ast.Load()),
                             slice=ast.Constant(value=other_var),
                             ctx=ast.Load()),
                         attr='append',
                         ctx=ast.Load()),
                     args=[ast.SetComp(
                  elt=ast.Name(id='elem', ctx=ast.Load()),
                  generators=[
                     ast.comprehension(
                        target=ast.Name(id='elem', ctx=ast.Store()),
                        iter=ast.Subscript(
                           value=ast.Name(id='structure', ctx=ast.Load()),
                           slice=ast.Constant(value=other_var),
                           ctx=ast.Load()),
                        ifs=[get_appropriate_comparison(propagator.right.operator, var, True)],
                        is_async=0)])],
                     keywords=[]))],

         orelse=[])


def generate_if_statement(derived_propagator):
    if len(derived_propagator.middle) == 0:
        if type(derived_propagator.right) == parsing_idpz3.Literal:
            return ast.If(
         test=ast.UnaryOp(
            op=ast.Not(),
            operand=ast.Call(
               func=ast.Name(id='all', ctx=ast.Load()),
               args=[
                  ast.GeneratorExp(
                     elt=ast.Compare(
                        left=ast.Name(id='elem', ctx=ast.Load()),
                        ops=[
                           ast.Eq()],
                        comparators=[
                           ast.Constant(value=derived_propagator.right.pos)]),
                     generators=[
                        ast.comprehension(
                           target=ast.Name(id='elem', ctx=ast.Store()),
                           iter=ast.Subscript(
                              value=ast.Name(id='structure', ctx=ast.Load()),
                              slice=ast.Constant(value=derived_propagator.right.atom),
                              ctx=ast.Load()),
                           ifs=[],
                           is_async=0)])],
               keywords=[])),
         body=[
             ast.Expr(
                 value=ast.Call(
                     func=ast.Attribute(
                         value=ast.Subscript(
                             value=ast.Name(id='new_changes', ctx=ast.Load()),
                             slice=ast.Constant(value=derived_propagator.right.atom),
                             ctx=ast.Load()),
                         attr='append',
                         ctx=ast.Load()),
                     args=[ast.SetComp(
                  elt=ast.Name(id='elem', ctx=ast.Load()),
                  generators=[
                     ast.comprehension(
                        target=ast.Name(id='elem', ctx=ast.Store()),
                        iter=ast.Subscript(
                           value=ast.Name(id='structure', ctx=ast.Load()),
                           slice=ast.Constant(value=derived_propagator.right.atom),
                           ctx=ast.Load()),
                        ifs=[
                           ast.Compare(
                              left=ast.Name(id='elem', ctx=ast.Load()),
                              ops=[
                                 ast.Eq()],
                              comparators=[
                                 ast.Constant(value=derived_propagator.right.pos)])],
                        is_async=0)])],
                     keywords=[]))],
            orelse = [])



        elif type(derived_propagator.right) == Equation:
            return generate_equality_consequences(derived_propagator.right, derived_propagator.right.exp1.name)
    else:
        if type(derived_propagator.right) == parsing_idpz3.Literal:
            and_list = []
            for literal in derived_propagator.middle:
                and_list.append(ast.Call(
            func=ast.Name(id='all', ctx=ast.Load()),
            args=[
               ast.GeneratorExp(
                  elt=ast.Compare(
                     left=ast.Name(id='elem', ctx=ast.Load()),
                     ops=[
                        ast.Eq()],
                     comparators=[
                        ast.Constant(value=literal.pos)]),
                  generators=[
                     ast.comprehension(
                        target=ast.Name(id='elem', ctx=ast.Store()),
                        iter=ast.Subscript(
                           value=ast.Name(id='structure', ctx=ast.Load()),
                           slice=ast.Constant(value=literal.atom),
                           ctx=ast.Load()),
                        ifs=[],
                        is_async=0)])],
            keywords=[]))
            return ast.If(
             test=ast.UnaryOp(
            op=ast.Not(),
            operand=ast.Call(
               func=ast.Name(id='all', ctx=ast.Load()),
               args=[
                  ast.GeneratorExp(
                     elt=ast.Compare(
                        left=ast.Name(id='elem', ctx=ast.Load()),
                        ops=[
                           ast.Eq()],
                        comparators=[
                           ast.Constant(value=derived_propagator.right.pos)]),
                     generators=[
                        ast.comprehension(
                           target=ast.Name(id='elem', ctx=ast.Store()),
                           iter=ast.Subscript(
                              value=ast.Name(id='structure', ctx=ast.Load()),
                              slice=ast.Constant(value=derived_propagator.right.atom),
                              ctx=ast.Load()),
                           ifs=[],
                           is_async=0)])],
               keywords=[])),
             body=[
                 ast.If(
                     test=ast.BoolOp(
                         op=ast.And(),
                         values=and_list),
                     body=[
                         ast.Expr(
                             value=ast.Call(
                                 func=ast.Attribute(
                                     value=ast.Subscript(
                                         value=ast.Name(id='new_changes', ctx=ast.Load()),
                                         slice=ast.Constant(value=derived_propagator.right.atom),
                                         ctx=ast.Load()),
                                     attr='append',
                                     ctx=ast.Load()),
                                 args=[ast.SetComp(
                                     elt=ast.Name(id='elem', ctx=ast.Load()),
                                     generators=[
                                         ast.comprehension(
                                             target=ast.Name(id='elem', ctx=ast.Store()),
                                             iter=ast.Subscript(
                                                 value=ast.Name(id='structure', ctx=ast.Load()),
                                                 slice=ast.Constant(value=derived_propagator.right.atom),
                                                 ctx=ast.Load()),
                                             ifs=[
                                                 ast.Compare(
                                                     left=ast.Name(id='elem', ctx=ast.Load()),
                                                     ops=[
                                                         ast.Eq()],
                                                     comparators=[
                                                         ast.Constant(value=derived_propagator.right.pos)])],
                                             is_async=0)])],
                                 keywords=[]))
                     ],
                     orelse=[])],
                orelse=[])





def group_derived_props(derived_props):
    grouped = {}
    for derived_prop in derived_props:
        if derived_prop.left == None:
            if None not in grouped.keys():
                grouped[None] = {derived_prop}
            else:
                grouped[None].add(derived_prop)
        if type(derived_prop.left) == parsing_idpz3.Literal:
            if derived_prop.left.atom not in grouped.keys():
                grouped[derived_prop.left.atom] = {derived_prop.left.pos : {derived_prop}}
            else:
                if derived_prop.left.pos not in grouped[derived_prop.left.atom].keys():
                    grouped[derived_prop.left.atom][derived_prop.left.pos] = {derived_prop}
                else:
                    grouped[derived_prop.left.atom][derived_prop.left.pos].add(derived_prop)
        elif type(derived_prop.left) == Equation:
            if derived_prop.left.exp1.name not in grouped.keys():
                grouped[derived_prop.left.exp1.name] = {(derived_prop.left.operator, derived_prop.left.exp2.name) : {derived_prop}}
            else:
                if (derived_prop.left.operator, derived_prop.left.exp2.name) not in grouped[derived_prop.left.exp1.name].keys():
                    grouped[derived_prop.left.exp1.name][(derived_prop.left.operator, derived_prop.left.exp2.name)] = {derived_prop}
                else:
                    grouped[derived_prop.left.exp1.name][(derived_prop.left.operator, derived_prop.left.exp2.name)].add(derived_prop)
        elif type(derived_prop) == EquationPropagator:
            if derived_prop.left.name not in grouped.keys():
               grouped[derived_prop.left.name] = {(derived_prop.middle[0].atom, derived_prop.middle[0].pos): {derived_prop}}
            else:
                if (derived_prop.middle[0].atom, derived_prop.middle[0].pos) not in grouped[derived_prop.left.name].keys():
                    grouped[derived_prop.left.name][(derived_prop.middle[0].atom, derived_prop.middle[0].pos)] = {derived_prop}
                else:
                    grouped[derived_prop.left.name][(derived_prop.middle[0].atom, derived_prop.middle[0].pos)].add(derived_prop)



    return grouped



def generate_equality_tests(atom, propagators):
    if_statements = []
    if_statements_for_key = []
    for key in propagators.keys():

        for i, propagator in enumerate(propagators[key]):
            if type(propagator) == DerivedPropagator:
                new_if_statement_for_key = ast.If(test=generate_equality_conditions(propagator.left, atom), body=generate_if_statement(propagator), orelse=[])
                if_statements_for_key.append(new_if_statement_for_key)
            elif type(propagator) == EquationPropagator:
                if i == 0:
                    new_propagator = DerivedPropagator(propagator.middle[0], [], propagator.right.switch())
                    new_if_statement_for_key = ast.If(test=generate_equality_conditions(propagator.right.switch(), atom, True), body=generate_condition_equality_consequences(new_propagator, atom), orelse=[])
                    if_statements_for_key.append(new_if_statement_for_key)
    new_if_statement = ast.If(
        test=ast.Compare(
            left=ast.Name(id='key', ctx=ast.Load()),
            ops=[
                ast.Eq()],
            comparators=[
                ast.Constant(value=atom)]), body=if_statements_for_key, orelse=[])
    if_statements.append(new_if_statement)
    return if_statements



def generate_unconditional_statement(propagator):
    if type(propagator.right) == parsing_idpz3.Literal:
        return ast.If(
         test=ast.Compare(
            left=ast.Name(id='key', ctx=ast.Load()),
            ops=[
               ast.NotEq()],
            comparators=[
               ast.Constant(value=propagator.right.atom)]),
         body=[
            generate_if_statement(propagator)],
        orelse=[])
    elif type(propagator.right) == Equation:
        return ast.If(
            test=ast.Compare(
                left=ast.Name(id='key', ctx=ast.Load()),
                ops=[
                    ast.NotEq()],
                comparators=[
                    ast.Constant(value=propagator.right.exp1.name)]),
            body=[
                generate_if_statement(propagator)],
        orelse=[])



def generate_atom_tests(atom, propagators):
    true_if_statements = []
    false_if_statements = []
    if True in propagators.keys():
        for prop in propagators[True]:
            true_if_statements.append(generate_if_statement(prop))
    else:
        true_if_statements.append(ast.Pass())
    if False in propagators.keys():
        for prop in propagators[False]:
            false_if_statements.append(generate_if_statement(prop))
    else:
        false_if_statements.append(ast.Pass())

    return ast.If(
         test=ast.Compare(
            left=ast.Name(id='key', ctx=ast.Load()),
            ops=[
               ast.Eq()],
            comparators=[
               ast.Constant(value=atom)]),
         body=[
            ast.If(
               test=ast.Call(
                  func=ast.Name(id='all', ctx=ast.Load()),
                  args=[
                     ast.GeneratorExp(
                        elt=ast.Compare(
                           left=ast.Name(id='elem', ctx=ast.Load()),
                           ops=[
                              ast.Eq()],
                           comparators=[
                              ast.Constant(value=True)]),
                        generators=[
                           ast.comprehension(
                              target=ast.Name(id='elem', ctx=ast.Store()),
                              iter=ast.Name(id='value', ctx=ast.Load()),
                              ifs=[],
                              is_async=0)])],
                  keywords=[]),
               body=[
                  true_if_statements],
               orelse=[
                  ast.If(
                     test=ast.Call(
                        func=ast.Name(id='all', ctx=ast.Load()),
                        args=[
                           ast.GeneratorExp(
                              elt=ast.Compare(
                                 left=ast.Name(id='elem', ctx=ast.Load()),
                                 ops=[
                                    ast.Eq()],
                                 comparators=[
                                    ast.Constant(value=False)]),
                              generators=[
                                 ast.comprehension(
                                    target=ast.Name(id='elem', ctx=ast.Store()),
                                    iter=ast.Name(id='value', ctx=ast.Load()),
                                    ifs=[],
                                    is_async=0)])],
                        keywords=[]),
                     body=[
                        false_if_statements],
                     orelse=[])])],
         orelse=[])



def generate_propagate(derived_props):
    if_statements = []
    unconditional_statements = []
    grouped = group_derived_props(derived_props)
    for atom in grouped.keys():
        if atom == None:
            for derived_prop in grouped[atom]:
                unconditional_statements.append(generate_if_statement(derived_prop))
        else:
            if True in grouped[atom].keys() or False in grouped[atom].keys():
                if_statements.append(generate_atom_tests(atom, grouped[atom]))
            else:
                if_statements.append(generate_equality_tests(atom, grouped[atom]))
    return ast.FunctionDef(
         name='propagate',
         args=ast.arguments(
            posonlyargs=[],
            args=[
               ast.arg(arg='changes')],
            kwonlyargs=[],
            kw_defaults=[],
            defaults=[]),
         body=[
             ast.Assign(
                 targets=[
                     ast.Name(id='new_changes', ctx=ast.Store())],
                 value=ast.DictComp(
                     key=ast.Name(id='key', ctx=ast.Load()),
                     value=ast.List(elts=[], ctx=ast.Load()),
                     generators=[
                         ast.comprehension(
                             target=ast.Name(id='key', ctx=ast.Store()),
                             iter=ast.Call(
                                 func=ast.Attribute(
                                     value=ast.Name(id='structure', ctx=ast.Load()),
                                     attr='keys',
                                     ctx=ast.Load()),
                                 args=[],
                                 keywords=[]),
                             ifs=[],
                             is_async=0)])),
            ast.For(
               target=ast.Tuple(
                  elts=[
                     ast.Name(id='key', ctx=ast.Store()),
                     ast.Name(id='value', ctx=ast.Store())],
                  ctx=ast.Store()),
               iter=ast.Call(
                  func=ast.Attribute(
                     value=ast.Name(id='changes', ctx=ast.Load()),
                     attr='items',
                     ctx=ast.Load()),
                  args=[],
                  keywords=[]),
               body=[unconditional_statements, if_statements],
                orelse=[]),
             ast.Return(
                 value=ast.Call(
                     func=ast.Name(id='intersect_changes', ctx=ast.Load()),
                     args=[
                         ast.Name(id='new_changes', ctx=ast.Load())],
                     keywords=[]))
         ],
        decorator_list=[])


def generate_propagation_loop_with_contradiction_check():
    return ast.FunctionDef(
         name='propagation_loop',
         args=ast.arguments(
            posonlyargs=[],
            args=[
               ast.arg(arg='changes')],
            kwonlyargs=[],
            kw_defaults=[],
            defaults=[]),
         body=[
            ast.Assign(
               targets=[
                  ast.Name(id='unsat_fields', ctx=ast.Store())],
               value=ast.Call(
                  func=ast.Name(id='check_unsat_fields', ctx=ast.Load()),
                  args=[
                     ast.Name(id='changes', ctx=ast.Load())],
                  keywords=[])),
            ast.While(
               test=ast.BoolOp(
                  op=ast.And(),
                  values=[
                     ast.Compare(
                        left=ast.Call(
                           func=ast.Name(id='len', ctx=ast.Load()),
                           args=[
                              ast.Name(id='changes', ctx=ast.Load())],
                           keywords=[]),
                        ops=[
                           ast.NotEq()],
                        comparators=[
                           ast.Constant(value=0)]),
                     ast.Compare(
                        left=ast.Call(
                           func=ast.Name(id='len', ctx=ast.Load()),
                           args=[
                              ast.Name(id='unsat_fields', ctx=ast.Load())],
                           keywords=[]),
                        ops=[
                           ast.Eq()],
                        comparators=[
                           ast.Constant(value=0)])]),
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
                        keywords=[])),
                  ast.Assign(
                     targets=[
                        ast.Name(id='unsat_fields', ctx=ast.Store())],
                     value=ast.Call(
                        func=ast.Name(id='check_unsat_fields', ctx=ast.Load()),
                        args=[
                           ast.Name(id='changes', ctx=ast.Load())],
                        keywords=[]))],
               orelse=[]),
            ast.Return(
               value=ast.Name(id='unsat_fields', ctx=ast.Load()))],
         decorator_list=[])
def generate_propagate_loop():
    return ast.FunctionDef(
         name='propagate_loop',
         args=ast.arguments(
            posonlyargs=[],
            args=[
               ast.arg(arg='field'),
               ast.arg(arg='value')],
            kwonlyargs=[],
            kw_defaults=[],
            defaults=[]),
         body=[
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
               orelse=[])],
        decorator_list=[])



def generate_get_dropdown_options():
    return ast.FunctionDef(
        name='get_dropdown_options',
        args=ast.arguments(
            posonlyargs=[],
            args=[
                ast.arg(arg='integer_list')],
            kwonlyargs=[],
            kw_defaults=[],
            defaults=[]),
        body=[
            ast.Assign(
                targets=[
                    ast.Name(id='options_list', ctx=ast.Store())],
                value=ast.List(elts=[], ctx=ast.Load())),
            ast.For(
                target=ast.Name(id='i', ctx=ast.Store()),
                iter=ast.Name(id='integer_list', ctx=ast.Load()),
                body=[
                    ast.Expr(
                        value=ast.Call(
                            func=ast.Attribute(
                                value=ast.Name(id='options_list', ctx=ast.Load()),
                                attr='append',
                                ctx=ast.Load()),
                            args=[
                                ast.Dict(
                                    keys=[
                                        ast.Constant(value='label'),
                                        ast.Constant(value='value')],
                                    values=[
                                        ast.Call(
                                            func=ast.Name(id='str', ctx=ast.Load()),
                                            args=[
                                                ast.Name(id='i', ctx=ast.Load())],
                                            keywords=[]),
                                        ast.Name(id='i', ctx=ast.Load())])],
                            keywords=[]))],
                orelse=[]),
            ast.Return(
                value=ast.Name(id='options_list', ctx=ast.Load()))],
        decorator_list=[])


def generate_convert_to_ui():
    return ast.FunctionDef(
         name='convert_to_ui',
         args=ast.arguments(
            posonlyargs=[],
            args=[
               ast.arg(arg='values')],
            kwonlyargs=[],
            kw_defaults=[],
            defaults=[]),
         body=[
            ast.If(
               test=ast.Compare(
                  left=ast.Name(id='values', ctx=ast.Load()),
                  ops=[
                     ast.Eq()],
                  comparators=[
                     ast.Set(
                        elts=[
                           ast.Constant(value=True),
                           ast.Constant(value=False)])]),
               body=[
                  ast.Return(
                     value=ast.List(elts=[], ctx=ast.Load()))],
               orelse=[]),
            ast.If(
               test=ast.Compare(
                  left=ast.Name(id='values', ctx=ast.Load()),
                  ops=[
                     ast.Eq()],
                  comparators=[
                     ast.Set(
                        elts=[
                           ast.Constant(value=True)])]),
               body=[
                  ast.Return(
                     value=ast.List(
                        elts=[
                           ast.Constant(value=True)],
                        ctx=ast.Load()))],
               orelse=[]),
            ast.If(
               test=ast.Compare(
                  left=ast.Name(id='values', ctx=ast.Load()),
                  ops=[
                     ast.Eq()],
                  comparators=[
                     ast.Set(
                        elts=[
                           ast.Constant(value=False)])]),
               body=[
                  ast.Return(
                     value=ast.List(
                        elts=[
                           ast.Constant(value=False)],
                        ctx=ast.Load()))],
               orelse=[
                  ast.Return(
                     value=ast.Call(
                        func=ast.Name(id='get_dropdown_options', ctx=ast.Load()),
                        args=[
                           ast.Name(id='values', ctx=ast.Load())],
                        keywords=[]))])],
         decorator_list=[])



def generate_convert_from_ui():
    return ast.FunctionDef(
        name='convert_from_ui',
        args=ast.arguments(
            posonlyargs=[],
            args=[
                ast.arg(arg='values')],
            kwonlyargs=[],
            kw_defaults=[],
            defaults=[]),
        body=[
            ast.If(
                test=ast.BoolOp(
                    op=ast.Or(),
                    values=[
                        ast.Compare(
                            left=ast.Name(id='values', ctx=ast.Load()),
                            ops=[
                                ast.Eq()],
                            comparators=[
                                ast.List(
                                    elts=[
                                        ast.Constant(value=True),
                                        ast.Constant(value=False)],
                                    ctx=ast.Load())]),
                        ast.Compare(
                            left=ast.Name(id='values', ctx=ast.Load()),
                            ops=[
                                ast.Eq()],
                            comparators=[
                                ast.List(
                                    elts=[
                                        ast.Constant(value=False),
                                        ast.Constant(value=True)],
                                    ctx=ast.Load())])]),
                body=[
                    ast.Return(
                        value=ast.Call(
                            func=ast.Name(id='set', ctx=ast.Load()),
                            args=[],
                            keywords=[]))],
                orelse=[]),
            ast.If(
                test=ast.Compare(
                    left=ast.Name(id='values', ctx=ast.Load()),
                    ops=[
                        ast.Eq()],
                    comparators=[
                        ast.List(
                            elts=[
                                ast.Constant(value=True)],
                            ctx=ast.Load())]),
                body=[
                    ast.Return(
                        value=ast.Set(
                            elts=[
                                ast.Constant(value=True)]))],
                orelse=[]),
            ast.If(
                test=ast.Compare(
                    left=ast.Name(id='values', ctx=ast.Load()),
                    ops=[
                        ast.Eq()],
                    comparators=[
                        ast.List(
                            elts=[
                                ast.Constant(value=False)],
                            ctx=ast.Load())]),
                body=[
                    ast.Return(
                        value=ast.Set(
                            elts=[
                                ast.Constant(value=False)]))],
                orelse=[
                    ast.Return(
                        value=ast.Constant(value=None))])],
        decorator_list=[])

def generate_unsat_message():
    return ast.FunctionDef(
        name='unsat_message',
        args=ast.arguments(
            posonlyargs=[],
            args=[
                ast.arg(arg='unsat_values')],
            kwonlyargs=[],
            kw_defaults=[],
            defaults=[]),
        body=[
            ast.Assign(
                targets=[
                    ast.Name(id='unsat_str', ctx=ast.Store())],
                value=ast.Constant(value='UNSAT: inconsistencies were detected in the following fields: ')),
            ast.For(
                target=ast.Name(id='unsat_val', ctx=ast.Store()),
                iter=ast.Name(id='unsat_values', ctx=ast.Load()),
                body=[
                    ast.AugAssign(
                        target=ast.Name(id='unsat_str', ctx=ast.Store()),
                        op=ast.Add(),
                        value=ast.BinOp(
                            left=ast.Name(id='unsat_val', ctx=ast.Load()),
                            op=ast.Add(),
                            right=ast.Constant(value=' ')))],
                orelse=[]),
            ast.AugAssign(
                target=ast.Name(id='unsat_str', ctx=ast.Store()),
                op=ast.Add(),
                value=ast.Constant(value='. Please reset the application.')),
            ast.Return(
                value=ast.Name(id='unsat_str', ctx=ast.Load()))],
        decorator_list=[])


def generate_launch_dash_app():
    return ast.Module(
   body=[
      ast.FunctionDef(
         name='launch_dash_app',
         args=ast.arguments(
            posonlyargs=[],
            args=[],
            kwonlyargs=[],
            kw_defaults=[],
            defaults=[]),
         body=[
            ast.Assign(
               targets=[
                  ast.Name(id='app', ctx=ast.Store())],
               value=ast.Call(
                  func=ast.Name(id='Dash', ctx=ast.Load()),
                  args=[
                     ast.Name(id='__name__', ctx=ast.Load())],
                  keywords=[])),
            ast.Assign(
               targets=[
                  ast.Name(id='boolean_variables', ctx=ast.Store())],
               value=ast.ListComp(
                  elt=ast.Name(id='var', ctx=ast.Load()),
                  generators=[
                     ast.comprehension(
                        target=ast.Name(id='var', ctx=ast.Store()),
                        iter=ast.Call(
                           func=ast.Attribute(
                              value=ast.Name(id='structure', ctx=ast.Load()),
                              attr='keys',
                              ctx=ast.Load()),
                           args=[],
                           keywords=[]),
                        ifs=[
                           ast.BoolOp(
                              op=ast.And(),
                              values=[
                                 ast.Compare(
                                    left=ast.Subscript(
                                       value=ast.Name(id='structure', ctx=ast.Load()),
                                       slice=ast.Name(id='var', ctx=ast.Load()),
                                       ctx=ast.Load()),
                                    ops=[
                                       ast.Eq()],
                                    comparators=[
                                       ast.Set(
                                          elts=[
                                             ast.Constant(value=True),
                                             ast.Constant(value=False)])]),
                                 ast.UnaryOp(
                                    op=ast.Not(),
                                    operand=ast.Call(
                                       func=ast.Attribute(
                                          value=ast.Name(id='var', ctx=ast.Load()),
                                          attr='startswith',
                                          ctx=ast.Load()),
                                       args=[
                                          ast.Constant(value='_')],
                                       keywords=[]))])],
                        is_async=0)])),
            ast.Expr(
                 value=ast.Call(
                     func=ast.Attribute(
                         value=ast.Name(id='boolean_variables', ctx=ast.Load()),
                         attr='sort',
                         ctx=ast.Load()),
                     args=[],
                     keywords=[])),
       ast.Assign(
               targets=[
                  ast.Name(id='integer_variables', ctx=ast.Store())],
               value=ast.ListComp(
                  elt=ast.Name(id='var', ctx=ast.Load()),
                  generators=[
                     ast.comprehension(
                        target=ast.Name(id='var', ctx=ast.Store()),
                        iter=ast.Call(
                           func=ast.Attribute(
                              value=ast.Name(id='structure', ctx=ast.Load()),
                              attr='keys',
                              ctx=ast.Load()),
                           args=[],
                           keywords=[]),
                        ifs=[
                           ast.Compare(
                              left=ast.Subscript(
                                 value=ast.Name(id='structure', ctx=ast.Load()),
                                 slice=ast.Name(id='var', ctx=ast.Load()),
                                 ctx=ast.Load()),
                              ops=[
                                 ast.NotEq()],
                              comparators=[
                                 ast.Set(
                                    elts=[
                                       ast.Constant(value=True),
                                       ast.Constant(value=False)])])],
                        is_async=0)])),
            ast.Assign(
               targets=[
                  ast.Attribute(
                     value=ast.Name(id='app', ctx=ast.Load()),
                     attr='layout',
                     ctx=ast.Store())],
               value=ast.Call(
                  func=ast.Attribute(
                     value=ast.Name(id='html', ctx=ast.Load()),
                     attr='Div',
                     ctx=ast.Load()),
                  args=[
                     ast.List(
                        elts=[
                           ast.Call(
                              func=ast.Attribute(
                                 value=ast.Name(id='html', ctx=ast.Load()),
                                 attr='H1',
                                 ctx=ast.Load()),
                              args=[
                                 ast.Constant(value='Interactive configuration')],
                              keywords=[]),
                           ast.Call(
                              func=ast.Attribute(
                                 value=ast.Name(id='html', ctx=ast.Load()),
                                 attr='Button',
                                 ctx=ast.Load()),
                              args=[
                                 ast.Constant(value='Reset')],
                              keywords=[
                                 ast.keyword(
                                    arg='id',
                                    value=ast.Constant(value='reset-button')),
                                 ast.keyword(
                                    arg='n_clicks',
                                    value=ast.Constant(value=0))]),
                           ast.Call(
                              func=ast.Attribute(
                                 value=ast.Name(id='html', ctx=ast.Load()),
                                 attr='Div',
                                 ctx=ast.Load()),
                              args=[
                                 ast.ListComp(
                                    elt=ast.Call(
                                       func=ast.Attribute(
                                          value=ast.Name(id='html', ctx=ast.Load()),
                                          attr='Div',
                                          ctx=ast.Load()),
                                       args=[
                                          ast.List(
                                             elts=[
                                                ast.Call(
                                                   func=ast.Attribute(
                                                      value=ast.Name(id='html', ctx=ast.Load()),
                                                      attr='Label',
                                                      ctx=ast.Load()),
                                                   args=[
                                                      ast.JoinedStr(
                                                         values=[
                                                            ast.FormattedValue(
                                                               value=ast.Name(id='var', ctx=ast.Load()),
                                                               conversion=-1),
                                                            ast.Constant(value=':')])],
                                                   keywords=[]),
                                                ast.Call(
                                                   func=ast.Attribute(
                                                      value=ast.Name(id='dcc', ctx=ast.Load()),
                                                      attr='Checklist',
                                                      ctx=ast.Load()),
                                                   args=[],
                                                   keywords=[
                                                      ast.keyword(
                                                         arg='id',
                                                         value=ast.Dict(
                                                            keys=[
                                                               ast.Constant(value='type'),
                                                               ast.Constant(value='index')],
                                                            values=[
                                                               ast.Constant(value='checkboxes'),
                                                               ast.Name(id='var', ctx=ast.Load())])),
                                                      ast.keyword(
                                                         arg='options',
                                                         value=ast.List(
                                                            elts=[
                                                               ast.Dict(
                                                                  keys=[
                                                                     ast.Constant(value='label'),
                                                                     ast.Constant(value='value')],
                                                                  values=[
                                                                     ast.Constant(value='True'),
                                                                     ast.Constant(value=True)]),
                                                               ast.Dict(
                                                                  keys=[
                                                                     ast.Constant(value='label'),
                                                                     ast.Constant(value='value')],
                                                                  values=[
                                                                     ast.Constant(value='False'),
                                                                     ast.Constant(value=False)])],
                                                            ctx=ast.Load())),
                                                      ast.keyword(
                                                         arg='value',
                                                         value=ast.List(elts=[], ctx=ast.Load())),
                                                      ast.keyword(
                                                         arg='inline',
                                                         value=ast.Constant(value=True))]),
                                                ast.Call(
                                                   func=ast.Attribute(
                                                      value=ast.Name(id='html', ctx=ast.Load()),
                                                      attr='Div',
                                                      ctx=ast.Load()),
                                                   args=[],
                                                   keywords=[
                                                      ast.keyword(
                                                         arg='id',
                                                         value=ast.Dict(
                                                            keys=[
                                                               ast.Constant(value='type'),
                                                               ast.Constant(value='index')],
                                                            values=[
                                                               ast.Constant(value='output'),
                                                               ast.Name(id='var', ctx=ast.Load())]))])],
                                             ctx=ast.Load())],
                                       keywords=[]),
                                    generators=[
                                       ast.comprehension(
                                          target=ast.Name(id='var', ctx=ast.Store()),
                                          iter=ast.Name(id='boolean_variables', ctx=ast.Load()),
                                          ifs=[],
                                          is_async=0)])],
                              keywords=[]),
                           ast.Call(
                              func=ast.Attribute(
                                 value=ast.Name(id='html', ctx=ast.Load()),
                                 attr='Div',
                                 ctx=ast.Load()),
                              args=[
                                 ast.ListComp(
                                    elt=ast.Call(
                                       func=ast.Attribute(
                                          value=ast.Name(id='html', ctx=ast.Load()),
                                          attr='Div',
                                          ctx=ast.Load()),
                                       args=[
                                          ast.List(
                                             elts=[
                                                ast.Call(
                                                   func=ast.Attribute(
                                                      value=ast.Name(id='html', ctx=ast.Load()),
                                                      attr='Label',
                                                      ctx=ast.Load()),
                                                   args=[
                                                      ast.JoinedStr(
                                                         values=[
                                                            ast.FormattedValue(
                                                               value=ast.Name(id='var', ctx=ast.Load()),
                                                               conversion=-1),
                                                            ast.Constant(value=':')])],
                                                   keywords=[]),
                                                ast.Call(
                                                   func=ast.Attribute(
                                                      value=ast.Name(id='dcc', ctx=ast.Load()),
                                                      attr='Dropdown',
                                                      ctx=ast.Load()),
                                                   args=[],
                                                   keywords=[
                                                      ast.keyword(
                                                         arg='id',
                                                         value=ast.Dict(
                                                            keys=[
                                                               ast.Constant(value='type'),
                                                               ast.Constant(value='index')],
                                                            values=[
                                                               ast.Constant(value='dropdown'),
                                                               ast.Name(id='var', ctx=ast.Load())])),
                                                      ast.keyword(
                                                         arg='options',
                                                         value=ast.Call(
                                                            func=ast.Name(id='get_dropdown_options', ctx=ast.Load()),
                                                            args=[
                                                               ast.Subscript(
                                                                  value=ast.Name(id='structure', ctx=ast.Load()),
                                                                  slice=ast.Name(id='var', ctx=ast.Load()),
                                                                  ctx=ast.Load())],
                                                            keywords=[])),
                                                      ast.keyword(
                                                         arg='placeholder',
                                                         value=ast.Constant(value='Select a number'))]),
                                                ast.Call(
                                                   func=ast.Attribute(
                                                      value=ast.Name(id='html', ctx=ast.Load()),
                                                      attr='Div',
                                                      ctx=ast.Load()),
                                                   args=[],
                                                   keywords=[
                                                      ast.keyword(
                                                         arg='id',
                                                         value=ast.Dict(
                                                            keys=[
                                                               ast.Constant(value='type'),
                                                               ast.Constant(value='index')],
                                                            values=[
                                                               ast.Constant(value='output'),
                                                               ast.Name(id='var', ctx=ast.Load())]))])],
                                             ctx=ast.Load())],
                                       keywords=[]),
                                    generators=[
                                       ast.comprehension(
                                          target=ast.Name(id='var', ctx=ast.Store()),
                                          iter=ast.Name(id='integer_variables', ctx=ast.Load()),
                                          ifs=[],
                                          is_async=0)])],
                              keywords=[]),
                           ast.Call(
                              func=ast.Attribute(
                                 value=ast.Name(id='html', ctx=ast.Load()),
                                 attr='Div',
                                 ctx=ast.Load()),
                              args=[
                                 ast.List(
                                    elts=[
                                       ast.Call(
                                          func=ast.Attribute(
                                             value=ast.Name(id='html', ctx=ast.Load()),
                                             attr='Div',
                                             ctx=ast.Load()),
                                          args=[],
                                          keywords=[
                                             ast.keyword(
                                                arg='id',
                                                value=ast.Dict(
                                                   keys=[
                                                      ast.Constant(value='type')],
                                                   values=[
                                                      ast.Constant(value='text-output')])),
                                             ast.keyword(
                                                arg='children',
                                                value=ast.Constant(value='No inconsistencies detected yet'))])],
                                    ctx=ast.Load())],
                              keywords=[])],
                        ctx=ast.Load())],
                  keywords=[])),
            ast.FunctionDef(
               name='handle_changes',
               args=ast.arguments(
                  posonlyargs=[],
                  args=[
                     ast.arg(arg='checkbox_values'),
                     ast.arg(arg='dropdown_values'),
                     ast.arg(arg='checkbox_ids'),
                     ast.arg(arg='dropdown_ids'),
                     ast.arg(arg='reset')],
                  kwonlyargs=[],
                  kw_defaults=[],
                  defaults=[]),
               body=[
                  ast.Assign(
                     targets=[
                        ast.Name(id='triggered', ctx=ast.Store())],
                     value=ast.Attribute(
                        value=ast.Name(id='callback_context', ctx=ast.Load()),
                        attr='triggered',
                        ctx=ast.Load())),
                  ast.If(
                     test=ast.Name(id='triggered', ctx=ast.Load()),
                     body=[
                        ast.Assign(
                           targets=[
                              ast.Name(id='changed_component', ctx=ast.Store())],
                           value=ast.Subscript(
                              value=ast.Call(
                                 func=ast.Attribute(
                                    value=ast.Subscript(
                                       value=ast.Subscript(
                                          value=ast.Name(id='triggered', ctx=ast.Load()),
                                          slice=ast.Constant(value=0),
                                          ctx=ast.Load()),
                                       slice=ast.Constant(value='prop_id'),
                                       ctx=ast.Load()),
                                    attr='split',
                                    ctx=ast.Load()),
                                 args=[
                                    ast.Constant(value='.')],
                                 keywords=[]),
                              slice=ast.Constant(value=0),
                              ctx=ast.Load())),
                        ast.Assign(
                           targets=[
                              ast.Name(id='changed_value', ctx=ast.Store())],
                           value=ast.Subscript(
                              value=ast.Subscript(
                                 value=ast.Name(id='triggered', ctx=ast.Load()),
                                 slice=ast.Constant(value=0),
                                 ctx=ast.Load()),
                              slice=ast.Constant(value='value'),
                              ctx=ast.Load())),
                        ast.If(
                           test=ast.Compare(
                              left=ast.Name(id='changed_component', ctx=ast.Load()),
                              ops=[
                                 ast.Eq()],
                              comparators=[
                                 ast.Constant(value='reset-button')]),
                           body=[
                              ast.Expr(
                                 value=ast.Call(
                                    func=ast.Name(id='handle_reset', ctx=ast.Load()),
                                    args=[],
                                    keywords=[])),
                              ast.Assign(
                                 targets=[
                                    ast.Name(id='checkbox_values', ctx=ast.Store())],
                                 value=ast.ListComp(
                                    elt=ast.List(elts=[], ctx=ast.Load()),
                                    generators=[
                                       ast.comprehension(
                                          target=ast.Name(id='_', ctx=ast.Store()),
                                          iter=ast.Name(id='boolean_variables', ctx=ast.Load()),
                                          ifs=[],
                                          is_async=0)])),
                              ast.Assign(
                                 targets=[
                                    ast.Name(id='dropdown_options', ctx=ast.Store())],
                                 value=ast.ListComp(
                                    elt=ast.Call(
                                       func=ast.Name(id='get_dropdown_options', ctx=ast.Load()),
                                       args=[
                                          ast.Subscript(
                                             value=ast.Name(id='structure', ctx=ast.Load()),
                                             slice=ast.Name(id='v', ctx=ast.Load()),
                                             ctx=ast.Load())],
                                       keywords=[]),
                                    generators=[
                                       ast.comprehension(
                                          target=ast.Name(id='v', ctx=ast.Store()),
                                          iter=ast.Name(id='integer_variables', ctx=ast.Load()),
                                          ifs=[],
                                          is_async=0)])),
                              ast.Return(
                                 value=ast.Tuple(
                                    elts=[
                                       ast.Name(id='checkbox_values', ctx=ast.Load()),
                                       ast.Name(id='dropdown_options', ctx=ast.Load()),
                                       ast.List(
                                          elts=[
                                             ast.Constant(value='No inconsistencies detected yet')],
                                          ctx=ast.Load())],
                                    ctx=ast.Load()))],
                           orelse=[]),
                        ast.Assign(
                           targets=[
                              ast.Name(id='changed_id', ctx=ast.Store())],
                           value=ast.Call(
                              func=ast.Name(id='eval', ctx=ast.Load()),
                              args=[
                                 ast.Name(id='changed_component', ctx=ast.Load())],
                              keywords=[])),
                        ast.If(
                           test=ast.Compare(
                              left=ast.Subscript(
                                 value=ast.Name(id='changed_id', ctx=ast.Load()),
                                 slice=ast.Constant(value='type'),
                                 ctx=ast.Load()),
                              ops=[
                                 ast.Eq()],
                              comparators=[
                                 ast.Constant(value='checkboxes')]),
                           body=[
                              ast.If(
                                 test=ast.Compare(
                                    left=ast.Call(
                                       func=ast.Name(id='len', ctx=ast.Load()),
                                       args=[
                                          ast.Name(id='changed_value', ctx=ast.Load())],
                                       keywords=[]),
                                    ops=[
                                       ast.Gt()],
                                    comparators=[
                                       ast.Constant(value=0)]),
                                 body=[
                                    ast.Assign(
                                       targets=[
                                          ast.Name(id='changes', ctx=ast.Store())],
                                       value=ast.Dict(
                                          keys=[
                                             ast.Subscript(
                                                value=ast.Name(id='changed_id', ctx=ast.Load()),
                                                slice=ast.Constant(value='index'),
                                                ctx=ast.Load())],
                                          values=[
                                             ast.Call(
                                                func=ast.Name(id='convert_from_ui', ctx=ast.Load()),
                                                args=[
                                                   ast.Name(id='changed_value', ctx=ast.Load())],
                                                keywords=[])])),
                                    ast.Assign(
                                       targets=[
                                          ast.Name(id='unsat_fields', ctx=ast.Store())],
                                       value=ast.Call(
                                          func=ast.Name(id='propagation_loop', ctx=ast.Load()),
                                          args=[
                                             ast.Name(id='changes', ctx=ast.Load())],
                                          keywords=[])),
                                    ast.If(
                                       test=ast.Compare(
                                          left=ast.Call(
                                             func=ast.Name(id='len', ctx=ast.Load()),
                                             args=[
                                                ast.Name(id='unsat_fields', ctx=ast.Load())],
                                             keywords=[]),
                                          ops=[
                                             ast.Eq()],
                                          comparators=[
                                             ast.Constant(value=0)]),
                                       body=[
                                          ast.Return(
                                             value=ast.Tuple(
                                                elts=[
                                                   ast.ListComp(
                                                      elt=ast.Call(
                                                         func=ast.Name(id='convert_to_ui', ctx=ast.Load()),
                                                         args=[
                                                            ast.Subscript(
                                                               value=ast.Name(id='structure', ctx=ast.Load()),
                                                               slice=ast.Name(id='v', ctx=ast.Load()),
                                                               ctx=ast.Load())],
                                                         keywords=[]),
                                                      generators=[
                                                         ast.comprehension(
                                                            target=ast.Name(id='v', ctx=ast.Store()),
                                                            iter=ast.Name(id='boolean_variables', ctx=ast.Load()),
                                                            ifs=[],
                                                            is_async=0)]),
                                                   ast.ListComp(
                                                      elt=ast.Call(
                                                         func=ast.Name(id='convert_to_ui', ctx=ast.Load()),
                                                         args=[
                                                            ast.Subscript(
                                                               value=ast.Name(id='structure', ctx=ast.Load()),
                                                               slice=ast.Name(id='v', ctx=ast.Load()),
                                                               ctx=ast.Load())],
                                                         keywords=[]),
                                                      generators=[
                                                         ast.comprehension(
                                                            target=ast.Name(id='v', ctx=ast.Store()),
                                                            iter=ast.Name(id='integer_variables', ctx=ast.Load()),
                                                            ifs=[],
                                                            is_async=0)]),
                                                   ast.List(
                                                      elts=[
                                                         ast.Constant(value='No inconsistencies detected yet')],
                                                      ctx=ast.Load())],
                                                ctx=ast.Load()))],
                                       orelse=[
                                          ast.Return(
                                             value=ast.Tuple(
                                                elts=[
                                                   ast.Name(id='checkbox_values', ctx=ast.Load()),
                                                   ast.ListComp(
                                                      elt=ast.Call(
                                                         func=ast.Name(id='convert_to_ui', ctx=ast.Load()),
                                                         args=[
                                                            ast.Subscript(
                                                               value=ast.Name(id='structure', ctx=ast.Load()),
                                                               slice=ast.Name(id='v', ctx=ast.Load()),
                                                               ctx=ast.Load())],
                                                         keywords=[]),
                                                      generators=[
                                                         ast.comprehension(
                                                            target=ast.Name(id='v', ctx=ast.Store()),
                                                            iter=ast.Name(id='integer_variables', ctx=ast.Load()),
                                                            ifs=[],
                                                            is_async=0)]),
                                                   ast.List(
                                                      elts=[
                                                         ast.Call(
                                                            func=ast.Name(id='unsat_message', ctx=ast.Load()),
                                                            args=[
                                                               ast.Name(id='unsat_fields', ctx=ast.Load())],
                                                            keywords=[])],
                                                      ctx=ast.Load())],
                                                ctx=ast.Load()))])],
                                 orelse=[])],
                           orelse=[]),
                        ast.If(
                           test=ast.Compare(
                              left=ast.Subscript(
                                 value=ast.Name(id='changed_id', ctx=ast.Load()),
                                 slice=ast.Constant(value='type'),
                                 ctx=ast.Load()),
                              ops=[
                                 ast.Eq()],
                              comparators=[
                                 ast.Constant(value='dropdown')]),
                           body=[
                              ast.If(
                                 test=ast.Compare(
                                    left=ast.Name(id='changed_value', ctx=ast.Load()),
                                    ops=[
                                       ast.NotEq()],
                                    comparators=[
                                       ast.Constant(value=None)]),
                                 body=[
                                    ast.Assign(
                                       targets=[
                                          ast.Name(id='changes', ctx=ast.Store())],
                                       value=ast.Dict(
                                          keys=[
                                             ast.Subscript(
                                                value=ast.Name(id='changed_id', ctx=ast.Load()),
                                                slice=ast.Constant(value='index'),
                                                ctx=ast.Load())],
                                          values=[
                                             ast.Set(
                                                elts=[
                                                   ast.Name(id='changed_value', ctx=ast.Load())])])),
                                    ast.Assign(
                                       targets=[
                                          ast.Name(id='unsat_fields', ctx=ast.Store())],
                                       value=ast.Call(
                                          func=ast.Name(id='propagation_loop', ctx=ast.Load()),
                                          args=[
                                             ast.Name(id='changes', ctx=ast.Load())],
                                          keywords=[])),
                                    ast.If(
                                       test=ast.Compare(
                                          left=ast.Call(
                                             func=ast.Name(id='len', ctx=ast.Load()),
                                             args=[
                                                ast.Name(id='unsat_fields', ctx=ast.Load())],
                                             keywords=[]),
                                          ops=[
                                             ast.Eq()],
                                          comparators=[
                                             ast.Constant(value=0)]),
                                       body=[
                                          ast.Return(
                                             value=ast.Tuple(
                                                elts=[
                                                   ast.ListComp(
                                                      elt=ast.Call(
                                                         func=ast.Name(id='convert_to_ui', ctx=ast.Load()),
                                                         args=[
                                                            ast.Subscript(
                                                               value=ast.Name(id='structure', ctx=ast.Load()),
                                                               slice=ast.Name(id='v', ctx=ast.Load()),
                                                               ctx=ast.Load())],
                                                         keywords=[]),
                                                      generators=[
                                                         ast.comprehension(
                                                            target=ast.Name(id='v', ctx=ast.Store()),
                                                            iter=ast.Name(id='boolean_variables', ctx=ast.Load()),
                                                            ifs=[],
                                                            is_async=0)]),
                                                   ast.ListComp(
                                                      elt=ast.Call(
                                                         func=ast.Name(id='convert_to_ui', ctx=ast.Load()),
                                                         args=[
                                                            ast.Subscript(
                                                               value=ast.Name(id='structure', ctx=ast.Load()),
                                                               slice=ast.Name(id='v', ctx=ast.Load()),
                                                               ctx=ast.Load())],
                                                         keywords=[]),
                                                      generators=[
                                                         ast.comprehension(
                                                            target=ast.Name(id='v', ctx=ast.Store()),
                                                            iter=ast.Name(id='integer_variables', ctx=ast.Load()),
                                                            ifs=[],
                                                            is_async=0)]),
                                                   ast.List(
                                                      elts=[
                                                         ast.Constant(value='No inconsistencies detected yet')],
                                                      ctx=ast.Load())],
                                                ctx=ast.Load()))],
                                       orelse=[
                                          ast.Return(
                                             value=ast.Tuple(
                                                elts=[
                                                   ast.Name(id='checkbox_values', ctx=ast.Load()),
                                                   ast.ListComp(
                                                      elt=ast.Call(
                                                         func=ast.Name(id='convert_to_ui', ctx=ast.Load()),
                                                         args=[
                                                            ast.Subscript(
                                                               value=ast.Name(id='structure', ctx=ast.Load()),
                                                               slice=ast.Name(id='v', ctx=ast.Load()),
                                                               ctx=ast.Load())],
                                                         keywords=[]),
                                                      generators=[
                                                         ast.comprehension(
                                                            target=ast.Name(id='v', ctx=ast.Store()),
                                                            iter=ast.Name(id='integer_variables', ctx=ast.Load()),
                                                            ifs=[],
                                                            is_async=0)]),
                                                   ast.List(
                                                      elts=[
                                                         ast.Call(
                                                            func=ast.Name(id='unsat_message', ctx=ast.Load()),
                                                            args=[
                                                               ast.Name(id='unsat_fields', ctx=ast.Load())],
                                                            keywords=[])],
                                                      ctx=ast.Load())],
                                                ctx=ast.Load()))])],
                                 orelse=[])],
                           orelse=[])],
                     orelse=[]),
                  ast.Return(
                     value=ast.Tuple(
                        elts=[
                           ast.Name(id='checkbox_values', ctx=ast.Load()),
                           ast.ListComp(
                              elt=ast.Call(
                                 func=ast.Name(id='convert_to_ui', ctx=ast.Load()),
                                 args=[
                                    ast.Subscript(
                                       value=ast.Name(id='structure', ctx=ast.Load()),
                                       slice=ast.Name(id='v', ctx=ast.Load()),
                                       ctx=ast.Load())],
                                 keywords=[]),
                              generators=[
                                 ast.comprehension(
                                    target=ast.Name(id='v', ctx=ast.Store()),
                                    iter=ast.Name(id='integer_variables', ctx=ast.Load()),
                                    ifs=[],
                                    is_async=0)]),
                           ast.List(
                              elts=[
                                 ast.Constant(value='No inconsistencies detected yet')],
                              ctx=ast.Load())],
                        ctx=ast.Load()))],
               decorator_list=[
                  ast.Call(
                     func=ast.Attribute(
                        value=ast.Name(id='app', ctx=ast.Load()),
                        attr='callback',
                        ctx=ast.Load()),
                     args=[
                        ast.List(
                           elts=[
                              ast.Call(
                                 func=ast.Name(id='Output', ctx=ast.Load()),
                                 args=[
                                    ast.Dict(
                                       keys=[
                                          ast.Constant(value='type'),
                                          ast.Constant(value='index')],
                                       values=[
                                          ast.Constant(value='checkboxes'),
                                          ast.Name(id='ALL', ctx=ast.Load())]),
                                    ast.Constant(value='value')],
                                 keywords=[]),
                              ast.Call(
                                 func=ast.Name(id='Output', ctx=ast.Load()),
                                 args=[
                                    ast.Dict(
                                       keys=[
                                          ast.Constant(value='type'),
                                          ast.Constant(value='index')],
                                       values=[
                                          ast.Constant(value='dropdown'),
                                          ast.Name(id='ALL', ctx=ast.Load())]),
                                    ast.Constant(value='options')],
                                 keywords=[]),
                              ast.Call(
                                 func=ast.Name(id='Output', ctx=ast.Load()),
                                 args=[
                                    ast.Dict(
                                       keys=[
                                          ast.Constant(value='type')],
                                       values=[
                                          ast.Constant(value='text-output')]),
                                    ast.Constant(value='children')],
                                 keywords=[])],
                           ctx=ast.Load()),
                        ast.List(
                           elts=[
                              ast.Call(
                                 func=ast.Name(id='Input', ctx=ast.Load()),
                                 args=[
                                    ast.Dict(
                                       keys=[
                                          ast.Constant(value='type'),
                                          ast.Constant(value='index')],
                                       values=[
                                          ast.Constant(value='checkboxes'),
                                          ast.Name(id='ALL', ctx=ast.Load())]),
                                    ast.Constant(value='value')],
                                 keywords=[]),
                              ast.Call(
                                 func=ast.Name(id='Input', ctx=ast.Load()),
                                 args=[
                                    ast.Dict(
                                       keys=[
                                          ast.Constant(value='type'),
                                          ast.Constant(value='index')],
                                       values=[
                                          ast.Constant(value='dropdown'),
                                          ast.Name(id='ALL', ctx=ast.Load())]),
                                    ast.Constant(value='value')],
                                 keywords=[]),
                              ast.Call(
                                 func=ast.Name(id='Input', ctx=ast.Load()),
                                 args=[
                                    ast.Constant(value='reset-button'),
                                    ast.Constant(value='n_clicks')],
                                 keywords=[])],
                           ctx=ast.Load()),
                        ast.List(
                           elts=[
                              ast.Call(
                                 func=ast.Name(id='State', ctx=ast.Load()),
                                 args=[
                                    ast.Dict(
                                       keys=[
                                          ast.Constant(value='type'),
                                          ast.Constant(value='index')],
                                       values=[
                                          ast.Constant(value='checkboxes'),
                                          ast.Name(id='ALL', ctx=ast.Load())]),
                                    ast.Constant(value='id')],
                                 keywords=[]),
                              ast.Call(
                                 func=ast.Name(id='State', ctx=ast.Load()),
                                 args=[
                                    ast.Dict(
                                       keys=[
                                          ast.Constant(value='type'),
                                          ast.Constant(value='index')],
                                       values=[
                                          ast.Constant(value='dropdown'),
                                          ast.Name(id='ALL', ctx=ast.Load())]),
                                    ast.Constant(value='id')],
                                 keywords=[])],
                           ctx=ast.Load())],
                     keywords=[])]),
            ast.Expr(
               value=ast.Call(
                  func=ast.Attribute(
                     value=ast.Name(id='app', ctx=ast.Load()),
                     attr='run_server',
                     ctx=ast.Load()),
                  args=[],
                  keywords=[
                     ast.keyword(
                        arg='debug',
                        value=ast.Constant(value=True))]))],
         decorator_list=[]),
      ast.If(
         test=ast.Compare(
            left=ast.Name(id='__name__', ctx=ast.Load()),
            ops=[
               ast.Eq()],
            comparators=[
               ast.Constant(value='__main__')]),
         body=[
            ast.Expr(
               value=ast.Call(
                  func=ast.Name(id='launch_dash_app', ctx=ast.Load()),
                  args=[],
                  keywords=[]))],
         orelse=[])],
   type_ignores=[])



def generate_dash_application():
    return ast.Module(
   body=[
      ast.ImportFrom(
         module='dash',
         names=[
            ast.alias(name='Dash'),
            ast.alias(name='html'),
            ast.alias(name='dcc'),
            ast.alias(name='State'),
            ast.alias(name='Input'),
            ast.alias(name='Output'),
            ast.alias(name='ALL')],
         level=0),
      ast.Assign(
         targets=[
            ast.Name(id='app', ctx=ast.Store())],
         value=ast.Call(
            func=ast.Name(id='Dash', ctx=ast.Load()),
            args=[
               ast.Name(id='__name__', ctx=ast.Load())],
            keywords=[])),

      ast.Assign(
           targets=[
               ast.Name(id='variables', ctx=ast.Store())],
           value=ast.SetComp(
               elt=ast.Name(id='v', ctx=ast.Load()),
               generators=[
                   ast.comprehension(
                       target=ast.Name(id='v', ctx=ast.Store()),
                       iter=ast.Call(
                           func=ast.Attribute(
                               value=ast.Name(id='structure', ctx=ast.Load()),
                               attr='keys',
                               ctx=ast.Load()),
                           args=[],
                           keywords=[]),
                       ifs=[
                           ast.UnaryOp(
                               op=ast.Not(),
                               operand=ast.Call(
                                   func=ast.Attribute(
                                       value=ast.Name(id='v', ctx=ast.Load()),
                                       attr='startswith',
                                       ctx=ast.Load()),
                                   args=[
                                       ast.Constant(value='_')],
                                   keywords=[]))],
                       is_async=0)])),

       ast.Assign(
         targets=[
            ast.Attribute(
               value=ast.Name(id='app', ctx=ast.Load()),
               attr='layout',
               ctx=ast.Store())],
         value=ast.Call(
            func=ast.Attribute(
               value=ast.Name(id='html', ctx=ast.Load()),
               attr='Div',
               ctx=ast.Load()),
            args=[
               ast.List(
                  elts=[
                     ast.Call(
                        func=ast.Attribute(
                           value=ast.Name(id='html', ctx=ast.Load()),
                           attr='H1',
                           ctx=ast.Load()),
                        args=[
                           ast.Constant(value='Interactive configuration')],
                        keywords=[]),
                     ast.Call(
                        func=ast.Attribute(
                           value=ast.Name(id='html', ctx=ast.Load()),
                           attr='Div',
                           ctx=ast.Load()),
                        args=[
                           ast.SetComp(
                              elt=ast.Call(
                                 func=ast.Attribute(
                                    value=ast.Name(id='html', ctx=ast.Load()),
                                    attr='Div',
                                    ctx=ast.Load()),
                                 args=[
                                    ast.List(
                                       elts=[
                                          ast.Call(
                                             func=ast.Attribute(
                                                value=ast.Name(id='html', ctx=ast.Load()),
                                                attr='Label',
                                                ctx=ast.Load()),
                                             args=[
                                                ast.JoinedStr(
                                                   values=[
                                                      ast.FormattedValue(
                                                         value=ast.Name(id='var', ctx=ast.Load()),
                                                         conversion=-1),
                                                      ast.Constant(value=':')])],
                                             keywords=[]),
                                          ast.Call(
                                             func=ast.Attribute(
                                                value=ast.Name(id='dcc', ctx=ast.Load()),
                                                attr='Checklist',
                                                ctx=ast.Load()),
                                             args=[],
                                             keywords=[
                                                ast.keyword(
                                                   arg='id',
                                                   value=ast.Dict(
                                                      keys=[
                                                         ast.Constant(value='type'),
                                                         ast.Constant(value='index')],
                                                      values=[
                                                         ast.Constant(value='checkboxes'),
                                                         ast.Name(id='var', ctx=ast.Load())])),
                                                ast.keyword(
                                                   arg='options',
                                                   value=ast.List(
                                                      elts=[
                                                         ast.Dict(
                                                            keys=[
                                                               ast.Constant(value='label'),
                                                               ast.Constant(value='value')],
                                                            values=[
                                                               ast.Constant(value='True'),
                                                               ast.Constant(value=True)]),
                                                         ast.Dict(
                                                            keys=[
                                                               ast.Constant(value='label'),
                                                               ast.Constant(value='value')],
                                                            values=[
                                                               ast.Constant(value='False'),
                                                               ast.Constant(value=False)])],
                                                      ctx=ast.Load())),
                                                ast.keyword(
                                                   arg='value',
                                                   value=ast.List(elts=[], ctx=ast.Load())),
                                                ast.keyword(
                                                   arg='inline',
                                                   value=ast.Constant(value=True))]),
                                          ast.Call(
                                             func=ast.Attribute(
                                                value=ast.Name(id='html', ctx=ast.Load()),
                                                attr='Div',
                                                ctx=ast.Load()),
                                             args=[],
                                             keywords=[
                                                ast.keyword(
                                                   arg='id',
                                                   value=ast.Dict(
                                                      keys=[
                                                         ast.Constant(value='type'),
                                                         ast.Constant(value='index')],
                                                      values=[
                                                         ast.Constant(value='output'),
                                                         ast.Name(id='var', ctx=ast.Load())]))])],
                                       ctx=ast.Load())],
                                 keywords=[]),
                              generators=[
                                 ast.comprehension(
                                    target=ast.Name(id='var', ctx=ast.Store()),
                                    iter=ast.Name(id='variables', ctx=ast.Load()),
                                    ifs=[],
                                    is_async=0)])],
                        keywords=[])],
                  ctx=ast.Load())],
            keywords=[])),
      ast.FunctionDef(
         name='update_output',
         args=ast.arguments(
            posonlyargs=[],
            args=[
               ast.arg(arg='selected_values_list'),
               ast.arg(arg='component_id_list')],
            kwonlyargs=[],
            kw_defaults=[],
            defaults=[]),
         body=[
            ast.Assign(
               targets=[
                  ast.Name(id='updated_values', ctx=ast.Store())],
               value=ast.Dict(keys=[], values=[])),
            ast.For(
               target=ast.Tuple(
                  elts=[
                     ast.Name(id='selected_values', ctx=ast.Store()),
                     ast.Name(id='component_id', ctx=ast.Store())],
                  ctx=ast.Store()),
               iter=ast.Call(
                  func=ast.Name(id='zip', ctx=ast.Load()),
                  args=[
                     ast.Name(id='selected_values_list', ctx=ast.Load()),
                     ast.Name(id='component_id_list', ctx=ast.Load())],
                  keywords=[]),
               body=[
                  ast.Assign(
                     targets=[
                        ast.Name(id='variable_name', ctx=ast.Store())],
                     value=ast.Subscript(
                        value=ast.Name(id='component_id', ctx=ast.Load()),
                        slice=ast.Constant(value='index'),
                        ctx=ast.Load())),
                  ast.If(
                     test=ast.Compare(
                        left=ast.Call(
                           func=ast.Name(id='len', ctx=ast.Load()),
                           args=[
                              ast.Name(id='selected_values', ctx=ast.Load())],
                           keywords=[]),
                        ops=[
                           ast.Gt()],
                        comparators=[
                           ast.Constant(value=0)]),
                     body=[
                        ast.Expr(
                           value=ast.Call(
                              func=ast.Name(id='propagate_loop', ctx=ast.Load()),
                              args=[
                                 ast.Name(id='variable_name', ctx=ast.Load()),
                                 ast.Subscript(
                                    value=ast.Name(id='selected_values', ctx=ast.Load()),
                                    slice=ast.UnaryOp(
                                       op=ast.USub(),
                                       operand=ast.Constant(value=1)),
                                    ctx=ast.Load())],
                              keywords=[])),
                        ast.For(
                           target=ast.Name(id='var', ctx=ast.Store()),
                           iter=ast.Call(
                              func=ast.Attribute(
                                 value=ast.Name(id='structure', ctx=ast.Load()),
                                 attr='keys',
                                 ctx=ast.Load()),
                              args=[],
                              keywords=[]),
                           body=[
                              ast.If(
                                 test=ast.Compare(
                                    left=ast.Subscript(
                                       value=ast.Name(id='structure', ctx=ast.Load()),
                                       slice=ast.Name(id='var', ctx=ast.Load()),
                                       ctx=ast.Load()),
                                    ops=[
                                       ast.NotEq()],
                                    comparators=[
                                       ast.Constant(value=None)]),
                                 body=[
                                    ast.Assign(
                                       targets=[
                                          ast.Subscript(
                                             value=ast.Name(id='updated_values', ctx=ast.Load()),
                                             slice=ast.Name(id='var', ctx=ast.Load()),
                                             ctx=ast.Store())],
                                       value=ast.List(
                                          elts=[
                                             ast.Subscript(
                                                value=ast.Name(id='structure', ctx=ast.Load()),
                                                slice=ast.Name(id='var', ctx=ast.Load()),
                                                ctx=ast.Load())],
                                          ctx=ast.Load()))],
                                 orelse=[])],
                           orelse=[])],
                     orelse=[])],
               orelse=[]),
            ast.Return(
               value=ast.SetComp(
                  elt=ast.Call(
                     func=ast.Attribute(
                        value=ast.Name(id='updated_values', ctx=ast.Load()),
                        attr='get',
                        ctx=ast.Load()),
                     args=[
                        ast.Name(id='var', ctx=ast.Load()),
                        ast.List(elts=[], ctx=ast.Load())],
                     keywords=[]),
                  generators=[
                     ast.comprehension(
                        target=ast.Name(id='var', ctx=ast.Store()),
                        iter=ast.Name(id='variables', ctx=ast.Load()),
                        ifs=[],
                        is_async=0)]))],
         decorator_list=[
            ast.Call(
               func=ast.Attribute(
                  value=ast.Name(id='app', ctx=ast.Load()),
                  attr='callback',
                  ctx=ast.Load()),
               args=[
                  ast.Call(
                     func=ast.Name(id='Output', ctx=ast.Load()),
                     args=[
                        ast.Dict(
                           keys=[
                              ast.Constant(value='type'),
                              ast.Constant(value='index')],
                           values=[
                              ast.Constant(value='checkboxes'),
                              ast.Name(id='ALL', ctx=ast.Load())]),
                        ast.Constant(value='value')],
                     keywords=[]),
                  ast.Call(
                     func=ast.Name(id='Input', ctx=ast.Load()),
                     args=[
                        ast.Dict(
                           keys=[
                              ast.Constant(value='type'),
                              ast.Constant(value='index')],
                           values=[
                              ast.Constant(value='checkboxes'),
                              ast.Name(id='ALL', ctx=ast.Load())]),
                        ast.Constant(value='value')],
                     keywords=[]),
                  ast.Call(
                     func=ast.Name(id='State', ctx=ast.Load()),
                     args=[
                        ast.Dict(
                           keys=[
                              ast.Constant(value='type'),
                              ast.Constant(value='index')],
                           values=[
                              ast.Constant(value='checkboxes'),
                              ast.Name(id='ALL', ctx=ast.Load())]),
                        ast.Constant(value='id')],
                     keywords=[])],
               keywords=[])]),
      ast.If(
         test=ast.Compare(
            left=ast.Name(id='__name__', ctx=ast.Load()),
            ops=[
               ast.Eq()],
            comparators=[
               ast.Constant(value='__main__')]),
         body=[
            ast.Expr(
               value=ast.Call(
                  func=ast.Attribute(
                     value=ast.Name(id='app', ctx=ast.Load()),
                     attr='run_server',
                     ctx=ast.Load()),
                  args=[],
                  keywords=[
                     ast.keyword(
                        arg='debug',
                        value=ast.Constant(value=True))]))],
         orelse=[])],
   type_ignores=[])

def generate(enf_rules, domain_rules, second_time=0):
    print("start: ", time.time() - second_time)
    initial_props = []
    for enf_rule in enf_rules:
        new_initial_props = derive_initial_propagators(enf_rule)
        initial_props.extend(new_initial_props)
    print("initial_props: ", time.time() - second_time)
    derived_props = set()
    for initial_prop in initial_props:
        new_derived_props = derive_derived_propagators(initial_prop)
        derived_props.update(new_derived_props)
    print("derived_props: ", time.time() - second_time)
    #derived_props = derive_derived_propagators_for_modifiable_set(initial_props, {"X"})


    initial_structure = generate_initial_structure(enf_rules, domain_rules)
    print("initial_structure: ", time.time() - second_time)
    update_structure = generate_update_structure()
    print("update_structure: ", time.time() - second_time)
    print_structure = generate_print_structure()
    print("print_structure: ", time.time() - second_time)
    check_unsat_fields = generate_check_unsat_fields()
    print("check_unsat_fields: ", time.time() - second_time)
    intersect_changes = generate_intersect_changes()
    print("intersect_changes: ", time.time() - second_time)
    propagate_function = generate_propagate(derived_props)
    print("propagate_function: ", time.time() - second_time)
    #feedback_loop = generate_feedback_loop() # for interaction with console
    propagation_loop = generate_propagation_loop_with_contradiction_check()
    print("propagation_loop ", time.time() - second_time)
    feedback_loop = generate_feedback_loop_with_contradiction_check() # for interaction with console, with contradiction checking
    print("feedback_loop ", time.time() - second_time)
    propagate_loop_function = generate_propagate_loop() # for dash
    dash_application = generate_dash_application()
    print("ast generation: ", time.time() - second_time)
    module = ast.Module(body=[initial_structure, update_structure, print_structure, check_unsat_fields, intersect_changes, propagate_function, propagation_loop, feedback_loop.body], type_ignores=[])

    dash_imports = generate_dash_imports()
    first_initial_structure = generate_initial_structure(enf_rules, domain_rules, "initial_structure")
    current_structure = generate_initial_structure(enf_rules, domain_rules, "structure")
    handle_reset = generate_handle_reset()
    get_dropdown_options = generate_get_dropdown_options()
    convert_to_ui = generate_convert_to_ui()
    convert_from_ui = generate_convert_from_ui()
    unsat_message = generate_unsat_message()
    launch_dash_app = generate_launch_dash_app()
    #dash_module = ast.Module(body=[dash_imports, first_initial_structure, current_structure, update_structure, handle_reset, check_unsat_fields, intersect_changes, propagate_function, propagation_loop, get_dropdown_options, convert_to_ui, convert_from_ui, unsat_message, launch_dash_app.body])
    #module = ast.Module(body=[generate_equality_conditions(Equation(Operator.GT, Atom('A'), Atom('B')), 'B', True)])
    #dash_module = ast.Module(body=[initial_structure, update_structure, propagate_function, propagate_loop_function, dash_application.body], type_ignores=[])

    #print(ast.dump(module, indent=4))
    print("ast before unparse: ", time.time() - second_time)
    code = astunparse.unparse(module)
    print("ast unparse: ", time.time() - second_time)
    with open("generated_code_1test.py", "w") as file:
        file.write(code)















