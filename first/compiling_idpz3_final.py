# Dit bestand bevat alle code om ENF-regels, die gegenereerd zijn in parsing_idpz3_xarray.py, om te zetten in een abstract syntax tree.
# Deze abstract syntax tree wordt dan ten slotte door astunparse omgezet naar een Python-bestand.



import parsing_idpz3_final

from ast import *
import random
import time

import astunparse

# Deze klasse maakt objecten aan die in een latere fase zullen omgezet worden naar AST's die DataArrays van de xarray library voorstellen.
class TempDataArray:
    def __init__(self, name, dims, coords):
        self.name = name
        self.dims = dims
        self.coords = coords

# Deze klasse stelt gekwantificeerde UNSAT-lists voor, zoals vermeld in __thesistekst__.
class UnsatList:
    def __init__(self, unsat_list, bindings):
        self.unsat_list = unsat_list.copy()
        self.bindings = bindings.copy()

# Deze klasse stelt SpecificPropagators voor, zoals vermeld in __thesistekst__.
class SpecificPropagator:
    def __init__(self, general, specific, bindings, new_binding, universal):
        self.general = general
        self.specific = specific
        self.bindings = bindings.copy()
        self.new_binding = new_binding
        self.universal = universal
# Deze klasse stelt GeneralPropagators voor, zoals vermeld in __thesistekst__.
class GeneralPropagator:
    def __init__(self, specific, general, bindings, new_binding, universal):
        self.specific = specific
        self.general = general
        self.bindings = bindings.copy()
        self.new_binding = new_binding
        self.universal = universal

# Deze klasse stelt FunctionPropagators voor, zoals vermeld in __thesistekst__.
class FunctionPropagator:
    def __init__(self, name):
        self.name = name

# Deze functie ontvangt ENF-regels, samen met een positie.
# Alle literals in de ENF-regel hebben een positie, en alle posities worden overlopen, de positie geeft aan welke literal aangepast is.
# Afhankelijk van deze info worden ENF-regels, samen met de positie van het aangepaste atoom,
# omgezet in UNSAT-lists, SpecificPropagators, of GeneralPropagators.
def get_unsat_lists(enf, position):
    unsat_lists = []
    if type(enf) == parsing_idpz3_final.ENFConjunctive:
        if position == 0:
            for lit in enf.right:
                unsat_lists.append(UnsatList([enf.left] + [lit.negate()], enf.bindings))
            unsat_lists.append(UnsatList([enf.left.negate()] + enf.right, enf.bindings))
        else:
            unsat_lists.append(UnsatList([enf.right[position-1].negate()] + [enf.left], enf.bindings))
            unsat_lists.append(UnsatList([enf.right[position-1]] + enf.right[:(position-1)] + enf.right[position:] + [enf.left.negate()], enf.bindings))
    if type(enf) == parsing_idpz3_final.ENFDisjunctive:
        if position == 0:
            for lit in enf.right:
                unsat_lists.append(UnsatList([enf.left.negate()] + [lit], enf.bindings))
            unsat_lists.append(UnsatList([enf.left] + [lit.negate() for lit in enf.right], enf.bindings))
        else:
            unsat_lists.append(UnsatList([enf.right[position-1]] + [enf.left.negate()], enf.bindings))
            unsat_lists.append(UnsatList([enf.right[position-1].negate()] + [lit.negate() for lit in enf.right[:(position-1)]] + [lit.negate() for lit in enf.right[position:]] + [enf.left], enf.bindings))
    if type(enf) == parsing_idpz3_final.ENFUniversal:
        if position == 0:
            unsat_lists.append(SpecificPropagator(enf.left, enf.right, enf.bindings, enf.new_binding, True))
        if position == 1:
            unsat_lists.append(GeneralPropagator(enf.right, enf.left, enf.bindings, enf.new_binding, True))
    if type(enf) == parsing_idpz3_final.ENFExistential:
        if position == 0:
            unsat_lists.append(SpecificPropagator(enf.left, enf.right, enf.bindings, enf.new_binding, False))
        if position == 1:
            unsat_lists.append(GeneralPropagator(enf.right, enf.left, enf.bindings, enf.new_binding, False))
    if type(enf) == parsing_idpz3_final.ENFReductive: #!x,y: A(x,y) <=> B(x)
        if position == 0:
            unsat_lists.append(GeneralPropagator(enf.left, enf.right, enf.bindings, enf.old_binding,enf.b))  #?
        if position == 1:
            unsat_lists.append(SpecificPropagator(enf.right, enf.left, enf.bindings, enf.old_binding, enf.b))
    return unsat_lists

# Hulpfunctie om eenvoudig element aan een dictionary toe te voegen.
def add_to_dict(d, k, elem):
    if k in d.keys():
        d[k].extend(elem)
    else:
        d[k] = elem

# Deze functie krijgt alle ENF-regels die in parsing_idpz3_xarray.py gegenereerd zijn als invoer.
# De functie overloopt alle literals (posities) in de regels en roept get_unsat_lists() op voor elke positie.
# Vervolgens worden de nieuwe propagators gegroepeerd op naam van het atoom.
def group_propagators(enf_rules, functions):
    #full_predicates = [predicate.name for predicate in predicates] + [";p_" + function.name for function in functions] # + hulpvariabelen!
    grouped_propagators = {}

    for enf_rule in enf_rules:
        if type(enf_rule) == parsing_idpz3_final.AssertLiteral:
            add_to_dict(grouped_propagators, enf_rule.literal.atom.name, [parsing_idpz3_final.AssertLiteral(enf_rule.literal)])
        if type(enf_rule) == parsing_idpz3_final.ENFConjunctive or type(enf_rule) == parsing_idpz3_final.ENFDisjunctive:
            add_to_dict(grouped_propagators, enf_rule.left.atom.name, get_unsat_lists(enf_rule, 0))
            for i, lit in enumerate(enf_rule.right):
                add_to_dict(grouped_propagators, lit.atom.name, get_unsat_lists(enf_rule, i+1))
        if type(enf_rule) == parsing_idpz3_final.ENFUniversal or type(enf_rule) == parsing_idpz3_final.ENFExistential or type(enf_rule) == parsing_idpz3_final.ENFReductive:
            add_to_dict(grouped_propagators, enf_rule.left.atom.name, get_unsat_lists(enf_rule, 0))
            add_to_dict(grouped_propagators, enf_rule.right.atom.name, get_unsat_lists(enf_rule, 1))

    for func in functions:
        add_to_dict(grouped_propagators, ';p;' + func.name, [FunctionPropagator(';p;' + func.name)])

    return grouped_propagators

# Deze functie stelt de data arrays (xarray.DataArray) op, op basis van de predicaten en functies in het originele IDP-programma.
# Elke dimensie moet een unieke naam krijgen, aangezien xarray.DataArray deze dimensies anders als identiek beschouwt.

#dims met zelfde naam?: specific/general propagate?
# zelfde variabele kan meerdere keren voorkomen met andere variabelen
# zelfde type kan meerdere keren voorkomen
# -> dims en coords moeten unieke namen bevatten (anders beschouwt DataArray dit als hetzelfde argument)!
# variabelen moeten gelinkt worden aan types in specific_propagate en general_propagate!
def construct_data_arrays(types, predicates, functions):
    temp_data_arrays = {}
    type_dict = {t.name : t.domain for t in types}
    for pred in predicates:
        coords = {f"x{i}" : type_dict[t] for i,t in enumerate(pred.argtypes)}
        temp_data_arrays[pred.name] = TempDataArray(pred.name, tuple(coords.keys()), coords)
    #for func in functions:
    #    coords = {f"x{i}" : type_dict[t] for i,t in enumerate(func.argtypes + [func.scopetype])}
    #    temp_data_arrays[';p;' + func.name] = TempDataArray(';p;' + func.name, tuple(coords.keys()), coords)
    return temp_data_arrays


# Determines the list of auxiliary variables that necessarily evaluate to true, hereby speeding up the propagation process.
def determine_true_list(enf_rules):
    true_list = []
    temp_true_list = [enf.literal.atom.name for enf in enf_rules if type(enf) == parsing_idpz3_final.AssertLiteral and enf.literal.pos and len(enf.literal.atom.args) == 0]

    while len(temp_true_list) > 0:
        new_temp_true_list = []
        for enf_rule in enf_rules:
            if type(enf_rule) != parsing_idpz3_final.AssertLiteral:
                if enf_rule.left.atom.name in temp_true_list:
                    if type(enf_rule) == parsing_idpz3_final.ENFConjunctive:
                        for lit in enf_rule.right:
                            if lit.pos:
                                true_list.append(lit.atom.name)
                                new_temp_true_list.append(lit.atom.name)
                    if type(enf_rule) == parsing_idpz3_final.ENFUniversal:
                        true_list.append(enf_rule.right.atom.name)
                        new_temp_true_list.append(enf_rule.right.atom.name)
        temp_true_list = new_temp_true_list
    return [elem for elem in true_list if elem.startswith('_X')]



# AST van een hulpfunctie
def generate_imports():
    return Module(
   body=[
      Import(
         names=[
            alias(name='math')]),
      Import(
         names=[
            alias(name='time')]),
      ImportFrom(
         module='enum',
         names=[
            alias(name='Enum')],
         level=0),
      ImportFrom(
         module='itertools',
         names=[
            alias(name='product')],
         level=0),
      Import(
         names=[
            alias(name='xarray', asname='xr')]),
      Import(
         names=[
            alias(name='numpy', asname='np')]),
      ImportFrom(
         module='dash',
         names=[
            alias(name='Dash'),
            alias(name='html'),
            alias(name='dcc'),
            alias(name='State'),
            alias(name='Input'),
            alias(name='Output'),
            alias(name='ALL'),
            alias(name='callback_context')],
         level=0)],
   type_ignores=[])

# AST van een hulpfunctie
def generate_auxiliary_classes():
    return Module(
   body=[
       ClassDef(
           name='EB',
           bases=[
               Name(id='Enum', ctx=Load())],
           keywords=[],
           body=[
               Assign(
                   targets=[
                       Name(id='TRUE', ctx=Store())],
                   value=Constant(value=1)),
               Assign(
                   targets=[
                       Name(id='FALSE', ctx=Store())],
                   value=Constant(value=2)),
               Assign(
                   targets=[
                       Name(id='UNKNOWN', ctx=Store())],
                   value=Constant(value=0)),
               Assign(
                   targets=[
                       Name(id='INCONSISTENT', ctx=Store())],
                   value=UnaryOp(
                       op=USub(),
                       operand=Constant(value=1))),
               Assign(
                   targets=[
                       Name(id='NONE', ctx=Store())],
                   value=UnaryOp(
                       op=USub(),
                       operand=Constant(value=2)))],
           decorator_list=[]),
      ClassDef(
         name='Change',
         bases=[],
         keywords=[],
         body=[
            FunctionDef(
               name='__init__',
               args=arguments(
                  posonlyargs=[],
                  args=[
                     arg(arg='self'),
                     arg(arg='name'),
                     arg(arg='true_slicing'),
                     arg(arg='false_slicing')],
                  kwonlyargs=[],
                  kw_defaults=[],
                  defaults=[]),
               body=[
                  Assign(
                     targets=[
                        Attribute(
                           value=Name(id='self', ctx=Load()),
                           attr='name',
                           ctx=Store())],
                     value=Name(id='name', ctx=Load())),
                  Assign(
                     targets=[
                        Attribute(
                           value=Name(id='self', ctx=Load()),
                           attr='true_slicing',
                           ctx=Store())],
                     value=Name(id='true_slicing', ctx=Load())),
                  Assign(
                     targets=[
                        Attribute(
                           value=Name(id='self', ctx=Load()),
                           attr='false_slicing',
                           ctx=Store())],
                     value=Name(id='false_slicing', ctx=Load()))],
               decorator_list=[])],
         decorator_list=[]),
      ClassDef(
         name='RuleComponent',
         bases=[],
         keywords=[],
         body=[
            FunctionDef(
               name='__init__',
               args=arguments(
                  posonlyargs=[],
                  args=[
                     arg(arg='self'),
                     arg(arg='name'),
                     arg(arg='slicing'),
                     arg(arg='b')],
                  kwonlyargs=[],
                  kw_defaults=[],
                  defaults=[]),
               body=[
                  Assign(
                     targets=[
                        Attribute(
                           value=Name(id='self', ctx=Load()),
                           attr='name',
                           ctx=Store())],
                     value=Name(id='name', ctx=Load())),
                  Assign(
                     targets=[
                        Attribute(
                           value=Name(id='self', ctx=Load()),
                           attr='slicing',
                           ctx=Store())],
                     value=Name(id='slicing', ctx=Load())),
                  Assign(
                     targets=[
                        Attribute(
                           value=Name(id='self', ctx=Load()),
                           attr='b',
                           ctx=Store())],
                     value=Name(id='b', ctx=Load()))],
               decorator_list=[])],
         decorator_list=[]),
      ClassDef(
         name='PropagateResult',
         bases=[],
         keywords=[],
         body=[
            FunctionDef(
               name='__init__',
               args=arguments(
                  posonlyargs=[],
                  args=[
                     arg(arg='self'),
                     arg(arg='truth'),
                     arg(arg='position')],
                  kwonlyargs=[],
                  kw_defaults=[],
                  defaults=[
                     Constant(value=0)]),
               body=[
                  Assign(
                     targets=[
                        Attribute(
                           value=Name(id='self', ctx=Load()),
                           attr='truth',
                           ctx=Store())],
                     value=Name(id='truth', ctx=Load())),
                  Assign(
                     targets=[
                        Attribute(
                           value=Name(id='self', ctx=Load()),
                           attr='position',
                           ctx=Store())],
                     value=Name(id='position', ctx=Load()))],
               decorator_list=[])],
         decorator_list=[])],
   type_ignores=[])

# Bepaalt de grootte van het domein van een type.
def domain_size(dom):
    if type(dom) == parsing_idpz3_final.IntegerRange:
        return dom.ub - dom.lb + 1
    else:
        return len(dom)

# Genereert het volledige domein van een type.
def create_full_domain(dom):
    if type(dom) == parsing_idpz3_final.IntegerRange:
        return list(range(dom.lb, dom.ub+1))
    else:
        return dom

# Genereert de AST voor data arrays, op basis van de TempDataArray objecten.
def generate_data_arrays(temp_data_arrays):
    list_elems = []
    for temp_da in temp_data_arrays.values():
        if len(temp_da.dims) == 0:
            data_array = Call(
                  func=Attribute(
                     value=Name(id='xr', ctx=Load()),
                     attr='DataArray',
                     ctx=Load()),
                  args=[
                     Call(
                        func=Attribute(
                           value=Name(id='np', ctx=Load()),
                           attr='array',
                           ctx=Load()),
                        args=[
                           Attribute(
                              value=Name(id='EB', ctx=Load()),
                              attr='UNKNOWN',
                              ctx=Load())],
                        keywords=[])],
                  keywords=[
                     keyword(
                        arg='name',
                        value=Constant(value=temp_da.name))])
            list_elems.append(data_array)
        else:
            dimension_sizes = [Constant(value=domain_size(temp_da.coords[d])) for d in temp_da.dims]
            dimensions = [Constant(value=dim) for dim in temp_da.dims]
            domains = [List(elts=[Constant(value=el) for el in create_full_domain(temp_da.coords[dim])], ctx=Load()) for dim in temp_da.dims]
            data_array = Call(
                  func=Attribute(
                     value=Name(id='xr', ctx=Load()),
                     attr='DataArray',
                     ctx=Load()),
                  args=[
                     Call(
                        func=Attribute(
                           value=Name(id='np', ctx=Load()),
                           attr='full',
                           ctx=Load()),
                        args=[
                           Tuple(
                              elts=dimension_sizes,
                              ctx=Load()),
                           Attribute(
                              value=Name(id='EB', ctx=Load()),
                              attr='UNKNOWN',
                              ctx=Load())],
                        keywords=[])],
                  keywords=[
                     keyword(
                        arg='name',
                        value=Constant(value=temp_da.name)),
                     keyword(
                        arg='dims',
                        value=Tuple(
                           elts=dimensions,
                           ctx=Load())),
                     keyword(
                        arg='coords',
                        value=Dict(
                           keys=dimensions,
                           values=domains))])
            list_elems.append(data_array)
    return Module(
   body=[
      Assign(
         targets=[
            Name(id='vars', ctx=Store())],
         value=List(
            elts=list_elems,
            ctx=Load()))],
   type_ignores=[])

# AST van een hulpfunctie
def generate_data_arrays_extra():
    return Module(body=[Assign(
         targets=[
            Name(id='var_dict', ctx=Store())],
         value=DictComp(
            key=Attribute(
               value=Name(id='var', ctx=Load()),
               attr='name',
               ctx=Load()),
            value=Name(id='var', ctx=Load()),
            generators=[
               comprehension(
                  target=Name(id='var', ctx=Store()),
                  iter=Name(id='vars', ctx=Load()),
                  ifs=[],
                  is_async=0)]))],
   type_ignores=[])
# AST van een hulpfunctie
def generate_data_arrays_extra_dash():
    return Module(
   body=[
      Assign(
         targets=[
            Name(id='var_dict_original', ctx=Store())],
         value=DictComp(
            key=Attribute(
               value=Name(id='var', ctx=Load()),
               attr='name',
               ctx=Load()),
            value=Name(id='var', ctx=Load()),
            generators=[
               comprehension(
                  target=Name(id='var', ctx=Store()),
                  iter=Name(id='vars', ctx=Load()),
                  ifs=[],
                  is_async=0)])),
      Assign(
         targets=[
            Name(id='var_dict', ctx=Store())],
         value=DictComp(
            key=Attribute(
               value=Name(id='var', ctx=Load()),
               attr='name',
               ctx=Load()),
            value=Call(
               func=Attribute(
                  value=Name(id='var', ctx=Load()),
                  attr='copy',
                  ctx=Load()),
               args=[],
               keywords=[
                  keyword(
                     arg='deep',
                     value=Constant(value=True))]),
            generators=[
               comprehension(
                  target=Name(id='var', ctx=Store()),
                  iter=Name(id='vars', ctx=Load()),
                  ifs=[],
                  is_async=0)])),
      FunctionDef(
         name='handle_reset',
         args=arguments(
            posonlyargs=[],
            args=[],
            kwonlyargs=[],
            kw_defaults=[],
            defaults=[]),
         body=[
            For(
               target=Name(id='var_name', ctx=Store()),
               iter=Call(
                  func=Attribute(
                     value=Name(id='var_dict', ctx=Load()),
                     attr='keys',
                     ctx=Load()),
                  args=[],
                  keywords=[]),
               body=[
                  Assign(
                     targets=[
                        Subscript(
                           value=Name(id='var_dict', ctx=Load()),
                           slice=Name(id='var_name', ctx=Load()),
                           ctx=Store())],
                     value=Call(
                        func=Attribute(
                           value=Subscript(
                              value=Name(id='var_dict_original', ctx=Load()),
                              slice=Name(id='var_name', ctx=Load()),
                              ctx=Load()),
                           attr='copy',
                           ctx=Load()),
                        args=[],
                        keywords=[
                           keyword(
                              arg='deep',
                              value=Constant(value=True))]))],
               orelse=[])],
         decorator_list=[])],
   type_ignores=[])


# AST van twee hulplijsten
def generate_true_and_unknown_lists(true_list):
    true_list_ast = []
    for elem in true_list:
        true_list_ast.append(Constant(value=elem))
    return Module(
   body=[
      Assign(
         targets=[
            Name(id='true_list', ctx=Store())],
         value=List(
            elts=true_list_ast,
            ctx=Load())),
      Assign(
         targets=[
            Name(id='unknown_list', ctx=Store())],
         value=ListComp(
            elt=Attribute(
               value=Name(id='var', ctx=Load()),
               attr='name',
               ctx=Load()),
            generators=[
               comprehension(
                  target=Name(id='var', ctx=Store()),
                  iter=Name(id='vars', ctx=Load()),
                  ifs=[],
                  is_async=0)]))],
   type_ignores=[])



# AST van een hulpfunctie
def generate_propagate_elem():
    return Module(
   body=[
      FunctionDef(
         name='propagate_elem',
         args=arguments(
            posonlyargs=[],
            args=[
               arg(arg='args')],
            kwonlyargs=[],
            kw_defaults=[],
            defaults=[]),
         body=[
            Assign(
               targets=[
                  Name(id='mask', ctx=Store())],
               value=Compare(
                  left=Name(id='args', ctx=Load()),
                  ops=[
                     NotEq()],
                  comparators=[
                     Attribute(
                        value=Name(id='EB', ctx=Load()),
                        attr='TRUE',
                        ctx=Load())])),
            Assign(
               targets=[
                  Name(id='s', ctx=Store())],
               value=Call(
                  func=Attribute(
                     value=Name(id='mask', ctx=Load()),
                     attr='sum',
                     ctx=Load()),
                  args=[],
                  keywords=[])),
            If(
               test=Compare(
                  left=Name(id='s', ctx=Load()),
                  ops=[
                     Eq()],
                  comparators=[
                     Constant(value=1)]),
               body=[
                  Assign(
                     targets=[
                        Name(id='index', ctx=Store())],
                     value=Subscript(
                        value=Subscript(
                           value=Call(
                              func=Attribute(
                                 value=Name(id='np', ctx=Load()),
                                 attr='where',
                                 ctx=Load()),
                              args=[
                                 Name(id='mask', ctx=Load())],
                              keywords=[]),
                           slice=Constant(value=0),
                           ctx=Load()),
                        slice=Constant(value=0),
                        ctx=Load())),
                  If(
                     test=Compare(
                        left=Subscript(
                           value=Name(id='args', ctx=Load()),
                           slice=Name(id='index', ctx=Load()),
                           ctx=Load()),
                        ops=[
                           Eq()],
                        comparators=[
                           Attribute(
                              value=Name(id='EB', ctx=Load()),
                              attr='UNKNOWN',
                              ctx=Load())]),
                     body=[
                        Return(
                           value=Call(
                              func=Name(id='PropagateResult', ctx=Load()),
                              args=[
                                 Attribute(
                                    value=Name(id='EB', ctx=Load()),
                                    attr='TRUE',
                                    ctx=Load()),
                                 Call(
                                    func=Attribute(
                                       value=Name(id='index', ctx=Load()),
                                       attr='item',
                                       ctx=Load()),
                                    args=[],
                                    keywords=[])],
                              keywords=[]))],
                     orelse=[]),
                  Return(
                     value=Call(
                        func=Name(id='PropagateResult', ctx=Load()),
                        args=[
                           Attribute(
                              value=Name(id='EB', ctx=Load()),
                              attr='NONE',
                              ctx=Load())],
                        keywords=[]))],
               orelse=[]),
            If(
               test=Compare(
                  left=Name(id='s', ctx=Load()),
                  ops=[
                     Eq()],
                  comparators=[
                     Constant(value=0)]),
               body=[
                  Return(
                     value=Call(
                        func=Name(id='PropagateResult', ctx=Load()),
                        args=[
                           Attribute(
                              value=Name(id='EB', ctx=Load()),
                              attr='INCONSISTENT',
                              ctx=Load())],
                        keywords=[]))],
               orelse=[]),
            Return(
               value=Call(
                  func=Name(id='PropagateResult', ctx=Load()),
                  args=[
                     Attribute(
                        value=Name(id='EB', ctx=Load()),
                        attr='NONE',
                        ctx=Load())],
                  keywords=[]))],
         decorator_list=[])],
   type_ignores=[])

# AST van een hulpfunctie
def generate_propagate_fill():
    return Module(
   body=[
      FunctionDef(
         name='propagate_fill',
         args=arguments(
            posonlyargs=[],
            args=[
               arg(arg='args')],
            kwonlyargs=[],
            kw_defaults=[],
            defaults=[]),
         body=[
            Assign(
               targets=[
                  Name(id='mapping', ctx=Store())],
               value=Dict(
                  keys=[
                     Attribute(
                        value=Name(id='EB', ctx=Load()),
                        attr='UNKNOWN',
                        ctx=Load()),
                     Attribute(
                        value=Name(id='EB', ctx=Load()),
                        attr='TRUE',
                        ctx=Load()),
                     Attribute(
                        value=Name(id='EB', ctx=Load()),
                        attr='FALSE',
                        ctx=Load())],
                  values=[
                     Attribute(
                        value=Name(id='EB', ctx=Load()),
                        attr='TRUE',
                        ctx=Load()),
                     Attribute(
                        value=Name(id='EB', ctx=Load()),
                        attr='NONE',
                        ctx=Load()),
                     Attribute(
                        value=Name(id='EB', ctx=Load()),
                        attr='INCONSISTENT',
                        ctx=Load())])),
            Return(
               value=ListComp(
                  elt=Call(
                     func=Attribute(
                        value=Name(id='mapping', ctx=Load()),
                        attr='get',
                        ctx=Load()),
                     args=[
                        Name(id='arg', ctx=Load()),
                        Name(id='arg', ctx=Load())],
                     keywords=[]),
                  generators=[
                     comprehension(
                        target=Name(id='arg', ctx=Store()),
                        iter=Name(id='args', ctx=Load()),
                        ifs=[],
                        is_async=0)]))],
         decorator_list=[])],
   type_ignores=[])

# AST van een hulpfunctie
def generate_get_from_data_array():
    return Module(
   body=[
      FunctionDef(
         name='get_from_data_array',
         args=arguments(
            posonlyargs=[],
            args=[
               arg(arg='data_array'),
               arg(arg='slices'),
               arg(arg='threshold')],
            kwonlyargs=[],
            kw_defaults=[],
            defaults=[
               Constant(value=100)]),
         body=[
            If(
               test=Compare(
                  left=Call(
                     func=Name(id='len', ctx=Load()),
                     args=[
                        Name(id='slices', ctx=Load())],
                     keywords=[]),
                  ops=[
                     Gt()],
                  comparators=[
                     Name(id='threshold', ctx=Load())]),
               body=[
                  Assign(
                     targets=[
                        Name(id='vals', ctx=Store())],
                     value=Attribute(
                        value=Subscript(
                           value=Attribute(
                              value=Call(
                                 func=Attribute(
                                    value=Name(id='data_array', ctx=Load()),
                                    attr='stack',
                                    ctx=Load()),
                                 args=[],
                                 keywords=[
                                    keyword(
                                       arg='points',
                                       value=Attribute(
                                          value=Name(id='data_array', ctx=Load()),
                                          attr='dims',
                                          ctx=Load()))]),
                              attr='loc',
                              ctx=Load()),
                           slice=Name(id='slices', ctx=Load()),
                           ctx=Load()),
                        attr='values',
                        ctx=Load()))],
               orelse=[
                  Assign(
                     targets=[
                        Name(id='index_list', ctx=Store())],
                     value=ListComp(
                        elt=Call(
                           func=Name(id='dict', ctx=Load()),
                           args=[
                              Call(
                                 func=Name(id='zip', ctx=Load()),
                                 args=[
                                    Attribute(
                                       value=Name(id='data_array', ctx=Load()),
                                       attr='dims',
                                       ctx=Load()),
                                    Name(id='t', ctx=Load())],
                                 keywords=[])],
                           keywords=[]),
                        generators=[
                           comprehension(
                              target=Name(id='t', ctx=Store()),
                              iter=Name(id='slices', ctx=Load()),
                              ifs=[],
                              is_async=0)])),
                  Assign(
                     targets=[
                        Name(id='vals', ctx=Store())],
                     value=ListComp(
                        elt=Call(
                           func=Attribute(
                              value=Attribute(
                                 value=Subscript(
                                    value=Attribute(
                                       value=Name(id='data_array', ctx=Load()),
                                       attr='loc',
                                       ctx=Load()),
                                    slice=Name(id='i', ctx=Load()),
                                    ctx=Load()),
                                 attr='values',
                                 ctx=Load()),
                              attr='item',
                              ctx=Load()),
                           args=[],
                           keywords=[]),
                        generators=[
                           comprehension(
                              target=Name(id='i', ctx=Store()),
                              iter=Name(id='index_list', ctx=Load()),
                              ifs=[],
                              is_async=0)]))]),
            Return(
               value=Name(id='vals', ctx=Load()))],
         decorator_list=[])],
   type_ignores=[])

# AST van een hulpfunctie
def generate_inverse():
    return Module(
   body=[
      FunctionDef(
         name='inverse',
         args=arguments(
            posonlyargs=[],
            args=[
               arg(arg='x')],
            kwonlyargs=[],
            kw_defaults=[],
            defaults=[]),
         body=[
            If(
               test=Compare(
                  left=Name(id='x', ctx=Load()),
                  ops=[
                     Eq()],
                  comparators=[
                     Attribute(
                        value=Name(id='EB', ctx=Load()),
                        attr='TRUE',
                        ctx=Load())]),
               body=[
                  Return(
                     value=Attribute(
                        value=Name(id='EB', ctx=Load()),
                        attr='FALSE',
                        ctx=Load()))],
               orelse=[]),
            If(
               test=Compare(
                  left=Name(id='x', ctx=Load()),
                  ops=[
                     Eq()],
                  comparators=[
                     Attribute(
                        value=Name(id='EB', ctx=Load()),
                        attr='FALSE',
                        ctx=Load())]),
               body=[
                  Return(
                     value=Attribute(
                        value=Name(id='EB', ctx=Load()),
                        attr='TRUE',
                        ctx=Load()))],
               orelse=[]),
            Return(
               value=Name(id='x', ctx=Load()))],
         decorator_list=[])],
   type_ignores=[])

# AST van een hulpfunctie
def generate_append_changes():
    return Module(
        body=[
            FunctionDef(
                name='append_changes',
                args=arguments(
                    posonlyargs=[],
                    args=[
                        arg(arg='old'),
                        arg(arg='new')],
                    kwonlyargs=[],
                    kw_defaults=[],
                    defaults=[]),
                body=[
                    Global(
                        names=[
                            'unknown_list']),
                    For(
                        target=Name(id='key', ctx=Store()),
                        iter=Call(
                            func=Attribute(
                                value=Name(id='new', ctx=Load()),
                                attr='keys',
                                ctx=Load()),
                            args=[],
                            keywords=[]),
                        body=[
                            If(
                                test=Compare(
                                    left=Name(id='key', ctx=Load()),
                                    ops=[
                                        In()],
                                    comparators=[
                                        Call(
                                            func=Attribute(
                                                value=Name(id='old', ctx=Load()),
                                                attr='keys',
                                                ctx=Load()),
                                            args=[],
                                            keywords=[])]),
                                body=[
                                    Expr(
                                        value=Call(
                                            func=Attribute(
                                                value=Attribute(
                                                    value=Subscript(
                                                        value=Name(id='old', ctx=Load()),
                                                        slice=Name(id='key', ctx=Load()),
                                                        ctx=Load()),
                                                    attr='true_slicing',
                                                    ctx=Load()),
                                                attr='extend',
                                                ctx=Load()),
                                            args=[
                                                Attribute(
                                                    value=Subscript(
                                                        value=Name(id='new', ctx=Load()),
                                                        slice=Name(id='key', ctx=Load()),
                                                        ctx=Load()),
                                                    attr='true_slicing',
                                                    ctx=Load())],
                                            keywords=[])),
                                    Expr(
                                        value=Call(
                                            func=Attribute(
                                                value=Attribute(
                                                    value=Subscript(
                                                        value=Name(id='old', ctx=Load()),
                                                        slice=Name(id='key', ctx=Load()),
                                                        ctx=Load()),
                                                    attr='false_slicing',
                                                    ctx=Load()),
                                                attr='extend',
                                                ctx=Load()),
                                            args=[
                                                Attribute(
                                                    value=Subscript(
                                                        value=Name(id='new', ctx=Load()),
                                                        slice=Name(id='key', ctx=Load()),
                                                        ctx=Load()),
                                                    attr='false_slicing',
                                                    ctx=Load())],
                                            keywords=[]))],
                                orelse=[
                                    Assign(
                                        targets=[
                                            Subscript(
                                                value=Name(id='old', ctx=Load()),
                                                slice=Name(id='key', ctx=Load()),
                                                ctx=Store())],
                                        value=Call(
                                            func=Name(id='Change', ctx=Load()),
                                            args=[
                                                Name(id='key', ctx=Load()),
                                                Attribute(
                                                    value=Subscript(
                                                        value=Name(id='new', ctx=Load()),
                                                        slice=Name(id='key', ctx=Load()),
                                                        ctx=Load()),
                                                    attr='true_slicing',
                                                    ctx=Load()),
                                                Attribute(
                                                    value=Subscript(
                                                        value=Name(id='new', ctx=Load()),
                                                        slice=Name(id='key', ctx=Load()),
                                                        ctx=Load()),
                                                    attr='false_slicing',
                                                    ctx=Load())],
                                            keywords=[]))])],
                        orelse=[]),
                    Assign(
                        targets=[
                            Name(id='unknown_list', ctx=Store())],
                        value=ListComp(
                            elt=Name(id='elem', ctx=Load()),
                            generators=[
                                comprehension(
                                    target=Name(id='elem', ctx=Store()),
                                    iter=Name(id='unknown_list', ctx=Load()),
                                    ifs=[
                                        Compare(
                                            left=Name(id='elem', ctx=Load()),
                                            ops=[
                                                NotIn()],
                                            comparators=[
                                                Call(
                                                    func=Attribute(
                                                        value=Name(id='new', ctx=Load()),
                                                        attr='keys',
                                                        ctx=Load()),
                                                    args=[],
                                                    keywords=[])])],
                                    is_async=0)]))],
                decorator_list=[])],
        type_ignores=[])


# AST van een hulpfunctie
def generate_get_from_data_array_wrap():
    return Module(
   body=[
      FunctionDef(
         name='get_from_data_array_wrap',
         args=arguments(
            posonlyargs=[],
            args=[
               arg(arg='name'),
               arg(arg='slice'),
               arg(arg='bool')],
            kwonlyargs=[],
            kw_defaults=[],
            defaults=[]),
         body=[
            If(
               test=Compare(
                  left=Name(id='name', ctx=Load()),
                  ops=[
                     Eq()],
                  comparators=[
                     Constant(value=';EQ')]),
               body=[
                  Assign(
                     targets=[
                        Name(id='temp_result', ctx=Store())],
                     value=ListComp(
                        elt=IfExp(
                           test=Compare(
                              left=Subscript(
                                 value=Name(id='s', ctx=Load()),
                                 slice=Constant(value=0),
                                 ctx=Load()),
                              ops=[
                                 Eq()],
                              comparators=[
                                 Subscript(
                                    value=Name(id='s', ctx=Load()),
                                    slice=Constant(value=1),
                                    ctx=Load())]),
                           body=Attribute(
                              value=Name(id='EB', ctx=Load()),
                              attr='TRUE',
                              ctx=Load()),
                           orelse=Attribute(
                              value=Name(id='EB', ctx=Load()),
                              attr='FALSE',
                              ctx=Load())),
                        generators=[
                           comprehension(
                              target=Name(id='s', ctx=Store()),
                              iter=Name(id='slice', ctx=Load()),
                              ifs=[],
                              is_async=0)]))],
               orelse=[
                  If(
                     test=Compare(
                        left=Name(id='name', ctx=Load()),
                        ops=[
                           Eq()],
                        comparators=[
                           Constant(value='_NEQ')]),
                     body=[
                        Assign(
                           targets=[
                              Name(id='temp_result', ctx=Store())],
                           value=ListComp(
                              elt=IfExp(
                                 test=Compare(
                                    left=Subscript(
                                       value=Name(id='s', ctx=Load()),
                                       slice=Constant(value=0),
                                       ctx=Load()),
                                    ops=[
                                       NotEq()],
                                    comparators=[
                                       Subscript(
                                          value=Name(id='s', ctx=Load()),
                                          slice=Constant(value=1),
                                          ctx=Load())]),
                                 body=Attribute(
                                    value=Name(id='EB', ctx=Load()),
                                    attr='TRUE',
                                    ctx=Load()),
                                 orelse=Attribute(
                                    value=Name(id='EB', ctx=Load()),
                                    attr='FALSE',
                                    ctx=Load())),
                              generators=[
                                 comprehension(
                                    target=Name(id='s', ctx=Store()),
                                    iter=Name(id='slice', ctx=Load()),
                                    ifs=[],
                                    is_async=0)]))],
                     orelse=[
                        If(
                           test=Compare(
                              left=Name(id='name', ctx=Load()),
                              ops=[
                                 Eq()],
                              comparators=[
                                 Constant(value='_LEQ')]),
                           body=[
                              Assign(
                                 targets=[
                                    Name(id='temp_result', ctx=Store())],
                                 value=ListComp(
                                    elt=IfExp(
                                       test=Compare(
                                          left=Subscript(
                                             value=Name(id='s', ctx=Load()),
                                             slice=Constant(value=0),
                                             ctx=Load()),
                                          ops=[
                                             LtE()],
                                          comparators=[
                                             Subscript(
                                                value=Name(id='s', ctx=Load()),
                                                slice=Constant(value=1),
                                                ctx=Load())]),
                                       body=Attribute(
                                          value=Name(id='EB', ctx=Load()),
                                          attr='TRUE',
                                          ctx=Load()),
                                       orelse=Attribute(
                                          value=Name(id='EB', ctx=Load()),
                                          attr='FALSE',
                                          ctx=Load())),
                                    generators=[
                                       comprehension(
                                          target=Name(id='s', ctx=Store()),
                                          iter=Name(id='slice', ctx=Load()),
                                          ifs=[],
                                          is_async=0)]))],
                           orelse=[
                              If(
                                 test=Compare(
                                    left=Name(id='name', ctx=Load()),
                                    ops=[
                                       Eq()],
                                    comparators=[
                                       Constant(value='_LE')]),
                                 body=[
                                    Assign(
                                       targets=[
                                          Name(id='temp_result', ctx=Store())],
                                       value=ListComp(
                                          elt=IfExp(
                                             test=Compare(
                                                left=Subscript(
                                                   value=Name(id='s', ctx=Load()),
                                                   slice=Constant(value=0),
                                                   ctx=Load()),
                                                ops=[
                                                   Lt()],
                                                comparators=[
                                                   Subscript(
                                                      value=Name(id='s', ctx=Load()),
                                                      slice=Constant(value=1),
                                                      ctx=Load())]),
                                             body=Attribute(
                                                value=Name(id='EB', ctx=Load()),
                                                attr='TRUE',
                                                ctx=Load()),
                                             orelse=Attribute(
                                                value=Name(id='EB', ctx=Load()),
                                                attr='FALSE',
                                                ctx=Load())),
                                          generators=[
                                             comprehension(
                                                target=Name(id='s', ctx=Store()),
                                                iter=Name(id='slice', ctx=Load()),
                                                ifs=[],
                                                is_async=0)]))],
                                 orelse=[
                                    If(
                                       test=Compare(
                                          left=Name(id='name', ctx=Load()),
                                          ops=[
                                             Eq()],
                                          comparators=[
                                             Constant(value='_GE')]),
                                       body=[
                                          Assign(
                                             targets=[
                                                Name(id='temp_result', ctx=Store())],
                                             value=ListComp(
                                                elt=IfExp(
                                                   test=Compare(
                                                      left=Subscript(
                                                         value=Name(id='s', ctx=Load()),
                                                         slice=Constant(value=0),
                                                         ctx=Load()),
                                                      ops=[
                                                         Gt()],
                                                      comparators=[
                                                         Subscript(
                                                            value=Name(id='s', ctx=Load()),
                                                            slice=Constant(value=1),
                                                            ctx=Load())]),
                                                   body=Attribute(
                                                      value=Name(id='EB', ctx=Load()),
                                                      attr='TRUE',
                                                      ctx=Load()),
                                                   orelse=Attribute(
                                                      value=Name(id='EB', ctx=Load()),
                                                      attr='FALSE',
                                                      ctx=Load())),
                                                generators=[
                                                   comprehension(
                                                      target=Name(id='s', ctx=Store()),
                                                      iter=Name(id='slice', ctx=Load()),
                                                      ifs=[],
                                                      is_async=0)]))],
                                       orelse=[
                                          If(
                                             test=Compare(
                                                left=Name(id='name', ctx=Load()),
                                                ops=[
                                                   Eq()],
                                                comparators=[
                                                   Constant(value='_GEQ')]),
                                             body=[
                                                Assign(
                                                   targets=[
                                                      Name(id='temp_result', ctx=Store())],
                                                   value=ListComp(
                                                      elt=IfExp(
                                                         test=Compare(
                                                            left=Subscript(
                                                               value=Name(id='s', ctx=Load()),
                                                               slice=Constant(value=0),
                                                               ctx=Load()),
                                                            ops=[
                                                               GtE()],
                                                            comparators=[
                                                               Subscript(
                                                                  value=Name(id='s', ctx=Load()),
                                                                  slice=Constant(value=1),
                                                                  ctx=Load())]),
                                                         body=Attribute(
                                                            value=Name(id='EB', ctx=Load()),
                                                            attr='TRUE',
                                                            ctx=Load()),
                                                         orelse=Attribute(
                                                            value=Name(id='EB', ctx=Load()),
                                                            attr='FALSE',
                                                            ctx=Load())),
                                                      generators=[
                                                         comprehension(
                                                            target=Name(id='s', ctx=Store()),
                                                            iter=Name(id='slice', ctx=Load()),
                                                            ifs=[],
                                                            is_async=0)]))],
                                             orelse=[
                                                If(
                                                   test=Compare(
                                                      left=Name(id='name', ctx=Load()),
                                                      ops=[
                                                         In()],
                                                      comparators=[
                                                         Name(id='true_list', ctx=Load())]),
                                                   body=[
                                                      Assign(
                                                         targets=[
                                                            Name(id='temp_result', ctx=Store())],
                                                         value=ListComp(
                                                            elt=Attribute(
                                                               value=Name(id='EB', ctx=Load()),
                                                               attr='TRUE',
                                                               ctx=Load()),
                                                            generators=[
                                                               comprehension(
                                                                  target=Name(id='_', ctx=Store()),
                                                                  iter=Name(id='slice', ctx=Load()),
                                                                  ifs=[],
                                                                  is_async=0)]))],
                                                   orelse=[
                                                      If(
                                                         test=Compare(
                                                            left=Name(id='name', ctx=Load()),
                                                            ops=[
                                                               In()],
                                                            comparators=[
                                                               Name(id='unknown_list', ctx=Load())]),
                                                         body=[
                                                            Return(
                                                               value=ListComp(
                                                                  elt=Attribute(
                                                                     value=Name(id='EB', ctx=Load()),
                                                                     attr='UNKNOWN',
                                                                     ctx=Load()),
                                                                  generators=[
                                                                     comprehension(
                                                                        target=Name(id='_', ctx=Store()),
                                                                        iter=Name(id='slice', ctx=Load()),
                                                                        ifs=[],
                                                                        is_async=0)]))],
                                                         orelse=[
                                                            Assign(
                                                               targets=[
                                                                  Name(id='temp_result', ctx=Store())],
                                                               value=Call(
                                                                  func=Name(id='get_from_data_array', ctx=Load()),
                                                                  args=[
                                                                     Subscript(
                                                                        value=Name(id='var_dict', ctx=Load()),
                                                                        slice=Name(id='name', ctx=Load()),
                                                                        ctx=Load()),
                                                                     Name(id='slice', ctx=Load())],
                                                                  keywords=[]))])])])])])])])]),
            If(
               test=Name(id='bool', ctx=Load()),
               body=[
                  Return(
                     value=Name(id='temp_result', ctx=Load()))],
               orelse=[
                  Return(
                     value=Call(
                        func=Call(
                           func=Attribute(
                              value=Name(id='np', ctx=Load()),
                              attr='vectorize',
                              ctx=Load()),
                           args=[
                              Name(id='inverse', ctx=Load())],
                           keywords=[]),
                        args=[
                           Name(id='temp_result', ctx=Load())],
                        keywords=[]))])],
         decorator_list=[])],
   type_ignores=[])


def generate_write_to_data_array():
    return Module(
   body=[
      FunctionDef(
         name='write_to_data_array',
         args=arguments(
            posonlyargs=[],
            args=[
               arg(arg='slice_dict')],
            kwonlyargs=[],
            kw_defaults=[],
            defaults=[]),
         body=[
            Assign(
               targets=[
                  Name(id='new_changes', ctx=Store())],
               value=Dict(keys=[], values=[])),
            For(
               target=Name(id='p', ctx=Store()),
               iter=Call(
                  func=Attribute(
                     value=Name(id='slice_dict', ctx=Load()),
                     attr='keys',
                     ctx=Load()),
                  args=[],
                  keywords=[]),
               body=[
                  If(
                     test=Compare(
                        left=Call(
                           func=Name(id='len', ctx=Load()),
                           args=[
                              Subscript(
                                 value=Name(id='slice_dict', ctx=Load()),
                                 slice=Name(id='p', ctx=Load()),
                                 ctx=Load())],
                           keywords=[]),
                        ops=[
                           Gt()],
                        comparators=[
                           Constant(value=100)]),
                     body=[
                        Assign(
                           targets=[
                              Name(id='da', ctx=Store())],
                           value=Subscript(
                              value=Name(id='var_dict', ctx=Load()),
                              slice=Attribute(
                                 value=Name(id='p', ctx=Load()),
                                 attr='name',
                                 ctx=Load()),
                              ctx=Load())),
                        Assign(
                           targets=[
                              Name(id='stacked', ctx=Store())],
                           value=Call(
                              func=Attribute(
                                 value=Subscript(
                                    value=Name(id='var_dict', ctx=Load()),
                                    slice=Attribute(
                                       value=Name(id='p', ctx=Load()),
                                       attr='name',
                                       ctx=Load()),
                                    ctx=Load()),
                                 attr='stack',
                                 ctx=Load()),
                              args=[],
                              keywords=[
                                 keyword(
                                    arg='points',
                                    value=Attribute(
                                       value=Name(id='da', ctx=Load()),
                                       attr='dims',
                                       ctx=Load()))])),
                        If(
                           test=Attribute(
                              value=Name(id='p', ctx=Load()),
                              attr='b',
                              ctx=Load()),
                           body=[
                              Assign(
                                 targets=[
                                    Subscript(
                                       value=Attribute(
                                          value=Name(id='stacked', ctx=Load()),
                                          attr='loc',
                                          ctx=Load()),
                                       slice=Subscript(
                                          value=Name(id='slice_dict', ctx=Load()),
                                          slice=Name(id='p', ctx=Load()),
                                          ctx=Load()),
                                       ctx=Store())],
                                 value=Attribute(
                                    value=Name(id='EB', ctx=Load()),
                                    attr='FALSE',
                                    ctx=Load())),
                              Expr(
                                 value=Call(
                                    func=Name(id='append_changes', ctx=Load()),
                                    args=[
                                       Name(id='new_changes', ctx=Load()),
                                       Dict(
                                          keys=[
                                             Attribute(
                                                value=Name(id='p', ctx=Load()),
                                                attr='name',
                                                ctx=Load())],
                                          values=[
                                             Call(
                                                func=Name(id='Change', ctx=Load()),
                                                args=[
                                                   Attribute(
                                                      value=Name(id='p', ctx=Load()),
                                                      attr='name',
                                                      ctx=Load()),
                                                   List(elts=[], ctx=Load()),
                                                   Subscript(
                                                      value=Name(id='slice_dict', ctx=Load()),
                                                      slice=Name(id='p', ctx=Load()),
                                                      ctx=Load())],
                                                keywords=[])])],
                                    keywords=[]))],
                           orelse=[
                              Assign(
                                 targets=[
                                    Subscript(
                                       value=Attribute(
                                          value=Name(id='stacked', ctx=Load()),
                                          attr='loc',
                                          ctx=Load()),
                                       slice=Subscript(
                                          value=Name(id='slice_dict', ctx=Load()),
                                          slice=Name(id='p', ctx=Load()),
                                          ctx=Load()),
                                       ctx=Store())],
                                 value=Attribute(
                                    value=Name(id='EB', ctx=Load()),
                                    attr='TRUE',
                                    ctx=Load())),
                              Expr(
                                 value=Call(
                                    func=Name(id='append_changes', ctx=Load()),
                                    args=[
                                       Name(id='new_changes', ctx=Load()),
                                       Dict(
                                          keys=[
                                             Attribute(
                                                value=Name(id='p', ctx=Load()),
                                                attr='name',
                                                ctx=Load())],
                                          values=[
                                             Call(
                                                func=Name(id='Change', ctx=Load()),
                                                args=[
                                                   Attribute(
                                                      value=Name(id='p', ctx=Load()),
                                                      attr='name',
                                                      ctx=Load()),
                                                   Subscript(
                                                      value=Name(id='slice_dict', ctx=Load()),
                                                      slice=Name(id='p', ctx=Load()),
                                                      ctx=Load()),
                                                   List(elts=[], ctx=Load())],
                                                keywords=[])])],
                                    keywords=[]))]),
                        Assign(
                           targets=[
                              Subscript(
                                 value=Name(id='var_dict', ctx=Load()),
                                 slice=Attribute(
                                    value=Name(id='p', ctx=Load()),
                                    attr='name',
                                    ctx=Load()),
                                 ctx=Store())],
                           value=Call(
                              func=Attribute(
                                 value=Name(id='stacked', ctx=Load()),
                                 attr='unstack',
                                 ctx=Load()),
                              args=[],
                              keywords=[]))],
                     orelse=[
                        If(
                           test=Attribute(
                              value=Name(id='p', ctx=Load()),
                              attr='b',
                              ctx=Load()),
                           body=[
                              For(
                                 target=Name(id='s', ctx=Store()),
                                 iter=Subscript(
                                    value=Name(id='slice_dict', ctx=Load()),
                                    slice=Name(id='p', ctx=Load()),
                                    ctx=Load()),
                                 body=[
                                    Assign(
                                       targets=[
                                          Subscript(
                                             value=Attribute(
                                                value=Subscript(
                                                   value=Name(id='var_dict', ctx=Load()),
                                                   slice=Attribute(
                                                      value=Name(id='p', ctx=Load()),
                                                      attr='name',
                                                      ctx=Load()),
                                                   ctx=Load()),
                                                attr='loc',
                                                ctx=Load()),
                                             slice=Name(id='s', ctx=Load()),
                                             ctx=Store())],
                                       value=Attribute(
                                          value=Name(id='EB', ctx=Load()),
                                          attr='FALSE',
                                          ctx=Load()))],
                                 orelse=[]),
                              Expr(
                                 value=Call(
                                    func=Name(id='append_changes', ctx=Load()),
                                    args=[
                                       Name(id='new_changes', ctx=Load()),
                                       Dict(
                                          keys=[
                                             Attribute(
                                                value=Name(id='p', ctx=Load()),
                                                attr='name',
                                                ctx=Load())],
                                          values=[
                                             Call(
                                                func=Name(id='Change', ctx=Load()),
                                                args=[
                                                   Attribute(
                                                      value=Name(id='p', ctx=Load()),
                                                      attr='name',
                                                      ctx=Load()),
                                                   List(elts=[], ctx=Load()),
                                                   Subscript(
                                                      value=Name(id='slice_dict', ctx=Load()),
                                                      slice=Name(id='p', ctx=Load()),
                                                      ctx=Load())],
                                                keywords=[])])],
                                    keywords=[]))],
                           orelse=[
                              For(
                                 target=Name(id='s', ctx=Store()),
                                 iter=Subscript(
                                    value=Name(id='slice_dict', ctx=Load()),
                                    slice=Name(id='p', ctx=Load()),
                                    ctx=Load()),
                                 body=[
                                    Assign(
                                       targets=[
                                          Subscript(
                                             value=Attribute(
                                                value=Subscript(
                                                   value=Name(id='var_dict', ctx=Load()),
                                                   slice=Attribute(
                                                      value=Name(id='p', ctx=Load()),
                                                      attr='name',
                                                      ctx=Load()),
                                                   ctx=Load()),
                                                attr='loc',
                                                ctx=Load()),
                                             slice=Name(id='s', ctx=Load()),
                                             ctx=Store())],
                                       value=Attribute(
                                          value=Name(id='EB', ctx=Load()),
                                          attr='TRUE',
                                          ctx=Load()))],
                                 orelse=[]),
                              Expr(
                                 value=Call(
                                    func=Name(id='append_changes', ctx=Load()),
                                    args=[
                                       Name(id='new_changes', ctx=Load()),
                                       Dict(
                                          keys=[
                                             Attribute(
                                                value=Name(id='p', ctx=Load()),
                                                attr='name',
                                                ctx=Load())],
                                          values=[
                                             Call(
                                                func=Name(id='Change', ctx=Load()),
                                                args=[
                                                   Attribute(
                                                      value=Name(id='p', ctx=Load()),
                                                      attr='name',
                                                      ctx=Load()),
                                                   Subscript(
                                                      value=Name(id='slice_dict', ctx=Load()),
                                                      slice=Name(id='p', ctx=Load()),
                                                      ctx=Load()),
                                                   List(elts=[], ctx=Load())],
                                                keywords=[])])],
                                    keywords=[]))])])],
               orelse=[]),
            Return(
               value=Name(id='new_changes', ctx=Load()))],
         decorator_list=[])],
   type_ignores=[])




def generate_handle_propagate_results():
    return Module(
   body=[
      FunctionDef(
         name='handle_propagate_results',
         args=arguments(
            posonlyargs=[],
            args=[
               arg(arg='rule'),
               arg(arg='result_list')],
            kwonlyargs=[],
            kw_defaults=[],
            defaults=[]),
         body=[
            Assign(
               targets=[
                  Name(id='incons_indices', ctx=Store())],
               value=Subscript(
                  value=Call(
                     func=Attribute(
                        value=Name(id='np', ctx=Load()),
                        attr='where',
                        ctx=Load()),
                     args=[
                        Compare(
                           left=Name(id='result_list', ctx=Load()),
                           ops=[
                              Eq()],
                           comparators=[
                              Call(
                                 func=Name(id='PropagateResult', ctx=Load()),
                                 args=[
                                    Attribute(
                                       value=Name(id='EB', ctx=Load()),
                                       attr='INCONSISTENT',
                                       ctx=Load())],
                                 keywords=[])])],
                     keywords=[]),
                  slice=Constant(value=0),
                  ctx=Load())),
            If(
               test=Compare(
                  left=Call(
                     func=Name(id='len', ctx=Load()),
                     args=[
                        Name(id='incons_indices', ctx=Load())],
                     keywords=[]),
                  ops=[
                     Gt()],
                  comparators=[
                     Constant(value=0)]),
               body=[
                  Raise(
                     exc=Call(
                        func=Name(id='Exception', ctx=Load()),
                        args=[
                           BinOp(
                              left=Constant(value='Inconsistency error in: '),
                              op=Add(),
                              right=Attribute(
                                 value=Subscript(
                                    value=Name(id='rule', ctx=Load()),
                                    slice=Constant(value=0),
                                    ctx=Load()),
                                 attr='name',
                                 ctx=Load()))],
                        keywords=[]))],
               orelse=[]),
            Assign(
               targets=[
                  Name(id='true_indices', ctx=Store())],
               value=Subscript(
                  value=Call(
                     func=Attribute(
                        value=Name(id='np', ctx=Load()),
                        attr='where',
                        ctx=Load()),
                     args=[
                        ListComp(
                           elt=Compare(
                              left=Attribute(
                                 value=Name(id='res', ctx=Load()),
                                 attr='truth',
                                 ctx=Load()),
                              ops=[
                                 Eq()],
                              comparators=[
                                 Attribute(
                                    value=Name(id='EB', ctx=Load()),
                                    attr='TRUE',
                                    ctx=Load())]),
                           generators=[
                              comprehension(
                                 target=Name(id='res', ctx=Store()),
                                 iter=Name(id='result_list', ctx=Load()),
                                 ifs=[],
                                 is_async=0)])],
                     keywords=[]),
                  slice=Constant(value=0),
                  ctx=Load())),
            If(
               test=Compare(
                  left=Call(
                     func=Name(id='len', ctx=Load()),
                     args=[
                        Name(id='true_indices', ctx=Load())],
                     keywords=[]),
                  ops=[
                     Gt()],
                  comparators=[
                     Constant(value=0)]),
               body=[
                  Assign(
                     targets=[
                        Name(id='changed_slices', ctx=Store())],
                     value=ListComp(
                        elt=Subscript(
                           value=Attribute(
                              value=Subscript(
                                 value=Name(id='rule', ctx=Load()),
                                 slice=Attribute(
                                    value=Subscript(
                                       value=Name(id='result_list', ctx=Load()),
                                       slice=Name(id='i', ctx=Load()),
                                       ctx=Load()),
                                    attr='position',
                                    ctx=Load()),
                                 ctx=Load()),
                              attr='slicing',
                              ctx=Load()),
                           slice=Name(id='i', ctx=Load()),
                           ctx=Load()),
                        generators=[
                           comprehension(
                              target=Name(id='i', ctx=Store()),
                              iter=Name(id='true_indices', ctx=Load()),
                              ifs=[],
                              is_async=0)])),
                  Assign(
                     targets=[
                        Name(id='changed_rcs', ctx=Store())],
                     value=ListComp(
                        elt=Subscript(
                           value=Name(id='rule', ctx=Load()),
                           slice=Attribute(
                              value=Subscript(
                                 value=Name(id='result_list', ctx=Load()),
                                 slice=Name(id='i', ctx=Load()),
                                 ctx=Load()),
                              attr='position',
                              ctx=Load()),
                           ctx=Load()),
                        generators=[
                           comprehension(
                              target=Name(id='i', ctx=Store()),
                              iter=Name(id='true_indices', ctx=Load()),
                              ifs=[],
                              is_async=0)])),
                  Assign(
                     targets=[
                        Name(id='slices_per_rc', ctx=Store())],
                     value=Dict(keys=[], values=[])),
                  For(
                     target=Tuple(
                        elts=[
                           Name(id='s', ctx=Store()),
                           Name(id='p', ctx=Store())],
                        ctx=Store()),
                     iter=Call(
                        func=Name(id='zip', ctx=Load()),
                        args=[
                           Name(id='changed_slices', ctx=Load()),
                           Name(id='changed_rcs', ctx=Load())],
                        keywords=[]),
                     body=[
                        If(
                           test=Compare(
                              left=Name(id='p', ctx=Load()),
                              ops=[
                                 NotIn()],
                              comparators=[
                                 Call(
                                    func=Attribute(
                                       value=Name(id='slices_per_rc', ctx=Load()),
                                       attr='keys',
                                       ctx=Load()),
                                    args=[],
                                    keywords=[])]),
                           body=[
                              Assign(
                                 targets=[
                                    Subscript(
                                       value=Name(id='slices_per_rc', ctx=Load()),
                                       slice=Name(id='p', ctx=Load()),
                                       ctx=Store())],
                                 value=List(
                                    elts=[
                                       Name(id='s', ctx=Load())],
                                    ctx=Load()))],
                           orelse=[
                              Expr(
                                 value=Call(
                                    func=Attribute(
                                       value=Subscript(
                                          value=Name(id='slices_per_rc', ctx=Load()),
                                          slice=Name(id='p', ctx=Load()),
                                          ctx=Load()),
                                       attr='append',
                                       ctx=Load()),
                                    args=[
                                       Name(id='s', ctx=Load())],
                                    keywords=[]))])],
                     orelse=[]),
                  Return(
                     value=Call(
                        func=Name(id='write_to_data_array', ctx=Load()),
                        args=[
                           Name(id='slices_per_rc', ctx=Load())],
                        keywords=[]))],
               orelse=[]),
            Return(
               value=Dict(keys=[], values=[]))],
         decorator_list=[])],
   type_ignores=[])



# AST van een hulpfunctie
def generate_propagate_wrap():
    return Module(
   body=[
      FunctionDef(
         name='propagate_wrap',
         args=arguments(
            posonlyargs=[],
            args=[
               arg(arg='rule')],
            kwonlyargs=[],
            kw_defaults=[],
            defaults=[]),
         body=[
            Assign(
               targets=[
                  Name(id='var_list', ctx=Store())],
               value=ListComp(
                  elt=Call(
                     func=Name(id='get_from_data_array_wrap', ctx=Load()),
                     args=[
                        Attribute(
                           value=Name(id='r', ctx=Load()),
                           attr='name',
                           ctx=Load()),
                        Attribute(
                           value=Name(id='r', ctx=Load()),
                           attr='slicing',
                           ctx=Load()),
                        Attribute(
                           value=Name(id='r', ctx=Load()),
                           attr='b',
                           ctx=Load())],
                     keywords=[]),
                  generators=[
                     comprehension(
                        target=Name(id='r', ctx=Store()),
                        iter=Name(id='rule', ctx=Load()),
                        ifs=[],
                        is_async=0)])),
            Assign(
               targets=[
                  Name(id='result_list', ctx=Store())],
               value=Call(
                  func=Attribute(
                     value=Name(id='np', ctx=Load()),
                     attr='apply_along_axis',
                     ctx=Load()),
                  args=[
                     Name(id='propagate_elem', ctx=Load())],
                  keywords=[
                     keyword(
                        arg='axis',
                        value=Constant(value=0)),
                     keyword(
                        arg='arr',
                        value=Call(
                           func=Attribute(
                              value=Name(id='np', ctx=Load()),
                              attr='array',
                              ctx=Load()),
                           args=[
                              Name(id='var_list', ctx=Load())],
                           keywords=[]))])),
            Assign(
               targets=[
                  Name(id='new_changes', ctx=Store())],
               value=Call(
                  func=Name(id='handle_propagate_results', ctx=Load()),
                  args=[
                     Name(id='rule', ctx=Load()),
                     Name(id='result_list', ctx=Load())],
                  keywords=[])),
            Return(
               value=Name(id='new_changes', ctx=Load()))],
         decorator_list=[])],
   type_ignores=[])



# AST van een hulpfunctie
def generate_propagate_fill_wrap():
    return Module(
   body=[
      FunctionDef(
         name='propagate_fill_wrap',
         args=arguments(
            posonlyargs=[],
            args=[
               arg(arg='big_array'),
               arg(arg='big_slices'),
               arg(arg='bool_value')],
            kwonlyargs=[],
            kw_defaults=[],
            defaults=[]),
         body=[
            Assign(
               targets=[
                  Name(id='args', ctx=Store())],
               value=ListComp(
                  elt=Call(
                     func=Name(id='get_from_data_array_wrap', ctx=Load()),
                     args=[
                        Attribute(
                           value=Name(id='big_array', ctx=Load()),
                           attr='name',
                           ctx=Load()),
                        Name(id='big_slice', ctx=Load()),
                        Name(id='bool_value', ctx=Load())],
                     keywords=[]),
                  generators=[
                     comprehension(
                        target=Name(id='big_slice', ctx=Store()),
                        iter=Name(id='big_slices', ctx=Load()),
                        ifs=[],
                        is_async=0)])),
            Assign(
               targets=[
                  Name(id='result_list', ctx=Store())],
               value=Call(
                  func=Attribute(
                     value=Name(id='np', ctx=Load()),
                     attr='apply_along_axis',
                     ctx=Load()),
                  args=[
                     Name(id='propagate_fill', ctx=Load())],
                  keywords=[
                     keyword(
                        arg='axis',
                        value=Constant(value=0)),
                     keyword(
                        arg='arr',
                        value=Call(
                           func=Attribute(
                              value=Name(id='np', ctx=Load()),
                              attr='array',
                              ctx=Load()),
                           args=[
                              Name(id='args', ctx=Load())],
                           keywords=[]))])),
            Assign(
               targets=[
                  Name(id='detected_changes', ctx=Store())],
               value=Dict(keys=[], values=[])),
            For(
               target=Tuple(
                  elts=[
                     Name(id='i', ctx=Store()),
                     Name(id='res', ctx=Store())],
                  ctx=Store()),
               iter=Call(
                  func=Name(id='enumerate', ctx=Load()),
                  args=[
                     Name(id='result_list', ctx=Load())],
                  keywords=[]),
               body=[
                  Assign(
                     targets=[
                        Name(id='incons_indices', ctx=Store())],
                     value=Subscript(
                        value=Call(
                           func=Attribute(
                              value=Name(id='np', ctx=Load()),
                              attr='where',
                              ctx=Load()),
                           args=[
                              Compare(
                                 left=Name(id='res', ctx=Load()),
                                 ops=[
                                    Eq()],
                                 comparators=[
                                    Attribute(
                                       value=Name(id='EB', ctx=Load()),
                                       attr='INCONSISTENT',
                                       ctx=Load())])],
                           keywords=[]),
                        slice=Constant(value=0),
                        ctx=Load())),
                  If(
                     test=Compare(
                        left=Call(
                           func=Name(id='len', ctx=Load()),
                           args=[
                              Name(id='incons_indices', ctx=Load())],
                           keywords=[]),
                        ops=[
                           Gt()],
                        comparators=[
                           Constant(value=0)]),
                     body=[
                        Raise(
                           exc=Call(
                              func=Name(id='Exception', ctx=Load()),
                              args=[
                                 Constant(value='Inconsistency error in: '),
                                 Attribute(
                                    value=Name(id='big_array', ctx=Load()),
                                    attr='name',
                                    ctx=Load())],
                              keywords=[]))],
                     orelse=[]),
                  Assign(
                     targets=[
                        Name(id='true_indices', ctx=Store())],
                     value=Subscript(
                        value=Call(
                           func=Attribute(
                              value=Name(id='np', ctx=Load()),
                              attr='where',
                              ctx=Load()),
                           args=[
                              Compare(
                                 left=Name(id='res', ctx=Load()),
                                 ops=[
                                    Eq()],
                                 comparators=[
                                    Attribute(
                                       value=Name(id='EB', ctx=Load()),
                                       attr='TRUE',
                                       ctx=Load())])],
                           keywords=[]),
                        slice=Constant(value=0),
                        ctx=Load())),
                  If(
                     test=Compare(
                        left=Call(
                           func=Name(id='len', ctx=Load()),
                           args=[
                              Name(id='true_indices', ctx=Load())],
                           keywords=[]),
                        ops=[
                           Gt()],
                        comparators=[
                           Constant(value=0)]),
                     body=[
                        Assign(
                           targets=[
                              Name(id='changed_slices', ctx=Store())],
                           value=ListComp(
                              elt=Subscript(
                                 value=Subscript(
                                    value=Name(id='big_slices', ctx=Load()),
                                    slice=Name(id='i', ctx=Load()),
                                    ctx=Load()),
                                 slice=Name(id='j', ctx=Load()),
                                 ctx=Load()),
                              generators=[
                                 comprehension(
                                    target=Name(id='j', ctx=Store()),
                                    iter=Name(id='true_indices', ctx=Load()),
                                    ifs=[],
                                    is_async=0)])),
                        Assign(
                           targets=[
                              Name(id='coords_per_dim', ctx=Store())],
                           value=Call(
                              func=Name(id='list', ctx=Load()),
                              args=[
                                 Call(
                                    func=Name(id='zip', ctx=Load()),
                                    args=[
                                       Starred(
                                          value=Name(id='changed_slices', ctx=Load()),
                                          ctx=Load())],
                                    keywords=[])],
                              keywords=[])),
                        Assign(
                           targets=[
                              Name(id='unique_coords_per_dim', ctx=Store())],
                           value=ListComp(
                              elt=Call(
                                 func=Name(id='list', ctx=Load()),
                                 args=[
                                    Call(
                                       func=Name(id='set', ctx=Load()),
                                       args=[
                                          Name(id='c', ctx=Load())],
                                       keywords=[])],
                                 keywords=[]),
                              generators=[
                                 comprehension(
                                    target=Name(id='c', ctx=Store()),
                                    iter=Name(id='coords_per_dim', ctx=Load()),
                                    ifs=[],
                                    is_async=0)])),
                        If(
                           test=Name(id='bool_value', ctx=Load()),
                           body=[
                              Assign(
                                 targets=[
                                    Subscript(
                                       value=Attribute(
                                          value=Name(id='big_array', ctx=Load()),
                                          attr='loc',
                                          ctx=Load()),
                                       slice=Tuple(
                                          elts=[
                                             Starred(
                                                value=Name(id='unique_coords_per_dim', ctx=Load()),
                                                ctx=Load())],
                                          ctx=Load()),
                                       ctx=Store())],
                                 value=Attribute(
                                    value=Name(id='EB', ctx=Load()),
                                    attr='TRUE',
                                    ctx=Load())),
                              Expr(
                                 value=Call(
                                    func=Name(id='append_changes', ctx=Load()),
                                    args=[
                                       Name(id='detected_changes', ctx=Load()),
                                       Dict(
                                          keys=[
                                             Attribute(
                                                value=Name(id='big_array', ctx=Load()),
                                                attr='name',
                                                ctx=Load())],
                                          values=[
                                             Call(
                                                func=Name(id='Change', ctx=Load()),
                                                args=[
                                                   Attribute(
                                                      value=Name(id='big_array', ctx=Load()),
                                                      attr='name',
                                                      ctx=Load()),
                                                   Name(id='changed_slices', ctx=Load()),
                                                   List(elts=[], ctx=Load())],
                                                keywords=[])])],
                                    keywords=[]))],
                           orelse=[
                              Assign(
                                 targets=[
                                    Subscript(
                                       value=Attribute(
                                          value=Name(id='big_array', ctx=Load()),
                                          attr='loc',
                                          ctx=Load()),
                                       slice=Tuple(
                                          elts=[
                                             Starred(
                                                value=Name(id='unique_coords_per_dim', ctx=Load()),
                                                ctx=Load())],
                                          ctx=Load()),
                                       ctx=Store())],
                                 value=Attribute(
                                    value=Name(id='EB', ctx=Load()),
                                    attr='FALSE',
                                    ctx=Load())),
                              Expr(
                                 value=Call(
                                    func=Name(id='append_changes', ctx=Load()),
                                    args=[
                                       Name(id='detected_changes', ctx=Load()),
                                       Dict(
                                          keys=[
                                             Attribute(
                                                value=Name(id='big_array', ctx=Load()),
                                                attr='name',
                                                ctx=Load())],
                                          values=[
                                             Call(
                                                func=Name(id='Change', ctx=Load()),
                                                args=[
                                                   Attribute(
                                                      value=Name(id='big_array', ctx=Load()),
                                                      attr='name',
                                                      ctx=Load()),
                                                   List(elts=[], ctx=Load()),
                                                   Name(id='changed_slices', ctx=Load())],
                                                keywords=[])])],
                                    keywords=[]))])],
                     orelse=[])],
               orelse=[]),
            Return(
               value=Name(id='detected_changes', ctx=Load()))],
         decorator_list=[])],
   type_ignores=[])




def generate_calculate_first_coordinate():
    return Module(
   body=[
      FunctionDef(
         name='calculate_first_coordinate',
         args=arguments(
            posonlyargs=[],
            args=[
               arg(arg='small_coordinate'),
               arg(arg='data_array'),
               arg(arg='changing_dims')],
            kwonlyargs=[],
            kw_defaults=[],
            defaults=[]),
         body=[
            Assign(
               targets=[
                  Name(id='new_coordinate', ctx=Store())],
               value=Call(
                  func=Name(id='tuple', ctx=Load()),
                  args=[
                     Name(id='small_coordinate', ctx=Load())],
                  keywords=[])),
            Assign(
               targets=[
                  Name(id='index', ctx=Store())],
               value=Constant(value=0)),
            For(
               target=Name(id='dim', ctx=Store()),
               iter=Attribute(
                  value=Name(id='data_array', ctx=Load()),
                  attr='dims',
                  ctx=Load()),
               body=[
                  If(
                     test=Compare(
                        left=Name(id='dim', ctx=Load()),
                        ops=[
                           In()],
                        comparators=[
                           Name(id='changing_dims', ctx=Load())]),
                     body=[
                        Assign(
                           targets=[
                              Name(id='new_coordinate', ctx=Store())],
                           value=BinOp(
                              left=BinOp(
                                 left=Subscript(
                                    value=Name(id='new_coordinate', ctx=Load()),
                                    slice=Slice(
                                       upper=Name(id='index', ctx=Load())),
                                    ctx=Load()),
                                 op=Add(),
                                 right=Tuple(
                                    elts=[
                                       Call(
                                          func=Attribute(
                                             value=Subscript(
                                                value=Subscript(
                                                   value=Attribute(
                                                      value=Name(id='data_array', ctx=Load()),
                                                      attr='coords',
                                                      ctx=Load()),
                                                   slice=Name(id='dim', ctx=Load()),
                                                   ctx=Load()),
                                                slice=Constant(value=0),
                                                ctx=Load()),
                                             attr='item',
                                             ctx=Load()),
                                          args=[],
                                          keywords=[])],
                                    ctx=Load())),
                              op=Add(),
                              right=Subscript(
                                 value=Name(id='new_coordinate', ctx=Load()),
                                 slice=Slice(
                                    lower=Name(id='index', ctx=Load())),
                                 ctx=Load())))],
                     orelse=[]),
                  AugAssign(
                     target=Name(id='index', ctx=Store()),
                     op=Add(),
                     value=Constant(value=1))],
               orelse=[]),
            Return(
               value=Name(id='new_coordinate', ctx=Load()))],
         decorator_list=[])],
   type_ignores=[])


def generate_calculate_next_coordinate():
    return Module(
   body=[
      FunctionDef(
         name='calculate_next_coordinate',
         args=arguments(
            posonlyargs=[],
            args=[
               arg(arg='coordinate'),
               arg(arg='data_array'),
               arg(arg='changing_dims')],
            kwonlyargs=[],
            kw_defaults=[],
            defaults=[]),
         body=[
            Assign(
               targets=[
                  Name(id='next_coordinate', ctx=Store())],
               value=Call(
                  func=Name(id='tuple', ctx=Load()),
                  args=[
                     Name(id='coordinate', ctx=Load())],
                  keywords=[])),
            Assign(
               targets=[
                  Name(id='index', ctx=Store())],
               value=Constant(value=0)),
            For(
               target=Name(id='dim', ctx=Store()),
               iter=Attribute(
                  value=Name(id='data_array', ctx=Load()),
                  attr='dims',
                  ctx=Load()),
               body=[
                  If(
                     test=Compare(
                        left=Name(id='dim', ctx=Load()),
                        ops=[
                           In()],
                        comparators=[
                           Name(id='changing_dims', ctx=Load())]),
                     body=[
                        Assign(
                           targets=[
                              Name(id='current_value', ctx=Store())],
                           value=Subscript(
                              value=Name(id='coordinate', ctx=Load()),
                              slice=Name(id='index', ctx=Load()),
                              ctx=Load())),
                        Assign(
                           targets=[
                              Name(id='current_coords', ctx=Store())],
                           value=Attribute(
                              value=Subscript(
                                 value=Attribute(
                                    value=Name(id='data_array', ctx=Load()),
                                    attr='coords',
                                    ctx=Load()),
                                 slice=Name(id='dim', ctx=Load()),
                                 ctx=Load()),
                              attr='values',
                              ctx=Load())),
                        Assign(
                           targets=[
                              Name(id='current_index', ctx=Store())],
                           value=Subscript(
                              value=Subscript(
                                 value=Call(
                                    func=Attribute(
                                       value=Name(id='np', ctx=Load()),
                                       attr='where',
                                       ctx=Load()),
                                    args=[
                                       Compare(
                                          left=Name(id='current_coords', ctx=Load()),
                                          ops=[
                                             Eq()],
                                          comparators=[
                                             Name(id='current_value', ctx=Load())])],
                                    keywords=[]),
                                 slice=Constant(value=0),
                                 ctx=Load()),
                              slice=Constant(value=0),
                              ctx=Load())),
                        If(
                           test=Compare(
                              left=Name(id='current_index', ctx=Load()),
                              ops=[
                                 Lt()],
                              comparators=[
                                 BinOp(
                                    left=Call(
                                       func=Name(id='len', ctx=Load()),
                                       args=[
                                          Name(id='current_coords', ctx=Load())],
                                       keywords=[]),
                                    op=Sub(),
                                    right=Constant(value=1))]),
                           body=[
                              If(
                                 test=Compare(
                                    left=Name(id='index', ctx=Load()),
                                    ops=[
                                       Lt()],
                                    comparators=[
                                       BinOp(
                                          left=Call(
                                             func=Name(id='len', ctx=Load()),
                                             args=[
                                                Attribute(
                                                   value=Name(id='data_array', ctx=Load()),
                                                   attr='dims',
                                                   ctx=Load())],
                                             keywords=[]),
                                          op=Sub(),
                                          right=Constant(value=1))]),
                                 body=[
                                    Assign(
                                       targets=[
                                          Name(id='next_coordinate', ctx=Store())],
                                       value=BinOp(
                                          left=BinOp(
                                             left=Subscript(
                                                value=Name(id='next_coordinate', ctx=Load()),
                                                slice=Slice(
                                                   upper=Name(id='index', ctx=Load())),
                                                ctx=Load()),
                                             op=Add(),
                                             right=Tuple(
                                                elts=[
                                                   Call(
                                                      func=Attribute(
                                                         value=Subscript(
                                                            value=Subscript(
                                                               value=Attribute(
                                                                  value=Name(id='data_array', ctx=Load()),
                                                                  attr='coords',
                                                                  ctx=Load()),
                                                               slice=Name(id='dim', ctx=Load()),
                                                               ctx=Load()),
                                                            slice=BinOp(
                                                               left=Name(id='current_index', ctx=Load()),
                                                               op=Add(),
                                                               right=Constant(value=1)),
                                                            ctx=Load()),
                                                         attr='item',
                                                         ctx=Load()),
                                                      args=[],
                                                      keywords=[])],
                                                ctx=Load())),
                                          op=Add(),
                                          right=Subscript(
                                             value=Name(id='next_coordinate', ctx=Load()),
                                             slice=Slice(
                                                lower=BinOp(
                                                   left=Name(id='index', ctx=Load()),
                                                   op=Add(),
                                                   right=Constant(value=1))),
                                             ctx=Load())))],
                                 orelse=[
                                    Assign(
                                       targets=[
                                          Name(id='next_coordinate', ctx=Store())],
                                       value=BinOp(
                                          left=Subscript(
                                             value=Name(id='next_coordinate', ctx=Load()),
                                             slice=Slice(
                                                upper=Name(id='index', ctx=Load())),
                                             ctx=Load()),
                                          op=Add(),
                                          right=Tuple(
                                             elts=[
                                                Call(
                                                   func=Attribute(
                                                      value=Subscript(
                                                         value=Subscript(
                                                            value=Attribute(
                                                               value=Name(id='data_array', ctx=Load()),
                                                               attr='coords',
                                                               ctx=Load()),
                                                            slice=Name(id='dim', ctx=Load()),
                                                            ctx=Load()),
                                                         slice=BinOp(
                                                            left=Name(id='current_index', ctx=Load()),
                                                            op=Add(),
                                                            right=Constant(value=1)),
                                                         ctx=Load()),
                                                      attr='item',
                                                      ctx=Load()),
                                                   args=[],
                                                   keywords=[])],
                                             ctx=Load())))]),
                              Return(
                                 value=Name(id='next_coordinate', ctx=Load()))],
                           orelse=[
                              If(
                                 test=Compare(
                                    left=Name(id='index', ctx=Load()),
                                    ops=[
                                       Lt()],
                                    comparators=[
                                       BinOp(
                                          left=Call(
                                             func=Name(id='len', ctx=Load()),
                                             args=[
                                                Attribute(
                                                   value=Name(id='data_array', ctx=Load()),
                                                   attr='dims',
                                                   ctx=Load())],
                                             keywords=[]),
                                          op=Sub(),
                                          right=Constant(value=1))]),
                                 body=[
                                    Assign(
                                       targets=[
                                          Name(id='next_coordinate', ctx=Store())],
                                       value=BinOp(
                                          left=BinOp(
                                             left=Subscript(
                                                value=Name(id='next_coordinate', ctx=Load()),
                                                slice=Slice(
                                                   upper=Name(id='index', ctx=Load())),
                                                ctx=Load()),
                                             op=Add(),
                                             right=Tuple(
                                                elts=[
                                                   Call(
                                                      func=Attribute(
                                                         value=Subscript(
                                                            value=Subscript(
                                                               value=Attribute(
                                                                  value=Name(id='data_array', ctx=Load()),
                                                                  attr='coords',
                                                                  ctx=Load()),
                                                               slice=Name(id='dim', ctx=Load()),
                                                               ctx=Load()),
                                                            slice=Constant(value=0),
                                                            ctx=Load()),
                                                         attr='item',
                                                         ctx=Load()),
                                                      args=[],
                                                      keywords=[])],
                                                ctx=Load())),
                                          op=Add(),
                                          right=Subscript(
                                             value=Name(id='next_coordinate', ctx=Load()),
                                             slice=Slice(
                                                lower=BinOp(
                                                   left=Name(id='index', ctx=Load()),
                                                   op=Add(),
                                                   right=Constant(value=1))),
                                             ctx=Load())))],
                                 orelse=[
                                    Return(
                                       value=Constant(value=None))])])],
                     orelse=[]),
                  AugAssign(
                     target=Name(id='index', ctx=Store()),
                     op=Add(),
                     value=Constant(value=1))],
               orelse=[])],
         decorator_list=[])],
   type_ignores=[])


def generate_incremental_propagate():
    return Module(
   body=[
      FunctionDef(
         name='incremental_propagate',
         args=arguments(
            posonlyargs=[],
            args=[
               arg(arg='data_array'),
               arg(arg='small_coordinates'),
               arg(arg='changing_dims'),
               arg(arg='b'),
               arg(arg='unknown_coordinates_list'),
               arg(arg='boolean_list'),
               arg(arg='small_array')],
            kwonlyargs=[],
            kw_defaults=[],
            defaults=[
               Constant(value=None),
               Constant(value=None),
               Constant(value=None)]),
         body=[
            Assign(
               targets=[
                  Name(id='continue_list', ctx=Store())],
               value=ListComp(
                  elt=Constant(value=True),
                  generators=[
                     comprehension(
                        target=Name(id='_', ctx=Store()),
                        iter=Call(
                           func=Name(id='range', ctx=Load()),
                           args=[
                              Call(
                                 func=Name(id='len', ctx=Load()),
                                 args=[
                                    Name(id='small_coordinates', ctx=Load())],
                                 keywords=[])],
                           keywords=[]),
                        ifs=[],
                        is_async=0)])),
            If(
               test=Compare(
                  left=Name(id='unknown_coordinates_list', ctx=Load()),
                  ops=[
                     Is()],
                  comparators=[
                     Constant(value=None)]),
               body=[
                  Assign(
                     targets=[
                        Name(id='unknown_coordinates_list', ctx=Store())],
                     value=ListComp(
                        elt=List(elts=[], ctx=Load()),
                        generators=[
                           comprehension(
                              target=Name(id='_', ctx=Store()),
                              iter=Call(
                                 func=Name(id='range', ctx=Load()),
                                 args=[
                                    Call(
                                       func=Name(id='len', ctx=Load()),
                                       args=[
                                          Name(id='small_coordinates', ctx=Load())],
                                       keywords=[])],
                                 keywords=[]),
                              ifs=[],
                              is_async=0)]))],
               orelse=[]),
            Assign(
               targets=[
                  Name(id='coordinates', ctx=Store())],
               value=ListComp(
                  elt=Call(
                     func=Name(id='calculate_first_coordinate', ctx=Load()),
                     args=[
                        Name(id='small_coordinate', ctx=Load()),
                        Name(id='data_array', ctx=Load()),
                        Name(id='changing_dims', ctx=Load())],
                     keywords=[]),
                  generators=[
                     comprehension(
                        target=Name(id='small_coordinate', ctx=Store()),
                        iter=Name(id='small_coordinates', ctx=Load()),
                        ifs=[],
                        is_async=0)])),
            While(
               test=BoolOp(
                  op=And(),
                  values=[
                     Call(
                        func=Name(id='any', ctx=Load()),
                        args=[
                           Name(id='continue_list', ctx=Load())],
                        keywords=[]),
                     Compare(
                        left=Constant(value=None),
                        ops=[
                           NotIn()],
                        comparators=[
                           Name(id='coordinates', ctx=Load())])]),
               body=[
                  Assign(
                     targets=[
                        Name(id='results', ctx=Store())],
                     value=Call(
                        func=Name(id='get_from_data_array_wrap', ctx=Load()),
                        args=[
                           Attribute(
                              value=Name(id='data_array', ctx=Load()),
                              attr='name',
                              ctx=Load()),
                           Name(id='coordinates', ctx=Load()),
                           Name(id='b', ctx=Load())],
                        keywords=[])),
                  Assign(
                     targets=[
                        Name(id='unknown_coordinates_list', ctx=Store())],
                     value=ListComp(
                        elt=IfExp(
                           test=BoolOp(
                              op=And(),
                              values=[
                                 Compare(
                                    left=Subscript(
                                       value=Name(id='results', ctx=Load()),
                                       slice=Name(id='i', ctx=Load()),
                                       ctx=Load()),
                                    ops=[
                                       Eq()],
                                    comparators=[
                                       Attribute(
                                          value=Name(id='EB', ctx=Load()),
                                          attr='UNKNOWN',
                                          ctx=Load())]),
                                 Compare(
                                    left=Call(
                                       func=Name(id='len', ctx=Load()),
                                       args=[
                                          Subscript(
                                             value=Name(id='unknown_coordinates_list', ctx=Load()),
                                             slice=Name(id='i', ctx=Load()),
                                             ctx=Load())],
                                       keywords=[]),
                                    ops=[
                                       LtE()],
                                    comparators=[
                                       Constant(value=1)])]),
                           body=BinOp(
                              left=Subscript(
                                 value=Name(id='unknown_coordinates_list', ctx=Load()),
                                 slice=Name(id='i', ctx=Load()),
                                 ctx=Load()),
                              op=Add(),
                              right=List(
                                 elts=[
                                    Subscript(
                                       value=Name(id='coordinates', ctx=Load()),
                                       slice=Name(id='i', ctx=Load()),
                                       ctx=Load())],
                                 ctx=Load())),
                           orelse=Subscript(
                              value=Name(id='unknown_coordinates_list', ctx=Load()),
                              slice=Name(id='i', ctx=Load()),
                              ctx=Load())),
                        generators=[
                           comprehension(
                              target=Name(id='i', ctx=Store()),
                              iter=Call(
                                 func=Name(id='range', ctx=Load()),
                                 args=[
                                    Call(
                                       func=Name(id='len', ctx=Load()),
                                       args=[
                                          Name(id='small_coordinates', ctx=Load())],
                                       keywords=[])],
                                 keywords=[]),
                              ifs=[],
                              is_async=0)])),
                  Assign(
                     targets=[
                        Name(id='continue_list', ctx=Store())],
                     value=ListComp(
                        elt=BoolOp(
                           op=And(),
                           values=[
                              BoolOp(
                                 op=Or(),
                                 values=[
                                    Compare(
                                       left=Subscript(
                                          value=Name(id='results', ctx=Load()),
                                          slice=Name(id='i', ctx=Load()),
                                          ctx=Load()),
                                       ops=[
                                          Eq()],
                                       comparators=[
                                          Attribute(
                                             value=Name(id='EB', ctx=Load()),
                                             attr='TRUE',
                                             ctx=Load())]),
                                    Compare(
                                       left=Subscript(
                                          value=Name(id='results', ctx=Load()),
                                          slice=Name(id='i', ctx=Load()),
                                          ctx=Load()),
                                       ops=[
                                          Eq()],
                                       comparators=[
                                          Attribute(
                                             value=Name(id='EB', ctx=Load()),
                                             attr='UNKNOWN',
                                             ctx=Load())])]),
                              Compare(
                                 left=Call(
                                    func=Name(id='len', ctx=Load()),
                                    args=[
                                       Subscript(
                                          value=Name(id='unknown_coordinates_list', ctx=Load()),
                                          slice=Name(id='i', ctx=Load()),
                                          ctx=Load())],
                                    keywords=[]),
                                 ops=[
                                    LtE()],
                                 comparators=[
                                    Constant(value=1)]),
                              Subscript(
                                 value=Name(id='continue_list', ctx=Load()),
                                 slice=Name(id='i', ctx=Load()),
                                 ctx=Load())]),
                        generators=[
                           comprehension(
                              target=Name(id='i', ctx=Store()),
                              iter=Call(
                                 func=Name(id='range', ctx=Load()),
                                 args=[
                                    Call(
                                       func=Name(id='len', ctx=Load()),
                                       args=[
                                          Name(id='results', ctx=Load())],
                                       keywords=[])],
                                 keywords=[]),
                              ifs=[],
                              is_async=0)])),
                  Assign(
                     targets=[
                        Name(id='coordinates', ctx=Store())],
                     value=ListComp(
                        elt=IfExp(
                           test=Subscript(
                              value=Name(id='continue_list', ctx=Load()),
                              slice=Name(id='i', ctx=Load()),
                              ctx=Load()),
                           body=Call(
                              func=Name(id='calculate_next_coordinate', ctx=Load()),
                              args=[
                                 Subscript(
                                    value=Name(id='coordinates', ctx=Load()),
                                    slice=Name(id='i', ctx=Load()),
                                    ctx=Load()),
                                 Name(id='data_array', ctx=Load()),
                                 Name(id='changing_dims', ctx=Load())],
                              keywords=[]),
                           orelse=Subscript(
                              value=Name(id='coordinates', ctx=Load()),
                              slice=Name(id='i', ctx=Load()),
                              ctx=Load())),
                        generators=[
                           comprehension(
                              target=Name(id='i', ctx=Store()),
                              iter=Call(
                                 func=Name(id='range', ctx=Load()),
                                 args=[
                                    Call(
                                       func=Name(id='len', ctx=Load()),
                                       args=[
                                          Name(id='coordinates', ctx=Load())],
                                       keywords=[])],
                                 keywords=[]),
                              ifs=[],
                              is_async=0)]))],
               orelse=[]),
            Assign(
               targets=[
                  Name(id='new_changes', ctx=Store())],
               value=Dict(keys=[], values=[])),
            For(
               target=Tuple(
                  elts=[
                     Name(id='i', ctx=Store()),
                     Name(id='coord_list', ctx=Store())],
                  ctx=Store()),
               iter=Call(
                  func=Name(id='enumerate', ctx=Load()),
                  args=[
                     Name(id='unknown_coordinates_list', ctx=Load())],
                  keywords=[]),
               body=[
                  If(
                     test=BoolOp(
                        op=And(),
                        values=[
                           Compare(
                              left=Call(
                                 func=Name(id='len', ctx=Load()),
                                 args=[
                                    Name(id='coord_list', ctx=Load())],
                                 keywords=[]),
                              ops=[
                                 Eq()],
                              comparators=[
                                 Constant(value=1)]),
                           Subscript(
                              value=Name(id='continue_list', ctx=Load()),
                              slice=Name(id='i', ctx=Load()),
                              ctx=Load())]),
                     body=[
                        Assign(
                           targets=[
                              Name(id='coord', ctx=Store())],
                           value=Subscript(
                              value=Name(id='coord_list', ctx=Load()),
                              slice=Constant(value=0),
                              ctx=Load())),
                        If(
                           test=BoolOp(
                              op=And(),
                              values=[
                                 Compare(
                                    left=Name(id='boolean_list', ctx=Load()),
                                    ops=[
                                       IsNot()],
                                    comparators=[
                                       Constant(value=None)]),
                                 Subscript(
                                    value=Name(id='boolean_list', ctx=Load()),
                                    slice=Name(id='i', ctx=Load()),
                                    ctx=Load())]),
                           body=[
                              If(
                                 test=Name(id='b', ctx=Load()),
                                 body=[
                                    Assign(
                                       targets=[
                                          Subscript(
                                             value=Attribute(
                                                value=Name(id='small_array', ctx=Load()),
                                                attr='loc',
                                                ctx=Load()),
                                             slice=Name(id='coord', ctx=Load()),
                                             ctx=Store())],
                                       value=Attribute(
                                          value=Name(id='EB', ctx=Load()),
                                          attr='TRUE',
                                          ctx=Load())),
                                    Expr(
                                       value=Call(
                                          func=Name(id='append_changes', ctx=Load()),
                                          args=[
                                             Name(id='new_changes', ctx=Load()),
                                             Dict(
                                                keys=[
                                                   Attribute(
                                                      value=Name(id='small_array', ctx=Load()),
                                                      attr='name',
                                                      ctx=Load())],
                                                values=[
                                                   Call(
                                                      func=Name(id='Change', ctx=Load()),
                                                      args=[
                                                         Attribute(
                                                            value=Name(id='small_array', ctx=Load()),
                                                            attr='name',
                                                            ctx=Load()),
                                                         List(
                                                            elts=[
                                                               Name(id='coord', ctx=Load())],
                                                            ctx=Load()),
                                                         List(elts=[], ctx=Load())],
                                                      keywords=[])])],
                                          keywords=[]))],
                                 orelse=[
                                    Assign(
                                       targets=[
                                          Subscript(
                                             value=Attribute(
                                                value=Name(id='small_array', ctx=Load()),
                                                attr='loc',
                                                ctx=Load()),
                                             slice=Name(id='coord', ctx=Load()),
                                             ctx=Store())],
                                       value=Attribute(
                                          value=Name(id='EB', ctx=Load()),
                                          attr='FALSE',
                                          ctx=Load())),
                                    Expr(
                                       value=Call(
                                          func=Name(id='append_changes', ctx=Load()),
                                          args=[
                                             Name(id='new_changes', ctx=Load()),
                                             Dict(
                                                keys=[
                                                   Attribute(
                                                      value=Name(id='small_array', ctx=Load()),
                                                      attr='name',
                                                      ctx=Load())],
                                                values=[
                                                   Call(
                                                      func=Name(id='Change', ctx=Load()),
                                                      args=[
                                                         Attribute(
                                                            value=Name(id='small_array', ctx=Load()),
                                                            attr='name',
                                                            ctx=Load()),
                                                         List(elts=[], ctx=Load()),
                                                         List(
                                                            elts=[
                                                               Name(id='coord', ctx=Load())],
                                                            ctx=Load())],
                                                      keywords=[])])],
                                          keywords=[]))])],
                           orelse=[
                              If(
                                 test=Name(id='b', ctx=Load()),
                                 body=[
                                    Assign(
                                       targets=[
                                          Subscript(
                                             value=Attribute(
                                                value=Name(id='data_array', ctx=Load()),
                                                attr='loc',
                                                ctx=Load()),
                                             slice=Name(id='coord', ctx=Load()),
                                             ctx=Store())],
                                       value=Attribute(
                                          value=Name(id='EB', ctx=Load()),
                                          attr='FALSE',
                                          ctx=Load())),
                                    Expr(
                                       value=Call(
                                          func=Name(id='append_changes', ctx=Load()),
                                          args=[
                                             Name(id='new_changes', ctx=Load()),
                                             Dict(
                                                keys=[
                                                   Attribute(
                                                      value=Name(id='data_array', ctx=Load()),
                                                      attr='name',
                                                      ctx=Load())],
                                                values=[
                                                   Call(
                                                      func=Name(id='Change', ctx=Load()),
                                                      args=[
                                                         Attribute(
                                                            value=Name(id='data_array', ctx=Load()),
                                                            attr='name',
                                                            ctx=Load()),
                                                         List(elts=[], ctx=Load()),
                                                         List(
                                                            elts=[
                                                               Name(id='coord', ctx=Load())],
                                                            ctx=Load())],
                                                      keywords=[])])],
                                          keywords=[]))],
                                 orelse=[
                                    Assign(
                                       targets=[
                                          Subscript(
                                             value=Attribute(
                                                value=Name(id='data_array', ctx=Load()),
                                                attr='loc',
                                                ctx=Load()),
                                             slice=Name(id='coord', ctx=Load()),
                                             ctx=Store())],
                                       value=Attribute(
                                          value=Name(id='EB', ctx=Load()),
                                          attr='TRUE',
                                          ctx=Load())),
                                    Expr(
                                       value=Call(
                                          func=Name(id='append_changes', ctx=Load()),
                                          args=[
                                             Name(id='new_changes', ctx=Load()),
                                             Dict(
                                                keys=[
                                                   Attribute(
                                                      value=Name(id='data_array', ctx=Load()),
                                                      attr='name',
                                                      ctx=Load())],
                                                values=[
                                                   Call(
                                                      func=Name(id='Change', ctx=Load()),
                                                      args=[
                                                         Attribute(
                                                            value=Name(id='data_array', ctx=Load()),
                                                            attr='name',
                                                            ctx=Load()),
                                                         List(
                                                            elts=[
                                                               Name(id='coord', ctx=Load())],
                                                            ctx=Load()),
                                                         List(elts=[], ctx=Load())],
                                                      keywords=[])])],
                                          keywords=[]))])])],
                     orelse=[]),
                  If(
                     test=BoolOp(
                        op=And(),
                        values=[
                           Compare(
                              left=Call(
                                 func=Name(id='len', ctx=Load()),
                                 args=[
                                    Name(id='coord_list', ctx=Load())],
                                 keywords=[]),
                              ops=[
                                 Eq()],
                              comparators=[
                                 Constant(value=0)]),
                           Subscript(
                              value=Name(id='continue_list', ctx=Load()),
                              slice=Name(id='i', ctx=Load()),
                              ctx=Load())]),
                     body=[
                        Raise(
                           exc=Call(
                              func=Name(id='Exception', ctx=Load()),
                              args=[
                                 BinOp(
                                    left=Constant(value='Inconsistency error in: '),
                                    op=Add(),
                                    right=Attribute(
                                       value=Name(id='data_array', ctx=Load()),
                                       attr='name',
                                       ctx=Load()))],
                              keywords=[]))],
                     orelse=[])],
               orelse=[]),
            Return(
               value=Name(id='new_changes', ctx=Load()))],
         decorator_list=[])],
   type_ignores=[])


def generate_incremental_propagate_wrap():
    return Module(
   body=[
      FunctionDef(
         name='incremental_propagate_wrap',
         args=arguments(
            posonlyargs=[],
            args=[
               arg(arg='big_array'),
               arg(arg='small_array'),
               arg(arg='small_coordinates'),
               arg(arg='changing_dims'),
               arg(arg='b')],
            kwonlyargs=[],
            kw_defaults=[],
            defaults=[]),
         body=[
            Assign(
               targets=[
                  Name(id='results', ctx=Store())],
               value=Call(
                  func=Name(id='get_from_data_array_wrap', ctx=Load()),
                  args=[
                     Attribute(
                        value=Name(id='small_array', ctx=Load()),
                        attr='name',
                        ctx=Load()),
                     Name(id='small_coordinates', ctx=Load()),
                     UnaryOp(
                        op=Not(),
                        operand=Name(id='b', ctx=Load()))],
                  keywords=[])),
            Assign(
               targets=[
                  Name(id='used_small_coordinates', ctx=Store())],
               value=List(elts=[], ctx=Load())),
            Assign(
               targets=[
                  Name(id='unknown_coordinates_list', ctx=Store())],
               value=List(elts=[], ctx=Load())),
            Assign(
               targets=[
                  Name(id='boolean_list', ctx=Store())],
               value=List(elts=[], ctx=Load())),
            For(
               target=Tuple(
                  elts=[
                     Name(id='i', ctx=Store()),
                     Name(id='res', ctx=Store())],
                  ctx=Store()),
               iter=Call(
                  func=Name(id='enumerate', ctx=Load()),
                  args=[
                     Name(id='results', ctx=Load())],
                  keywords=[]),
               body=[
                  If(
                     test=Compare(
                        left=Name(id='res', ctx=Load()),
                        ops=[
                           Eq()],
                        comparators=[
                           Attribute(
                              value=Name(id='EB', ctx=Load()),
                              attr='TRUE',
                              ctx=Load())]),
                     body=[
                        Expr(
                           value=Call(
                              func=Attribute(
                                 value=Name(id='used_small_coordinates', ctx=Load()),
                                 attr='append',
                                 ctx=Load()),
                              args=[
                                 Subscript(
                                    value=Name(id='small_coordinates', ctx=Load()),
                                    slice=Name(id='i', ctx=Load()),
                                    ctx=Load())],
                              keywords=[])),
                        Expr(
                           value=Call(
                              func=Attribute(
                                 value=Name(id='unknown_coordinates_list', ctx=Load()),
                                 attr='append',
                                 ctx=Load()),
                              args=[
                                 List(elts=[], ctx=Load())],
                              keywords=[])),
                        Expr(
                           value=Call(
                              func=Attribute(
                                 value=Name(id='boolean_list', ctx=Load()),
                                 attr='append',
                                 ctx=Load()),
                              args=[
                                 Constant(value=False)],
                              keywords=[]))],
                     orelse=[]),
                  If(
                     test=Compare(
                        left=Name(id='res', ctx=Load()),
                        ops=[
                           Eq()],
                        comparators=[
                           Attribute(
                              value=Name(id='EB', ctx=Load()),
                              attr='UNKNOWN',
                              ctx=Load())]),
                     body=[
                        Expr(
                           value=Call(
                              func=Attribute(
                                 value=Name(id='used_small_coordinates', ctx=Load()),
                                 attr='append',
                                 ctx=Load()),
                              args=[
                                 Subscript(
                                    value=Name(id='small_coordinates', ctx=Load()),
                                    slice=Name(id='i', ctx=Load()),
                                    ctx=Load())],
                              keywords=[])),
                        Expr(
                           value=Call(
                              func=Attribute(
                                 value=Name(id='unknown_coordinates_list', ctx=Load()),
                                 attr='append',
                                 ctx=Load()),
                              args=[
                                 List(
                                    elts=[
                                       Subscript(
                                          value=Name(id='small_coordinates', ctx=Load()),
                                          slice=Name(id='i', ctx=Load()),
                                          ctx=Load())],
                                    ctx=Load())],
                              keywords=[])),
                        Expr(
                           value=Call(
                              func=Attribute(
                                 value=Name(id='boolean_list', ctx=Load()),
                                 attr='append',
                                 ctx=Load()),
                              args=[
                                 Constant(value=True)],
                              keywords=[]))],
                     orelse=[])],
               orelse=[]),
            If(
               test=Compare(
                  left=Call(
                     func=Name(id='len', ctx=Load()),
                     args=[
                        Name(id='used_small_coordinates', ctx=Load())],
                     keywords=[]),
                  ops=[
                     Gt()],
                  comparators=[
                     Constant(value=0)]),
               body=[
                  Return(
                     value=Call(
                        func=Name(id='incremental_propagate', ctx=Load()),
                        args=[
                           Name(id='big_array', ctx=Load()),
                           Name(id='used_small_coordinates', ctx=Load()),
                           Name(id='changing_dims', ctx=Load()),
                           Name(id='b', ctx=Load()),
                           Name(id='unknown_coordinates_list', ctx=Load()),
                           Name(id='boolean_list', ctx=Load()),
                           Name(id='small_array', ctx=Load())],
                        keywords=[]))],
               orelse=[]),
            Return(
               value=Dict(keys=[], values=[]))],
         decorator_list=[])],
   type_ignores=[])






# AST van een hulpfunctie
def generate_map_indices():
    return Module(
   body=[
      FunctionDef(
         name='map_indices',
         args=arguments(
            posonlyargs=[],
            args=[
               arg(arg='index'),
               arg(arg='binding1'),
               arg(arg='binding2')],
            kwonlyargs=[],
            kw_defaults=[],
            defaults=[]),
         body=[
            Assign(
               targets=[
                  Name(id='match_with_index', ctx=Store())],
               value=Dict(keys=[], values=[])),
            For(
               target=Tuple(
                  elts=[
                     Name(id='i', ctx=Store()),
                     Name(id='bind1', ctx=Store())],
                  ctx=Store()),
               iter=Call(
                  func=Name(id='enumerate', ctx=Load()),
                  args=[
                     Name(id='binding1', ctx=Load())],
                  keywords=[]),
               body=[
                  Assign(
                     targets=[
                        Subscript(
                           value=Name(id='match_with_index', ctx=Load()),
                           slice=Name(id='bind1', ctx=Load()),
                           ctx=Store())],
                     value=Subscript(
                        value=Name(id='index', ctx=Load()),
                        slice=Name(id='i', ctx=Load()),
                        ctx=Load()))],
               orelse=[]),
            Assign(
               targets=[
                  Name(id='new_index', ctx=Store())],
               value=Call(
                  func=Name(id='tuple', ctx=Load()),
                  args=[],
                  keywords=[])),
            For(
               target=Name(id='bind2', ctx=Store()),
               iter=Name(id='binding2', ctx=Load()),
               body=[
                  If(
                     test=Compare(
                        left=Name(id='bind2', ctx=Load()),
                        ops=[
                           In()],
                        comparators=[
                           Call(
                              func=Attribute(
                                 value=Name(id='match_with_index', ctx=Load()),
                                 attr='keys',
                                 ctx=Load()),
                              args=[],
                              keywords=[])]),
                     body=[
                        AugAssign(
                           target=Name(id='new_index', ctx=Store()),
                           op=Add(),
                           value=Tuple(
                              elts=[
                                 Subscript(
                                    value=Name(id='match_with_index', ctx=Load()),
                                    slice=Name(id='bind2', ctx=Load()),
                                    ctx=Load())],
                              ctx=Load()))],
                     orelse=[
                        AugAssign(
                           target=Name(id='new_index', ctx=Store()),
                           op=Add(),
                           value=Tuple(
                              elts=[
                                 Name(id='bind2', ctx=Load())],
                              ctx=Load()))])],
               orelse=[]),
            Return(
               value=Name(id='new_index', ctx=Load()))],
         decorator_list=[])],
   type_ignores=[])

# AST van een hulpfunctie
def generate_is_valid_index():
    return Module(
   body=[
      FunctionDef(
         name='is_valid_index',
         args=arguments(
            posonlyargs=[],
            args=[
               arg(arg='s'),
               arg(arg='argument'),
               arg(arg='quantified_var')],
            kwonlyargs=[],
            kw_defaults=[],
            defaults=[]),
         body=[
            Assign(
               targets=[
                  Name(id='var_mapping', ctx=Store())],
               value=Dict(keys=[], values=[])),
            For(
               target=Tuple(
                  elts=[
                     Name(id='i', ctx=Store()),
                     Name(id='elem', ctx=Store())],
                  ctx=Store()),
               iter=Call(
                  func=Name(id='enumerate', ctx=Load()),
                  args=[
                     Name(id='s', ctx=Load())],
                  keywords=[]),
               body=[
                  If(
                     test=Compare(
                        left=Subscript(
                           value=Name(id='argument', ctx=Load()),
                           slice=Name(id='i', ctx=Load()),
                           ctx=Load()),
                        ops=[
                           NotIn()],
                        comparators=[
                           Name(id='quantified_var', ctx=Load())]),
                     body=[
                        If(
                           test=Compare(
                              left=Name(id='elem', ctx=Load()),
                              ops=[
                                 NotEq()],
                              comparators=[
                                 Subscript(
                                    value=Name(id='argument', ctx=Load()),
                                    slice=Name(id='i', ctx=Load()),
                                    ctx=Load())]),
                           body=[
                              Return(
                                 value=Constant(value=False))],
                           orelse=[])],
                     orelse=[
                        Assign(
                           targets=[
                              Name(id='arg', ctx=Store())],
                           value=Subscript(
                              value=Name(id='argument', ctx=Load()),
                              slice=Name(id='i', ctx=Load()),
                              ctx=Load())),
                        If(
                           test=Compare(
                              left=Name(id='arg', ctx=Load()),
                              ops=[
                                 In()],
                              comparators=[
                                 Call(
                                    func=Attribute(
                                       value=Name(id='var_mapping', ctx=Load()),
                                       attr='keys',
                                       ctx=Load()),
                                    args=[],
                                    keywords=[])]),
                           body=[
                              If(
                                 test=Compare(
                                    left=Name(id='elem', ctx=Load()),
                                    ops=[
                                       NotEq()],
                                    comparators=[
                                       Subscript(
                                          value=Name(id='var_mapping', ctx=Load()),
                                          slice=Name(id='arg', ctx=Load()),
                                          ctx=Load())]),
                                 body=[
                                    Return(
                                       value=Constant(value=False))],
                                 orelse=[])],
                           orelse=[
                              Assign(
                                 targets=[
                                    Subscript(
                                       value=Name(id='var_mapping', ctx=Load()),
                                       slice=Name(id='arg', ctx=Load()),
                                       ctx=Store())],
                                 value=Name(id='elem', ctx=Load()))])])],
               orelse=[]),
            Return(
               value=Constant(value=True))],
         decorator_list=[])],
   type_ignores=[])

# AST van een hulpfunctie
def generate_map_indices_wrap():
    return Module(
   body=[
      FunctionDef(
         name='map_indices_wrap',
         args=arguments(
            posonlyargs=[],
            args=[
               arg(arg='argument_dict'),
               arg(arg='changed_var'),
               arg(arg='slicing'),
               arg(arg='quantified_var')],
            kwonlyargs=[],
            kw_defaults=[],
            defaults=[]),
         body=[
            If(
               test=Compare(
                  left=Call(
                     func=Name(id='len', ctx=Load()),
                     args=[
                        Name(id='slicing', ctx=Load())],
                     keywords=[]),
                  ops=[
                     Eq()],
                  comparators=[
                     Constant(value=0)]),
               body=[
                  Return(
                     value=Constant(value=None))],
               orelse=[]),
            Assign(
               targets=[
                  Name(id='slicing_dict', ctx=Store())],
               value=Dict(keys=[], values=[])),
            Assign(
               targets=[
                  Name(id='valid_slicing', ctx=Store())],
               value=ListComp(
                  elt=Name(id='s', ctx=Load()),
                  generators=[
                     comprehension(
                        target=Name(id='s', ctx=Store()),
                        iter=Name(id='slicing', ctx=Load()),
                        ifs=[
                           Call(
                              func=Name(id='is_valid_index', ctx=Load()),
                              args=[
                                 Name(id='s', ctx=Load()),
                                 Subscript(
                                    value=Name(id='argument_dict', ctx=Load()),
                                    slice=Name(id='changed_var', ctx=Load()),
                                    ctx=Load()),
                                 Name(id='quantified_var', ctx=Load())],
                              keywords=[])],
                        is_async=0)])),
            Assign(
               targets=[
                  Subscript(
                     value=Name(id='slicing_dict', ctx=Load()),
                     slice=Name(id='changed_var', ctx=Load()),
                     ctx=Store())],
               value=Name(id='valid_slicing', ctx=Load())),
            For(
               target=Tuple(
                  elts=[
                     Name(id='key', ctx=Store()),
                     Name(id='val', ctx=Store())],
                  ctx=Store()),
               iter=Call(
                  func=Attribute(
                     value=Name(id='argument_dict', ctx=Load()),
                     attr='items',
                     ctx=Load()),
                  args=[],
                  keywords=[]),
               body=[
                  If(
                     test=Compare(
                        left=Name(id='val', ctx=Load()),
                        ops=[
                           NotEq()],
                        comparators=[
                           Subscript(
                              value=Name(id='argument_dict', ctx=Load()),
                              slice=Name(id='changed_var', ctx=Load()),
                              ctx=Load())]),
                     body=[
                        Assign(
                           targets=[
                              Name(id='new_slicing', ctx=Store())],
                           value=ListComp(
                              elt=Call(
                                 func=Name(id='map_indices', ctx=Load()),
                                 args=[
                                    Name(id='index', ctx=Load()),
                                    Subscript(
                                       value=Name(id='argument_dict', ctx=Load()),
                                       slice=Name(id='changed_var', ctx=Load()),
                                       ctx=Load()),
                                    Subscript(
                                       value=Name(id='argument_dict', ctx=Load()),
                                       slice=Name(id='key', ctx=Load()),
                                       ctx=Load())],
                                 keywords=[]),
                              generators=[
                                 comprehension(
                                    target=Name(id='index', ctx=Store()),
                                    iter=Subscript(
                                       value=Name(id='slicing_dict', ctx=Load()),
                                       slice=Name(id='changed_var', ctx=Load()),
                                       ctx=Load()),
                                    ifs=[],
                                    is_async=0)])),
                        Assign(
                           targets=[
                              Subscript(
                                 value=Name(id='slicing_dict', ctx=Load()),
                                 slice=Name(id='key', ctx=Load()),
                                 ctx=Store())],
                           value=Name(id='new_slicing', ctx=Load()))],
                     orelse=[
                        Assign(
                           targets=[
                              Subscript(
                                 value=Name(id='slicing_dict', ctx=Load()),
                                 slice=Name(id='key', ctx=Load()),
                                 ctx=Store())],
                           value=Name(id='valid_slicing', ctx=Load()))])],
               orelse=[]),
            Return(
               value=Name(id='slicing_dict', ctx=Load()))],
         decorator_list=[])],
   type_ignores=[])

# AST van een hulpfunctie
def generate_add_dims():
    return Module(
   body=[
      FunctionDef(
         name='add_dims',
         args=arguments(
            posonlyargs=[],
            args=[
               arg(arg='slicing'),
               arg(arg='new'),
               arg(arg='extra_dims')],
            kwonlyargs=[],
            kw_defaults=[],
            defaults=[]),
         body=[
            Assign(
               targets=[
                  Name(id='new_slicing', ctx=Store())],
               value=List(elts=[], ctx=Load())),
            Expr(
               value=Call(
                  func=Attribute(
                     value=Name(id='new_slicing', ctx=Load()),
                     attr='append',
                     ctx=Load()),
                  args=[
                     Call(
                        func=Attribute(
                           value=Name(id='slicing', ctx=Load()),
                           attr='copy',
                           ctx=Load()),
                        args=[],
                        keywords=[])],
                  keywords=[])),
            Assign(
               targets=[
                  Name(id='new_domains', ctx=Store())],
               value=ListComp(
                  elt=Attribute(
                     value=Subscript(
                        value=Attribute(
                           value=Name(id='new', ctx=Load()),
                           attr='coords',
                           ctx=Load()),
                        slice=Name(id='dim', ctx=Load()),
                        ctx=Load()),
                     attr='values',
                     ctx=Load()),
                  generators=[
                     comprehension(
                        target=Name(id='dim', ctx=Store()),
                        iter=Name(id='extra_dims', ctx=Load()),
                        ifs=[],
                        is_async=0)])),
            For(
               target=Name(id='comb', ctx=Store()),
               iter=Call(
                  func=Name(id='product', ctx=Load()),
                  args=[
                     Starred(
                        value=Name(id='new_domains', ctx=Load()),
                        ctx=Load())],
                  keywords=[]),
               body=[
                  Assign(
                     targets=[
                        Name(id='new_slice', ctx=Store())],
                     value=Call(
                        func=Attribute(
                           value=Name(id='slicing', ctx=Load()),
                           attr='copy',
                           ctx=Load()),
                        args=[],
                        keywords=[])),
                  Assign(
                     targets=[
                        Name(id='index', ctx=Store())],
                     value=Constant(value=0)),
                  Assign(
                     targets=[
                        Name(id='c_index', ctx=Store())],
                     value=Constant(value=0)),
                  For(
                     target=Name(id='dim', ctx=Store()),
                     iter=Attribute(
                        value=Name(id='new', ctx=Load()),
                        attr='dims',
                        ctx=Load()),
                     body=[
                        If(
                           test=Compare(
                              left=Name(id='dim', ctx=Load()),
                              ops=[
                                 In()],
                              comparators=[
                                 Name(id='extra_dims', ctx=Load())]),
                           body=[
                              Assign(
                                 targets=[
                                    Name(id='new_slice', ctx=Store())],
                                 value=ListComp(
                                    elt=BinOp(
                                       left=BinOp(
                                          left=Subscript(
                                             value=Name(id='elem', ctx=Load()),
                                             slice=Slice(
                                                upper=Name(id='index', ctx=Load())),
                                             ctx=Load()),
                                          op=Add(),
                                          right=Tuple(
                                             elts=[
                                                Call(
                                                   func=Attribute(
                                                      value=Subscript(
                                                         value=Name(id='comb', ctx=Load()),
                                                         slice=Name(id='c_index', ctx=Load()),
                                                         ctx=Load()),
                                                      attr='item',
                                                      ctx=Load()),
                                                   args=[],
                                                   keywords=[])],
                                             ctx=Load())),
                                       op=Add(),
                                       right=Subscript(
                                          value=Name(id='elem', ctx=Load()),
                                          slice=Slice(
                                             lower=Name(id='index', ctx=Load())),
                                          ctx=Load())),
                                    generators=[
                                       comprehension(
                                          target=Name(id='elem', ctx=Store()),
                                          iter=Name(id='new_slice', ctx=Load()),
                                          ifs=[],
                                          is_async=0)])),
                              AugAssign(
                                 target=Name(id='c_index', ctx=Store()),
                                 op=Add(),
                                 value=Constant(value=1))],
                           orelse=[]),
                        AugAssign(
                           target=Name(id='index', ctx=Store()),
                           op=Add(),
                           value=Constant(value=1))],
                     orelse=[]),
                  Expr(
                     value=Call(
                        func=Attribute(
                           value=Name(id='new_slicing', ctx=Load()),
                           attr='append',
                           ctx=Load()),
                        args=[
                           Name(id='new_slice', ctx=Load())],
                        keywords=[]))],
               orelse=[]),
            Return(
               value=ListComp(
                  elt=Call(
                     func=Name(id='list', ctx=Load()),
                     args=[
                        Name(id='val', ctx=Load())],
                     keywords=[]),
                  generators=[
                     comprehension(
                        target=Tuple(
                           elts=[
                              Name(id='key', ctx=Store()),
                              Name(id='val', ctx=Store())],
                           ctx=Store()),
                        iter=Call(
                           func=Name(id='zip', ctx=Load()),
                           args=[
                              Subscript(
                                 value=Name(id='new_slicing', ctx=Load()),
                                 slice=Constant(value=0),
                                 ctx=Load()),
                              Call(
                                 func=Name(id='zip', ctx=Load()),
                                 args=[
                                    Starred(
                                       value=Subscript(
                                          value=Name(id='new_slicing', ctx=Load()),
                                          slice=Slice(
                                             lower=Constant(value=1)),
                                          ctx=Load()),
                                       ctx=Load())],
                                 keywords=[])],
                           keywords=[]),
                        ifs=[],
                        is_async=0)]))],
         decorator_list=[])],
   type_ignores=[])

# AST van een hulpfunctie
def generate_reduce_dims():
    return Module(
   body=[
      FunctionDef(
         name='reduce_dims',
         args=arguments(
            posonlyargs=[],
            args=[
               arg(arg='slicing'),
               arg(arg='old'),
               arg(arg='extra_dims')],
            kwonlyargs=[],
            kw_defaults=[],
            defaults=[]),
         body=[
            Assign(
               targets=[
                  Name(id='indices', ctx=Store())],
               value=Call(
                  func=Attribute(
                     value=Name(id='np', ctx=Load()),
                     attr='array',
                     ctx=Load()),
                  args=[
                     ListComp(
                        elt=Name(id='i', ctx=Load()),
                        generators=[
                           comprehension(
                              target=Tuple(
                                 elts=[
                                    Name(id='i', ctx=Store()),
                                    Name(id='value', ctx=Store())],
                                 ctx=Store()),
                              iter=Call(
                                 func=Name(id='enumerate', ctx=Load()),
                                 args=[
                                    Attribute(
                                       value=Name(id='old', ctx=Load()),
                                       attr='dims',
                                       ctx=Load())],
                                 keywords=[]),
                              ifs=[
                                 Compare(
                                    left=Name(id='value', ctx=Load()),
                                    ops=[
                                       NotIn()],
                                    comparators=[
                                       Name(id='extra_dims', ctx=Load())])],
                              is_async=0)])],
                  keywords=[])),
            Assign(
               targets=[
                  Name(id='new_slicing', ctx=Store())],
               value=SetComp(
                  elt=Call(
                     func=Name(id='tuple', ctx=Load()),
                     args=[
                        GeneratorExp(
                           elt=Subscript(
                              value=Name(id='tup', ctx=Load()),
                              slice=Name(id='i', ctx=Load()),
                              ctx=Load()),
                           generators=[
                              comprehension(
                                 target=Name(id='i', ctx=Store()),
                                 iter=Name(id='indices', ctx=Load()),
                                 ifs=[],
                                 is_async=0)])],
                     keywords=[]),
                  generators=[
                     comprehension(
                        target=Name(id='tup', ctx=Store()),
                        iter=Name(id='slicing', ctx=Load()),
                        ifs=[],
                        is_async=0)])),
            Return(
               value=Name(id='new_slicing', ctx=Load()))],
         decorator_list=[])],
   type_ignores=[])

# AST van een hulpfunctie
def generate_specific_propagation():
    return Module(
   body=[
      FunctionDef(
         name='specific_propagation',
         args=arguments(
            posonlyargs=[],
            args=[
               arg(arg='small'),
               arg(arg='big'),
               arg(arg='true_slices'),
               arg(arg='false_slices'),
               arg(arg='new_dims'),
               arg(arg='universal')],
            kwonlyargs=[],
            kw_defaults=[],
            defaults=[]),
         body=[
            Assign(
               targets=[
                  Name(id='big_array', ctx=Store())],
               value=Subscript(
                  value=Name(id='var_dict', ctx=Load()),
                  slice=Name(id='big', ctx=Load()),
                  ctx=Load())),
            Assign(
               targets=[
                  Name(id='new_changes', ctx=Store())],
               value=Dict(keys=[], values=[])),
            If(
               test=Compare(
                  left=Call(
                     func=Name(id='len', ctx=Load()),
                     args=[
                        Name(id='true_slices', ctx=Load())],
                     keywords=[]),
                  ops=[
                     Gt()],
                  comparators=[
                     Constant(value=0)]),
               body=[
                  If(
                     test=Name(id='universal', ctx=Load()),
                     body=[
                        Assign(
                           targets=[
                              Name(id='big_slices', ctx=Store())],
                           value=Call(
                              func=Name(id='add_dims', ctx=Load()),
                              args=[
                                 Name(id='true_slices', ctx=Load()),
                                 Name(id='big_array', ctx=Load()),
                                 Name(id='new_dims', ctx=Load())],
                              keywords=[])),
                        If(
                           test=Compare(
                              left=Name(id='big', ctx=Load()),
                              ops=[
                                 In()],
                              comparators=[
                                 Name(id='true_list', ctx=Load())]),
                           body=[
                              Assign(
                                 targets=[
                                    Name(id='detected_changes', ctx=Store())],
                                 value=Dict(
                                    keys=[
                                       Name(id='big', ctx=Load())],
                                    values=[
                                       Call(
                                          func=Name(id='Change', ctx=Load()),
                                          args=[
                                             Name(id='big', ctx=Load()),
                                             ListComp(
                                                elt=Name(id='item', ctx=Load()),
                                                generators=[
                                                   comprehension(
                                                      target=Name(id='sublist', ctx=Store()),
                                                      iter=Name(id='big_slices', ctx=Load()),
                                                      ifs=[],
                                                      is_async=0),
                                                   comprehension(
                                                      target=Name(id='item', ctx=Store()),
                                                      iter=Name(id='sublist', ctx=Load()),
                                                      ifs=[],
                                                      is_async=0)]),
                                             List(elts=[], ctx=Load())],
                                          keywords=[])]))],
                           orelse=[
                              Try(
                                 body=[
                                    Assign(
                                       targets=[
                                          Name(id='detected_changes', ctx=Store())],
                                       value=Call(
                                          func=Name(id='propagate_fill_wrap', ctx=Load()),
                                          args=[
                                             Name(id='big_array', ctx=Load()),
                                             Name(id='big_slices', ctx=Load()),
                                             Constant(value=True)],
                                          keywords=[]))],
                                 handlers=[
                                    ExceptHandler(
                                       type=Name(id='Exception', ctx=Load()),
                                       name='e',
                                       body=[
                                          Raise(
                                             exc=Call(
                                                func=Name(id='Exception', ctx=Load()),
                                                args=[
                                                   Name(id='e', ctx=Load())],
                                                keywords=[]))])],
                                 orelse=[],
                                 finalbody=[])]),
                        Expr(
                           value=Call(
                              func=Name(id='append_changes', ctx=Load()),
                              args=[
                                 Name(id='new_changes', ctx=Load()),
                                 Name(id='detected_changes', ctx=Load())],
                              keywords=[]))],
                     orelse=[
                        Try(
                           body=[
                              Assign(
                                 targets=[
                                    Name(id='detected_changes', ctx=Store())],
                                 value=Call(
                                    func=Name(id='incremental_propagate', ctx=Load()),
                                    args=[
                                       Name(id='big_array', ctx=Load()),
                                       Name(id='true_slices', ctx=Load()),
                                       Name(id='new_dims', ctx=Load()),
                                       Constant(value=False)],
                                    keywords=[]))],
                           handlers=[
                              ExceptHandler(
                                 type=Name(id='Exception', ctx=Load()),
                                 name='e',
                                 body=[
                                    Raise(
                                       exc=Call(
                                          func=Name(id='Exception', ctx=Load()),
                                          args=[
                                             Name(id='e', ctx=Load())],
                                          keywords=[]))])],
                           orelse=[],
                           finalbody=[]),
                        Expr(
                           value=Call(
                              func=Name(id='append_changes', ctx=Load()),
                              args=[
                                 Name(id='new_changes', ctx=Load()),
                                 Name(id='detected_changes', ctx=Load())],
                              keywords=[]))])],
               orelse=[]),
            If(
               test=Compare(
                  left=Call(
                     func=Name(id='len', ctx=Load()),
                     args=[
                        Name(id='false_slices', ctx=Load())],
                     keywords=[]),
                  ops=[
                     Gt()],
                  comparators=[
                     Constant(value=0)]),
               body=[
                  If(
                     test=Name(id='universal', ctx=Load()),
                     body=[
                        Try(
                           body=[
                              Assign(
                                 targets=[
                                    Name(id='detected_changes', ctx=Store())],
                                 value=Call(
                                    func=Name(id='incremental_propagate', ctx=Load()),
                                    args=[
                                       Name(id='big_array', ctx=Load()),
                                       Name(id='false_slices', ctx=Load()),
                                       Name(id='new_dims', ctx=Load()),
                                       Constant(value=True)],
                                    keywords=[]))],
                           handlers=[
                              ExceptHandler(
                                 type=Name(id='Exception', ctx=Load()),
                                 name='e',
                                 body=[
                                    Raise(
                                       exc=Call(
                                          func=Name(id='Exception', ctx=Load()),
                                          args=[
                                             Name(id='e', ctx=Load())],
                                          keywords=[]))])],
                           orelse=[],
                           finalbody=[]),
                        Expr(
                           value=Call(
                              func=Name(id='append_changes', ctx=Load()),
                              args=[
                                 Name(id='new_changes', ctx=Load()),
                                 Name(id='detected_changes', ctx=Load())],
                              keywords=[]))],
                     orelse=[
                        Assign(
                           targets=[
                              Name(id='big_slices', ctx=Store())],
                           value=Call(
                              func=Name(id='add_dims', ctx=Load()),
                              args=[
                                 Name(id='false_slices', ctx=Load()),
                                 Name(id='big_array', ctx=Load()),
                                 Name(id='new_dims', ctx=Load())],
                              keywords=[])),
                        Try(
                           body=[
                              Assign(
                                 targets=[
                                    Name(id='detected_changes', ctx=Store())],
                                 value=Call(
                                    func=Name(id='propagate_fill_wrap', ctx=Load()),
                                    args=[
                                       Name(id='big_array', ctx=Load()),
                                       Name(id='big_slices', ctx=Load()),
                                       Constant(value=False)],
                                    keywords=[]))],
                           handlers=[
                              ExceptHandler(
                                 type=Name(id='Exception', ctx=Load()),
                                 name='e',
                                 body=[
                                    Raise(
                                       exc=Call(
                                          func=Name(id='Exception', ctx=Load()),
                                          args=[
                                             Name(id='e', ctx=Load())],
                                          keywords=[]))])],
                           orelse=[],
                           finalbody=[]),
                        Expr(
                           value=Call(
                              func=Name(id='append_changes', ctx=Load()),
                              args=[
                                 Name(id='new_changes', ctx=Load()),
                                 Name(id='detected_changes', ctx=Load())],
                              keywords=[]))])],
               orelse=[]),
            Return(
               value=Name(id='new_changes', ctx=Load()))],
         decorator_list=[])],
   type_ignores=[])


# AST van een hulpfunctie
def generate_general_propagation():
    return Module(
   body=[
      FunctionDef(
         name='general_propagation',
         args=arguments(
            posonlyargs=[],
            args=[
               arg(arg='big'),
               arg(arg='small'),
               arg(arg='true_slices'),
               arg(arg='false_slices'),
               arg(arg='old_dims'),
               arg(arg='universal')],
            kwonlyargs=[],
            kw_defaults=[],
            defaults=[]),
         body=[
            Assign(
               targets=[
                  Name(id='small_array', ctx=Store())],
               value=Subscript(
                  value=Name(id='var_dict', ctx=Load()),
                  slice=Name(id='small', ctx=Load()),
                  ctx=Load())),
            Assign(
               targets=[
                  Name(id='big_array', ctx=Store())],
               value=Subscript(
                  value=Name(id='var_dict', ctx=Load()),
                  slice=Name(id='big', ctx=Load()),
                  ctx=Load())),
            Assign(
               targets=[
                  Name(id='new_changes', ctx=Store())],
               value=Dict(keys=[], values=[])),
            If(
               test=Compare(
                  left=Call(
                     func=Name(id='len', ctx=Load()),
                     args=[
                        Name(id='true_slices', ctx=Load())],
                     keywords=[]),
                  ops=[
                     Gt()],
                  comparators=[
                     Constant(value=0)]),
               body=[
                  Assign(
                     targets=[
                        Name(id='small_slices', ctx=Store())],
                     value=Call(
                        func=Name(id='reduce_dims', ctx=Load()),
                        args=[
                           Name(id='true_slices', ctx=Load()),
                           Name(id='big_array', ctx=Load()),
                           Name(id='old_dims', ctx=Load())],
                        keywords=[])),
                  If(
                     test=Name(id='universal', ctx=Load()),
                     body=[
                        Try(
                           body=[
                              Assign(
                                 targets=[
                                    Name(id='detected_changes', ctx=Store())],
                                 value=Call(
                                    func=Name(id='incremental_propagate_wrap', ctx=Load()),
                                    args=[
                                       Name(id='big_array', ctx=Load()),
                                       Name(id='small_array', ctx=Load()),
                                       Call(
                                          func=Name(id='list', ctx=Load()),
                                          args=[
                                             Name(id='small_slices', ctx=Load())],
                                          keywords=[]),
                                       Name(id='old_dims', ctx=Load()),
                                       Constant(value=True)],
                                    keywords=[])),
                              Expr(
                                 value=Call(
                                    func=Name(id='append_changes', ctx=Load()),
                                    args=[
                                       Name(id='new_changes', ctx=Load()),
                                       Name(id='detected_changes', ctx=Load())],
                                    keywords=[]))],
                           handlers=[
                              ExceptHandler(
                                 type=Name(id='Exception', ctx=Load()),
                                 name='e',
                                 body=[
                                    Raise(
                                       exc=Call(
                                          func=Name(id='Exception', ctx=Load()),
                                          args=[
                                             Name(id='e', ctx=Load())],
                                          keywords=[]))])],
                           orelse=[],
                           finalbody=[])],
                     orelse=[
                        Try(
                           body=[
                              Assign(
                                 targets=[
                                    Name(id='detected_changes', ctx=Store())],
                                 value=Call(
                                    func=Name(id='propagate_wrap', ctx=Load()),
                                    args=[
                                       List(
                                          elts=[
                                             Call(
                                                func=Name(id='RuleComponent', ctx=Load()),
                                                args=[
                                                   Name(id='small', ctx=Load()),
                                                   Call(
                                                      func=Name(id='list', ctx=Load()),
                                                      args=[
                                                         Name(id='small_slices', ctx=Load())],
                                                      keywords=[]),
                                                   Constant(value=False)],
                                                keywords=[])],
                                          ctx=Load())],
                                    keywords=[])),
                              Expr(
                                 value=Call(
                                    func=Name(id='append_changes', ctx=Load()),
                                    args=[
                                       Name(id='new_changes', ctx=Load()),
                                       Name(id='detected_changes', ctx=Load())],
                                    keywords=[]))],
                           handlers=[
                              ExceptHandler(
                                 type=Name(id='Exception', ctx=Load()),
                                 name='e',
                                 body=[
                                    Raise(
                                       exc=Call(
                                          func=Name(id='Exception', ctx=Load()),
                                          args=[
                                             Name(id='e', ctx=Load())],
                                          keywords=[]))])],
                           orelse=[],
                           finalbody=[])])],
               orelse=[]),
            If(
               test=Compare(
                  left=Call(
                     func=Name(id='len', ctx=Load()),
                     args=[
                        Name(id='false_slices', ctx=Load())],
                     keywords=[]),
                  ops=[
                     Gt()],
                  comparators=[
                     Constant(value=0)]),
               body=[
                  Assign(
                     targets=[
                        Name(id='small_slices', ctx=Store())],
                     value=Call(
                        func=Name(id='reduce_dims', ctx=Load()),
                        args=[
                           Name(id='false_slices', ctx=Load()),
                           Name(id='big_array', ctx=Load()),
                           Name(id='old_dims', ctx=Load())],
                        keywords=[])),
                  If(
                     test=Name(id='universal', ctx=Load()),
                     body=[
                        Try(
                           body=[
                              Assign(
                                 targets=[
                                    Name(id='detected_changes', ctx=Store())],
                                 value=Call(
                                    func=Name(id='propagate_wrap', ctx=Load()),
                                    args=[
                                       List(
                                          elts=[
                                             Call(
                                                func=Name(id='RuleComponent', ctx=Load()),
                                                args=[
                                                   Name(id='small', ctx=Load()),
                                                   Call(
                                                      func=Name(id='list', ctx=Load()),
                                                      args=[
                                                         Name(id='small_slices', ctx=Load())],
                                                      keywords=[]),
                                                   Constant(value=True)],
                                                keywords=[])],
                                          ctx=Load())],
                                    keywords=[])),
                              Expr(
                                 value=Call(
                                    func=Name(id='append_changes', ctx=Load()),
                                    args=[
                                       Name(id='new_changes', ctx=Load()),
                                       Name(id='detected_changes', ctx=Load())],
                                    keywords=[]))],
                           handlers=[
                              ExceptHandler(
                                 type=Name(id='Exception', ctx=Load()),
                                 name='e',
                                 body=[
                                    Raise(
                                       exc=Call(
                                          func=Name(id='Exception', ctx=Load()),
                                          args=[
                                             Name(id='e', ctx=Load())],
                                          keywords=[]))])],
                           orelse=[],
                           finalbody=[])],
                     orelse=[
                        Try(
                           body=[
                              Assign(
                                 targets=[
                                    Name(id='detected_changes', ctx=Store())],
                                 value=Call(
                                    func=Name(id='incremental_propagate_wrap', ctx=Load()),
                                    args=[
                                       Name(id='big_array', ctx=Load()),
                                       Name(id='small_array', ctx=Load()),
                                       Call(
                                          func=Name(id='list', ctx=Load()),
                                          args=[
                                             Name(id='small_slices', ctx=Load())],
                                          keywords=[]),
                                       Name(id='old_dims', ctx=Load()),
                                       Constant(value=False)],
                                    keywords=[])),
                              Expr(
                                 value=Call(
                                    func=Name(id='append_changes', ctx=Load()),
                                    args=[
                                       Name(id='new_changes', ctx=Load()),
                                       Name(id='detected_changes', ctx=Load())],
                                    keywords=[]))],
                           handlers=[
                              ExceptHandler(
                                 type=Name(id='Exception', ctx=Load()),
                                 name='e',
                                 body=[
                                    Raise(
                                       exc=Call(
                                          func=Name(id='Exception', ctx=Load()),
                                          args=[
                                             Name(id='e', ctx=Load())],
                                          keywords=[]))])],
                           orelse=[],
                           finalbody=[])])],
               orelse=[]),
            Return(
               value=Name(id='new_changes', ctx=Load()))],
         decorator_list=[])],
   type_ignores=[])


# AST van een hulpfunctie

def generate_add_all_function_outputs():
    return Module(
   body=[
      FunctionDef(
         name='add_all_function_outputs',
         args=arguments(
            posonlyargs=[],
            args=[
               arg(arg='data_array'),
               arg(arg='slice')],
            kwonlyargs=[],
            kw_defaults=[],
            defaults=[]),
         body=[
            Assign(
               targets=[
                  Name(id='all_outputs', ctx=Store())],
               value=List(elts=[], ctx=Load())),
            Assign(
               targets=[
                  Name(id='scope', ctx=Store())],
               value=Attribute(
                  value=Subscript(
                     value=Attribute(
                        value=Name(id='data_array', ctx=Load()),
                        attr='coords',
                        ctx=Load()),
                     slice=Subscript(
                        value=Attribute(
                           value=Name(id='data_array', ctx=Load()),
                           attr='dims',
                           ctx=Load()),
                        slice=UnaryOp(
                           op=USub(),
                           operand=Constant(value=1)),
                        ctx=Load()),
                     ctx=Load()),
                  attr='values',
                  ctx=Load())),
            For(
               target=Name(id='elem', ctx=Store()),
               iter=Name(id='scope', ctx=Load()),
               body=[
                  If(
                     test=Compare(
                        left=Name(id='elem', ctx=Load()),
                        ops=[
                           NotEq()],
                        comparators=[
                           Subscript(
                              value=Name(id='slice', ctx=Load()),
                              slice=UnaryOp(
                                 op=USub(),
                                 operand=Constant(value=1)),
                              ctx=Load())]),
                     body=[
                        Expr(
                           value=Call(
                              func=Attribute(
                                 value=Name(id='all_outputs', ctx=Load()),
                                 attr='append',
                                 ctx=Load()),
                              args=[
                                 BinOp(
                                    left=Subscript(
                                       value=Name(id='slice', ctx=Load()),
                                       slice=Slice(
                                          upper=UnaryOp(
                                             op=USub(),
                                             operand=Constant(value=1))),
                                       ctx=Load()),
                                    op=Add(),
                                    right=Tuple(
                                       elts=[
                                          Call(
                                             func=Attribute(
                                                value=Name(id='elem', ctx=Load()),
                                                attr='item',
                                                ctx=Load()),
                                             args=[],
                                             keywords=[])],
                                       ctx=Load()))],
                              keywords=[]))],
                     orelse=[])],
               orelse=[]),
            Return(
               value=Name(id='all_outputs', ctx=Load()))],
         decorator_list=[])],
   type_ignores=[])


# AST van een hulpfunctie

def generate_function_propagation():
    return Module(
   body=[
      FunctionDef(
         name='function_propagation',
         args=arguments(
            posonlyargs=[],
            args=[
               arg(arg='name'),
               arg(arg='true_slices'),
               arg(arg='false_slices')],
            kwonlyargs=[],
            kw_defaults=[],
            defaults=[]),
         body=[
            Assign(
               targets=[
                  Name(id='new_changes', ctx=Store())],
               value=Dict(keys=[], values=[])),
            Assign(
               targets=[
                  Name(id='data_array', ctx=Store())],
               value=Subscript(
                  value=Name(id='var_dict', ctx=Load()),
                  slice=Name(id='name', ctx=Load()),
                  ctx=Load())),
            If(
               test=Compare(
                  left=Call(
                     func=Name(id='len', ctx=Load()),
                     args=[
                        Name(id='true_slices', ctx=Load())],
                     keywords=[]),
                  ops=[
                     Gt()],
                  comparators=[
                     Constant(value=0)]),
               body=[
                  Assign(
                     targets=[
                        Name(id='corresponding_function_slices', ctx=Store())],
                     value=ListComp(
                        elt=Call(
                           func=Name(id='add_all_function_outputs', ctx=Load()),
                           args=[
                              Name(id='data_array', ctx=Load()),
                              Name(id='slice', ctx=Load())],
                           keywords=[]),
                        generators=[
                           comprehension(
                              target=Name(id='slice', ctx=Store()),
                              iter=Name(id='true_slices', ctx=Load()),
                              ifs=[],
                              is_async=0)])),
                  Try(
                     body=[
                        Assign(
                           targets=[
                              Name(id='detected_changes', ctx=Store())],
                           value=Call(
                              func=Name(id='propagate_fill_wrap', ctx=Load()),
                              args=[
                                 Name(id='data_array', ctx=Load()),
                                 Name(id='corresponding_function_slices', ctx=Load()),
                                 Constant(value=False)],
                              keywords=[]))],
                     handlers=[
                        ExceptHandler(
                           type=Name(id='Exception', ctx=Load()),
                           name='e',
                           body=[
                              Raise(
                                 exc=Call(
                                    func=Name(id='Exception', ctx=Load()),
                                    args=[
                                       Name(id='e', ctx=Load())],
                                    keywords=[]))])],
                     orelse=[],
                     finalbody=[]),
                  Expr(
                     value=Call(
                        func=Name(id='append_changes', ctx=Load()),
                        args=[
                           Name(id='new_changes', ctx=Load()),
                           Name(id='detected_changes', ctx=Load())],
                        keywords=[]))],
               orelse=[]),
            If(
               test=Compare(
                  left=Call(
                     func=Name(id='len', ctx=Load()),
                     args=[
                        Name(id='false_slices', ctx=Load())],
                     keywords=[]),
                  ops=[
                     Gt()],
                  comparators=[
                     Constant(value=0)]),
               body=[
                  Assign(
                     targets=[
                        Name(id='last_dim', ctx=Store())],
                     value=Subscript(
                        value=Attribute(
                           value=Subscript(
                              value=Name(id='var_dict', ctx=Load()),
                              slice=Name(id='name', ctx=Load()),
                              ctx=Load()),
                           attr='dims',
                           ctx=Load()),
                        slice=UnaryOp(
                           op=USub(),
                           operand=Constant(value=1)),
                        ctx=Load())),
                  Assign(
                     targets=[
                        Name(id='reduced_slices', ctx=Store())],
                     value=Call(
                        func=Name(id='reduce_dims', ctx=Load()),
                        args=[
                           Name(id='false_slices', ctx=Load()),
                           Name(id='data_array', ctx=Load()),
                           List(
                              elts=[
                                 Name(id='last_dim', ctx=Load())],
                              ctx=Load())],
                        keywords=[])),
                  Try(
                     body=[
                        Assign(
                           targets=[
                              Name(id='detected_changes', ctx=Store())],
                           value=Call(
                              func=Name(id='incremental_propagate', ctx=Load()),
                              args=[
                                 Subscript(
                                    value=Name(id='var_dict', ctx=Load()),
                                    slice=Name(id='name', ctx=Load()),
                                    ctx=Load()),
                                 Call(
                                    func=Name(id='list', ctx=Load()),
                                    args=[
                                       Name(id='reduced_slices', ctx=Load())],
                                    keywords=[]),
                                 List(
                                    elts=[
                                       Name(id='last_dim', ctx=Load())],
                                    ctx=Load()),
                                 Constant(value=False)],
                              keywords=[]))],
                     handlers=[
                        ExceptHandler(
                           type=Name(id='Exception', ctx=Load()),
                           name='e',
                           body=[
                              Raise(
                                 exc=Call(
                                    func=Name(id='Exception', ctx=Load()),
                                    args=[
                                       Name(id='e', ctx=Load())],
                                    keywords=[]))])],
                     orelse=[],
                     finalbody=[]),
                  Expr(
                     value=Call(
                        func=Name(id='append_changes', ctx=Load()),
                        args=[
                           Name(id='new_changes', ctx=Load()),
                           Name(id='detected_changes', ctx=Load())],
                        keywords=[]))],
               orelse=[]),
            Return(
               value=Name(id='new_changes', ctx=Load()))],
         decorator_list=[])],
   type_ignores=[])






# Deze functie zet een UNSAT-lijst om in een AST bestaande uit RuleComponents. Deze RuleComponents zijn samen een 'normal propagator' (__thesistekst__)
def get_rule_components_from_unsat_list(unsat_list):
    rule = []
    for lit in unsat_list.unsat_list:
        rule.append(Call(
            func=Name(id='RuleComponent', ctx=Load()),
            args=[
                Constant(value=lit.atom.name),
                Subscript(
                    value=Name(id='slicing_dict', ctx=Load()),
                    slice=Constant(value=lit.atom.name),
                    ctx=Load()),
                Constant(value=lit.pos)],
            keywords=[]))
    return rule

# Deze functie voegt de code voor een 'normal propagator' toe aan de propagate() functie (__thesistekst__)
def generate_propagate_rule_from_unsat_set(unsat_list, var, truth):
    if truth:
        change_array = 'true_slicing'
    else:
        change_array = 'false_slicing'
    quantified_var = [Constant(value=var.name) for var in unsat_list.bindings]
    argument_keys = [Constant(value=lit.atom.name) for lit in unsat_list.unsat_list]
    argument_values = [List(elts=[Constant(value=arg.name) for arg in lit.atom.args], ctx=Load()) for lit in unsat_list.unsat_list]
    rule_components = get_rule_components_from_unsat_list(unsat_list)
    #argument_dict
    return Module(
   body=[
       If(
         test=Compare(
            left=Call(
               func=Name(id='len', ctx=Load()),
               args=[
                  Attribute(
                     value=Name(id='change', ctx=Load()),
                     attr=change_array,
                     ctx=Load())],
               keywords=[]),
            ops=[
               Gt()],
            comparators=[
               Constant(value=0)]),
         body=[
            Assign(
               targets=[
                  Name(id='quantified_var', ctx=Store())],
               value=List(
                  elts=quantified_var,
                  ctx=Load())),
            Assign(
               targets=[
                  Name(id='argument_dict', ctx=Store())],
               value=Dict(
                  keys=argument_keys,
                  values=argument_values)),
            Assign(
               targets=[
                  Name(id='slicing_dict', ctx=Store())],
               value=Call(
                  func=Name(id='map_indices_wrap', ctx=Load()),
                  args=[
                     Name(id='argument_dict', ctx=Load()),
                     Attribute(
                        value=Name(id='change', ctx=Load()),
                        attr='name',
                        ctx=Load()),
                     Attribute(
                        value=Name(id='change', ctx=Load()),
                        attr=change_array,
                        ctx=Load()),
                     Name(id='quantified_var', ctx=Load())],
                  keywords=[])),
            If(
               test=BoolOp(
                  op=And(),
                  values=[
                     Compare(
                        left=Name(id='slicing_dict', ctx=Load()),
                        ops=[
                           IsNot()],
                        comparators=[
                           Constant(value=None)]),
                     Compare(
                        left=Call(
                           func=Name(id='len', ctx=Load()),
                           args=[
                              Subscript(
                                 value=Name(id='slicing_dict', ctx=Load()),
                                 slice=Constant(value=var),
                                 ctx=Load())],
                           keywords=[]),
                        ops=[
                           Gt()],
                        comparators=[
                           Constant(value=0)])]),
               body=[
                  Try(
                     body=[
                        Assign(
                           targets=[
                              Name(id='detected_changes', ctx=Store())],
                           value=Call(
                              func=Name(id='propagate_wrap', ctx=Load()),
                              args=[
                                 List(
                                    elts=rule_components,
                                    ctx=Load())],
                              keywords=[])),
                        Expr(
                           value=Call(
                              func=Name(id='append_changes', ctx=Load()),
                              args=[
                                 Name(id='new_changes', ctx=Load()),
                                 Name(id='detected_changes', ctx=Load())],
                              keywords=[]))],
                     handlers=[
                        ExceptHandler(
                           type=Name(id='Exception', ctx=Load()),
                           name='e',
                           body=[
                              Raise(
                                 exc=Call(
                                    func=Name(id='Exception', ctx=Load()),
                                    args=[
                                       Name(id='e', ctx=Load())],
                                    keywords=[]))])],
                     orelse=[],
                     finalbody=[])],
               orelse=[])],
         orelse=[])],
   type_ignores=[])

# Deze functie bepaalt de nieuwe dimensies van een atoom vergeleken met een ander atoom.
def determine_new_dimensions(old, new):
    new_dims = []
    old_arguments = [arg.name for arg in old.atom.args]
    for i, arg in enumerate(new.atom.args):
        if arg.name not in old_arguments:
            new_dims.append(Constant(value=f'x{i}'))
    return new_dims


# Deze functie voegt de code voor een 'specific propagator' toe aan de propagate() functie (__thesistekst__)
def generate_propagate_rule_from_specific_propagation(sp):
    new_dims = determine_new_dimensions(sp.general, sp.specific)
    return Module(
   body=[
      Try(
         body=[
            Assign(
               targets=[
                  Name(id='new_dims', ctx=Store())],
               value=List(
                  elts=new_dims,
                  ctx=Load())),
            Assign(
               targets=[
                  Name(id='detected_changes', ctx=Store())],
               value=Call(
                  func=Name(id='specific_propagation', ctx=Load()),
                  args=[
                     Constant(value=sp.general.atom.name),
                     Constant(value=sp.specific.atom.name),
                     Attribute(
                        value=Name(id='change', ctx=Load()),
                        attr='true_slicing',
                        ctx=Load()),
                     Attribute(
                        value=Name(id='change', ctx=Load()),
                        attr='false_slicing',
                        ctx=Load()),
                     Name(id='new_dims', ctx=Load()),
                     Constant(value=sp.universal)],
                  keywords=[])),
            Expr(
               value=Call(
                  func=Name(id='append_changes', ctx=Load()),
                  args=[
                     Name(id='new_changes', ctx=Load()),
                     Name(id='detected_changes', ctx=Load())],
                  keywords=[]))],
         handlers=[
            ExceptHandler(
               type=Name(id='Exception', ctx=Load()),
               name='e',
               body=[
                  Raise(
                     exc=Call(
                        func=Name(id='Exception', ctx=Load()),
                        args=[
                           Name(id='e', ctx=Load())],
                        keywords=[]))])],
         orelse=[],
         finalbody=[])],
   type_ignores=[])

# Deze functie voegt de code voor een 'general propagator' toe aan de propagate() functie (__thesistekst__)
def generate_propagate_rule_from_general_propagation(ge):
    old_dims = determine_new_dimensions(ge.general, ge.specific)
    return Module(
        body=[
      Try(
         body=[
            Assign(
               targets=[
                  Name(id='old_dims', ctx=Store())],
               value=List(
                  elts=old_dims,
                  ctx=Load())),
            Assign(
               targets=[
                  Name(id='detected_changes', ctx=Store())],
               value=Call(
                  func=Name(id='general_propagation', ctx=Load()),
                  args=[
                     Constant(value=ge.specific.atom.name),
                     Constant(value=ge.general.atom.name),
                     Attribute(
                        value=Name(id='change', ctx=Load()),
                        attr='true_slicing',
                        ctx=Load()),
                     Attribute(
                        value=Name(id='change', ctx=Load()),
                        attr='false_slicing',
                        ctx=Load()),
                     Name(id='old_dims', ctx=Load()),
                     Constant(value=ge.universal)],
                  keywords=[])),
            Expr(
               value=Call(
                  func=Name(id='append_changes', ctx=Load()),
                  args=[
                     Name(id='new_changes', ctx=Load()),
                     Name(id='detected_changes', ctx=Load())],
                  keywords=[]))],
         handlers=[
            ExceptHandler(
               type=Name(id='Exception', ctx=Load()),
               name='e',
               body=[
                  Raise(
                     exc=Call(
                        func=Name(id='Exception', ctx=Load()),
                        args=[
                           Name(id='e', ctx=Load())],
                        keywords=[]))])],
         orelse=[],
         finalbody=[])],
   type_ignores=[])


def generate_propagate_rule_from_function_propagation(prop):
    return Module(
   body=[
      Try(
         body=[
            Assign(
               targets=[
                  Name(id='detected_changes', ctx=Store())],
               value=Call(
                  func=Name(id='function_propagation', ctx=Load()),
                  args=[
                     Constant(value=prop.name),
                     Attribute(
                        value=Name(id='change', ctx=Load()),
                        attr='true_slicing',
                        ctx=Load()),
                     Attribute(
                        value=Name(id='change', ctx=Load()),
                        attr='false_slicing',
                        ctx=Load())],
                  keywords=[])),
            Expr(
               value=Call(
                  func=Name(id='append_changes', ctx=Load()),
                  args=[
                     Name(id='new_changes', ctx=Load()),
                     Name(id='detected_changes', ctx=Load())],
                  keywords=[]))],
         handlers=[
            ExceptHandler(
               type=Name(id='Exception', ctx=Load()),
               name='e',
               body=[
                  Raise(
                     exc=Call(
                        func=Name(id='Exception', ctx=Load()),
                        args=[
                           Name(id='e', ctx=Load())],
                        keywords=[]))])],
         orelse=[],
         finalbody=[])],
   type_ignores=[])


# Deze functie genereert de code voor alle propagators (normal propagators, specific propagators, general propagators) die bij een bepaald atoom horen.
def generate_propagator_code(var_name, propagators):
    if_body = []
    for prop in propagators:
        if type(prop) == UnsatList:
            truth_value = prop.unsat_list[0].pos
            if_body.append(generate_propagate_rule_from_unsat_set(prop, var_name, truth_value).body)
        if type(prop) == SpecificPropagator:
            if_body.append(generate_propagate_rule_from_specific_propagation(prop))
        if type(prop) == GeneralPropagator:
            if_body.append(generate_propagate_rule_from_general_propagation(prop))
        if type(prop) == FunctionPropagator:
            if_body.append(generate_propagate_rule_from_function_propagation(prop))
    return If(
         test=Compare(
            left=Attribute(
               value=Name(id='change', ctx=Load()),
               attr='name',
               ctx=Load()),
            ops=[
               Eq()],
            comparators=[
               Constant(value=var_name)]),
         body=if_body,
         orelse=[])



# Deze functie genereert de propagate() functie op basis van de dictionary die voor elk atoom in het IDP-programma propagators bevat.
def generate_propagate(grouped_propagators):
    cases = []
    for key, val in grouped_propagators.items():
        propagators = generate_propagator_code(key, val)
        cases.append(propagators)
    return Module(
   body=[
      FunctionDef(
         name='propagate',
         args=arguments(
            posonlyargs=[],
            args=[
               arg(arg='changes')],
            kwonlyargs=[],
            kw_defaults=[],
            defaults=[]),
         body=[
            Assign(
               targets=[
                  Name(id='new_changes', ctx=Store())],
               value=Dict(keys=[], values=[])),
            For(
               target=Name(id='change', ctx=Store()),
               iter=Call(
                  func=Attribute(
                     value=Name(id='changes', ctx=Load()),
                     attr='values',
                     ctx=Load()),
                  args=[],
                  keywords=[]),
               body=cases,
               orelse=[]),
            Return(
               value=Name(id='new_changes', ctx=Load()))],
         decorator_list=[])],
   type_ignores=[])

# AST voor hulpfunctie
def generate_propagate_full():
    return Module(
   body=[
      FunctionDef(
         name='propagate_full',
         args=arguments(
            posonlyargs=[],
            args=[
               arg(arg='changes')],
            kwonlyargs=[],
            kw_defaults=[],
            defaults=[]),
         body=[
            While(
               test=Compare(
                  left=Call(
                     func=Name(id='len', ctx=Load()),
                     args=[
                        Name(id='changes', ctx=Load())],
                     keywords=[]),
                  ops=[
                     NotEq()],
                  comparators=[
                     Constant(value=0)]),
               body=[
                  Assign(
                     targets=[
                        Name(id='changes', ctx=Store())],
                     value=Call(
                        func=Name(id='propagate', ctx=Load()),
                        args=[
                           Name(id='changes', ctx=Load())],
                        keywords=[]))],
               orelse=[])],
         decorator_list=[])],
   type_ignores=[])

# Deze functie genereert code om wiskundige vergelijkingsoperatoren te ondersteunen.
def get_domain_elements_tested_on_equality(enfs, types):
    domain_elem = set()
    operators = set()
    for enf in enfs:
        if type(enf) == parsing_idpz3_final.ENFConjunctive:
            if len(enf.right) == 1 and enf.right[0].atom.name in [';EQ', '_NEQ', '_GE', '_GEQ', '_LE', '_LEQ']:
                operators.add(enf.right[0].atom.name)
                tested_types = [var.type for var in enf.bindings]
                tested_domains = [create_full_domain(t.domain) for t in types if t.name in tested_types]
                tested_domains_flat = [item for sublist in tested_domains for item in sublist]
                domain_elem.update(set(tested_domains_flat))
    return domain_elem, operators

# AST voor hulpfunctie
def generate_fill_in_interpreted_domain():
    return Module(
   body=[
      FunctionDef(
         name='fill_in_interpreted_domain',
         args=arguments(
            posonlyargs=[],
            args=[
               arg(arg='predicate_list')],
            kwonlyargs=[],
            kw_defaults=[],
            defaults=[]),
         body=[
            Assign(
               targets=[
                  Name(id='changes', ctx=Store())],
               value=Dict(keys=[], values=[])),
            For(
               target=Name(id='pred', ctx=Store()),
               iter=Name(id='predicate_list', ctx=Load()),
               body=[
                  Assign(
                     targets=[
                        Name(id='data_array', ctx=Store())],
                     value=Subscript(
                        value=Name(id='var_dict', ctx=Load()),
                        slice=Name(id='pred', ctx=Load()),
                        ctx=Load())),
                  Assign(
                     targets=[
                        Name(id='mask', ctx=Store())],
                     value=Compare(
                        left=Name(id='data_array', ctx=Load()),
                        ops=[
                           NotEq()],
                        comparators=[
                           Attribute(
                              value=Name(id='EB', ctx=Load()),
                              attr='TRUE',
                              ctx=Load())])),
                  Assign(
                     targets=[
                        Subscript(
                           value=Attribute(
                              value=Name(id='data_array', ctx=Load()),
                              attr='values',
                              ctx=Load()),
                           slice=Name(id='mask', ctx=Load()),
                           ctx=Store())],
                     value=Attribute(
                        value=Name(id='EB', ctx=Load()),
                        attr='FALSE',
                        ctx=Load())),
                  Assign(
                     targets=[
                        Name(id='index_tuples', ctx=Store())],
                     value=Call(
                        func=Attribute(
                           value=Name(id='np', ctx=Load()),
                           attr='argwhere',
                           ctx=Load()),
                        args=[
                           Attribute(
                              value=Name(id='mask', ctx=Load()),
                              attr='values',
                              ctx=Load())],
                        keywords=[])),
                  Assign(
                     targets=[
                        Name(id='false_indices', ctx=Store())],
                     value=ListComp(
                        elt=Call(
                           func=Name(id='tuple', ctx=Load()),
                           args=[
                              GeneratorExp(
                                 elt=Subscript(
                                    value=Attribute(
                                       value=Subscript(
                                          value=Name(id='data_array', ctx=Load()),
                                          slice=Name(id='d', ctx=Load()),
                                          ctx=Load()),
                                       attr='values',
                                       ctx=Load()),
                                    slice=Name(id='i', ctx=Load()),
                                    ctx=Load()),
                                 generators=[
                                    comprehension(
                                       target=Tuple(
                                          elts=[
                                             Name(id='d', ctx=Store()),
                                             Name(id='i', ctx=Store())],
                                          ctx=Store()),
                                       iter=Call(
                                          func=Name(id='zip', ctx=Load()),
                                          args=[
                                             Attribute(
                                                value=Name(id='data_array', ctx=Load()),
                                                attr='dims',
                                                ctx=Load()),
                                             Name(id='idx', ctx=Load())],
                                          keywords=[]),
                                       ifs=[],
                                       is_async=0)])],
                           keywords=[]),
                        generators=[
                           comprehension(
                              target=Name(id='idx', ctx=Store()),
                              iter=Name(id='index_tuples', ctx=Load()),
                              ifs=[],
                              is_async=0)])),
                  Expr(
                     value=Call(
                        func=Name(id='append_changes', ctx=Load()),
                        args=[
                           Name(id='changes', ctx=Load()),
                           Dict(
                              keys=[
                                 Name(id='pred', ctx=Load())],
                              values=[
                                 Call(
                                    func=Name(id='Change', ctx=Load()),
                                    args=[
                                       Name(id='pred', ctx=Load()),
                                       List(elts=[], ctx=Load()),
                                       Name(id='false_indices', ctx=Load())],
                                    keywords=[])])],
                        keywords=[]))],
               orelse=[]),
            Return(
               value=Name(id='changes', ctx=Load()))],
         decorator_list=[])],
   type_ignores=[])

# AST voor hulpfunctie
def generate_get_changes_for_comparison_operators():
    return Module(
   body=[
      FunctionDef(
         name='get_changes_for_comparison_operators',
         args=arguments(
            posonlyargs=[],
            args=[
               arg(arg='operator_list'),
               arg(arg='domain')],
            kwonlyargs=[],
            kw_defaults=[],
            defaults=[]),
         body=[
            Assign(
               targets=[
                  Name(id='changes', ctx=Store())],
               value=Dict(keys=[], values=[])),
            If(
               test=BoolOp(
                  op=Or(),
                  values=[
                     Compare(
                        left=Constant(value=';EQ'),
                        ops=[
                           In()],
                        comparators=[
                           Name(id='operator_list', ctx=Load())]),
                     Compare(
                        left=Constant(value='_NEQ'),
                        ops=[
                           In()],
                        comparators=[
                           Name(id='operator_list', ctx=Load())])]),
               body=[
                  Assign(
                     targets=[
                        Name(id='equal_pairs', ctx=Store())],
                     value=ListComp(
                        elt=Tuple(
                           elts=[
                              Name(id='elem', ctx=Load()),
                              Name(id='elem', ctx=Load())],
                           ctx=Load()),
                        generators=[
                           comprehension(
                              target=Name(id='elem', ctx=Store()),
                              iter=Name(id='domain', ctx=Load()),
                              ifs=[],
                              is_async=0)])),
                  Assign(
                     targets=[
                        Name(id='unequal_pairs', ctx=Store())],
                     value=ListComp(
                        elt=Tuple(
                           elts=[
                              Name(id='elem1', ctx=Load()),
                              Name(id='elem2', ctx=Load())],
                           ctx=Load()),
                        generators=[
                           comprehension(
                              target=Name(id='elem1', ctx=Store()),
                              iter=Name(id='domain', ctx=Load()),
                              ifs=[],
                              is_async=0),
                           comprehension(
                              target=Name(id='elem2', ctx=Store()),
                              iter=Name(id='domain', ctx=Load()),
                              ifs=[
                                 Compare(
                                    left=Name(id='elem1', ctx=Load()),
                                    ops=[
                                       NotEq()],
                                    comparators=[
                                       Name(id='elem2', ctx=Load())])],
                              is_async=0)])),
                  If(
                     test=Compare(
                        left=Constant(value=';EQ'),
                        ops=[
                           In()],
                        comparators=[
                           Name(id='operator_list', ctx=Load())]),
                     body=[
                        Expr(
                           value=Call(
                              func=Name(id='append_changes', ctx=Load()),
                              args=[
                                 Name(id='changes', ctx=Load()),
                                 Dict(
                                    keys=[
                                       Constant(value=';EQ')],
                                    values=[
                                       Call(
                                          func=Name(id='Change', ctx=Load()),
                                          args=[
                                             Constant(value=';EQ'),
                                             Name(id='equal_pairs', ctx=Load()),
                                             Name(id='unequal_pairs', ctx=Load())],
                                          keywords=[])])],
                              keywords=[]))],
                     orelse=[]),
                  If(
                     test=Compare(
                        left=Constant(value='_NEQ'),
                        ops=[
                           In()],
                        comparators=[
                           Name(id='operator_list', ctx=Load())]),
                     body=[
                        Expr(
                           value=Call(
                              func=Name(id='append_changes', ctx=Load()),
                              args=[
                                 Name(id='changes', ctx=Load()),
                                 Dict(
                                    keys=[
                                       Constant(value='_NEQ')],
                                    values=[
                                       Call(
                                          func=Name(id='Change', ctx=Load()),
                                          args=[
                                             Constant(value='_NEQ'),
                                             Name(id='unequal_pairs', ctx=Load()),
                                             Name(id='equal_pairs', ctx=Load())],
                                          keywords=[])])],
                              keywords=[]))],
                     orelse=[])],
               orelse=[]),
            If(
               test=BoolOp(
                  op=Or(),
                  values=[
                     Compare(
                        left=Constant(value='_LEQ'),
                        ops=[
                           In()],
                        comparators=[
                           Name(id='operator_list', ctx=Load())]),
                     Compare(
                        left=Constant(value='_LE'),
                        ops=[
                           In()],
                        comparators=[
                           Name(id='operator_list', ctx=Load())]),
                     Compare(
                        left=Constant(value='_GEQ'),
                        ops=[
                           In()],
                        comparators=[
                           Name(id='operator_list', ctx=Load())]),
                     Compare(
                        left=Constant(value='_GE'),
                        ops=[
                           In()],
                        comparators=[
                           Name(id='operator_list', ctx=Load())])]),
               body=[
                  Assign(
                     targets=[
                        Name(id='integer_domain', ctx=Store())],
                     value=SetComp(
                        elt=Name(id='elem', ctx=Load()),
                        generators=[
                           comprehension(
                              target=Name(id='elem', ctx=Store()),
                              iter=Name(id='domain', ctx=Load()),
                              ifs=[
                                 Compare(
                                    left=Call(
                                       func=Name(id='type', ctx=Load()),
                                       args=[
                                          Name(id='elem', ctx=Load())],
                                       keywords=[]),
                                    ops=[
                                       Eq()],
                                    comparators=[
                                       Name(id='int', ctx=Load())])],
                              is_async=0)])),
                  Assign(
                     targets=[
                        Name(id='integer_pairs', ctx=Store())],
                     value=ListComp(
                        elt=Tuple(
                           elts=[
                              Name(id='elem1', ctx=Load()),
                              Name(id='elem2', ctx=Load())],
                           ctx=Load()),
                        generators=[
                           comprehension(
                              target=Name(id='elem1', ctx=Store()),
                              iter=Name(id='integer_domain', ctx=Load()),
                              ifs=[],
                              is_async=0),
                           comprehension(
                              target=Name(id='elem2', ctx=Store()),
                              iter=Name(id='integer_domain', ctx=Load()),
                              ifs=[],
                              is_async=0)])),
                  Assign(
                     targets=[
                        Name(id='integer_equal_pairs', ctx=Store())],
                     value=ListComp(
                        elt=Tuple(
                           elts=[
                              Name(id='elem', ctx=Load()),
                              Name(id='elem', ctx=Load())],
                           ctx=Load()),
                        generators=[
                           comprehension(
                              target=Name(id='elem', ctx=Store()),
                              iter=Name(id='integer_domain', ctx=Load()),
                              ifs=[],
                              is_async=0)])),
                  Assign(
                     targets=[
                        Name(id='integer_gt_pairs', ctx=Store())],
                     value=ListComp(
                        elt=Tuple(
                           elts=[
                              Name(id='elem1', ctx=Load()),
                              Name(id='elem2', ctx=Load())],
                           ctx=Load()),
                        generators=[
                           comprehension(
                              target=Name(id='elem1', ctx=Store()),
                              iter=Name(id='integer_domain', ctx=Load()),
                              ifs=[],
                              is_async=0),
                           comprehension(
                              target=Name(id='elem2', ctx=Store()),
                              iter=Name(id='integer_domain', ctx=Load()),
                              ifs=[
                                 Compare(
                                    left=Name(id='elem1', ctx=Load()),
                                    ops=[
                                       Gt()],
                                    comparators=[
                                       Name(id='elem2', ctx=Load())])],
                              is_async=0)])),
                  If(
                     test=Compare(
                        left=Constant(value='_LEQ'),
                        ops=[
                           In()],
                        comparators=[
                           Name(id='operator_list', ctx=Load())]),
                     body=[
                        Expr(
                           value=Call(
                              func=Name(id='append_changes', ctx=Load()),
                              args=[
                                 Name(id='changes', ctx=Load()),
                                 Dict(
                                    keys=[
                                       Constant(value='_LEQ')],
                                    values=[
                                       Call(
                                          func=Name(id='Change', ctx=Load()),
                                          args=[
                                             Constant(value='_LEQ'),
                                             ListComp(
                                                elt=Name(id='pair', ctx=Load()),
                                                generators=[
                                                   comprehension(
                                                      target=Name(id='pair', ctx=Store()),
                                                      iter=Name(id='integer_pairs', ctx=Load()),
                                                      ifs=[
                                                         Compare(
                                                            left=Name(id='pair', ctx=Load()),
                                                            ops=[
                                                               NotIn()],
                                                            comparators=[
                                                               Name(id='integer_gt_pairs', ctx=Load())])],
                                                      is_async=0)]),
                                             Name(id='integer_gt_pairs', ctx=Load())],
                                          keywords=[])])],
                              keywords=[]))],
                     orelse=[]),
                  If(
                     test=Compare(
                        left=Constant(value='_LE'),
                        ops=[
                           In()],
                        comparators=[
                           Name(id='operator_list', ctx=Load())]),
                     body=[
                        Expr(
                           value=Call(
                              func=Name(id='append_changes', ctx=Load()),
                              args=[
                                 Name(id='changes', ctx=Load()),
                                 Dict(
                                    keys=[
                                       Constant(value='_LE')],
                                    values=[
                                       Call(
                                          func=Name(id='Change', ctx=Load()),
                                          args=[
                                             Constant(value='_LE'),
                                             ListComp(
                                                elt=Name(id='pair', ctx=Load()),
                                                generators=[
                                                   comprehension(
                                                      target=Name(id='pair', ctx=Store()),
                                                      iter=Name(id='integer_pairs', ctx=Load()),
                                                      ifs=[
                                                         BoolOp(
                                                            op=And(),
                                                            values=[
                                                               Compare(
                                                                  left=Name(id='pair', ctx=Load()),
                                                                  ops=[
                                                                     NotIn()],
                                                                  comparators=[
                                                                     Name(id='integer_gt_pairs', ctx=Load())]),
                                                               Compare(
                                                                  left=Name(id='pair', ctx=Load()),
                                                                  ops=[
                                                                     NotIn()],
                                                                  comparators=[
                                                                     Name(id='integer_equal_pairs', ctx=Load())])])],
                                                      is_async=0)]),
                                             BinOp(
                                                left=Name(id='integer_gt_pairs', ctx=Load()),
                                                op=Add(),
                                                right=Name(id='integer_equal_pairs', ctx=Load()))],
                                          keywords=[])])],
                              keywords=[]))],
                     orelse=[]),
                  If(
                     test=Compare(
                        left=Constant(value='_GE'),
                        ops=[
                           In()],
                        comparators=[
                           Name(id='operator_list', ctx=Load())]),
                     body=[
                        Expr(
                           value=Call(
                              func=Name(id='append_changes', ctx=Load()),
                              args=[
                                 Name(id='changes', ctx=Load()),
                                 Dict(
                                    keys=[
                                       Constant(value='_GE')],
                                    values=[
                                       Call(
                                          func=Name(id='Change', ctx=Load()),
                                          args=[
                                             Constant(value='_GE'),
                                             Name(id='integer_gt_pairs', ctx=Load()),
                                             ListComp(
                                                elt=Name(id='pair', ctx=Load()),
                                                generators=[
                                                   comprehension(
                                                      target=Name(id='pair', ctx=Store()),
                                                      iter=Name(id='integer_pairs', ctx=Load()),
                                                      ifs=[
                                                         Compare(
                                                            left=Name(id='pair', ctx=Load()),
                                                            ops=[
                                                               NotIn()],
                                                            comparators=[
                                                               Name(id='integer_gt_pairs', ctx=Load())])],
                                                      is_async=0)])],
                                          keywords=[])])],
                              keywords=[]))],
                     orelse=[]),
                  If(
                     test=Compare(
                        left=Constant(value='_GEQ'),
                        ops=[
                           In()],
                        comparators=[
                           Name(id='operator_list', ctx=Load())]),
                     body=[
                        Expr(
                           value=Call(
                              func=Name(id='append_changes', ctx=Load()),
                              args=[
                                 Name(id='changes', ctx=Load()),
                                 Dict(
                                    keys=[
                                       Constant(value='_GEQ')],
                                    values=[
                                       Call(
                                          func=Name(id='Change', ctx=Load()),
                                          args=[
                                             Constant(value='_GEQ'),
                                             BinOp(
                                                left=Name(id='integer_gt_pairs', ctx=Load()),
                                                op=Add(),
                                                right=Name(id='integer_equal_pairs', ctx=Load())),
                                             ListComp(
                                                elt=Name(id='pair', ctx=Load()),
                                                generators=[
                                                   comprehension(
                                                      target=Name(id='pair', ctx=Store()),
                                                      iter=Name(id='integer_pairs', ctx=Load()),
                                                      ifs=[
                                                         BoolOp(
                                                            op=And(),
                                                            values=[
                                                               Compare(
                                                                  left=Name(id='pair', ctx=Load()),
                                                                  ops=[
                                                                     NotIn()],
                                                                  comparators=[
                                                                     Name(id='integer_gt_pairs', ctx=Load())]),
                                                               Compare(
                                                                  left=Name(id='pair', ctx=Load()),
                                                                  ops=[
                                                                     NotIn()],
                                                                  comparators=[
                                                                     Name(id='integer_equal_pairs', ctx=Load())])])],
                                                      is_async=0)])],
                                          keywords=[])])],
                              keywords=[]))],
                     orelse=[])],
               orelse=[]),
            Return(
               value=Name(id='changes', ctx=Load()))],
         decorator_list=[])],
   type_ignores=[])


# Deze functie implementeert de initial_propagation() functie. Hiervoor kijkt het naar Assert-regels (__thesistekst__).
# Na toepassing van het ENF-algoritme zijn Assert-regels regels over een propositioneel symbool dat een regel voorstelt, en dat dus moet evalueren tot True.
# Ook bevat deze functie code om kennis over wiskundige vergelijkingsoperatoren te propageren.
def generate_initial_propagation(grouped_propagators, equality_domain, interpreted_predicates, operator_set):
    tuple_list = []
    for key, val in grouped_propagators.items():
        for prop in val:
            if type(prop) == parsing_idpz3_final.AssertLiteral:
                if prop.literal.pos:
                    truth_string = 'TRUE'
                else:
                    truth_string = 'FALSE'

                arg_list = []
                for arg in prop.literal.atom.args:
                    arg_list.append(Constant(value=arg.name))

                tuple_list.append(Tuple(
                                    elts=[
                                        Constant(value=prop.literal.atom.name),
                                        Tuple(elts=arg_list, ctx=Load()),
                                        Attribute(
                                            value=Name(id='EB', ctx=Load()),
                                            attr=truth_string,
                                            ctx=Load())],
                                    ctx=Load()))

    interpreted_predicates_list = []
    for elem in interpreted_predicates:
        interpreted_predicates_list.append(Constant(value=elem))
    equality_domain_list = []

    for elem in equality_domain:
        equality_domain_list.append(Constant(value=elem))

    operator_list = []
    for elem in operator_set:
        operator_list.append(Constant(value=elem))



    return Module(
   body=[
      FunctionDef(
         name='initial_propagation',
         args=arguments(
            posonlyargs=[],
            args=[],
            kwonlyargs=[],
            kw_defaults=[],
            defaults=[]),
         body=[
            Assign(
               targets=[
                  Name(id='asserted_literals', ctx=Store())],
               value=List(
                  elts=tuple_list,
                  ctx=Load())),
            Assign(
               targets=[
                  Name(id='changes', ctx=Store())],
               value=Dict(keys=[], values=[])),
            For(
               target=Name(id='asserted_lit', ctx=Store()),
               iter=Name(id='asserted_literals', ctx=Load()),
               body=[
                  Assign(
                     targets=[
                        Subscript(
                           value=Attribute(
                              value=Subscript(
                                 value=Name(id='var_dict', ctx=Load()),
                                 slice=Subscript(
                                    value=Name(id='asserted_lit', ctx=Load()),
                                    slice=Constant(value=0),
                                    ctx=Load()),
                                 ctx=Load()),
                              attr='loc',
                              ctx=Load()),
                           slice=Subscript(
                              value=Name(id='asserted_lit', ctx=Load()),
                              slice=Constant(value=1),
                              ctx=Load()),
                           ctx=Store())],
                     value=Subscript(
                        value=Name(id='asserted_lit', ctx=Load()),
                        slice=Constant(value=2),
                        ctx=Load())),
                  If(
                     test=Compare(
                        left=Subscript(
                           value=Name(id='asserted_lit', ctx=Load()),
                           slice=Constant(value=2),
                           ctx=Load()),
                        ops=[
                           Eq()],
                        comparators=[
                           Attribute(
                              value=Name(id='EB', ctx=Load()),
                              attr='TRUE',
                              ctx=Load())]),
                     body=[
                        Expr(
                           value=Call(
                              func=Name(id='append_changes', ctx=Load()),
                              args=[
                                 Name(id='changes', ctx=Load()),
                                 Dict(
                                    keys=[
                                       Subscript(
                                          value=Name(id='asserted_lit', ctx=Load()),
                                          slice=Constant(value=0),
                                          ctx=Load())],
                                    values=[
                                       Call(
                                          func=Name(id='Change', ctx=Load()),
                                          args=[
                                             Subscript(
                                                value=Name(id='asserted_lit', ctx=Load()),
                                                slice=Constant(value=0),
                                                ctx=Load()),
                                             List(
                                                elts=[
                                                   Subscript(
                                                      value=Name(id='asserted_lit', ctx=Load()),
                                                      slice=Constant(value=1),
                                                      ctx=Load())],
                                                ctx=Load()),
                                             List(elts=[], ctx=Load())],
                                          keywords=[])])],
                              keywords=[]))],
                     orelse=[
                        If(
                           test=Compare(
                              left=Subscript(
                                 value=Name(id='asserted_lit', ctx=Load()),
                                 slice=Constant(value=2),
                                 ctx=Load()),
                              ops=[
                                 Eq()],
                              comparators=[
                                 Attribute(
                                    value=Name(id='EB', ctx=Load()),
                                    attr='FALSE',
                                    ctx=Load())]),
                           body=[
                              Expr(
                                 value=Call(
                                    func=Name(id='append_changes', ctx=Load()),
                                    args=[
                                       Name(id='changes', ctx=Load()),
                                       Dict(
                                          keys=[
                                             Subscript(
                                                value=Name(id='asserted_lit', ctx=Load()),
                                                slice=Constant(value=0),
                                                ctx=Load())],
                                          values=[
                                             Call(
                                                func=Name(id='Change', ctx=Load()),
                                                args=[
                                                   Subscript(
                                                      value=Name(id='asserted_lit', ctx=Load()),
                                                      slice=Constant(value=0),
                                                      ctx=Load()),
                                                   List(elts=[], ctx=Load()),
                                                   List(
                                                      elts=[
                                                         Subscript(
                                                            value=Name(id='asserted_lit', ctx=Load()),
                                                            slice=Constant(value=1),
                                                            ctx=Load())],
                                                      ctx=Load())],
                                                keywords=[])])],
                                    keywords=[]))],
                           orelse=[])])],
               orelse=[]),
            Expr(
               value=Call(
                  func=Name(id='append_changes', ctx=Load()),
                  args=[
                     Name(id='changes', ctx=Load()),
                     Call(
                        func=Name(id='fill_in_interpreted_domain', ctx=Load()),
                        args=[
                           List(elts=interpreted_predicates_list, ctx=Load())],
                        keywords=[])],
                  keywords=[])),
            Assign(
               targets=[
                  Name(id='operator_list', ctx=Store())],
               value=List(
                  elts=operator_list,
                  ctx=Load())),
            Assign(
               targets=[
                  Name(id='domain', ctx=Store())],
               value=List(
                  elts=equality_domain_list,
                  ctx=Load())),
            Assign(
               targets=[
                  Name(id='comparison_changes', ctx=Store())],
               value=Call(
                  func=Name(id='get_changes_for_comparison_operators', ctx=Load()),
                  args=[
                     Name(id='operator_list', ctx=Load()),
                     Name(id='domain', ctx=Load())],
                  keywords=[])),
            Expr(
               value=Call(
                  func=Name(id='append_changes', ctx=Load()),
                  args=[
                     Name(id='changes', ctx=Load()),
                     Name(id='comparison_changes', ctx=Load())],
                  keywords=[])),
            Expr(
               value=Call(
                  func=Name(id='propagate_full', ctx=Load()),
                  args=[
                     Name(id='changes', ctx=Load())],
                  keywords=[]))],
         decorator_list=[])],
   type_ignores=[])

# AST voor hulpfunctie
def generate_get_grounded_variable_name():
    return Module(
   body=[
      FunctionDef(
         name='get_grounded_variable_name',
         args=arguments(
            posonlyargs=[],
            args=[
               arg(arg='name'),
               arg(arg='comb')],
            kwonlyargs=[],
            kw_defaults=[],
            defaults=[]),
         body=[
            Assign(
               targets=[
                  Name(id='var_name', ctx=Store())],
               value=Name(id='name', ctx=Load())),
            For(
               target=Name(id='elem', ctx=Store()),
               iter=Name(id='comb', ctx=Load()),
               body=[
                  AugAssign(
                     target=Name(id='var_name', ctx=Store()),
                     op=Add(),
                     value=BinOp(
                        left=Constant(value='_'),
                        op=Add(),
                        right=Call(
                           func=Name(id='str', ctx=Load()),
                           args=[
                              Call(
                                 func=Attribute(
                                    value=Name(id='elem', ctx=Load()),
                                    attr='item',
                                    ctx=Load()),
                                 args=[],
                                 keywords=[])],
                           keywords=[])))],
               orelse=[]),
            Return(
               value=Name(id='var_name', ctx=Load()))],
         decorator_list=[])],
   type_ignores=[])

# AST voor hulpfunctie
def generate_get_grounded_variables_for_display():
    return Module(
   body=[
      FunctionDef(
         name='get_grounded_variables_for_display',
         args=arguments(
            posonlyargs=[],
            args=[
               arg(arg='var_name')],
            kwonlyargs=[],
            kw_defaults=[],
            defaults=[]),
         body=[
            Assign(
               targets=[
                  Name(id='ground_vars', ctx=Store())],
               value=Dict(keys=[], values=[])),
            Assign(
               targets=[
                  Name(id='data_array', ctx=Store())],
               value=Subscript(
                  value=Name(id='var_dict', ctx=Load()),
                  slice=Name(id='var_name', ctx=Load()),
                  ctx=Load())),
            Assign(
               targets=[
                  Name(id='name', ctx=Store())],
               value=Attribute(
                  value=Name(id='data_array', ctx=Load()),
                  attr='name',
                  ctx=Load())),
            Assign(
               targets=[
                  Name(id='new_domains', ctx=Store())],
               value=ListComp(
                  elt=Attribute(
                     value=Subscript(
                        value=Attribute(
                           value=Name(id='data_array', ctx=Load()),
                           attr='coords',
                           ctx=Load()),
                        slice=Name(id='dim', ctx=Load()),
                        ctx=Load()),
                     attr='values',
                     ctx=Load()),
                  generators=[
                     comprehension(
                        target=Name(id='dim', ctx=Store()),
                        iter=Attribute(
                           value=Name(id='data_array', ctx=Load()),
                           attr='dims',
                           ctx=Load()),
                        ifs=[],
                        is_async=0)])),
            For(
               target=Name(id='comb', ctx=Store()),
               iter=Call(
                  func=Name(id='product', ctx=Load()),
                  args=[
                     Starred(
                        value=Name(id='new_domains', ctx=Load()),
                        ctx=Load())],
                  keywords=[]),
               body=[
                  Assign(
                     targets=[
                        Name(id='ground_var_name', ctx=Store())],
                     value=Call(
                        func=Name(id='get_grounded_variable_name', ctx=Load()),
                        args=[
                           Name(id='name', ctx=Load()),
                           Name(id='comb', ctx=Load())],
                        keywords=[])),
                  Assign(
                     targets=[
                        Subscript(
                           value=Name(id='ground_vars', ctx=Load()),
                           slice=Name(id='ground_var_name', ctx=Load()),
                           ctx=Store())],
                     value=Call(
                        func=Attribute(
                           value=Attribute(
                              value=Subscript(
                                 value=Attribute(
                                    value=Name(id='data_array', ctx=Load()),
                                    attr='loc',
                                    ctx=Load()),
                                 slice=Name(id='comb', ctx=Load()),
                                 ctx=Load()),
                              attr='values',
                              ctx=Load()),
                           attr='item',
                           ctx=Load()),
                        args=[],
                        keywords=[]))],
               orelse=[]),
            Return(
               value=Name(id='ground_vars', ctx=Load()))],
         decorator_list=[])],
   type_ignores=[])

# AST voor hulpfunctie
def generate_terminal_test():
    return Module(
   body=[
      FunctionDef(
         name='test_on_user_input',
         args=arguments(
            posonlyargs=[],
            args=[],
            kwonlyargs=[],
            kw_defaults=[],
            defaults=[]),
         body=[
            Assign(
               targets=[
                  Name(id='current_var', ctx=Store())],
               value=Constant(value='')),
            Assign(
               targets=[
                  Name(id='start', ctx=Store())],
               value=Call(
                  func=Attribute(
                     value=Name(id='time', ctx=Load()),
                     attr='time',
                     ctx=Load()),
                  args=[],
                  keywords=[])),
            Expr(
               value=Call(
                  func=Name(id='initial_propagation', ctx=Load()),
                  args=[],
                  keywords=[])),
            Assign(
               targets=[
                  Name(id='end', ctx=Store())],
               value=Call(
                  func=Attribute(
                     value=Name(id='time', ctx=Load()),
                     attr='time',
                     ctx=Load()),
                  args=[],
                  keywords=[])),
            Expr(
               value=Call(
                  func=Name(id='print', ctx=Load()),
                  args=[
                     Constant(value='Initial propagation: '),
                     BinOp(
                        left=Name(id='end', ctx=Load()),
                        op=Sub(),
                        right=Name(id='start', ctx=Load()))],
                  keywords=[])),
            For(
               target=Name(id='var_name', ctx=Store()),
               iter=Call(
                  func=Attribute(
                     value=Name(id='var_dict', ctx=Load()),
                     attr='keys',
                     ctx=Load()),
                  args=[],
                  keywords=[]),
               body=[
                  If(
                     test=UnaryOp(
                        op=Not(),
                        operand=Call(
                           func=Attribute(
                              value=Name(id='var_name', ctx=Load()),
                              attr='startswith',
                              ctx=Load()),
                           args=[
                              Constant(value='_')],
                           keywords=[])),
                     body=[
                        Expr(
                           value=Call(
                              func=Name(id='print', ctx=Load()),
                              args=[
                                 Constant(value='__________________________')],
                              keywords=[])),
                        Assign(
                           targets=[
                              Name(id='grounded_var', ctx=Store())],
                           value=Call(
                              func=Name(id='get_grounded_variables_for_display', ctx=Load()),
                              args=[
                                 Name(id='var_name', ctx=Load())],
                              keywords=[])),
                        For(
                           target=Tuple(
                              elts=[
                                 Name(id='key', ctx=Store()),
                                 Name(id='val', ctx=Store())],
                              ctx=Store()),
                           iter=Call(
                              func=Attribute(
                                 value=Name(id='grounded_var', ctx=Load()),
                                 attr='items',
                                 ctx=Load()),
                              args=[],
                              keywords=[]),
                           body=[
                              Expr(
                                 value=Call(
                                    func=Name(id='print', ctx=Load()),
                                    args=[
                                       BinOp(
                                          left=BinOp(
                                             left=Name(id='key', ctx=Load()),
                                             op=Add(),
                                             right=Constant(value=': ')),
                                          op=Add(),
                                          right=Call(
                                             func=Name(id='str', ctx=Load()),
                                             args=[
                                                Name(id='val', ctx=Load())],
                                             keywords=[]))],
                                    keywords=[]))],
                           orelse=[]),
                        Expr(
                           value=Call(
                              func=Name(id='print', ctx=Load()),
                              args=[
                                 Constant(value='__________________________')],
                              keywords=[]))],
                     orelse=[])],
               orelse=[]),
            While(
               test=Compare(
                  left=Call(
                     func=Attribute(
                        value=Name(id='current_var', ctx=Load()),
                        attr='lower',
                        ctx=Load()),
                     args=[],
                     keywords=[]),
                  ops=[
                     NotEq()],
                  comparators=[
                     Constant(value='stop')]),
               body=[
                  Assign(
                     targets=[
                        Name(id='current_var', ctx=Store())],
                     value=Call(
                        func=Name(id='input', ctx=Load()),
                        args=[
                           Constant(value='Give the name of the variable\n')],
                        keywords=[])),
                  If(
                     test=Compare(
                        left=Name(id='current_var', ctx=Load()),
                        ops=[
                           NotIn()],
                        comparators=[
                           Call(
                              func=Attribute(
                                 value=Name(id='var_dict', ctx=Load()),
                                 attr='keys',
                                 ctx=Load()),
                              args=[],
                              keywords=[])]),
                     body=[
                        Expr(
                           value=Call(
                              func=Name(id='print', ctx=Load()),
                              args=[
                                 Constant(value="Try again, this variable doesn't exist")],
                              keywords=[])),
                        Continue()],
                     orelse=[]),
                  Assign(
                     targets=[
                        Name(id='args', ctx=Store())],
                     value=List(elts=[], ctx=Load())),
                  For(
                     target=Name(id='i', ctx=Store()),
                     iter=Call(
                        func=Name(id='range', ctx=Load()),
                        args=[
                           Call(
                              func=Name(id='len', ctx=Load()),
                              args=[
                                 Attribute(
                                    value=Subscript(
                                       value=Name(id='var_dict', ctx=Load()),
                                       slice=Name(id='current_var', ctx=Load()),
                                       ctx=Load()),
                                    attr='dims',
                                    ctx=Load())],
                              keywords=[])],
                        keywords=[]),
                     body=[
                        Assign(
                           targets=[
                              Name(id='new_arg', ctx=Store())],
                           value=Call(
                              func=Name(id='input', ctx=Load()),
                              args=[
                                 JoinedStr(
                                    values=[
                                       Constant(value='Give argument number '),
                                       FormattedValue(
                                          value=BinOp(
                                             left=Name(id='i', ctx=Load()),
                                             op=Add(),
                                             right=Constant(value=1)),
                                          conversion=-1),
                                       Constant(value=':\n')])],
                              keywords=[])),
                        If(
                           test=Call(
                              func=Attribute(
                                 value=Name(id='new_arg', ctx=Load()),
                                 attr='isdigit',
                                 ctx=Load()),
                              args=[],
                              keywords=[]),
                           body=[
                              Expr(
                                 value=Call(
                                    func=Attribute(
                                       value=Name(id='args', ctx=Load()),
                                       attr='append',
                                       ctx=Load()),
                                    args=[
                                       Call(
                                          func=Name(id='int', ctx=Load()),
                                          args=[
                                             Name(id='new_arg', ctx=Load())],
                                          keywords=[])],
                                    keywords=[]))],
                           orelse=[
                              Expr(
                                 value=Call(
                                    func=Attribute(
                                       value=Name(id='args', ctx=Load()),
                                       attr='append',
                                       ctx=Load()),
                                    args=[
                                       Name(id='new_arg', ctx=Load())],
                                    keywords=[]))])],
                     orelse=[]),
                  Assign(
                     targets=[
                        Name(id='b', ctx=Store())],
                     value=Call(
                        func=Name(id='input', ctx=Load()),
                        args=[
                           Constant(value='True (1) or false (0)?\n')],
                        keywords=[])),
                  If(
                     test=Compare(
                        left=Name(id='b', ctx=Load()),
                        ops=[
                           NotEq()],
                        comparators=[
                           Constant(value='0')]),
                     body=[
                        Assign(
                           targets=[
                              Name(id='b_val', ctx=Store())],
                           value=Attribute(
                              value=Name(id='EB', ctx=Load()),
                              attr='TRUE',
                              ctx=Load()))],
                     orelse=[
                        Assign(
                           targets=[
                              Name(id='b_val', ctx=Store())],
                           value=Attribute(
                              value=Name(id='EB', ctx=Load()),
                              attr='FALSE',
                              ctx=Load()))]),
                  Assign(
                     targets=[
                        Name(id='current_array', ctx=Store())],
                     value=Subscript(
                        value=Name(id='var_dict', ctx=Load()),
                        slice=Name(id='current_var', ctx=Load()),
                        ctx=Load())),
                  If(
                     test=Compare(
                        left=Subscript(
                           value=Attribute(
                              value=Name(id='current_array', ctx=Load()),
                              attr='loc',
                              ctx=Load()),
                           slice=Tuple(
                              elts=[
                                 Starred(
                                    value=Name(id='args', ctx=Load()),
                                    ctx=Load())],
                              ctx=Load()),
                           ctx=Load()),
                        ops=[
                           Eq()],
                        comparators=[
                           Attribute(
                              value=Name(id='EB', ctx=Load()),
                              attr='UNKNOWN',
                              ctx=Load())]),
                     body=[
                        Assign(
                           targets=[
                              Subscript(
                                 value=Attribute(
                                    value=Name(id='current_array', ctx=Load()),
                                    attr='loc',
                                    ctx=Load()),
                                 slice=Tuple(
                                    elts=[
                                       Starred(
                                          value=Name(id='args', ctx=Load()),
                                          ctx=Load())],
                                    ctx=Load()),
                                 ctx=Store())],
                           value=Name(id='b_val', ctx=Load()))],
                     orelse=[
                        Expr(
                           value=Call(
                              func=Name(id='print', ctx=Load()),
                              args=[
                                 Constant(value='Sorry, this variable is already assigned a value')],
                              keywords=[])),
                        Continue()]),
                  Assign(
                     targets=[
                        Name(id='change', ctx=Store())],
                     value=Dict(keys=[], values=[])),
                  If(
                     test=Compare(
                        left=Name(id='b_val', ctx=Load()),
                        ops=[
                           Eq()],
                        comparators=[
                           Attribute(
                              value=Name(id='EB', ctx=Load()),
                              attr='TRUE',
                              ctx=Load())]),
                     body=[
                        Expr(
                           value=Call(
                              func=Name(id='append_changes', ctx=Load()),
                              args=[
                                 Name(id='change', ctx=Load()),
                                 Dict(
                                    keys=[
                                       Name(id='current_var', ctx=Load())],
                                    values=[
                                       Call(
                                          func=Name(id='Change', ctx=Load()),
                                          args=[
                                             Name(id='current_var', ctx=Load()),
                                             List(
                                                elts=[
                                                   Call(
                                                      func=Name(id='tuple', ctx=Load()),
                                                      args=[
                                                         Name(id='args', ctx=Load())],
                                                      keywords=[])],
                                                ctx=Load()),
                                             List(elts=[], ctx=Load())],
                                          keywords=[])])],
                              keywords=[]))],
                     orelse=[
                        Expr(
                           value=Call(
                              func=Name(id='append_changes', ctx=Load()),
                              args=[
                                 Name(id='change', ctx=Load()),
                                 Dict(
                                    keys=[
                                       Name(id='current_var', ctx=Load())],
                                    values=[
                                       Call(
                                          func=Name(id='Change', ctx=Load()),
                                          args=[
                                             Name(id='current_var', ctx=Load()),
                                             List(elts=[], ctx=Load()),
                                             List(
                                                elts=[
                                                   Call(
                                                      func=Name(id='tuple', ctx=Load()),
                                                      args=[
                                                         Name(id='args', ctx=Load())],
                                                      keywords=[])],
                                                ctx=Load())],
                                          keywords=[])])],
                              keywords=[]))]),
                  Assign(
                     targets=[
                        Name(id='start', ctx=Store())],
                     value=Call(
                        func=Attribute(
                           value=Name(id='time', ctx=Load()),
                           attr='time',
                           ctx=Load()),
                        args=[],
                        keywords=[])),
                  Expr(
                     value=Call(
                        func=Name(id='propagate_full', ctx=Load()),
                        args=[
                           Name(id='change', ctx=Load())],
                        keywords=[])),
                  Assign(
                     targets=[
                        Name(id='end', ctx=Store())],
                     value=Call(
                        func=Attribute(
                           value=Name(id='time', ctx=Load()),
                           attr='time',
                           ctx=Load()),
                        args=[],
                        keywords=[])),
                  For(
                     target=Name(id='var_name', ctx=Store()),
                     iter=Call(
                        func=Attribute(
                           value=Name(id='var_dict', ctx=Load()),
                           attr='keys',
                           ctx=Load()),
                        args=[],
                        keywords=[]),
                     body=[
                        If(
                           test=UnaryOp(
                              op=Not(),
                              operand=Call(
                                 func=Attribute(
                                    value=Name(id='var_name', ctx=Load()),
                                    attr='startswith',
                                    ctx=Load()),
                                 args=[
                                    Constant(value='_')],
                                 keywords=[])),
                           body=[
                              Expr(
                                 value=Call(
                                    func=Name(id='print', ctx=Load()),
                                    args=[
                                       Constant(value='__________________________')],
                                    keywords=[])),
                              Assign(
                                 targets=[
                                    Name(id='grounded_var', ctx=Store())],
                                 value=Call(
                                    func=Name(id='get_grounded_variables_for_display', ctx=Load()),
                                    args=[
                                       Name(id='var_name', ctx=Load())],
                                    keywords=[])),
                              For(
                                 target=Tuple(
                                    elts=[
                                       Name(id='key', ctx=Store()),
                                       Name(id='val', ctx=Store())],
                                    ctx=Store()),
                                 iter=Call(
                                    func=Attribute(
                                       value=Name(id='grounded_var', ctx=Load()),
                                       attr='items',
                                       ctx=Load()),
                                    args=[],
                                    keywords=[]),
                                 body=[
                                    Expr(
                                       value=Call(
                                          func=Name(id='print', ctx=Load()),
                                          args=[
                                             BinOp(
                                                left=BinOp(
                                                   left=Name(id='key', ctx=Load()),
                                                   op=Add(),
                                                   right=Constant(value=': ')),
                                                op=Add(),
                                                right=Call(
                                                   func=Name(id='str', ctx=Load()),
                                                   args=[
                                                      Name(id='val', ctx=Load())],
                                                   keywords=[]))],
                                          keywords=[]))],
                                 orelse=[]),
                              Expr(
                                 value=Call(
                                    func=Name(id='print', ctx=Load()),
                                    args=[
                                       Constant(value='__________________________')],
                                    keywords=[]))],
                           orelse=[])],
                     orelse=[]),
                  Expr(
                     value=Call(
                        func=Name(id='print', ctx=Load()),
                        args=[
                           Constant(value='Time to propagate: '),
                           BinOp(
                              left=Name(id='end', ctx=Load()),
                              op=Sub(),
                              right=Name(id='start', ctx=Load()))],
                        keywords=[]))],
               orelse=[])],
         decorator_list=[]),
      Expr(
         value=Call(
            func=Name(id='test_on_user_input', ctx=Load()),
            args=[],
            keywords=[]))],
   type_ignores=[])


# AST voor hulpfunctie
def generate_dash_functionality():
    return Module(
   body=[
      FunctionDef(
         name='unground',
         args=arguments(
            posonlyargs=[],
            args=[
               arg(arg='ground_name')],
            kwonlyargs=[],
            kw_defaults=[],
            defaults=[]),
         body=[
            Assign(
               targets=[
                  Name(id='parts', ctx=Store())],
               value=Call(
                  func=Attribute(
                     value=Name(id='ground_name', ctx=Load()),
                     attr='split',
                     ctx=Load()),
                  args=[
                     Constant(value='_')],
                  keywords=[])),
            Assign(
               targets=[
                  Name(id='name', ctx=Store())],
               value=Subscript(
                  value=Name(id='parts', ctx=Load()),
                  slice=Constant(value=0),
                  ctx=Load())),
            Assign(
               targets=[
                  Name(id='args', ctx=Store())],
               value=Call(
                  func=Name(id='tuple', ctx=Load()),
                  args=[
                     GeneratorExp(
                        elt=IfExp(
                           test=Call(
                              func=Attribute(
                                 value=Name(id='x', ctx=Load()),
                                 attr='isdigit',
                                 ctx=Load()),
                              args=[],
                              keywords=[]),
                           body=Call(
                              func=Name(id='int', ctx=Load()),
                              args=[
                                 Name(id='x', ctx=Load())],
                              keywords=[]),
                           orelse=Name(id='x', ctx=Load())),
                        generators=[
                           comprehension(
                              target=Name(id='x', ctx=Store()),
                              iter=Subscript(
                                 value=Name(id='parts', ctx=Load()),
                                 slice=Slice(
                                    lower=Constant(value=1)),
                                 ctx=Load()),
                              ifs=[],
                              is_async=0)])],
                  keywords=[])),
            Return(
               value=Tuple(
                  elts=[
                     Name(id='name', ctx=Load()),
                     Name(id='args', ctx=Load())],
                  ctx=Load()))],
         decorator_list=[]),
      FunctionDef(
         name='get_dropdown_options',
         args=arguments(
            posonlyargs=[],
            args=[
               arg(arg='integer_list')],
            kwonlyargs=[],
            kw_defaults=[],
            defaults=[]),
         body=[
            Assign(
               targets=[
                  Name(id='options_list', ctx=Store())],
               value=List(elts=[], ctx=Load())),
            For(
               target=Name(id='i', ctx=Store()),
               iter=Name(id='integer_list', ctx=Load()),
               body=[
                  Expr(
                     value=Call(
                        func=Attribute(
                           value=Name(id='options_list', ctx=Load()),
                           attr='append',
                           ctx=Load()),
                        args=[
                           Dict(
                              keys=[
                                 Constant(value='label'),
                                 Constant(value='value')],
                              values=[
                                 Call(
                                    func=Name(id='str', ctx=Load()),
                                    args=[
                                       Name(id='i', ctx=Load())],
                                    keywords=[]),
                                 Name(id='i', ctx=Load())])],
                        keywords=[]))],
               orelse=[]),
            Return(
               value=Name(id='options_list', ctx=Load()))],
         decorator_list=[]),
      FunctionDef(
         name='convert_to_ui',
         args=arguments(
            posonlyargs=[],
            args=[
               arg(arg='values')],
            kwonlyargs=[],
            kw_defaults=[],
            defaults=[]),
         body=[
            If(
               test=Compare(
                  left=Name(id='values', ctx=Load()),
                  ops=[
                     Eq()],
                  comparators=[
                     Attribute(
                        value=Name(id='EB', ctx=Load()),
                        attr='UNKNOWN',
                        ctx=Load())]),
               body=[
                  Return(
                     value=List(elts=[], ctx=Load()))],
               orelse=[]),
            If(
               test=Compare(
                  left=Name(id='values', ctx=Load()),
                  ops=[
                     Eq()],
                  comparators=[
                     Attribute(
                        value=Name(id='EB', ctx=Load()),
                        attr='TRUE',
                        ctx=Load())]),
               body=[
                  Return(
                     value=List(
                        elts=[
                           Constant(value=True)],
                        ctx=Load()))],
               orelse=[]),
            If(
               test=Compare(
                  left=Name(id='values', ctx=Load()),
                  ops=[
                     Eq()],
                  comparators=[
                     Attribute(
                        value=Name(id='EB', ctx=Load()),
                        attr='FALSE',
                        ctx=Load())]),
               body=[
                  Return(
                     value=List(
                        elts=[
                           Constant(value=False)],
                        ctx=Load()))],
               orelse=[]),
            If(
               test=Compare(
                  left=Name(id='values', ctx=Load()),
                  ops=[
                     Eq()],
                  comparators=[
                     Attribute(
                        value=Name(id='EB', ctx=Load()),
                        attr='INCONSISTENT',
                        ctx=Load())]),
               body=[
                  Return(
                     value=List(elts=[], ctx=Load()))],
               orelse=[
                  Return(
                     value=Call(
                        func=Name(id='get_dropdown_options', ctx=Load()),
                        args=[
                           Name(id='values', ctx=Load())],
                        keywords=[]))])],
         decorator_list=[]),
      FunctionDef(
         name='convert_from_ui',
         args=arguments(
            posonlyargs=[],
            args=[
               arg(arg='values')],
            kwonlyargs=[],
            kw_defaults=[],
            defaults=[]),
         body=[
            If(
               test=BoolOp(
                  op=Or(),
                  values=[
                     Compare(
                        left=Name(id='values', ctx=Load()),
                        ops=[
                           Eq()],
                        comparators=[
                           List(
                              elts=[
                                 Constant(value=True),
                                 Constant(value=False)],
                              ctx=Load())]),
                     Compare(
                        left=Name(id='values', ctx=Load()),
                        ops=[
                           Eq()],
                        comparators=[
                           List(
                              elts=[
                                 Constant(value=False),
                                 Constant(value=True)],
                              ctx=Load())])]),
               body=[
                  Return(
                     value=Attribute(
                        value=Name(id='EB', ctx=Load()),
                        attr='INCONSISTENT',
                        ctx=Load()))],
               orelse=[]),
            If(
               test=Compare(
                  left=Name(id='values', ctx=Load()),
                  ops=[
                     Eq()],
                  comparators=[
                     List(
                        elts=[
                           Constant(value=True)],
                        ctx=Load())]),
               body=[
                  Return(
                     value=Attribute(
                        value=Name(id='EB', ctx=Load()),
                        attr='TRUE',
                        ctx=Load()))],
               orelse=[]),
            If(
               test=Compare(
                  left=Name(id='values', ctx=Load()),
                  ops=[
                     Eq()],
                  comparators=[
                     List(
                        elts=[
                           Constant(value=False)],
                        ctx=Load())]),
               body=[
                  Return(
                     value=Attribute(
                        value=Name(id='EB', ctx=Load()),
                        attr='FALSE',
                        ctx=Load()))],
               orelse=[
                  Return(
                     value=Attribute(
                        value=Name(id='EB', ctx=Load()),
                        attr='UNKNOWN',
                        ctx=Load()))])],
         decorator_list=[]),
      FunctionDef(
         name='launch_dash_app',
         args=arguments(
            posonlyargs=[],
            args=[],
            kwonlyargs=[],
            kw_defaults=[],
            defaults=[]),
         body=[
            Assign(
               targets=[
                  Name(id='app', ctx=Store())],
               value=Call(
                  func=Name(id='Dash', ctx=Load()),
                  args=[
                     Name(id='__name__', ctx=Load())],
                  keywords=[])),
            Expr(
               value=Call(
                  func=Name(id='initial_propagation', ctx=Load()),
                  args=[],
                  keywords=[])),
            Assign(
               targets=[
                  Name(id='structure', ctx=Store())],
               value=Dict(keys=[], values=[])),
            For(
               target=Name(id='var_name', ctx=Store()),
               iter=Call(
                  func=Attribute(
                     value=Name(id='var_dict', ctx=Load()),
                     attr='keys',
                     ctx=Load()),
                  args=[],
                  keywords=[]),
               body=[
                  Expr(
                     value=Call(
                        func=Attribute(
                           value=Name(id='structure', ctx=Load()),
                           attr='update',
                           ctx=Load()),
                        args=[
                           Call(
                              func=Name(id='get_grounded_variables_for_display', ctx=Load()),
                              args=[
                                 Name(id='var_name', ctx=Load())],
                              keywords=[])],
                        keywords=[]))],
               orelse=[]),
            Assign(
               targets=[
                  Name(id='boolean_variables', ctx=Store())],
               value=ListComp(
                  elt=Name(id='v', ctx=Load()),
                  generators=[
                     comprehension(
                        target=Name(id='v', ctx=Store()),
                        iter=Call(
                           func=Attribute(
                              value=Name(id='structure', ctx=Load()),
                              attr='keys',
                              ctx=Load()),
                           args=[],
                           keywords=[]),
                        ifs=[
                           UnaryOp(
                              op=Not(),
                              operand=Call(
                                 func=Attribute(
                                    value=Name(id='v', ctx=Load()),
                                    attr='startswith',
                                    ctx=Load()),
                                 args=[
                                    Constant(value='_')],
                                 keywords=[]))],
                        is_async=0)])),
            Expr(
               value=Call(
                  func=Attribute(
                     value=Name(id='boolean_variables', ctx=Load()),
                     attr='sort',
                     ctx=Load()),
                  args=[],
                  keywords=[])),
            Assign(
               targets=[
                  Name(id='integer_variables', ctx=Store())],
               value=List(elts=[], ctx=Load())),
            Assign(
               targets=[
                  Attribute(
                     value=Name(id='app', ctx=Load()),
                     attr='layout',
                     ctx=Store())],
               value=Call(
                  func=Attribute(
                     value=Name(id='html', ctx=Load()),
                     attr='Div',
                     ctx=Load()),
                  args=[
                     List(
                        elts=[
                           Call(
                              func=Attribute(
                                 value=Name(id='html', ctx=Load()),
                                 attr='H1',
                                 ctx=Load()),
                              args=[
                                 Constant(value='Interactive configuration')],
                              keywords=[]),
                           Call(
                              func=Attribute(
                                 value=Name(id='html', ctx=Load()),
                                 attr='Button',
                                 ctx=Load()),
                              args=[
                                 Constant(value='Reset')],
                              keywords=[
                                 keyword(
                                    arg='id',
                                    value=Constant(value='reset-button')),
                                 keyword(
                                    arg='n_clicks',
                                    value=Constant(value=0))]),
                           Call(
                              func=Attribute(
                                 value=Name(id='html', ctx=Load()),
                                 attr='Div',
                                 ctx=Load()),
                              args=[
                                 ListComp(
                                    elt=Call(
                                       func=Attribute(
                                          value=Name(id='html', ctx=Load()),
                                          attr='Div',
                                          ctx=Load()),
                                       args=[
                                          List(
                                             elts=[
                                                Call(
                                                   func=Attribute(
                                                      value=Name(id='html', ctx=Load()),
                                                      attr='Label',
                                                      ctx=Load()),
                                                   args=[
                                                      JoinedStr(
                                                         values=[
                                                            FormattedValue(
                                                               value=Name(id='var', ctx=Load()),
                                                               conversion=-1),
                                                            Constant(value=':')])],
                                                   keywords=[]),
                                                Call(
                                                   func=Attribute(
                                                      value=Name(id='dcc', ctx=Load()),
                                                      attr='Checklist',
                                                      ctx=Load()),
                                                   args=[],
                                                   keywords=[
                                                      keyword(
                                                         arg='id',
                                                         value=Dict(
                                                            keys=[
                                                               Constant(value='type'),
                                                               Constant(value='index')],
                                                            values=[
                                                               Constant(value='checkboxes'),
                                                               Name(id='var', ctx=Load())])),
                                                      keyword(
                                                         arg='options',
                                                         value=List(
                                                            elts=[
                                                               Dict(
                                                                  keys=[
                                                                     Constant(value='label'),
                                                                     Constant(value='value')],
                                                                  values=[
                                                                     Constant(value='True'),
                                                                     Constant(value=True)]),
                                                               Dict(
                                                                  keys=[
                                                                     Constant(value='label'),
                                                                     Constant(value='value')],
                                                                  values=[
                                                                     Constant(value='False'),
                                                                     Constant(value=False)])],
                                                            ctx=Load())),
                                                      keyword(
                                                         arg='value',
                                                         value=Call(
                                                            func=Name(id='convert_to_ui', ctx=Load()),
                                                            args=[
                                                               Subscript(
                                                                  value=Name(id='structure', ctx=Load()),
                                                                  slice=Name(id='var', ctx=Load()),
                                                                  ctx=Load())],
                                                            keywords=[])),
                                                      keyword(
                                                         arg='inline',
                                                         value=Constant(value=True))]),
                                                Call(
                                                   func=Attribute(
                                                      value=Name(id='html', ctx=Load()),
                                                      attr='Div',
                                                      ctx=Load()),
                                                   args=[],
                                                   keywords=[
                                                      keyword(
                                                         arg='id',
                                                         value=Dict(
                                                            keys=[
                                                               Constant(value='type'),
                                                               Constant(value='index')],
                                                            values=[
                                                               Constant(value='output'),
                                                               Name(id='var', ctx=Load())]))])],
                                             ctx=Load())],
                                       keywords=[]),
                                    generators=[
                                       comprehension(
                                          target=Name(id='var', ctx=Store()),
                                          iter=Name(id='boolean_variables', ctx=Load()),
                                          ifs=[],
                                          is_async=0)])],
                              keywords=[]),
                           Call(
                              func=Attribute(
                                 value=Name(id='html', ctx=Load()),
                                 attr='Div',
                                 ctx=Load()),
                              args=[
                                 ListComp(
                                    elt=Call(
                                       func=Attribute(
                                          value=Name(id='html', ctx=Load()),
                                          attr='Div',
                                          ctx=Load()),
                                       args=[
                                          List(
                                             elts=[
                                                Call(
                                                   func=Attribute(
                                                      value=Name(id='html', ctx=Load()),
                                                      attr='Label',
                                                      ctx=Load()),
                                                   args=[
                                                      JoinedStr(
                                                         values=[
                                                            FormattedValue(
                                                               value=Name(id='var', ctx=Load()),
                                                               conversion=-1),
                                                            Constant(value=':')])],
                                                   keywords=[]),
                                                Call(
                                                   func=Attribute(
                                                      value=Name(id='dcc', ctx=Load()),
                                                      attr='Dropdown',
                                                      ctx=Load()),
                                                   args=[],
                                                   keywords=[
                                                      keyword(
                                                         arg='id',
                                                         value=Dict(
                                                            keys=[
                                                               Constant(value='type'),
                                                               Constant(value='index')],
                                                            values=[
                                                               Constant(value='dropdown'),
                                                               Name(id='var', ctx=Load())])),
                                                      keyword(
                                                         arg='options',
                                                         value=Call(
                                                            func=Name(id='get_dropdown_options', ctx=Load()),
                                                            args=[
                                                               Subscript(
                                                                  value=Name(id='structure', ctx=Load()),
                                                                  slice=Name(id='var', ctx=Load()),
                                                                  ctx=Load())],
                                                            keywords=[])),
                                                      keyword(
                                                         arg='placeholder',
                                                         value=Constant(value='Select a number'))]),
                                                Call(
                                                   func=Attribute(
                                                      value=Name(id='html', ctx=Load()),
                                                      attr='Div',
                                                      ctx=Load()),
                                                   args=[],
                                                   keywords=[
                                                      keyword(
                                                         arg='id',
                                                         value=Dict(
                                                            keys=[
                                                               Constant(value='type'),
                                                               Constant(value='index')],
                                                            values=[
                                                               Constant(value='output'),
                                                               Name(id='var', ctx=Load())]))])],
                                             ctx=Load())],
                                       keywords=[]),
                                    generators=[
                                       comprehension(
                                          target=Name(id='var', ctx=Store()),
                                          iter=Name(id='integer_variables', ctx=Load()),
                                          ifs=[],
                                          is_async=0)])],
                              keywords=[]),
                           Call(
                              func=Attribute(
                                 value=Name(id='html', ctx=Load()),
                                 attr='Div',
                                 ctx=Load()),
                              args=[
                                 List(
                                    elts=[
                                       Call(
                                          func=Attribute(
                                             value=Name(id='html', ctx=Load()),
                                             attr='Div',
                                             ctx=Load()),
                                          args=[],
                                          keywords=[
                                             keyword(
                                                arg='id',
                                                value=Dict(
                                                   keys=[
                                                      Constant(value='type')],
                                                   values=[
                                                      Constant(value='text-output')])),
                                             keyword(
                                                arg='children',
                                                value=Constant(value='No inconsistencies detected yet'))])],
                                    ctx=Load())],
                              keywords=[])],
                        ctx=Load())],
                  keywords=[])),
            FunctionDef(
               name='handle_changes',
               args=arguments(
                  posonlyargs=[],
                  args=[
                     arg(arg='checkbox_values'),
                     arg(arg='dropdown_values'),
                     arg(arg='checkbox_ids'),
                     arg(arg='dropdown_ids'),
                     arg(arg='reset')],
                  kwonlyargs=[],
                  kw_defaults=[],
                  defaults=[]),
               body=[
                  Assign(
                     targets=[
                        Name(id='triggered', ctx=Store())],
                     value=Attribute(
                        value=Name(id='callback_context', ctx=Load()),
                        attr='triggered',
                        ctx=Load())),
                  If(
                     test=Name(id='triggered', ctx=Load()),
                     body=[
                        Assign(
                           targets=[
                              Name(id='changed_component', ctx=Store())],
                           value=Subscript(
                              value=Call(
                                 func=Attribute(
                                    value=Subscript(
                                       value=Subscript(
                                          value=Name(id='triggered', ctx=Load()),
                                          slice=Constant(value=0),
                                          ctx=Load()),
                                       slice=Constant(value='prop_id'),
                                       ctx=Load()),
                                    attr='split',
                                    ctx=Load()),
                                 args=[
                                    Constant(value='.')],
                                 keywords=[]),
                              slice=Constant(value=0),
                              ctx=Load())),
                        Assign(
                           targets=[
                              Name(id='changed_value', ctx=Store())],
                           value=Subscript(
                              value=Subscript(
                                 value=Name(id='triggered', ctx=Load()),
                                 slice=Constant(value=0),
                                 ctx=Load()),
                              slice=Constant(value='value'),
                              ctx=Load())),
                        If(
                           test=Compare(
                              left=Name(id='changed_component', ctx=Load()),
                              ops=[
                                 Eq()],
                              comparators=[
                                 Constant(value='reset-button')]),
                           body=[
                              Expr(
                                 value=Call(
                                    func=Name(id='print', ctx=Load()),
                                    args=[
                                       Constant(value='reset is being handled')],
                                    keywords=[])),
                              Expr(
                                 value=Call(
                                    func=Name(id='handle_reset', ctx=Load()),
                                    args=[],
                                    keywords=[])),
                              Expr(
                                 value=Call(
                                    func=Name(id='initial_propagation', ctx=Load()),
                                    args=[],
                                    keywords=[])),
                              For(
                                 target=Name(id='var_name', ctx=Store()),
                                 iter=Call(
                                    func=Attribute(
                                       value=Name(id='var_dict', ctx=Load()),
                                       attr='keys',
                                       ctx=Load()),
                                    args=[],
                                    keywords=[]),
                                 body=[
                                    Expr(
                                       value=Call(
                                          func=Attribute(
                                             value=Name(id='structure', ctx=Load()),
                                             attr='update',
                                             ctx=Load()),
                                          args=[
                                             Call(
                                                func=Name(id='get_grounded_variables_for_display', ctx=Load()),
                                                args=[
                                                   Name(id='var_name', ctx=Load())],
                                                keywords=[])],
                                          keywords=[]))],
                                 orelse=[]),
                              Assign(
                                 targets=[
                                    Name(id='checkbox_values', ctx=Store())],
                                 value=ListComp(
                                    elt=Call(
                                       func=Name(id='convert_to_ui', ctx=Load()),
                                       args=[
                                          Subscript(
                                             value=Name(id='structure', ctx=Load()),
                                             slice=Name(id='val', ctx=Load()),
                                             ctx=Load())],
                                       keywords=[]),
                                    generators=[
                                       comprehension(
                                          target=Name(id='val', ctx=Store()),
                                          iter=Name(id='boolean_variables', ctx=Load()),
                                          ifs=[],
                                          is_async=0)])),
                              Assign(
                                 targets=[
                                    Name(id='dropdown_options', ctx=Store())],
                                 value=ListComp(
                                    elt=Call(
                                       func=Name(id='get_dropdown_options', ctx=Load()),
                                       args=[
                                          Subscript(
                                             value=Name(id='structure', ctx=Load()),
                                             slice=Name(id='v', ctx=Load()),
                                             ctx=Load())],
                                       keywords=[]),
                                    generators=[
                                       comprehension(
                                          target=Name(id='v', ctx=Store()),
                                          iter=Name(id='integer_variables', ctx=Load()),
                                          ifs=[],
                                          is_async=0)])),
                              Return(
                                 value=Tuple(
                                    elts=[
                                       Name(id='checkbox_values', ctx=Load()),
                                       Name(id='dropdown_options', ctx=Load()),
                                       List(
                                          elts=[
                                             Constant(value='No inconsistencies detected yet')],
                                          ctx=Load())],
                                    ctx=Load()))],
                           orelse=[]),
                        Assign(
                           targets=[
                              Name(id='changed_id', ctx=Store())],
                           value=Call(
                              func=Name(id='eval', ctx=Load()),
                              args=[
                                 Name(id='changed_component', ctx=Load())],
                              keywords=[])),
                        If(
                           test=Compare(
                              left=Subscript(
                                 value=Name(id='changed_id', ctx=Load()),
                                 slice=Constant(value='type'),
                                 ctx=Load()),
                              ops=[
                                 Eq()],
                              comparators=[
                                 Constant(value='checkboxes')]),
                           body=[
                              If(
                                 test=Compare(
                                    left=Call(
                                       func=Name(id='len', ctx=Load()),
                                       args=[
                                          Name(id='changed_value', ctx=Load())],
                                       keywords=[]),
                                    ops=[
                                       Gt()],
                                    comparators=[
                                       Constant(value=0)]),
                                 body=[
                                    Assign(
                                       targets=[
                                          Name(id='grounded_name', ctx=Store())],
                                       value=Subscript(
                                          value=Name(id='changed_id', ctx=Load()),
                                          slice=Constant(value='index'),
                                          ctx=Load())),
                                    Expr(
                                       value=Call(
                                          func=Name(id='print', ctx=Load()),
                                          args=[
                                             Constant(value='Grounded name: '),
                                             Name(id='grounded_name', ctx=Load())],
                                          keywords=[])),
                                    Assign(
                                       targets=[
                                          Name(id='grounded_value', ctx=Store())],
                                       value=Call(
                                          func=Name(id='convert_from_ui', ctx=Load()),
                                          args=[
                                             Name(id='changed_value', ctx=Load())],
                                          keywords=[])),
                                    Expr(
                                       value=Call(
                                          func=Name(id='print', ctx=Load()),
                                          args=[
                                             Constant(value='Grounded value: '),
                                             Name(id='grounded_value', ctx=Load())],
                                          keywords=[])),
                                    Assign(
                                       targets=[
                                          Tuple(
                                             elts=[
                                                Name(id='name', ctx=Store()),
                                                Name(id='arguments', ctx=Store())],
                                             ctx=Store())],
                                       value=Call(
                                          func=Name(id='unground', ctx=Load()),
                                          args=[
                                             Name(id='grounded_name', ctx=Load())],
                                          keywords=[])),
                                    Assign(
                                       targets=[
                                          Subscript(
                                             value=Attribute(
                                                value=Subscript(
                                                   value=Name(id='var_dict', ctx=Load()),
                                                   slice=Name(id='name', ctx=Load()),
                                                   ctx=Load()),
                                                attr='loc',
                                                ctx=Load()),
                                             slice=Tuple(
                                                elts=[
                                                   Starred(
                                                      value=Name(id='arguments', ctx=Load()),
                                                      ctx=Load())],
                                                ctx=Load()),
                                             ctx=Store())],
                                       value=Name(id='grounded_value', ctx=Load())),
                                    Expr(
                                       value=Call(
                                          func=Name(id='print', ctx=Load()),
                                          args=[
                                             Constant(value='Name: '),
                                             Name(id='name', ctx=Load())],
                                          keywords=[])),
                                    Expr(
                                       value=Call(
                                          func=Name(id='print', ctx=Load()),
                                          args=[
                                             Constant(value='Arguments: '),
                                             Name(id='arguments', ctx=Load())],
                                          keywords=[])),
                                    Assign(
                                       targets=[
                                          Name(id='changes', ctx=Store())],
                                       value=Dict(keys=[], values=[])),
                                    If(
                                       test=Compare(
                                          left=Name(id='grounded_value', ctx=Load()),
                                          ops=[
                                             Eq()],
                                          comparators=[
                                             Attribute(
                                                value=Name(id='EB', ctx=Load()),
                                                attr='TRUE',
                                                ctx=Load())]),
                                       body=[
                                          Expr(
                                             value=Call(
                                                func=Name(id='append_changes', ctx=Load()),
                                                args=[
                                                   Name(id='changes', ctx=Load()),
                                                   Dict(
                                                      keys=[
                                                         Name(id='name', ctx=Load())],
                                                      values=[
                                                         Call(
                                                            func=Name(id='Change', ctx=Load()),
                                                            args=[
                                                               Name(id='name', ctx=Load()),
                                                               List(
                                                                  elts=[
                                                                     Call(
                                                                        func=Name(id='tuple', ctx=Load()),
                                                                        args=[
                                                                           Name(id='arguments', ctx=Load())],
                                                                        keywords=[])],
                                                                  ctx=Load()),
                                                               List(elts=[], ctx=Load())],
                                                            keywords=[])])],
                                                keywords=[]))],
                                       orelse=[]),
                                    If(
                                       test=Compare(
                                          left=Name(id='grounded_value', ctx=Load()),
                                          ops=[
                                             Eq()],
                                          comparators=[
                                             Attribute(
                                                value=Name(id='EB', ctx=Load()),
                                                attr='FALSE',
                                                ctx=Load())]),
                                       body=[
                                          Expr(
                                             value=Call(
                                                func=Name(id='append_changes', ctx=Load()),
                                                args=[
                                                   Name(id='changes', ctx=Load()),
                                                   Dict(
                                                      keys=[
                                                         Name(id='name', ctx=Load())],
                                                      values=[
                                                         Call(
                                                            func=Name(id='Change', ctx=Load()),
                                                            args=[
                                                               Name(id='name', ctx=Load()),
                                                               List(elts=[], ctx=Load()),
                                                               List(
                                                                  elts=[
                                                                     Call(
                                                                        func=Name(id='tuple', ctx=Load()),
                                                                        args=[
                                                                           Name(id='arguments', ctx=Load())],
                                                                        keywords=[])],
                                                                  ctx=Load())],
                                                            keywords=[])])],
                                                keywords=[]))],
                                       orelse=[]),
                                    If(
                                       test=Compare(
                                          left=Name(id='grounded_value', ctx=Load()),
                                          ops=[
                                             Eq()],
                                          comparators=[
                                             Attribute(
                                                value=Name(id='EB', ctx=Load()),
                                                attr='INCONSISTENT',
                                                ctx=Load())]),
                                       body=[
                                          Return(
                                             value=Tuple(
                                                elts=[
                                                   Name(id='checkbox_values', ctx=Load()),
                                                   ListComp(
                                                      elt=Call(
                                                         func=Name(id='convert_to_ui', ctx=Load()),
                                                         args=[
                                                            Subscript(
                                                               value=Name(id='structure', ctx=Load()),
                                                               slice=Name(id='v', ctx=Load()),
                                                               ctx=Load())],
                                                         keywords=[]),
                                                      generators=[
                                                         comprehension(
                                                            target=Name(id='v', ctx=Store()),
                                                            iter=Name(id='integer_variables', ctx=Load()),
                                                            ifs=[],
                                                            is_async=0)]),
                                                   List(
                                                      elts=[
                                                         Constant(value='Unauthorized change, please reset')],
                                                      ctx=Load())],
                                                ctx=Load()))],
                                       orelse=[]),
                                    Assign(
                                       targets=[
                                          Name(id='start', ctx=Store())],
                                       value=Call(
                                          func=Attribute(
                                             value=Name(id='time', ctx=Load()),
                                             attr='time',
                                             ctx=Load()),
                                          args=[],
                                          keywords=[])),
                                    Try(
                                       body=[
                                          Expr(
                                             value=Call(
                                                func=Name(id='propagate_full', ctx=Load()),
                                                args=[
                                                   Name(id='changes', ctx=Load())],
                                                keywords=[])),
                                          Assign(
                                             targets=[
                                                Name(id='end', ctx=Store())],
                                             value=Call(
                                                func=Attribute(
                                                   value=Name(id='time', ctx=Load()),
                                                   attr='time',
                                                   ctx=Load()),
                                                args=[],
                                                keywords=[])),
                                          Expr(
                                             value=Call(
                                                func=Name(id='print', ctx=Load()),
                                                args=[
                                                   Constant(value='Time taken: '),
                                                   BinOp(
                                                      left=Name(id='end', ctx=Load()),
                                                      op=Sub(),
                                                      right=Name(id='start', ctx=Load()))],
                                                keywords=[])),
                                          For(
                                             target=Name(id='var_name', ctx=Store()),
                                             iter=Call(
                                                func=Attribute(
                                                   value=Name(id='var_dict', ctx=Load()),
                                                   attr='keys',
                                                   ctx=Load()),
                                                args=[],
                                                keywords=[]),
                                             body=[
                                                Expr(
                                                   value=Call(
                                                      func=Attribute(
                                                         value=Name(id='structure', ctx=Load()),
                                                         attr='update',
                                                         ctx=Load()),
                                                      args=[
                                                         Call(
                                                            func=Name(id='get_grounded_variables_for_display', ctx=Load()),
                                                            args=[
                                                               Name(id='var_name', ctx=Load())],
                                                            keywords=[])],
                                                      keywords=[]))],
                                             orelse=[]),
                                          Return(
                                             value=Tuple(
                                                elts=[
                                                   ListComp(
                                                      elt=Call(
                                                         func=Name(id='convert_to_ui', ctx=Load()),
                                                         args=[
                                                            Subscript(
                                                               value=Name(id='structure', ctx=Load()),
                                                               slice=Name(id='v', ctx=Load()),
                                                               ctx=Load())],
                                                         keywords=[]),
                                                      generators=[
                                                         comprehension(
                                                            target=Name(id='v', ctx=Store()),
                                                            iter=Name(id='boolean_variables', ctx=Load()),
                                                            ifs=[],
                                                            is_async=0)]),
                                                   ListComp(
                                                      elt=Call(
                                                         func=Name(id='convert_to_ui', ctx=Load()),
                                                         args=[
                                                            Subscript(
                                                               value=Name(id='structure', ctx=Load()),
                                                               slice=Name(id='v', ctx=Load()),
                                                               ctx=Load())],
                                                         keywords=[]),
                                                      generators=[
                                                         comprehension(
                                                            target=Name(id='v', ctx=Store()),
                                                            iter=Name(id='integer_variables', ctx=Load()),
                                                            ifs=[],
                                                            is_async=0)]),
                                                   List(
                                                      elts=[
                                                         Constant(value='No inconsistencies detected yet')],
                                                      ctx=Load())],
                                                ctx=Load()))],
                                       handlers=[
                                          ExceptHandler(
                                             type=Name(id='Exception', ctx=Load()),
                                             name='e',
                                             body=[
                                                Expr(
                                                   value=Call(
                                                      func=Name(id='print', ctx=Load()),
                                                      args=[
                                                         Constant(value='Inconsistent!')],
                                                      keywords=[])),
                                                Expr(
                                                   value=Call(
                                                      func=Name(id='print', ctx=Load()),
                                                      args=[
                                                         Name(id='e', ctx=Load())],
                                                      keywords=[])),
                                                Return(
                                                   value=Tuple(
                                                      elts=[
                                                         Name(id='checkbox_values', ctx=Load()),
                                                         ListComp(
                                                            elt=Call(
                                                               func=Name(id='convert_to_ui', ctx=Load()),
                                                               args=[
                                                                  Subscript(
                                                                     value=Name(id='structure', ctx=Load()),
                                                                     slice=Name(id='v', ctx=Load()),
                                                                     ctx=Load())],
                                                               keywords=[]),
                                                            generators=[
                                                               comprehension(
                                                                  target=Name(id='v', ctx=Store()),
                                                                  iter=Name(id='integer_variables', ctx=Load()),
                                                                  ifs=[],
                                                                  is_async=0)]),
                                                         List(
                                                            elts=[
                                                               Name(id='e', ctx=Load())],
                                                            ctx=Load())],
                                                      ctx=Load()))])],
                                       orelse=[],
                                       finalbody=[])],
                                 orelse=[])],
                           orelse=[]),
                        If(
                           test=Compare(
                              left=Subscript(
                                 value=Name(id='changed_id', ctx=Load()),
                                 slice=Constant(value='type'),
                                 ctx=Load()),
                              ops=[
                                 Eq()],
                              comparators=[
                                 Constant(value='dropdown')]),
                           body=[
                              If(
                                 test=Compare(
                                    left=Name(id='changed_value', ctx=Load()),
                                    ops=[
                                       NotEq()],
                                    comparators=[
                                       Constant(value=None)]),
                                 body=[
                                    Assign(
                                       targets=[
                                          Name(id='changes', ctx=Store())],
                                       value=Dict(
                                          keys=[
                                             Subscript(
                                                value=Name(id='changed_id', ctx=Load()),
                                                slice=Constant(value='index'),
                                                ctx=Load())],
                                          values=[
                                             Set(
                                                elts=[
                                                   Name(id='changed_value', ctx=Load())])])),
                                    Assign(
                                       targets=[
                                          Name(id='unsat_fields', ctx=Store())],
                                       value=Call(
                                          func=Name(id='propagate_full', ctx=Load()),
                                          args=[
                                             Name(id='changes', ctx=Load())],
                                          keywords=[])),
                                    If(
                                       test=Compare(
                                          left=Call(
                                             func=Name(id='len', ctx=Load()),
                                             args=[
                                                Name(id='unsat_fields', ctx=Load())],
                                             keywords=[]),
                                          ops=[
                                             Eq()],
                                          comparators=[
                                             Constant(value=0)]),
                                       body=[
                                          Return(
                                             value=Tuple(
                                                elts=[
                                                   ListComp(
                                                      elt=Call(
                                                         func=Name(id='convert_to_ui', ctx=Load()),
                                                         args=[
                                                            Subscript(
                                                               value=Name(id='structure', ctx=Load()),
                                                               slice=Name(id='v', ctx=Load()),
                                                               ctx=Load())],
                                                         keywords=[]),
                                                      generators=[
                                                         comprehension(
                                                            target=Name(id='v', ctx=Store()),
                                                            iter=Name(id='boolean_variables', ctx=Load()),
                                                            ifs=[],
                                                            is_async=0)]),
                                                   ListComp(
                                                      elt=Call(
                                                         func=Name(id='convert_to_ui', ctx=Load()),
                                                         args=[
                                                            Subscript(
                                                               value=Name(id='structure', ctx=Load()),
                                                               slice=Name(id='v', ctx=Load()),
                                                               ctx=Load())],
                                                         keywords=[]),
                                                      generators=[
                                                         comprehension(
                                                            target=Name(id='v', ctx=Store()),
                                                            iter=Name(id='integer_variables', ctx=Load()),
                                                            ifs=[],
                                                            is_async=0)]),
                                                   List(
                                                      elts=[
                                                         Constant(value='No inconsistencies detected yet')],
                                                      ctx=Load())],
                                                ctx=Load()))],
                                       orelse=[
                                          Return(
                                             value=Tuple(
                                                elts=[
                                                   Name(id='checkbox_values', ctx=Load()),
                                                   ListComp(
                                                      elt=Call(
                                                         func=Name(id='convert_to_ui', ctx=Load()),
                                                         args=[
                                                            Subscript(
                                                               value=Name(id='structure', ctx=Load()),
                                                               slice=Name(id='v', ctx=Load()),
                                                               ctx=Load())],
                                                         keywords=[]),
                                                      generators=[
                                                         comprehension(
                                                            target=Name(id='v', ctx=Store()),
                                                            iter=Name(id='integer_variables', ctx=Load()),
                                                            ifs=[],
                                                            is_async=0)]),
                                                   List(elts=[], ctx=Load())],
                                                ctx=Load()))])],
                                 orelse=[])],
                           orelse=[])],
                     orelse=[]),
                  Return(
                     value=Tuple(
                        elts=[
                           Name(id='checkbox_values', ctx=Load()),
                           ListComp(
                              elt=Call(
                                 func=Name(id='convert_to_ui', ctx=Load()),
                                 args=[
                                    Subscript(
                                       value=Name(id='structure', ctx=Load()),
                                       slice=Name(id='v', ctx=Load()),
                                       ctx=Load())],
                                 keywords=[]),
                              generators=[
                                 comprehension(
                                    target=Name(id='v', ctx=Store()),
                                    iter=Name(id='integer_variables', ctx=Load()),
                                    ifs=[],
                                    is_async=0)]),
                           List(
                              elts=[
                                 Constant(value='No inconsistencies detected yet')],
                              ctx=Load())],
                        ctx=Load()))],
               decorator_list=[
                  Call(
                     func=Attribute(
                        value=Name(id='app', ctx=Load()),
                        attr='callback',
                        ctx=Load()),
                     args=[
                        List(
                           elts=[
                              Call(
                                 func=Name(id='Output', ctx=Load()),
                                 args=[
                                    Dict(
                                       keys=[
                                          Constant(value='type'),
                                          Constant(value='index')],
                                       values=[
                                          Constant(value='checkboxes'),
                                          Name(id='ALL', ctx=Load())]),
                                    Constant(value='value')],
                                 keywords=[]),
                              Call(
                                 func=Name(id='Output', ctx=Load()),
                                 args=[
                                    Dict(
                                       keys=[
                                          Constant(value='type'),
                                          Constant(value='index')],
                                       values=[
                                          Constant(value='dropdown'),
                                          Name(id='ALL', ctx=Load())]),
                                    Constant(value='options')],
                                 keywords=[]),
                              Call(
                                 func=Name(id='Output', ctx=Load()),
                                 args=[
                                    Dict(
                                       keys=[
                                          Constant(value='type')],
                                       values=[
                                          Constant(value='text-output')]),
                                    Constant(value='children')],
                                 keywords=[])],
                           ctx=Load()),
                        List(
                           elts=[
                              Call(
                                 func=Name(id='Input', ctx=Load()),
                                 args=[
                                    Dict(
                                       keys=[
                                          Constant(value='type'),
                                          Constant(value='index')],
                                       values=[
                                          Constant(value='checkboxes'),
                                          Name(id='ALL', ctx=Load())]),
                                    Constant(value='value')],
                                 keywords=[]),
                              Call(
                                 func=Name(id='Input', ctx=Load()),
                                 args=[
                                    Dict(
                                       keys=[
                                          Constant(value='type'),
                                          Constant(value='index')],
                                       values=[
                                          Constant(value='dropdown'),
                                          Name(id='ALL', ctx=Load())]),
                                    Constant(value='value')],
                                 keywords=[]),
                              Call(
                                 func=Name(id='Input', ctx=Load()),
                                 args=[
                                    Constant(value='reset-button'),
                                    Constant(value='n_clicks')],
                                 keywords=[])],
                           ctx=Load()),
                        List(
                           elts=[
                              Call(
                                 func=Name(id='State', ctx=Load()),
                                 args=[
                                    Dict(
                                       keys=[
                                          Constant(value='type'),
                                          Constant(value='index')],
                                       values=[
                                          Constant(value='checkboxes'),
                                          Name(id='ALL', ctx=Load())]),
                                    Constant(value='id')],
                                 keywords=[]),
                              Call(
                                 func=Name(id='State', ctx=Load()),
                                 args=[
                                    Dict(
                                       keys=[
                                          Constant(value='type'),
                                          Constant(value='index')],
                                       values=[
                                          Constant(value='dropdown'),
                                          Name(id='ALL', ctx=Load())]),
                                    Constant(value='id')],
                                 keywords=[])],
                           ctx=Load())],
                     keywords=[])]),
            Expr(
               value=Call(
                  func=Attribute(
                     value=Name(id='app', ctx=Load()),
                     attr='run_server',
                     ctx=Load()),
                  args=[],
                  keywords=[
                     keyword(
                        arg='debug',
                        value=Constant(value=True))]))],
         decorator_list=[]),
      If(
         test=Compare(
            left=Name(id='__name__', ctx=Load()),
            ops=[
               Eq()],
            comparators=[
               Constant(value='__main__')]),
         body=[
            Expr(
               value=Call(
                  func=Name(id='launch_dash_app', ctx=Load()),
                  args=[],
                  keywords=[]))],
         orelse=[])],
   type_ignores=[])


# Hoofdfunctie: ontvangt alle ENF-regels, types, predikaten, functies, en predikaten die geïnterpreteerd worden in de structuur.
# Deze invoer komt van parsing_idpz3_xarray.py
# Met deze invoer worden alle onderdelen van het gegenereerde programma opgebouwd en samengevoegd tot een AST.
# Deze AST wordt dan met astunparse omgezet tot een uitvoerbaar bestand.

def generate(enf_rules, types, predicates, functions, interpreted_predicates, dash=False):
    # make data arrays: types, predicates, functions necessary + auxiliary var!

    grouped_propagators = group_propagators(enf_rules, functions)
    temp_data_arrays = construct_data_arrays(types, predicates, functions)
    true_list = determine_true_list(enf_rules)
    equality_domain, operator_set = get_domain_elements_tested_on_equality(enf_rules, types)
    imports = generate_imports()
    auxiliary_classes = generate_auxiliary_classes()
    data_arrays = generate_data_arrays(temp_data_arrays)
    data_arrays_extra = generate_data_arrays_extra()
    true_and_unknown_lists = generate_true_and_unknown_lists(true_list)
    data_arrays_extra_dash = generate_data_arrays_extra_dash()
    propagate_elem = generate_propagate_elem()
    propagate_fill = generate_propagate_fill()
    get_from_data_array = generate_get_from_data_array()
    inverse = generate_inverse()
    append_changes = generate_append_changes()
    get_from_data_array_wrap = generate_get_from_data_array_wrap()
    write_to_data_array = generate_write_to_data_array()
    handle_propagate_results = generate_handle_propagate_results()
    propagate_wrap = generate_propagate_wrap()
    propagate_fill_wrap = generate_propagate_fill_wrap()
    calculate_first_coordinate = generate_calculate_first_coordinate()
    calculate_next_coordinate = generate_calculate_next_coordinate()
    incremental_propagate = generate_incremental_propagate()
    incremental_propagate_wrap = generate_incremental_propagate_wrap()
    map_indices = generate_map_indices()
    is_valid_index = generate_is_valid_index()
    map_indices_wrap = generate_map_indices_wrap()
    add_dims = generate_add_dims()
    reduce_dims = generate_reduce_dims()
    specific_propagation = generate_specific_propagation()
    general_propagation = generate_general_propagation()
    add_all_function_outputs = generate_add_all_function_outputs()
    function_propagation = generate_function_propagation()
    propagate = generate_propagate(grouped_propagators)
    propagate_full = generate_propagate_full()
    fill_in_interpreted_domain = generate_fill_in_interpreted_domain()
    get_changes_for_comparison_operators = generate_get_changes_for_comparison_operators()
    initial_propagation = generate_initial_propagation(grouped_propagators, equality_domain, interpreted_predicates, operator_set)
    get_grounded_variable_name = generate_get_grounded_variable_name()
    get_grounded_variables_for_display = generate_get_grounded_variables_for_display()
    terminal_test = generate_terminal_test()
    dash_functionality = generate_dash_functionality()
    #prop_list = generate_propagate_rule_from_unsat_set(grouped_propagators['_X2'][0], '_X2', True)
    #spec_prop = generate_propagate_rule_from_specific_propagation(grouped_propagators['_X3'][0])
    #gen_prop = generate_propagate_rule_from_general_propagation(grouped_propagators[';p_C'][0])
    #module = Module(body=gen_prop.body)
    if dash:
        module = Module(body=imports.body + auxiliary_classes.body + data_arrays.body + data_arrays_extra_dash.body + true_and_unknown_lists.body + propagate_elem.body + propagate_fill.body + get_from_data_array.body + inverse.body + append_changes.body + get_from_data_array_wrap.body + write_to_data_array.body + handle_propagate_results.body +
                         propagate_wrap.body + propagate_fill_wrap.body + calculate_first_coordinate.body + calculate_next_coordinate.body + incremental_propagate.body + incremental_propagate_wrap.body + map_indices.body + is_valid_index.body + map_indices_wrap.body + add_dims.body + reduce_dims.body + specific_propagation.body +
                         general_propagation.body + add_all_function_outputs.body + function_propagation.body + propagate.body + propagate_full.body + fill_in_interpreted_domain.body + get_changes_for_comparison_operators.body + initial_propagation.body + get_grounded_variable_name.body + get_grounded_variables_for_display.body + dash_functionality.body)
    else:
        module = Module(body=imports.body + auxiliary_classes.body + data_arrays.body + data_arrays_extra.body + true_and_unknown_lists.body + propagate_elem.body + propagate_fill.body + get_from_data_array.body + inverse.body + append_changes.body + get_from_data_array_wrap.body + write_to_data_array.body + handle_propagate_results.body +
                         propagate_wrap.body + propagate_fill_wrap.body + calculate_first_coordinate.body + calculate_next_coordinate.body + incremental_propagate.body + incremental_propagate_wrap.body + map_indices.body + is_valid_index.body + map_indices_wrap.body + add_dims.body + reduce_dims.body + specific_propagation.body +
                         general_propagation.body + add_all_function_outputs.body + function_propagation.body + propagate.body + propagate_full.body + fill_in_interpreted_domain.body + get_changes_for_comparison_operators.body + initial_propagation.body + get_grounded_variable_name.body + get_grounded_variables_for_display.body + terminal_test.body)

    code = astunparse.unparse(module)

    with open("generated_code_final.py", "w") as file:
        file.write(code)


# !x: A(x) <=> !y: ~B(x,y): oké of niet?