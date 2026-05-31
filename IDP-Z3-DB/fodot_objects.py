"""
This file defines all fodot objects. A "fodot object" is each relevant FO(.)
concept.  Basically, you can think of it as all symbols and all formula
constructs.
"""

import z3
from tree_sitter import Node
from collections import defaultdict
import itertools
import re
import time


types = {}
symbols = {'prop': {}, 'cons': {}, 'pred': {}, 'func': {}}
symbol_interpretation = {}
subsymbol_interpretation = {}
var_interpretation = {}
variables = {}
z3_types = {}

symbols_to_apply = {}

timings = {'parse': 0, 'ground': 0, 'solve': 0}


class KB():
    def __init__(self):
        self.formulas = set()
        self._smt = None

    @property
    def smt(self):
        if self._smt is None:
            self._smt = self.to_ground_smt_lib()
        return self._smt

    def create_type_from_node(self, node: Node):
        # Create Type object.
        name = node.children[1].text.decode()
        decl = node.text.decode()
        print(name)
        print(decl)
        # Check if the type also contains an interpretation.
        # If yes, add the children.
        type_elements = []
        if len(node.children) > 2:
            interpretation = node.children[2]
            if interpretation.children[2].type == 'range_enumeration':
                # From "{0..10}", generate list of values.
                lb = int(interpretation.children[2].children[0].text.decode())
                rb = int(interpretation.children[2].children[2].text.decode())
                type_elements = [str(x) for x in list(range(lb, rb+1))]

            else:
                enumeration = interpretation.children[2]
                # Grab the enumeration from the AST.
                type_elements = [x.text.decode() for x in enumeration.children
                                 if x.type == 'type_element']
        types[name] = Type(name, enumeration=type_elements, decl=decl)

    def create_prop_from_node(self, node: Node):
        # Create Proposition object.
        name = node.children[0].text.decode()
        decl = node.text.decode()
        symbols['prop'][name] = Proposition(name, decl)

    def create_cons_from_node(self, node: Node):
        # Create Constant object.
        name = node.children[0].text.decode()
        decl = node.text.decode()
        rtype = node.children[3].text.decode()
        symbols['cons'][name] = Constant(name, decl, rtype)

    def create_func_from_node(self, node: Node):
        name = node.children[0].text.decode()
        args = []
        decl = node.text.decode()
        rtype = node.children[-1].text.decode()
        # Collect all args
        args.append(node.children[2].text.decode())
        for i in range(5, len(node.children), 2):
            args.append(node.children[i-1].text.decode())

        symbols['func'][name] = Function(name, args, rtype, decl)

    def create_pred_from_node(self, node: Node):
        name = node.children[0].text.decode()
        args = []
        decl = node.text.decode()
        # Collect all args
        args.append(node.children[2].text.decode())
        for i in range(5, len(node.children), 2):
            args.append(node.children[i-1].text.decode())

        symbols['pred'][name] = Predicate(name, args, decl)

    def apply_interpretation_from_node(self, node: Node):
        """
        Set the interpretation of a symbol (including type).
        """
        for i in range(1, len(node.children)-1, 3):
            # Iterate over (symbol, interpretation) pair
            symbol_name = node.children[i].text.decode()
            interpretation = node.children[i+1].children[2]

            # Find out which type of symbol it is, and format their enumeration
            # accordingly.
            if symbol_name in types:
                # TODO: support range {x..y}
                elements = [x.text.decode() for x in interpretation.children
                            if x.type == 'type_element']
                types[symbol_name].set_enum(elements)
                continue

            elif symbol_name in symbols['pred']:
                # If the arity == 1, the parser has collected a bunch of
                # type_elements.
                if symbols['pred'][symbol_name].arity == 1:
                    elements = [(x.text.decode(),) for x in
                                interpretation.children
                                if x.type == 'type_element']
                    symbol_interpretation[symbol_name] = elements
                    continue
                # If the arity > 1, we need to first gather all the argument
                # values.
                pos_sets = []
                for j in range(1, len(interpretation.children)-1, 4):
                    enum_node = interpretation.children[j]
                    elements = [x.text.decode() for x in
                                enum_node.children
                                if x.type == 'type_element']
                    pos_sets.append(tuple(elements))
                symbol_interpretation[symbol_name] = pos_sets
            elif symbol_name in symbols['func']:
                # First, find out if '(..)' are used. This will decide our step
                # size when looping over the element enumeration.
                # Below code seems needlessly complicated. That's because it
                # is, but I am writing this with a slight headache so it's only
                # fair you get one too. :-)
                if interpretation.children[0].type == '(':
                    step_size = 6
                    start = 1
                    out_offset = 3
                else:
                    step_size = 4
                    start = 0
                    out_offset = 2

                if (else_node := interpretation.next_sibling.next_sibling):
                    # We use a defaultdict in the case of an `else` in the
                    # interpretation. This ensures that any lookup for which
                    # the key has not explicitly been defined in the structure
                    # will result in the else value.
                    def def_val(value):
                        return lambda: value
                    else_val = else_node.next_sibling.text.decode()
                    pos_sets = defaultdict(def_val(else_val))
                else:
                    pos_sets = {}

                for j in range(start, len(interpretation.children), step_size):
                    enum_node = interpretation.children[j]
                    out_node = interpretation.children[j+out_offset]
                    elements = [x.text.decode() for x in
                                enum_node.children
                                if x.type == 'type_element']
                    out_elem = out_node.text.decode()
                    pos_sets[tuple(elements)] = out_elem
                symbol_interpretation[symbol_name] = pos_sets
            else:
                raise ValueError(f'Oops! Todo: interpretation for'
                                 f'{symbol_name}')


    def add_formula_from_node(self, node: Node):
        self.formulas.add(FOFormula.create_formula_from_node(node))

    def to_ground_smt_lib(self):
        smt = ''
        for typ in types.values():
            smt += typ.to_ground_smt_lib() + '\n'
        for symbol_type in ['prop', 'cons', 'pred', 'func']:
            for symbol in symbols[symbol_type].values():
                smt += symbol.to_ground_smt_lib() + '\n'
        for formula in self.formulas:
            smt_formula = formula.to_ground_smt_lib()
            if len(symbols_to_apply) == 0:
                smt += f'(assert {smt_formula})' + '\n'
            else:
                # We need to "apply" some symbols. Basically, this happens when
                # a formula contains nested symbols: we need to "expand" them.
                # E.g., the formula x(y()) would get translated to `x-y`.
                # Here, the `-y` needs to be applied to all of y's possible
                # values, and we add this formula to an implication. So, if y
                # has {1, 2} as possible values, we want the following:
                # ```
                # (and (implies (= y 1) (= x-1 true))
                #      (implies (= y 2) (= x-2 true))
                # ```
                # Not sure if this covers all possible cases though. Let's find
                # out!
                for apply_repl in list(symbols_to_apply.keys())[::-1]:
                    apply_symbol = symbols_to_apply[apply_repl]
                    if apply_symbol in symbols['cons']:
                        apply_type = types[symbols['cons'][apply_symbol].rtype]
                    else:
                        apply_type = types[symbols['func'][apply_symbol].rtype]
                    applied_formulas = []
                    for val in apply_type.enum:
                        applied_formula = re.sub(f'-{apply_repl}'+r'\b',
                                                 f'-{val}',
                                                 smt_formula)
                        impl = f'(implies (= {apply_repl} {val}) {applied_formula})'
                        applied_formulas.append(impl)
                    smt_formula = f'(and {" ".join(applied_formulas)})'
                smt += f'(assert {smt_formula})\n'
                symbols_to_apply.clear()
        return smt

    def generate_bools_for_func(self) -> str:
        """ Generate additional booleans representing functions

        Returns smt used to ensure propagation returns complete results.
        For each function on a finite domain, we iterate over its sets of
        arguments and do two things:
        * Introduce a new propostion `_p_func_arg1_[..]_argn`
        * an equivalence between that proposition and the function

        """
        smt = ''
        items = list(symbols['func'].items()) + list(symbols['cons'].items())
        for (name, func) in items:
        # for (name, func) in symbols['cons'].items():
            if func.rtype in ['Int', 'Real']:
                continue
            domains = [types[x].enum for x in func.args]
            domains += [types[func.rtype].enum]
            arg_sets = set(itertools.product(*domains))
            for arg_set in arg_sets:
                bool_name = f"_p_{name}_" + "_".join(arg_set)
                func_name = f"{name}-" + "-".join(arg_set[:-1])
                func_name = func_name.strip('-')  # In the case of constant
                smt += f"(declare-const {bool_name} Bool)\n"
                smt += (f"(assert (= {bool_name}"
                        f" (= {func_name} {arg_set[-1]})"
                        f"))\n")
                variables[bool_name] = z3.Bool(bool_name)
        return smt

    def model_expand(self, max_models=1):
        solver = z3.Solver()
        ground_time = time.time()
        smt = z3.parse_smt2_string(self.smt)
        timings['ground'] += time.time() - ground_time
        solver.add(smt)

        model_count = 1
        solve_time = time.time()
        while solver.check() == z3.sat:
            start = time.time()
            # Get the model.
            model = solver.model()

            neg_model = []
            output = {}
            for var_name, var in variables.items():
                name, *args = var_name.split('-')
                if name in symbol_interpretation:
                    # Don't print symbols interpreted in the structure.
                    continue
                var_val = model[var]

                # Negate the solution so we can find another one.
                neg_model.append(var != var_val)

                if name not in output:
                    output[name] = []

                # For pred: if true, add it to the output.
                if str(var_val) == 'True' and len(args) > 0:  # True Predicate.
                    output[name].append(f'({", ".join(args)})')
                elif str(var_val) == 'False' and len(args) > 0:  # False Pred
                    continue
                elif str(var_val) == 'True':  # True Proposition.
                    output[name].append('True')
                elif str(var_val) == 'False':  # False Proposition.
                    output[name].append('False')
                # For func: add result to output
                else:
                    output[name].append(f'({", ".join(args)}) -> {str(var_val)}')
            solver.add(z3.Or(neg_model))

            print(f'\nModel {model_count}')
            print('='*10)
            for var, values in output.items():
                if len(values) == 0:
                    # Irrelevant symbol.
                    continue
                elif values[0] in ['True', 'False']:  # Proposition
                    print(f'{var} := {values[0]}.')
                else:
                    print(f'{var} := {{{", ".join(values)}}}.')
            if model_count >= max_models:
                break
            model_count += 1
            print(f'{model_count}: {time.time()-start}')
        timings['solve'] += time.time() - solve_time

    def propagate(self, complete=True):
        start = time.time()
        solver = z3.Solver()
        complete = False
        ground_time = time.time()
        if complete:
            smt = z3.parse_smt2_string(self.smt +
                                       self.generate_bools_for_func())
        else:
            smt = z3.parse_smt2_string(self.smt)
        timings['ground'] += time.time() - ground_time
        solver.add(smt)

        unknown_var = [variables[x] for x in list(variables.keys())
                       if x.split('-')[0] not in symbol_interpretation]
        cons = solver.consequences([], unknown_var)
        if str(cons[0]) != 'sat':
            raise ValueError
        for con in cons[1]:
            symbol = str(con.children()[1])
            neg = False
            if 'Not' == symbol[0:3]:
                neg = True
                symbol = symbol[4:-1]

            if symbol.startswith('_p_'):
                args = symbol.split('_')
                symbol_name = args[2]
                value = args[-1]
                args = args[3:-1]
                symbol_ass = f"{symbol_name}({', '.join(args)}) = {value}"
            elif '==' in symbol:
                symbol, value = symbol.split(' == ')
                args = symbol.split('-')
                symbol_ass = f"{args[0]}({', '.join(args[1:])}) = {value}"
            else:
                args = symbol.split('-')
                symbol_ass = f"{args[0]}({', '.join(args[1:])})"
            print(f"{'Not ' if neg else ''}{symbol_ass}")
        timings['solve'] += time.time() - start



class FOSymbol():
    def __init__(self, name: str, decl: str = ''):
        self.name = name
        self.decl = decl
        self.enum = None

    def to_ground_smt_lib(self):
        raise Exception('TODO!')


class Type(FOSymbol):
    def __init__(self, name: str, decl: str, enumeration: list = []):
        super().__init__(name, decl)
        self.enum = enumeration
        self.is_int = all(x.isdigit() for x in self.enum)
        self.is_real = all(x.replace('.', '', 1).isdigit() for x in self.enum)

    def __str__(self):
        return f'Type {self.name}'

    def to_ground_smt_lib(self):
        # FO(.) types are translated to datatypes in SMT, not sorts.
        # Syntax: (declare-datatypes () ((NAME VAL1 VAL2 VAL3)))
        # Format (declare-datatypes () ((S A B C)))
        # If the type is a (range of) int or a real, we do not need to do this.
        # We also want to create a Z3 sort to use when creating new variables.
        data_type = z3.Datatype(self.name)
        if not (self.is_int or self.is_real):
            for x in self.enum:
                data_type.declare(x)
            z3_types[self.name] = data_type.create()
            return f'(declare-datatypes () (({self.name} {" ".join(self.enum)})))'
        else:
            z3_types[self.name] = z3.IntSort()
            return ''

    def set_enum(self, enumeration):
        self.enum = enumeration
        self.is_int = all(x.isdigit() for x in self.enum)
        self.is_real = all(x.replace('.', '', 1).isdigit() for x in self.enum)


class Predicate(FOSymbol):
    def __init__(self, name: str, args: str, decl: str):
        super().__init__(name, decl)
        self.args = args
        self.arity = len(args)

        self.__verify_args()

    def __verify_args(self):
        """
        Verify whether all arguments are of a known type.

        Returns None
        Raaises ValueError: if one of the arguments does not exist.
        """
        for arg in self.args:
            if arg not in types:
                raise ValueError(f'Undeclared type: "{arg}"')

    def to_ground_smt_lib(self):
        # In SMT, we represent a predicate as a function mapping on Bool.
        # We generate a boolean constant for each possible set of input
        # arguments.
        # Syntax: (declare-const NAME Bool)

        domains = [types[x].enum for x in self.args]
        arg_sets = set(itertools.product(*domains))
        declarations = []
        for arg_set in arg_sets:
            idx = '-'.join(arg_set)
            appl_name = f'{self.name}-{idx}'
            declarations.append(f'(declare-const {appl_name} Bool)')
            variables[appl_name] = z3.Bool(appl_name)

            # If we already know the symbol's interpretation,
            # assert the values. Else, do nothing
            if self.name not in symbol_interpretation:
                continue
            if arg_set in symbol_interpretation[self.name]:
                declarations.append(f'(assert {appl_name})')
            else:
                declarations.append(f'(assert (not {appl_name}))')

        return '\n'.join(declarations)


class Proposition(Predicate):
    def __init__(self, name: str, decl: str):
        super().__init__(name, [], decl)

    def to_ground_smt_lib(self):
        # In SMT, we represent a proposition as a Boolean constant.
        variables[self.name] = z3.Bool(self.name)
        return f'(declare-const {self.name} Bool)'


class Function(Predicate):
    def __init__(self, name: str, args: str, rtype: str, decl: str):
        super().__init__(name, args, decl)
        self.rtype = rtype

        self.__verify_rtype()

    def __verify_rtype(self):
        """
        Verify the rtype.

        Returns None
        Raises ValueError: if the rtype does not exist.
        """
        if self.rtype not in ['Int', 'Real'] and self.rtype not in types:
            raise ValueError(f'Undeclared type: "{self.rtype}"')

    def to_smt_lib(self):
        # Syntax: (declare-fun NAME (ARG1 .. ARGN) ARGM)
        func_declaration = f'(declare-fun {self.name} ({" ".join(self.args)}) {self.rtype})'

        if self.rtype in ['Int', 'Real']:
            return f'{func_declaration}'

        # In FO(.), functions have an inherent constraint: exactly one of the
        # output values must be true. So, for each possible set of inputs, we
        # create a disjunction for each possible output value.
        # We only need to do this if the function isn't already interpreted.
        # (We cannot do these if the rtype is Int or Real, for obvious reasons)
        func_constraint = '(assert (and '
        if self.arity == 0:
            #TODO
            raise Exception
        else:
            # Generate the set of possible input variables.
            input_domains = [types[x].enum for x in self.args]
            input_sets = set(itertools.product(*input_domains))
            output_domain = [x for x in types[self.rtype].enum]
            for input_set in input_sets:
                disjunction = ' (or '
                for output_val in output_domain:
                    disjunction += f'(= ({self.name} {" ".join(input_set)})'
                    disjunction += f' {output_val})'
                disjunction += ')\n'
                func_constraint += disjunction

            # Also assert its interpretation. Do not use `define_fun` because
            # this is not part of SMT-lib, but rather a Z3 construct.
            # `declare-fun` + `assert` is equivalent.
        func_constraint += '))'
        return f'{func_declaration}\n{func_constraint}'

    def to_ground_smt_lib(self):
        # For each possible set of input arguments, we need to generate a 0-ary
        # constant.
        # Syntax: (declare-fun NAME () ARGM)
        domains = [types[x].enum for x in self.args]
        arg_sets = set(itertools.product(*domains))
        declarations = []
        func_constraints = []
        assert_constraints = []
        for arg_set in arg_sets:
            idx = '-'.join(arg_set)
            appl_name = f'{self.name}-{idx}'

            # Function mapping on Int and Real are easy: add their declaration
            # to the list and their Z3 variable to the global variables.
            if self.rtype in ['Int', 'Real']:
                declarations.append(f'\n(declare-const {appl_name} {self.rtype})')

                if self.rtype == 'Int':
                    variables[appl_name] = z3.Const(appl_name, z3.IntSort())
                else:
                    variables[appl_name] = z3.Const(appl_name, z3.RealSort())
                continue

            # Functions mapping on user-defined types are a bit more tricky.
            # We first do the same as above by creating a declaration and
            # adding their Z3 variable to the global variables.
            # Then, we need to either set its interpreted value, or add the
            # function constraint.
            if types[self.rtype].is_int:
                rtype = 'Int'
            elif types[self.rtype].is_real:
                rtype = 'Real'
            else:
                rtype = self.rtype
            declarations.append(f'\n(declare-const {appl_name} {rtype})')

            variables[appl_name] = z3.Const(appl_name, z3_types[self.rtype])

            if self.rtype in ['Int', 'Real']:
                return f'{func_declaration}'

            # If the symbol is already interpreted, assert the correct values.
            # Otherwise, set the output constraints of the function.
            if self.name in symbol_interpretation:
                assert_constraints.append(f'(assert (= {appl_name} {symbol_interpretation[self.name][arg_set]}))\n')
            else:
                # In FO(.), functions have an inherent constraint: exactly
                # one of the output values must be true. So, for each
                # possible set of inputs, we create a disjunction for each
                # possible output value. We only need to do this if
                # the function isn't already interpreted.
                # (We cannot do these if the rtype is Int or Real,
                #  for obvious reasons)
                func_constraint = '\n(assert (or'
                output_domain = [x for x in types[self.rtype].enum]
                for output_val in output_domain:
                    func_constraint += f' (= {appl_name} {output_val})'
                func_constraint += '))'
                func_constraints.append(func_constraint)
        return f'{" ".join(declarations)}\n{"".join(func_constraints)}\n{"".join(assert_constraints)}'

class Constant(Function):
    def __init__(self, name: str, decl: str, rtype: str):
        super().__init__(name, [], rtype, decl)

    def to_ground_smt_lib(self):
        if self.rtype in ['Int', 'Real']:
            # Add a Z3 variable to the global list.
            if self.rtype == 'Int':
                variables[self.name] = z3.Const(self.name, z3.IntSort())
            else:
                variables[self.name] = z3.Const(self.name, z3.RealSort())

            return f'(declare-const {self.name} {self.rtype})'
        else:
            # If no built-in type was used, we need to also add the function
            # constraint.
            type_constraint = []
            if types[self.rtype].is_int or types[self.rtype].is_real:
                rtype = 'Int' if types[self.rtype].is_int else 'Real'
                declaration = f'(declare-const {self.name} {rtype})'

                if rtype == 'Int':
                    variables[self.name] = z3.Const(self.name, z3.IntSort())
                else:
                    variables[self.name] = z3.Const(self.name, z3.RealSort())
            else:
                declaration = f'(declare-const {self.name} {self.rtype})'
                variables[self.name] = z3.Const(self.name, z3_types[self.rtype])
            # In FO(.), constants that are subtypes of Int or Real need to be
            # limited to their type's values.
            type_constraints = []
            for val in types[self.rtype].enum:
                type_constraints.append(f'(= {self.name} {val})')
            type_assertion = f'(assert (or {" ".join(type_constraints)}))'

            return f'{declaration}\n{type_assertion}\n'

# TODO: build lots of verification (e.g., correct type? etc)


class FOFormula():
    def __init__(self, decl):
        self.decl = decl

    @staticmethod
    def create_formula_from_node(formula_node: Node):
        # Grab the specific node from the formula node.
        # Formula node typically only has one child, namely the Fodot-node.
        # It can sometimes also contain parentheses, which are ignore (see
        # below)
        try:
            node = formula_node.children[0]
        except:
            breakpoint()
        decl = node.text.decode()
        # TODO: do this with a hash table!!!
        if node.type == 'implication':
            # Create antecedent and precedent children.
            precedent = FOFormula.create_formula_from_node(node.children[0])
            antecedent = FOFormula.create_formula_from_node(node.children[2])
            return Implication(precedent, antecedent, decl)
        elif node.type == 'applied_symbol':
            symbol_name = node.children[0].text.decode()
            if len(node.children) == 3:
                args = []
            else:
                # Create a formula object for each argument node.
                # args = [FOFormula.create_formula_from_node(x)
                #         for x in node.children[2:]
                #         if x.type == 'symbol_name']
                # Above code only works if no functions/constants were used.
                # args = [FOFormula.create_formula_from_node(node.children[2])]
                args = [FOFormula.create_formula_from_node(x) for x in node.children
                        if x.type == 'formula']
            return AppliedSymbol(symbol_name, args, decl)
        elif node.type in ['inequality', 'le', 'ge', 'geq', 'leq',
                           'equality']:
            # TODO: re-order list in order of probability
            left_arg = FOFormula.create_formula_from_node(node.children[0])
            right_arg = FOFormula.create_formula_from_node(node.children[2])
            if node.type == 'inequality':
                comp_type = '~='
            elif node.type == 'le':
                comp_type = '<'
            elif node.type == 'ge':
                comp_type = '>'
            elif node.type == 'geq':
                comp_type = '>='
            elif node.type == 'leq':
                comp_type = '<='
            else:
                comp_type = '='
            return Comparison(comp_type, left_arg, right_arg, decl)
        elif node.type == 'land':
            left_arg = FOFormula.create_formula_from_node(node.children[0])
            right_arg = FOFormula.create_formula_from_node(node.children[2])
            return And(left_arg, right_arg, decl)
        elif node.type == 'lor':
            left_arg = FOFormula.create_formula_from_node(node.children[0])
            right_arg = FOFormula.create_formula_from_node(node.children[2])
            return Or(left_arg, right_arg, decl)
        elif node.type in ['sum', 'subtraction', 'multiplication',
                           'division']:
            left_arg = FOFormula.create_formula_from_node(node.children[0])
            right_arg = FOFormula.create_formula_from_node(node.children[2])
            if node.type == 'sum':
                math_type = '+'
            elif node.type == 'subtraction':
                math_type = '-'
            elif node.type == 'multiplication':
                math_type = '*'
            elif node.type == 'division':
                math_type = '/'
            return MathOp(math_type, left_arg, right_arg, decl)
        elif node.type == 'neg':
            arg = FOFormula.create_formula_from_node(node.children[1])
            return Negation(arg, decl)
        elif node.type in ['universal', 'existential']:
            # TODO: CLEAN UP THIS MESS BELOW >;(
            # If there is a single quantification, e.g.,
            # !x in Type: ...
            if len(node.children) == 4:
                quant = node.children[0].text.decode()
                quant_vars = [x.text.decode() for x in node.children[1].children if x.type=='variable']
                type_offset = len(quant_vars)*2
                quant_type = node.children[1].children[type_offset].text.decode()
                formula = FOFormula.create_formula_from_node(node.children[-1])
                if len(quant_vars) > 1:
                    for quant_var in quant_vars[1:]:
                        formula = Quantification(quant, quant_type, quant_var,
                                                 formula, decl)
                return Quantification(quant, quant_type, quant_vars[0], formula,
                                      decl)
            # If there are multiple quantifications, e.g.,
            # !x in Typ1, y in Typ2:
            else:
                # Create quantification objects for each quantification.
                # There's probably a better way to do this? But it works quite
                # well. :-)
                # First, make the formula that appears after the
                # quantification.
                formula = FOFormula.create_formula_from_node(node.children[-1])

                # Then, for each quantification after the first one, create a
                # quantification formula
                for i in range(len(node.children)-3, 1, -2):
                    quant = node.children[0].text.decode()
                    quant_vars = [x.text.decode() for x in node.children[1].children if x.type=='variable']
                    quant_type = node.children[i].children[2].text.decode()
                    if len(quant_vars) > 1:
                        for quant_var in quant_vars[1:]:
                            formula = Quantification(quant, quant_type,
                                                     quant_var,
                                                     formula, decl)
                    formula = Quantification(quant, quant_type, quant_vars[0],
                                             formula, decl)
                # Finally, create the outer-most quantification.
                quant = node.children[0].text.decode()
                quant_vars = [x.text.decode() for x in node.children[1].children if x.type=='variable']
                quant_type = node.children[1].children[2].text.decode()
                if len(quant_vars) > 1:
                    for quant_var in quant_vars[1:]:
                        formula = Quantification(quant, quant_type,
                                                 quant_var, formula, decl)
                return Quantification(quant, quant_type, quant_vars[0], formula,
                                      decl)
        elif node.type == 'type_element':
            return Element(node.text.decode(), decl)

        elif node.type == 'equivalence':
            # This is a bit cheating: we create two implications, one in each
            # direction, and join them using a conjunction.
            # Should probably see if we can model this more elegantly.
            left_form = FOFormula.create_formula_from_node(node.children[0])
            right_form = FOFormula.create_formula_from_node(node.children[2])
            left_implication = Implication(left_form, right_form, decl)
            right_implication = Implication(right_form, left_form, decl)
            return And(left_implication, right_implication, '')
        elif node.type == 'in_operator':
            left_form = FOFormula.create_formula_from_node(node.children[0])
            elems = [Element(x.text.decode(), decl) for x in node.children
                     if x.type == 'type_element']
            formula = Comparison('=', left_form, elems[0], decl)
            for elem in elems[1:]:
                new_form = Comparison('=', left_form, elem, decl)
                formula = Or(formula, new_form, decl)
            return formula
        elif node.type == '(':
            return FOFormula.create_formula_from_node(formula_node.children[1])
        else:
            print(node)
            print(node.type)
            print(node.children)
            breakpoint()
            raise Exception(f'Cannot parse {node.type} yet')
        return 'lol'

    def to_ground_smt_lib(self):
        raise Exception('This should not have happened. Oops!')

    def interpreted(self):
        return False


class Implication(FOFormula):
    def __init__(self, precedent: FOFormula, antecedent: FOFormula, decl: str):
        super().__init__(decl)
        self.precedent = precedent
        self.antecedent = antecedent

    def __str__(self):
        return f'{self.precedent} => {self.antecedent}'

    def to_ground_smt_lib(self):
        # If the precedent is interpreted, we can can simplify the output.
        if self.precedent.interpreted():
            if self.precedent.evaluate_true():
                # Return the antecedent if the precedent is always True
                return (f'{self.antecedent.to_ground_smt_lib()}')
            else:
                # Return nothing if the antecedent is not satisfied.
                return ''
        return (f'(implies {self.precedent.to_ground_smt_lib()}'
                f' {self.antecedent.to_ground_smt_lib()})')


class AppliedSymbol(FOFormula):
    # TODO: cache the results of `are_args_interpreted`, `to_ground_smt_lib`,
    # ...
    # Same goes for the other classes which reuse these concepts!
    def __init__(self, symbol_name: str, args: list[str], decl):
        super().__init__(decl)
        self.symbol_name = symbol_name
        self.args = args
        self.arity = len(self.args)

    def __str__(self):
        return f'{self.symbol_name}({", ".join(self.args)})'

    def interpreted(self):
        return self.symbol_name in symbol_interpretation and self.are_args_interpreted()

    def evaluate_true(self):
        # This is only called when we know the symbol is interpreted -- we do
        # not need to check that again.
        arg_set = tuple(x.to_ground_smt_lib() for x in self.args)
        if arg_set in symbol_interpretation[self.symbol_name]:
            return True
        else:
            return False

    def are_args_interpreted(self):
        # TODO: there has to be a faster way to do this....
        # especially in quantification!
        for arg in self.args:
            if not arg.interpreted():
                return False
        return True

    def to_ground_smt_lib(self):
        if self.arity == 0:
            if self.interpreted():
                return symbol_interpretation[self.symbol_name]
            else:
                return f'{self.symbol_name}'
        elif (self.symbol_name in symbol_interpretation
              and self.are_args_interpreted()):
            # If the symbol is interpreted, return the interpretation instead.
            arg_set = tuple(x.to_ground_smt_lib() for x in self.args)

            if arg_set in symbol_interpretation[self.symbol_name]:
                try:
                    # If it's a function, return the value.
                    return symbol_interpretation[self.symbol_name][arg_set]
                except TypeError:
                    # if it's a predicate, return 'true'
                    return 'true'
            else:
                return 'false'
        else:
            # If all arguments are elements, make a naive translation.
            argstr = ""
            for arg in self.args:
                argstr += f"-{arg.to_ground_smt_lib()}"
            for x in self.args:
                if isinstance(x, AppliedSymbol):
                    symbols_to_apply[x.to_ground_smt_lib()] = x.symbol_name
            return f'{self.symbol_name}{argstr}'

class BinaryOp(FOFormula):
    def __init__(self, operator: str, left_arg: FOFormula,
                 right_arg: FOFormula, decl: str):
        super().__init__(decl)
        self.operator = operator
        self.left_arg = left_arg
        self.right_arg = right_arg

    def to_ground_smt_lib(self):
        left_smt = self.left_arg.to_ground_smt_lib()
        right_smt = self.right_arg.to_ground_smt_lib()
        if left_smt and right_smt:
            return (f'({self.operator} {self.left_arg.to_ground_smt_lib()}'
                    f' {self.right_arg.to_ground_smt_lib()})')
        else:
            # In case both args can be reduced, return nothering.
            return ''


class Comparison(BinaryOp):
    def __init__(self, comp_type: str, left_arg: FOFormula,
                 right_arg: FOFormula, decl: str):
        super().__init__(comp_type, left_arg, right_arg, decl)

        assert self.operator in ['=', '<', '>', '>=', '<=', '~=']

    def interpreted(self):
        # For now, only = and ~= can be interpreted for more than 1 level deep.
        if self.operator in ['=', '~=']:
            return (self.left_arg.interpreted() and
                    self.right_arg.interpreted())

        return (isinstance(self.left_arg, Element) and
                isinstance(self.right_arg, Element))

    def evaluate_true(self):
        if self.operator == '~=':
            return (self.left_arg.to_ground_smt_lib()
                    != self.right_arg.to_ground_smt_lib())
        elif self.operator == '=':
            return (self.left_arg.to_ground_smt_lib()
                    == self.right_arg.to_ground_smt_lib())
        raise Exception('Not implemented')

    def to_ground_smt_lib(self):
        if self.operator != '~=':
            return super().to_ground_smt_lib()
        else:
            # "~=" requires a special translation to SMT.
            return (f'(not (= {self.left_arg.to_ground_smt_lib()}'
                    f' {self.right_arg.to_ground_smt_lib()}))')

class Negation(FOFormula):
    def __init__(self, arg: FOFormula, decl: str):
        super().__init__(decl)
        self.arg = arg

    def to_ground_smt_lib(self):
        return f'(not {self.arg.to_ground_smt_lib()})'


class And(BinaryOp):
    def __init__(self, left_arg: FOFormula, right_arg: FOFormula, decl: str):
        super().__init__('and', left_arg, right_arg, decl)

    def to_smt_lib(self):
        # Check if the conjunction can be simplified. I.e., if either the left
        # or the right arg is interpreted as False, we can drop the conjunction
        # altogether. If an arg evaluates to True, we can drop that arg and
        # simply keep the other.
        if self.left_arg.interpreted():
            if self.left_arg.evaluate_true():
                # If the left arg already evaluates to true, we can just pass
                # the right arg.
                return self.right_arg.to_smt_lib()
            else:
                # If the left arg is false, the entire clause is false.
                return 'false'
        if self.right_arg.interpreted():
            if self.right_arg.evaluate_true():
                # If the right arg already evaluates to true, we can just pass
                # the left arg.
                return self.left_arg.to_smt_lib()
            else:
                # If the right arg is false, the entire clause is false.
                return 'false'
        # If neither are interpreted, generate standard binary op smt.
        return super().to_smt_lib()

    def to_ground_smt_lib(self):
        # Check if the conjunction can be simplified. I.e., if either the left
        # or the right arg is interpreted as False, we can drop the conjunction
        # altogether. If an arg evaluates to True, we can drop that arg and
        # simply keep the other.
        if self.left_arg.interpreted():
            if self.left_arg.evaluate_true():
                # If the left arg already evaluates to true, we can just pass
                # the right arg.
                return self.right_arg.to_ground_smt_lib()
            else:
                # If the left arg is false, the entire clause is false.
                return 'false'
        if self.right_arg.interpreted():
            if self.right_arg.evaluate_true():
                # If the right arg already evaluates to true, we can just pass
                # the left arg.
                return self.left_arg.to_ground_smt_lib()
            else:
                # If the right arg is false, the entire clause is false.
                return 'false'
        # If neither are interpreted, generate standard binary op smt.
        return super().to_ground_smt_lib()


class Or(BinaryOp):
    def __init__(self, left_arg: FOFormula, right_arg: FOFormula, decl: str):
        super().__init__('or', left_arg, right_arg, decl)


class MathOp(BinaryOp):
    def __init__(self, math_type: str, left_arg: FOFormula,
                 right_arg: FOFormula, decl: str):
        super().__init__(math_type, left_arg, right_arg, decl)

    def interpreted(self):
        return (self.left_arg.interpreted() and self.right_arg.interpreted())

    def to_ground_smt_lib(self):
        # When both arguments are already interpreted, we can pre-calculate the
        # value in some cases.
        if not self.interpreted():
            return super().to_ground_smt_lib()
        left_smt = self.left_arg.to_ground_smt_lib()
        right_smt = self.right_arg.to_ground_smt_lib()

        if left_smt.isdigit() and right_smt.isdigit():
            left_num = int(left_smt)
            right_num = int(right_smt)
        else:
            left_num = float(left_smt)
            right_num = float(right_smt)

        # TODO: check if this could result in weird errors with floats or
        # divisions
        if self.operator == '+':
            return str(left_num + right_num)
        elif self.operator == '-':
            return str(left_num - right_num)
        elif self.operator == '*':
            return str(left_num * right_num)
        elif self.operator == '/':
            return str(left_num / right_num)
        else:
            super().to_ground_smt_lib()


class Quantification(FOFormula):
    def __init__(self, quant: str, quant_type: str, quant_var: str,
                 formula: FOFormula, decl: str):
        super().__init__(decl)
        self.quant = quant
        self.quant_type = quant_type
        self.quant_var = quant_var
        self.formula = formula

    def to_ground_smt_lib(self):
        # We cannot use SMT-LIB's built-in quantifiers (e.g., forall), as this
        # only works with sorts whereas we use datatypes to represent our
        # types.
        # In other words: foreach only works over uninterpreted domains.
        # So, we """ground""" our quantifiers by writing them as the
        # conjunction/disjunction of their cartesion product.
        formulas = set()
        for val in types[self.quant_type].enum:
            var_interpretation[self.quant_var] = val
            formula = self.formula.to_ground_smt_lib()
            if formula:
                formulas.add(formula)

        if len(formulas) == 1:
            return f'{formulas.pop()}'
        elif len(formulas) == 0:
            return ''
        else:
            if self.quant == '!':
                return f'(and {" ".join(formulas)})'
            else:
                return f'(or {" ".join(formulas)})'

        # formula = self.formula.to_ground_smt_lib()

        # # Now expand the formula for each value of the type domain.
        # formulas = set()
        # quant_var = self.quant_vars[0]
        # for val in types[self.quant_type].enum:
        #     # formulas.add(formula.replace(f' {quant_var} ', f' {val}') + '\n')
        #     formulas.add(re.sub(r'\b' + quant_var + r'\b', f'{val}', formula))
        # conjunction = f'(and {" ".join(formulas)})'
        # return conjunction


class Element(FOFormula):
    def __init__(self, name: str, decl: str):
        super().__init__(decl)
        self.name = name

    def interpreted(self):
        # An element is always interpreted.
        return True

    def to_ground_smt_lib(self):
        if self.name in var_interpretation:
            # If our element is an interpreted variable, return the
            # interpretation. This is used to simplify formulas.
            return var_interpretation[self.name]
        return self.name

    def __str__(self):
        if self.name in var_interpretation:
            return var_interpretation[self.name]
        return self.name
