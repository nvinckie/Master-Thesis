import re
import z3
from tree_sitter import Node
from collections import defaultdict
import itertools
from z3 import Datatype
from database_manager import DB_Manager

types = {}
int_types = []
symbols = {'prop': {}, 'cons': {}, 'pred': {}, 'func': {}}
symbol_interpretation = {}
db_manager = DB_Manager()
timings = {'parse': 0, 'ground': 0, 'solve': 0}

class Query_KB():
    def __init__(self):
        self.formulas = set()
        self._smt = None
        self.queries_create_type = []
        self.queries_insert_type = []
        self.queries_create_func_and_pred = []

    # Generates queries for fully interpreted predicates
    def generate_predicate_enumeration_queries(self):
        enumeration_queries = []
        for predicate in symbols['pred']:
            if predicate in symbol_interpretation:
                enumeration_queries.append(f'ALTER TABLE {predicate} DROP COLUMN truth ')
                vals = symbol_interpretation[predicate]
                insert_queries = f'INSERT OR IGNORE INTO {predicate} VALUES {", ".join(f'{val}' for val in vals)}'
                if symbols['pred'][predicate].arity == 1: # small hack for unary predicates
                    insert_queries = insert_queries.replace(",)", ")")
                if len(vals) != 0:
                    enumeration_queries.append(insert_queries.replace("'", "\""))
                symbols['pred'][predicate].partial = False
        return enumeration_queries

    # Conjunctions are eliminated by adding their two arguments to the list of formulae
    def eliminate_conjunctions_from_formulas(self):
        to_add = set()
        to_remove = set()
        for formula in self.formulas:
            if isinstance(formula, And):
                to_remove.add(formula)
                to_add = to_add.union([formula.left_arg, formula.right_arg])
        self.formulas = self.formulas.difference(to_remove).union(to_add)

    # Facts listed in the theory, can influence the database of facts
    def generate_fact_queries(self):
        queries = []
        for formula in self.formulas:
            if not isinstance(formula, Quantification):
                # process function facts
                if isinstance(formula, Comparison) and formula.operator == "=":
                    # if positive: f(a)=b is true
                    if isinstance(formula.left_arg, Element) and isinstance(formula.right_arg, AppliedSymbol):
                        element = formula.left_arg
                        function_application = formula.right_arg
                    elif isinstance(formula.left_arg, AppliedSymbol) and isinstance(formula.right_arg, Element):
                        element = formula.right_arg
                        function_application = formula.left_arg
                    else:
                        element = None
                    if element is not None:
                        func = symbols['func'][function_application.symbol_name]
                        return_values = types[func.rtype].enum
                        query = f'INSERT INTO {function_application.symbol_name} VALUES '
                        return_values = [element.decl]
                        for el in return_values:
                            line = (
                                    '(' + ','.join(["'"+arg.decl+"'" for arg in function_application.args])
                                    + ',"' + el + "'")
                            if element.decl == el:
                                line += ',1),'
                            else:
                                line += ',0),'
                            query += '\n' + line
                        queries.append(query[:-1])
                        formula.has_been_used_in_fact_query = True
                if isinstance(formula, Comparison) and formula.operator == "~=":
                    # if negative: f(a)=b is false
                    if isinstance(formula.left_arg, Element) and isinstance(formula.right_arg, AppliedSymbol):
                        element = formula.left_arg
                        function_application = formula.right_arg
                    elif isinstance(formula.left_arg, AppliedSymbol) and isinstance(formula.right_arg, Element):
                        element = formula.right_arg
                        function_application = formula.left_arg
                    else:
                        element = None
                    if element is not None:
                        query = f'INSERT INTO {function_application.symbol_name} VALUES ('
                        query += ','.join(["'"+arg.decl+"'" for arg in function_application.args])
                        query += f",'{element.decl}',0)"
                        queries.append(query)
                        formula.has_been_used_in_fact_query = True

                # process predicate positive facts:
                elif isinstance(formula, AppliedSymbol):
                    pred = symbols['pred'][formula.symbol_name]
                    if pred.partial:
                        query = f'INSERT INTO {formula.symbol_name} VALUES ('
                        query += ','.join(["'"+arg.decl+"'" for arg in formula.args]) + ',1)'
                        queries.append(query)
                        formula.has_been_used_in_fact_query = True
                # process predicate negative facts:
                elif isinstance(formula, Negation) and isinstance(formula.arg, AppliedSymbol):
                    formula_neg = formula.arg
                    pred = symbols['pred'][formula_neg.symbol_name]
                    if pred.partial:
                        query = f'INSERT INTO {formula_neg.symbol_name} VALUES ('
                        query += ','.join(["'"+arg.decl+"'" for arg in formula_neg.args]) + ',0)'
                        queries.append(query)
                        formula.has_been_used_in_fact_query = True
        return queries

    # Generating quantified fact queries
    def generate_quantified_fact_queries(self):
        q_fact_queries = []
        for formula in self.formulas:
            if isinstance(formula, Quantification):
                queries = formula.ground(quantified_vars=None, fact_query=True)
                if queries:
                    q_fact_queries += queries
                    formula.has_been_used_in_fact_query = True
        return q_fact_queries

    # Main grounding function
    def to_ground_smt_lib(self):
        smt_string = ""
        # Declaring types
        for function_name in symbols['func']:
            function_declaration = f'(declare-fun {function_name} ('
            function = symbols['func'][function_name]
            function_declaration += ' '.join(function.args) + ')'
            return_type = function.rtype
            if return_type in int_types:
                return_type = 'Int'
            function_declaration += f' {return_type})\n'
            smt_string += function_declaration
        for pred_name in symbols['pred']:
            pred = symbols['pred'][pred_name]
            if pred.partial or db_manager.naive:
                pred_declaration = f'(declare-fun {pred_name} ('
                pred_declaration += ' '.join(pred.args) + ') Bool)\n'
                smt_string += pred_declaration
        for int_type in int_types:
            smt_string = smt_string.replace(int_type, 'Int')
        # Grounding formulas
        for formula in self.formulas:
            if not formula.has_been_used_in_fact_query:
                formula_grounding = formula.ground(None)
                smt_string += f'(assert {formula_grounding} )\n'
        if '(assert false' in smt_string:
            return smt_string
        # Grounding functions
        for function_name in symbols['func']:
            function_grounding = self.grounding_function(function_name)
            if function_grounding != "":
                smt_string += f'(assert {function_grounding} )\n'
        # Grounding partially interpreted predicates of which we know something
        for pred_name in symbols['pred']:
            if symbols['pred'][pred_name].partial:
                predicate_grounding = self.grounding_partial_predicate(pred_name)
                if predicate_grounding != "":
                    smt_string += f'(assert {predicate_grounding} )\n'
            elif db_manager.naive:
                predicate_grounding = self.grounding_fully_interpreted_predicate_naively(pred_name)
                smt_string += f'(assert {predicate_grounding} )\n'
        return smt_string

    def grounding_function(self, function_name):
        def args_val(res):
            string = ""
            for el in res[:-2]:
                string += el+" "
            return string[:-1],res[-2]
        query = f'SELECT * FROM {function_name}'
        results = db_manager.apply_query(query).fetchall()
        grounding_lines = []
        for result in results:
            args,val = args_val(result)
            if result[-1] == 1:
                grounding_lines += f' (= ({function_name} {args}) {val}) \n'
            else:
                grounding_lines += f' (not (= ({function_name} {args}) {val}))\n'
        if len(grounding_lines) == 0:
            return ""
        if len(grounding_lines) == 1:
            return grounding_lines[0]
        grounding_string = '(and \n'
        for line in grounding_lines:
            grounding_string += line
        return grounding_string + ')'

    def grounding_fully_interpreted_predicate_naively(self, pred_name):
        def args(res):
            string = ""
            for el in res:
                string += el+" "
            return string[:-1]
        query = f'SELECT * FROM {pred_name}'
        results = db_manager.apply_query(query).fetchall()
        grounding_lines = []
        for result in results:
            argss = args(result)
            grounding_lines += f' ({pred_name} {argss}) \n'
        grounding_string = '(and \n'
        for line in grounding_lines:
            grounding_string += line
        pred = symbols['pred'][pred_name]
        orig_col_names = ",".join([col for col in pred.args])
        query = f'SELECT * FROM ({orig_col_names}) WHERE ('
        for col_name in orig_col_names.split(","):
            query += col_name + ','
        query = query[:-1] + f') NOT IN (SELECT * FROM {pred_name})'
        grounding_lines = []
        results = db_manager.apply_query(query).fetchall()
        for result in results:
            argss = args(result)
            grounding_lines += f' (not ({pred_name} {argss})) \n'
        for line in grounding_lines:
            grounding_string += line
        return grounding_string + ')'

    def grounding_partial_predicate(self, pred_name):
        def args(res):
            string = ""
            for el in res[:-1]:
                string += el+" "
            return string[:-1]
        query = f'SELECT * FROM {pred_name}'
        results = db_manager.apply_query(query).fetchall()
        grounding_lines = []
        for result in results:
            argss = args(result)
            if result[-1] == 1:
                grounding_lines += f' ({pred_name} {argss}) \n'
            else:
                grounding_lines += f' (not ({pred_name} {argss}))\n'
        if len(grounding_lines) == 0:
            return ""
        if len(grounding_lines) == 1:
            return grounding_lines[0]
        grounding_string = '(and \n'
        for line in grounding_lines:
            grounding_string += line
        return grounding_string + ')'

    def smt(self):
        if self._smt is None:
            self._smt = self.to_ground_smt_lib()
        return self._smt

    # Solving
    def model_expand(self, max_nr_models=1):
        solver = z3.Solver()
        smt_string = self.smt()
        # Optimisation: if clearly sat/unsat, no need to build anything!
        if "assert false" in smt_string:
            print("UNSAT - no models available")
        elif "assert true" in smt_string and not "assert (" in smt_string:
            print("Theory trivially SAT")
        else:
            sorts = {}
            for typ in types:
                if typ not in int_types:
                    datatype = Datatype(typ)
                    for el in types[typ].enum:
                        datatype.declare(el)
                    z3datatype = datatype.create()
                    sorts[typ] = z3datatype
                    locals()[typ] = z3datatype

            formulas = z3.parse_smt2_string(smt_string, sorts=sorts)
            solver.add(formulas)
            satisfiable = solver.check()
            if satisfiable == z3.sat:
                print("SAT!")
            models = []
            nr_found = 0
            # Not implemented: finding more than one model
            while satisfiable == z3.sat and nr_found < max_nr_models:
                model = solver.model()
                models.append(model)
                nr_found += 1
            if nr_found > 0:
                for model in models:
                    print(model)
                    print("="*20)
            else:
                print("UNSAT - no models available")

    def create_type_from_node(self, node: Node):
        # Create Type object.
        name = node.children[1].text.decode()
        decl = node.text.decode()
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
                int_types.append(name)
            else:
                enumeration = interpretation.children[2]
                # Grab the enumeration from the AST.
                type_elements = [x.text.decode() for x in enumeration.children
                                 if x.type == 'type_element']
                type_elements.sort()
                if type_elements[0].isdigit():
                    int_types.append(name)
        types[name] = Type(name, enumeration=type_elements, decl=decl)
        queries = types[name].generate_query()
        self.queries_create_type.append(queries[0])
        if queries[1] != '':
            self.queries_insert_type.append(queries[1])

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
        self.queries_create_func_and_pred.append(symbols['func'][name].generate_query())

    def create_pred_from_node(self, node: Node):
        name = node.children[0].text.decode()
        args = []
        decl = node.text.decode()
        # Collect all args
        args.append(node.children[2].text.decode())
        for i in range(5, len(node.children), 2):
            args.append(node.children[i-1].text.decode())
        symbols['pred'][name] = Predicate(name, args, decl)
        self.queries_create_func_and_pred.append(symbols['pred'][name].generate_query())

    def apply_interpretation_from_node(self, node: Node):
        # Set the interpretation of a symbol (including type).
        for i in range(1, len(node.children)-1, 3):
            # Iterate over (symbol, interpretation) pair
            symbol_name = node.children[i].text.decode()
            if symbol_name in types or symbol_name in symbols['pred'] or symbol_name in symbols['func']:
                interpretation = node.children[i+1].children[2]
            # Find out which type of symbol it is, and format their enumeration accordingly.
            if symbol_name in types:
                elements = [x.text.decode() for x in interpretation.children
                            if x.type == 'type_element']
                types[symbol_name].set_enum(elements)
                if elements[0].isdigit():
                    int_types.append(symbol_name)
                queries = types[symbol_name].generate_query()
                self.queries_insert_type.append(queries[1])
                continue
            elif symbol_name in symbols['pred']:
                # If the arity == 1, the parser has collected a bunch of type_elements
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
                if interpretation.children[0].type == '(':
                    step_size = 6
                    start = 1
                    out_offset = 3
                else:
                    step_size = 4
                    start = 0
                    out_offset = 2
                if (else_node := interpretation.next_sibling.next_sibling):
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

    def add_formula_from_node(self, node: Node):
        self.formulas.add(FOFormula.create_formula_from_node(node))


class FOSymbol():
    def __init__(self, name: str, decl: str = ''):
        self.name = name
        self.decl = decl
        self.enum = None


class Type(FOSymbol):
    def __init__(self, name: str, decl: str, enumeration: list = []):
        super().__init__(name, decl)
        self.enum = enumeration
        self.is_int = all(x.isdigit() for x in self.enum)
        self.is_real = all(x.replace('.', '', 1).isdigit() for x in self.enum)

    def __str__(self):
        return f'Type {self.name}'

    # Query to create type and insert values
    def generate_query(self):
        create_query = f'CREATE TABLE "{self.name}" ("{self.name}"	TEXT, PRIMARY KEY("{self.name}"))'
        insert_query = ''
        if self.enum != []:
            insert_query = f'INSERT INTO {self.name} VALUES '
            for i in self.enum:
                insert_query += f"('{i}'),"
            insert_query = insert_query[:-1]
        return create_query, insert_query

    def set_enum(self, enumeration):
        self.enum = enumeration
        self.is_int = all(x.isdigit() for x in self.enum)
        self.is_real = all(x.replace('.', '', 1).isdigit() for x in self.enum)


class Predicate(FOSymbol):
    def __init__(self, name: str, args: str, decl: str):
        super().__init__(name, decl)
        self.args = args
        self.arity = len(args)
        self.map_mask_original = {}
        self.unique_column_names = self.generate_unique_names(args)
        self.partial = True
        self.__verify_args()

    # Sometimes, unique names (aliases) need to be created
    def generate_unique_names(self, list_of_columns):
        counts = {}
        for column in list_of_columns:
            if column not in counts:
                counts[column] = list_of_columns.count(column)
        indices_to_add = {}
        for column in list_of_columns:
            if counts[column] > 1:
                indices_to_add[column] = 1
        unique = []
        for column in list_of_columns:
            if counts[column] == 1:
                unique.append(column)
                self.map_mask_original[column] = column
            else:
                mask = f'{column}_{indices_to_add[column]}'
                self.map_mask_original[mask] = column
                unique.append(mask)
                indices_to_add[column] += 1
        return unique

    # Sometimes, we need the originals
    def original_column_types(self):
        lst = []
        for col in self.unique_column_names:
            lst.append(self.map_mask_original[col])
        return lst

    # Generate create table query for predicate
    def generate_query(self):
        create_query = f'CREATE TABLE "{self.name}" ('
        create_query += ", ".join([f'{column} TEXT' for column in self.unique_column_names])
        create_query += ", truth INTEGER, "
        create_query += f"PRIMARY KEY ({", ".join([f'{column} ' for column in self.unique_column_names])}), "
        create_query += ", ".join([f'FOREIGN KEY ("{column}") REFERENCES "{self.map_mask_original[column]}"("{self.map_mask_original[column]}")' for column in self.unique_column_names])+")"
        return create_query

    def __verify_args(self):
        # Verify whether all arguments are of a known type
        for arg in self.args:
            if arg not in types:
                raise ValueError(f'Undeclared type: "{arg}"')


# Not used, could probably be deleted
class Proposition(Predicate):
    def __init__(self, name: str, decl: str):
        super().__init__(name, [], decl)


class Function(Predicate):
    def __init__(self, name: str, args: str, rtype: str, decl: str):
        super().__init__(name, args, decl)
        self.rtype = rtype
        self.unique_args_and_rtype = self.generate_unique_names(args+[rtype])
        self.__verify_rtype()

    # Generate create table query for function
    def generate_query(self):
        create_query = f'CREATE TABLE "{self.name}" ('
        create_query += ", ".join([f'{column} TEXT ' for column in self.unique_args_and_rtype])
        create_query += ", truth INTEGER, "
        create_query += f"PRIMARY KEY ({", ".join([f'{column} ' for column in self.unique_args_and_rtype])}), "
        create_query += ", ".join([f'FOREIGN KEY ("{column}") REFERENCES "{self.map_mask_original[column]}"("{self.map_mask_original[column]}")' for column in self.unique_args_and_rtype])+")"
        return create_query

    def __verify_rtype(self):
        # Verify the rtype
        if self.rtype not in ['Int', 'Real'] and self.rtype not in types:
            raise ValueError(f'Undeclared type: "{self.rtype}"')


class Constant(Function):
    def __init__(self, name: str, decl: str, rtype: str):
        super().__init__(name, [], rtype, decl)


class FOFormula():
    def __init__(self, decl):
        self.decl = decl
        self.has_been_used_in_fact_query = False

    # Lots of the options have not been used (arithmetic etc.)
    @staticmethod
    def create_formula_from_node(formula_node: Node):
        # Grab the specific node from the formula node
        try:
            node = formula_node.children[0]
        except:
            breakpoint()
        decl = node.text.decode()
        if node.type == 'implication':
            # Create antecedent and precedent children.
            arrow = node.children[1].type
            precedent = FOFormula.create_formula_from_node(node.children[0])
            antecedent = FOFormula.create_formula_from_node(node.children[2])
            if arrow == '<=':
                return Implication(antecedent, precedent, decl)
            return Implication(precedent, antecedent, decl)
        elif node.type == 'applied_symbol':
            symbol_name = node.children[0].text.decode()
            if len(node.children) == 3:
                args = []
            else:
                # Create a formula object for each argument node
                args = [FOFormula.create_formula_from_node(x) for x in node.children
                        if x.type == 'formula']
            return AppliedSymbol(symbol_name, args, decl)
        elif node.type in ['inequality', 'le', 'ge', 'geq', 'leq',
                           'equality']:
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
            # If there is a single quantification, e.g. !x in Type: ...
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
            # If there are multiple quantifications, e.g. # !x in Typ1, y in Typ2:
            else:
                # Create quantification objects for each quantification
                formula = FOFormula.create_formula_from_node(node.children[-1])
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
            raise Exception(f'Cannot parse {node.type} yet')

    def ground(self, quantified_vars=None):
        raise Exception('Cannot ground top-level FOFormula, should have been implemented in subclass')

    def interpreted(self):
        return False


class Implication(FOFormula):
    def __init__(self, antecedent: FOFormula, consequent: FOFormula, decl: str):
        super().__init__(decl)
        self.antecedent = antecedent
        self.consequent = consequent

    def __str__(self):
        return f'{self.antecedent} => {self.consequent}'

    def ground(self, quantified_vars=None, consequent_tree=None):
        # "p=>q" not under scope of quantifier --> reduce to ~pvq
        if quantified_vars is None:
            return Or(Negation(self.antecedent, self.antecedent.decl), self.consequent, self.consequent.decl).ground(quantified_vars)
        # Assume that A=>B is universally quantified and A ranges only over fully interpreted predicates
        else:
            tree = quantified_vars.make_expression_tree(self.antecedent)
            query = quantified_vars.generate_materialisation_query(tree)
            res = db_manager.cursor_last_result_set.execute(query + " LIMIT 1")
            first = res.fetchone()
            if first is None:
                return None
            if consequent_tree is None:
                consequent_tree = quantified_vars.make_expression_tree(self.consequent)
            elif consequent_tree.op == 'false':
                return 'false'
            res = db_manager.cursor_last_result_set.execute(query)
            if db_manager.database_manager == "duckdb":
                res = res.df().itertuples(index=False)
            grounding = quantified_vars.generate_grounding("and", consequent_tree, res)
            return grounding


class AppliedSymbol(FOFormula):
    def __init__(self, symbol_name: str, args: list[str], decl):
        super().__init__(decl)
        self.symbol_name = symbol_name
        self.args = args
        self.arity = len(self.args)

    def __str__(self):
        args = [n.name for n in self.args]
        if self.arity == 1:
            return f'({self.symbol_name} {args[0]})'
        return f'({self.symbol_name} {" ".join(args)})'

    # Grounding by, in certain cases, consulting the db
    def ground(self, quantified_vars=None, function_negative_constant=None):
        # Not under the scope of quantifier(s)
        if quantified_vars is None:
            # Function
            if self.symbol_name in symbols['func']:
                func = symbols['func'][self.symbol_name]
                query = f'SELECT * FROM {self.symbol_name} WHERE'
                for i in range(func.arity):
                    query += f" {func.unique_args_and_rtype[i]}='{self.args[i]}' AND"
                query += " truth=1"
                res = db_manager.apply_query(query + " LIMIT 1").fetchone()
                if res is not None and res[-1] == 1:
                    return res[-2]
                if function_negative_constant is not None:
                    query = query[:-1] + f"0 AND {func.rtype}='{function_negative_constant}' LIMIT 1"
                    if not db_manager.apply_query_result_is_empty(query):
                        return 'false'
                return self.__str__()
            # Predicate not part of quantification
            if self.symbol_name in symbols['pred']:
                pred = symbols['pred'][self.symbol_name]
                query = f'SELECT * FROM {self.symbol_name} WHERE'
                for i in range(pred.arity):
                    query += f" {pred.unique_column_names[i]}='{self.args[i]}' AND"
                query = query[:-3] + " LIMIT 1"
                # If fully interpreted: check whether fact holds in db
                if not pred.partial:
                    if not db_manager.apply_query_result_is_empty(query):
                        return "true"
                    else:
                        return "false"
                # If partially interpreted: check whether it holds or not
                # and if not found, return the fact as a string
                else:
                    res = db_manager.apply_query(query).fetchone()
                    if res is not None:
                        if res[-1] == 0:
                            return 'false'
                        return 'true'
                    return self.__str__()
        # Now we know we're grounding a quantified formula
        # First, check if we're evaluating a materialised tuple
        if quantified_vars.dict_var_materialisation is not None:
            # Predicate
            if not db_manager.naive and self.symbol_name in symbols['pred']:
                pred = symbols['pred'][self.symbol_name]
                args = []
                for arg in self.args:
                    if arg.decl in quantified_vars.dict_var_materialisation:
                        args += [quantified_vars.dict_var_materialisation[arg.decl]]
                    else:
                        args += [arg.decl]
                query = f'SELECT * FROM {self.symbol_name} WHERE'
                for i in range(pred.arity):
                    query += f" {pred.unique_column_names[i]}='{args[i]}' AND"
                # If fully interpreted: check whether fact holds in db
                query = query[:-3] + "LIMIT 1"
                if not pred.partial:
                    if not db_manager.apply_query_result_is_empty(query):
                        return "true"
                    return "false"
                # If partially interpreted: check whether it holds
                # If no value known, simply return the fact as a string
                else:
                    if db_manager.has_facts:
                        res = db_manager.apply_query(query).fetchone()
                        if res is not None:
                            if res[-1] == 0:
                                return 'false'
                        return 'true'
            # Function
            if not db_manager.naive and self.symbol_name in symbols['func']:
                func = symbols['func'][self.symbol_name]
                args = []
                for arg in self.args:
                    if arg.decl in quantified_vars.dict_var_materialisation:
                        args += [quantified_vars.dict_var_materialisation[arg.decl]]
                    else:
                        args += [arg.decl]
                query = f'SELECT * FROM {self.symbol_name} WHERE'
                for i in range(func.arity):
                    query += f" {func.unique_args_and_rtype[i]}='{args[i]}' AND"
                query += ' truth=1'
                if db_manager.has_facts:
                    res = db_manager.apply_query(query + " LIMIT 1").fetchone()
                    if res is not None:
                        return res[-2]
                if db_manager.has_facts and function_negative_constant is not None:
                    r_type_uniqe = func.unique_args_and_rtype[-1]
                    query = query[:-1] + f"0 AND {r_type_uniqe}='{function_negative_constant}'  LIMIT 1"
                    if not db_manager.apply_query_result_is_empty(query):
                        return 'false'
            grounding_string = f'({self.symbol_name} '
            for arg in self.args:
                if arg.decl in quantified_vars.dict_var_materialisation:
                    grounding_string += f'{quantified_vars.dict_var_materialisation[arg.decl]} '
                else:
                    grounding_string += f'{arg.decl} '
            return grounding_string[:-1]+')'
        # If not materialised, a small hack: return query rather than grounding, this is used
        # to generate a query to find a SAT-set of a formula with only fully interpreted formulas
        elif self.symbol_name in symbols['pred'] and not symbols['pred'][self.symbol_name].partial:
            query = '('
            pred = symbols['pred'][self.symbol_name]
            unique_names = quantified_vars.generate_unique_type_names()
            type_names = quantified_vars.dict_var_type
            query_elements = []
            constant_conditions = {}
            for i in range(pred.arity):
                symbol = self.args[i].name
                if symbol in type_names:
                    query += f'{unique_names[symbol]}.{type_names[symbol]},'
                    query_elements.append(pred.unique_column_names[i])
                else:
                    constant_conditions[pred.unique_column_names[i]] = symbol
            query = query[:-1] + ') IN (SELECT '
            for query_element in query_elements:
                query += f'{self.symbol_name}.{query_element}, '
            query = query[:-2] + ' FROM ' + self.symbol_name
            if constant_conditions == {}:
                query += ')'
                return query
            else:
                query += ' WHERE '
                for cond in constant_conditions:
                    query += f"{cond}='{constant_conditions[cond]}' AND "
                return query[:-4] + ')'


class BinaryOp(FOFormula):
    def __init__(self, operator: str, left_arg: FOFormula,
                 right_arg: FOFormula, decl: str):
        super().__init__(decl)
        self.operator = operator
        self.left_arg = left_arg
        self.right_arg = right_arg


class Comparison(BinaryOp):
    def __init__(self, comp_type: str, left_arg: FOFormula,
                 right_arg: FOFormula, decl: str):
        super().__init__(comp_type, left_arg, right_arg, decl)
        assert self.operator in ['=', '<', '>', '>=', '<=', '~=']

    def ground(self, quantified_vars=None):
        if self.operator == '~=':
            to_negate = Comparison('=',self.left_arg,self.right_arg,self.decl)
            return Negation(to_negate,f'(not {self.decl})').ground(quantified_vars)
        if isinstance(self.left_arg, AppliedSymbol) and isinstance(self.right_arg, Element):
            if self.left_arg.ground(quantified_vars, function_negative_constant=self.right_arg) == 'false':
                return 'false'
        larg = self.left_arg.ground(quantified_vars)
        rarg = self.right_arg.ground(quantified_vars)
        if larg == rarg:
            return 'true'
        # small hack to avoid e.g. (= b1 b2) but allow (= f(a1) b1)
        if '(' not in larg and '(' not in rarg and larg != rarg:
            return 'false'
        return f'(= {larg} {rarg})'


class Negation(FOFormula):
    def __init__(self, arg: FOFormula, decl: str):
        super().__init__(decl)
        self.arg = arg

    def ground(self, quantified_vars=None):
        argument = self.arg.ground(quantified_vars)
        if argument == 'true':
            return 'false'
        if argument == 'false':
            return 'true'
        return f'(not {argument})'


class And(BinaryOp):
    def __init__(self, left_arg: FOFormula, right_arg: FOFormula, decl: str):
        super().__init__('and', left_arg, right_arg, decl)

    def ground(self, quantified_vars=None, consequent_tree=None):
        if quantified_vars is None:
            larg = self.left_arg.ground(quantified_vars)
            if larg == 'false':
                return 'false'
            rarg = self.right_arg.ground(quantified_vars)
            if rarg == 'false':
                return 'false'
            if larg == 'true' and rarg == 'true':
                return 'true'
            if larg == 'true':
                return rarg
            if rarg == 'true':
                return larg
            return f'(and {larg} {rarg})'
        #Assume that A&B is existentially quantified and A ranges only over non-partial predicates
        else:
            tree = quantified_vars.make_expression_tree(self.left_arg)
            query = quantified_vars.generate_materialisation_query(tree)
            res = db_manager.cursor_last_result_set.execute(query + " LIMIT 1")
            first = res.fetchone()
            if first is None:
                return None
            elif consequent_tree.op == 'true':
                return 'true'
            if consequent_tree is None:
                consequent_tree = quantified_vars.make_expression_tree(self.right_arg)
            res = db_manager.cursor_last_result_set.execute(query)
            if db_manager.database_manager == "duckdb":
                res = res.df().itertuples(index=False)
            grounding = quantified_vars.generate_grounding("or", consequent_tree, res)
            return grounding


class Or(BinaryOp):
    def __init__(self, left_arg: FOFormula, right_arg: FOFormula, decl: str):
        super().__init__('or', left_arg, right_arg, decl)

    def ground(self, quantified_vars=None):
        larg = self.left_arg.ground(quantified_vars)
        if larg == 'true':
            return 'true'
        rarg = self.right_arg.ground(quantified_vars)
        if rarg == 'true':
            return 'true'
        if larg == 'false' and rarg == 'false':
            return 'false'
        if larg == 'false':
            return rarg
        if rarg == 'false':
            return larg
        return f'(or {larg} {rarg})'


# Not used, could probably be deleted
class MathOp(BinaryOp):
    def __init__(self, math_type: str, left_arg: FOFormula,
                 right_arg: FOFormula, decl: str):
        super().__init__(math_type, left_arg, right_arg, decl)

    def interpreted(self):
        return (self.left_arg.interpreted() and self.right_arg.interpreted())


class Quantification(FOFormula):
    def __init__(self, quant: str, quant_type: str, quant_var: str,
                 formula: FOFormula, decl: str):
        super().__init__(decl)
        self.quant = quant
        self.quant_type = quant_type
        self.quant_var = quant_var
        self.formula = formula

    def ground(self, quantified_vars=None, fact_query=False):
        if quantified_vars is None:
            quantified_vars = Quantified_Vars(self.quant_var, self.quant_type, self.quant)
        else:
            quantified_vars.add(self.quant_var, self.quant_type, self.quant)
        # If the quantification goes further (e.g. !x !y), pass on the quantified_vars
        if isinstance(self.formula, Quantification):
            return self.formula.ground(quantified_vars, fact_query)

        # Ground function exploited to generate quantified fact queries
        if fact_query:
            if quantified_vars.only_universal():
                consequent = quantified_vars.make_expression_tree(self.formula)
                consequent_elements = consequent.yield_conjunction_elements_at_base_level()
                antecedent = ExpressionTree('true')
                if isinstance(self.formula, Implication) and not consequent.contains_only_fully_interpreted_predicates():
                    antecedent = quantified_vars.make_expression_tree(self.formula.antecedent)
                    consequent = quantified_vars.make_expression_tree(self.formula.consequent)
                    consequent_elements = consequent.yield_conjunction_elements_at_base_level()
                if antecedent.op == 'true' or antecedent.contains_only_fully_interpreted_predicates():
                    if consequent_elements:
                        query = quantified_vars.generate_materialisation_query(antecedent)
                        res = db_manager.apply_query(query).fetchall()
                        insert_queries = []
                        if len(res) == 0:
                            return ""
                        for consequent_element in consequent_elements:
                            symbol = ""
                            truth = "1"
                            constant = ""
                            if isinstance(consequent_element.op, AppliedSymbol):
                                symbol = consequent_element.op
                                thing = symbols['pred'][symbol.symbol_name]
                                columns = thing.unique_column_names
                            elif consequent_element.op == '~' and isinstance(consequent_element.children[0].op, AppliedSymbol):
                                symbol = consequent_element.children[0].op
                                truth = "0"
                                thing = symbols['pred'][symbol.symbol_name]
                                columns = thing.unique_column_names
                            elif consequent_element.op == '~':
                                symbol = consequent_element.children[0].children[0].op
                                truth = "0"
                                constant = consequent_element.children[0].children[1].op.decl
                                thing = symbols['func'][symbol.symbol_name]
                                columns = thing.unique_args_and_rtype
                            else:
                                symbol = consequent_element.children[0].op
                                constant = consequent_element.children[1].op.decl
                                thing = symbols['func'][symbol.symbol_name]
                                columns = thing.unique_args_and_rtype
                            insert_query = f'INSERT OR IGNORE INTO {symbol.symbol_name} ({','.join(columns)},truth) VALUES \n'
                            for tuple in res:
                                quantified_vars.materialise(tuple)
                                insert_query += '('
                                for arg in symbol.args:
                                    if arg.decl in quantified_vars.dict_var_materialisation:
                                        val = quantified_vars.dict_var_materialisation[arg.decl]
                                    else:
                                        val = arg.decl
                                    insert_query += f"'{val}',"
                                if constant != "":
                                    insert_query += f"'{constant}',"
                                insert_query += f'{truth}),\n'
                            insert_queries.append(insert_query[:-2])
                        return insert_queries
            return False

        # Grounding naively
        if db_manager.naive:
            tree = quantified_vars.make_expression_tree(self.formula)
            lists = []
            quantor_list = []
            for key in quantified_vars.dict_var_type:
                quantor_list.append(quantified_vars.dict_var_quant[key])
                query = f'SELECT * FROM {quantified_vars.dict_var_type[key]}'
                lst = [t[0] for t in db_manager.apply_query(query, False).fetchall()]
                lists.append(lst)
            def make_smt(lst, op):
                a = '(and '
                if op =='?':
                    a = '(or '
                for el in lst:
                    a += (el + " ")
                return a + ')'

            def expand_quantifiers(qs, domains, tree, env=None):
                if env is None:
                    env = []
                if not qs:
                    return quantified_vars.generate_grounding("doesntmatter", tree, [env])
                q = qs[0]
                dom = domains[0]
                subforms = [expand_quantifiers(qs[1:], domains[1:], tree, env + [v]) for v in dom]
                return make_smt(subforms, q)
            naive_grounding = expand_quantifiers(quantor_list, lists, tree)
            return naive_grounding

        # Below: the implementation for the 4 supported quantifier succession types
        if quantified_vars.only_universal():
            tree = quantified_vars.make_expression_tree(self.formula)
            preds = tree.fully_interpreted_predicates_mentioned()
            if preds == []:
                self.formula = Implication(Element('true','true'), self.formula, 'constructed')
            else:
                groundings = ['AND: ']
                to_ground = []
                for i in range(2**len(preds)):
                    bitstring = str(bin(i))[2:]
                    bitstring = "0"*(len(preds)-len(bitstring)) + bitstring
                    antecedent = make_antecedent_for_normal_form(preds, bitstring)
                    tree = quantified_vars.make_expression_tree(self.formula)
                    tree.make_consequent_for_normal_form(preds, bitstring)
                    tree.simplify()
                    if tree.op == 'false':
                        to_ground = [bitstring] + to_ground
                    elif tree.op != 'false' and tree.op != 'true':
                        to_ground = to_ground + [bitstring]
                for bitstring in to_ground:
                    bitstring = "0"*(len(preds)-len(bitstring)) + bitstring
                    antecedent = make_antecedent_for_normal_form(preds, bitstring)
                    tree = quantified_vars.make_expression_tree(self.formula)
                    tree.make_consequent_for_normal_form(preds, bitstring)
                    tree.simplify()
                    if tree.op == 'false':
                        formula = Implication(antecedent, Element('hack','hack'), 'constructed')
                        grounding = formula.ground(quantified_vars=quantified_vars, consequent_tree=tree)
                        if grounding is not None:
                            return 'false'
                    elif tree.op != 'false' and tree.op != 'true':
                        formula = Implication(antecedent, Element('hack','hack'), 'constructed')
                        grounding = formula.ground(quantified_vars=quantified_vars, consequent_tree=tree)
                        if grounding is not None:
                            groundings.append(grounding)
                if len(groundings) == 2:
                    return groundings[1]
                if len(groundings) == 1:
                    return "true"
                else:
                    string = "(and "
                    for gr in groundings[1:]:
                        if gr == 'false':
                            return 'false'
                        string += gr + '\n'
                    return string + ")"
            return self.formula.ground(quantified_vars)

        if quantified_vars.only_existential():
            tree = quantified_vars.make_expression_tree(self.formula)
            preds = tree.fully_interpreted_predicates_mentioned()
            if preds == []:
                self.formula = And(Element('true','true'), self.formula, 'constructed')
            else:
                groundings = ['OR: ']
                to_ground = []
                for i in range(2**len(preds)):
                    bitstring = str(bin(i))[2:]
                    bitstring = "0"*(len(preds)-len(bitstring)) + bitstring
                    antecedent = make_antecedent_for_normal_form(preds, bitstring)
                    tree = quantified_vars.make_expression_tree(self.formula)
                    tree.make_consequent_for_normal_form(preds, bitstring)
                    tree.simplify()
                    if tree.op == 'true':
                        to_ground = [bitstring] + to_ground
                    if tree.op != 'true' and tree.op != 'false':
                        to_ground += [bitstring]
                for bitstring in to_ground:
                    bitstring = "0"*(len(preds)-len(bitstring)) + bitstring
                    antecedent = make_antecedent_for_normal_form(preds, bitstring)
                    tree = quantified_vars.make_expression_tree(self.formula)
                    tree.make_consequent_for_normal_form(preds, bitstring)
                    tree.simplify()
                    if tree.op == 'true':
                        formula = And(antecedent, Element('hack','hack'), 'constructed')
                        grounding = formula.ground(quantified_vars=quantified_vars, consequent_tree=tree)
                        if grounding is not None:
                            return 'true'
                    if tree.op != 'true' and tree.op != 'false':
                        formula = And(antecedent, Element('hack','hack'), 'constructed')
                        grounding = formula.ground(quantified_vars=quantified_vars, consequent_tree=tree)
                        if grounding is not None:
                            groundings.append(grounding)
                if len(groundings) == 2:
                    return groundings[1]
                if len(groundings) == 1:
                    return "false"
                else:
                    string = "(or "
                    for gr in groundings[1:]:
                        if gr == 'true':
                            return 'true'
                        string += gr + '\n'
                    return string
            return self.formula.ground(quantified_vars)

        if quantified_vars.forall_exists():
            tree = quantified_vars.make_expression_tree(self.formula)
            preds = tree.fully_interpreted_predicates_mentioned()
            # Caution: if preds is empty, grounding should take place over full cartesian product
            # of the types involved (not been implemented)
            J_NT = []
            S_j_s = {}
            P_prime = {}
            S_top = []
            to_ground_triv = []
            to_ground_real = []
            for i in range(2**len(preds)):
                bitstring = str(bin(i))[2:]
                bitstring = "0"*(len(preds)-len(bitstring)) + bitstring
                tree = quantified_vars.make_expression_tree(self.formula)
                tree.make_consequent_for_normal_form(preds, bitstring)
                tree.simplify()
                if tree.op == 'true':
                    to_ground_triv += [bitstring]
                elif tree.op != 'false':
                    to_ground_real += [bitstring]
            for bitstring in to_ground_triv:
                tree = quantified_vars.make_expression_tree(self.formula)
                tree.make_consequent_for_normal_form(preds, bitstring)
                tree.simplify()
                antecedent = make_antecedent_for_normal_form(preds, bitstring)
                ant_tree = quantified_vars.make_expression_tree(antecedent)
                query = quantified_vars.generate_materialisation_query(ant_tree)
                res = db_manager.apply_query(query)
                if db_manager.database_manager == "duckdb":
                    res = res.df().itertuples(index=False)
                else:
                    res = res.fetchall()
                S_top += res
            X_types = list(quantified_vars.dict_var_type.values())[:quantified_vars.quantifiers_as_string().index('?')]
            X_enums = [types[t].enum for t in X_types]
            X = list(itertools.product(*X_enums))
            X_NT = []
            length = len(X[0])
            for x in X:
                x = x[:length]
                is_non_trivial = True
                for t in S_top:
                    if t[:length] == x:
                        is_non_trivial = False
                        break
                if is_non_trivial:
                    X_NT.append(x)
            if len(X_NT) == 0:
                return 'true'
            for bitstring in to_ground_real:
                tree = quantified_vars.make_expression_tree(self.formula)
                tree.make_consequent_for_normal_form(preds, bitstring)
                tree.simplify()
                antecedent = make_antecedent_for_normal_form(preds, bitstring)
                ant_tree = quantified_vars.make_expression_tree(antecedent)
                query = quantified_vars.generate_materialisation_query(ant_tree)
                res = db_manager.apply_query(query)
                if db_manager.database_manager == "duckdb":
                    res = res.fetchall()
                else:
                    res = res.fetchall()
                J_NT.append(bitstring)
                S_j_s[bitstring] = res
                P_prime[bitstring] = tree
            if len(J_NT) == 0:
                return 'false'
            grounding = ''
            if len(X_NT) > 1:
                grounding = '(and'
            for x in X_NT:
                conditions = []
                for j in J_NT:
                    tuples_we_want = []
                    for t in S_j_s[j]:
                        if t[:length] == x:
                            tuples_we_want.append(t)
                    conditions += [quantified_vars.generate_grounding('or', P_prime[j], tuples_we_want)]
                if len(conditions) == 0:
                    return 'false'
                if len(conditions) == 1:
                    if conditions[0] != 'true':
                        grounding += ' ' + conditions[0]
                else:
                    grounding += ' (or ' + ' '.join(conditions) + ')'
            if len(X_NT) > 1:
                grounding += ') '
            if grounding == '(and) ':
                return 'true'
            return grounding

        if quantified_vars.exists_forall():
            tree = quantified_vars.make_expression_tree(self.formula)
            preds = tree.fully_interpreted_predicates_mentioned()
            # Caution: if preds is empty, grounding should take place over full cartesian product
            # of the types involved (not been implemented)
            S_j_s = {}
            S_bottom = []
            T_Y = {}
            X_types = list(quantified_vars.dict_var_type.values())[:quantified_vars.quantifiers_as_string().index('!')]
            X_enums = [types[t].enum for t in X_types]
            X = list(itertools.product(*X_enums))
            Y_types = list(quantified_vars.dict_var_type.values())[quantified_vars.quantifiers_as_string().index('!'):]
            Y_enums = [types[t].enum for t in Y_types]
            Y = list(itertools.product(*Y_enums))
            X_NT = []
            length = len(X[0])
            to_ground_triv = []
            to_ground_real = []
            for i in range(2**len(preds)):
                bitstring = str(bin(i))[2:]
                bitstring = "0"*(len(preds)-len(bitstring)) + bitstring
                tree = quantified_vars.make_expression_tree(self.formula)
                tree.make_consequent_for_normal_form(preds, bitstring)
                tree.simplify()
                if tree.op == 'false':
                    to_ground_triv += [bitstring]
                elif tree.op == 'true':
                    to_ground_real += [bitstring]
            for bitstring in to_ground_triv:
                tree = quantified_vars.make_expression_tree(self.formula)
                tree.make_consequent_for_normal_form(preds, bitstring)
                tree.simplify()
                antecedent = make_antecedent_for_normal_form(preds, bitstring)
                ant_tree = quantified_vars.make_expression_tree(antecedent)
                query = quantified_vars.generate_materialisation_query(ant_tree)
                res = db_manager.apply_query(query)
                if db_manager.database_manager == "duckdb":
                    res = res.df().itertuples(index=False)
                else:
                    res = res.fetchall()
                S_bottom += res
            for x in X:
                x = x[:length]
                is_non_trivial = True
                for t in S_bottom:
                    if t[:length] == x:
                        is_non_trivial = False
                        break
                if is_non_trivial:
                    X_NT.append(x)
            if len(X_NT) == 0:
                return 'false'
            for bitstring in to_ground_real:
                antecedent = make_antecedent_for_normal_form(preds, bitstring)
                ant_tree = quantified_vars.make_expression_tree(antecedent)
                query = quantified_vars.generate_materialisation_query(ant_tree)
                res = db_manager.apply_query(query)
                if db_manager.database_manager == "duckdb":
                    res = res.fetchall()
                else:
                    res = res.fetchall()
                for tup in res:
                    x = tup[:length]
                    lst = T_Y.get(x, [])
                    T_Y[x] = lst + [tup[length:]]
            grounding = ''
            if len(X_NT) > 1:
                grounding = ' (or '
            tree = quantified_vars.make_expression_tree(self.formula)
            for x in X_NT:
                T_Y_x = T_Y.get(x,[])
                if len(T_Y_x) == len(Y):
                    return 'true'
                tuples_we_want = []
                for y in Y:
                    if y not in T_Y_x:
                        tuples_we_want.append(x+y)
                grounding += quantified_vars.generate_grounding('and', tree, tuples_we_want) + "\n"
            if len(X_NT) > 1:
                grounding += ') '
            return grounding

        else:
            raise Exception("unknown combination of quantifiers")


class Element(FOFormula):
    def __init__(self, name: str, decl: str):
        super().__init__(decl)
        self.name = name

    def __str__(self):
        return self.name

    def ground(self, quantified_vars=None):
        return self.name


class Quantified_Vars():
    def __init__(self, var, its_type, its_quant):
        self.dict_var_type = {var: its_type} # linking variables to their type
        self.dict_var_quant = {var: its_quant} # linking variables to their quantifier
        self.dict_var_materialisation = None

    def add(self, var, its_type, its_quant):
        self.dict_var_type[var] = its_type
        self.dict_var_quant[var] = its_quant

    def generate_unique_type_names(self):
        type_list = list(self.dict_var_type.values())
        counts = {}
        for t in type_list:
            if t not in counts:
                counts[t] = type_list.count(t)
        indices_to_add = {}
        for t in type_list:
            if counts[t] > 1:
                indices_to_add[t] = 1
        unique = {}
        for var in self.dict_var_type:
            if counts[self.dict_var_type[var]] == 1:
                unique[var] = self.dict_var_type[var]
            else:
                mask = f'{self.dict_var_type[var]}_{indices_to_add[self.dict_var_type[var]]}'
                indices_to_add[self.dict_var_type[var]] += 1
                unique[var] = mask
        return unique

    def only_universal(self):
        return not "?" in list(self.dict_var_quant.values())
    def only_existential(self):
        return not "!" in list(self.dict_var_quant.values())
    def quantifiers_as_string(self):
        return ''.join(list(self.dict_var_quant.values()))
    def forall_exists(self):
        pattern = re.compile(r'^!+\?+$')
        return bool(pattern.match(self.quantifiers_as_string()))
    def exists_forall(self):
        pattern = re.compile(r'^\?+!+$')
        return bool(pattern.match(self.quantifiers_as_string()))

    # Caution: could break if non-standard (orders of) quantified variables are used (I think)
    def materialise(self, tuple):
        self.dict_var_materialisation = {}
        i = 0
        for var in self.dict_var_type:
            self.dict_var_materialisation[var] = tuple[i]
            i+=1

    def make_expression_tree(self, formula,level=0):
        if isinstance(formula, And):
            tree = ExpressionTree("and", level=level)
            l_child = self.make_expression_tree(formula.left_arg,level+1)
            r_child = self.make_expression_tree(formula.right_arg,level+1)
            tree.children = [l_child,r_child]
            return tree
        if isinstance(formula, Or):
            tree = ExpressionTree("or",level=level)
            l_child = self.make_expression_tree(formula.left_arg,level+1)
            r_child = self.make_expression_tree(formula.right_arg,level+1)
            tree.children = [l_child,r_child]
            return tree
        if isinstance(formula, Negation):
            return ExpressionTree("~", [self.make_expression_tree(formula.arg,level+1)],level=level)
        if isinstance(formula, Implication):
            tree = ExpressionTree("or",level=level)
            l_child = self.make_expression_tree(Negation(formula.antecedent, formula.antecedent.decl),level+1)
            r_child = self.make_expression_tree(formula.consequent,level+1)
            tree.children = [l_child,r_child]
            return tree
        if isinstance(formula, Comparison) and formula.operator == '~=':
            positive = Comparison('=', formula.left_arg, formula.right_arg, formula.decl)
            return ExpressionTree('~', children=[self.make_expression_tree(positive,level=level+1)],level=level)
        if isinstance(formula, Comparison) and formula.operator == '=':
            l_child = self.make_expression_tree(formula.left_arg,level=level+1)
            r_child = self.make_expression_tree(formula.right_arg,level=level+1)
            return ExpressionTree('=', children=[l_child,r_child],level=level)
        if isinstance(formula, AppliedSymbol):
            return ExpressionTree(formula,level=level)
        if isinstance(formula, Element) and formula.name == 'true':
            return ExpressionTree('true',level=level)
        if isinstance(formula, Element) and formula.name == 'false':
            return ExpressionTree('false', level=level)
        if isinstance(formula, Element):
            return ExpressionTree(formula,level=level)
        else:
            raise Exception("missed logical construct for " + str(type(formula)) + formula.decl)

    def generate_materialisation_query(self, tree):
        query = 'SELECT '
        unique_names = self.generate_unique_type_names()
        query_elements = []
        for var in self.dict_var_type:
            query += f'{unique_names[var]}.{self.dict_var_type[var]}, '
            query_elements.append(f'{self.dict_var_type[var]} {unique_names[var]}')
        query = query[:-2] + ' FROM ' + ', '.join(query_elements)
        if tree.op == 'true':
            return query
        query += ' WHERE '
        def where_conditions(tree):
            if tree.op == 'or':
                return f'( {where_conditions(tree.children[0])} OR {where_conditions(tree.children[1])})'
            if tree.op == 'and':
                return f'( {where_conditions(tree.children[0])} AND {where_conditions(tree.children[1])})'
            if tree.op == '~':
                return f'( NOT ({where_conditions(tree.children[0])}) )'
            # in the context of materialising, we know it must be something like "x = y"
            if tree.op == '=':
                l_arg = tree.children[0].op.name
                r_arg = tree.children[1].op.name
                return f'({unique_names[l_arg]}.{self.dict_var_type[l_arg]} = {unique_names[r_arg]}.{self.dict_var_type[l_arg]})'
            # now we know it's a leaf => exploit hack in AppliedSymbol grounding (which will return part of a query)
            else:
                clause = tree.op.ground(self)
                return clause
        wheres = where_conditions(tree)
        return query + wheres

    def generate_grounding(self, op, tree, res):
        grounding = f'({op} \n  '
        if op == 'doesntmatter':
            grounding = ""
        def ground(tree,level=0):
            if tree.op == 'or':
                larg = ground(tree.children[0],level+1)
                if larg == 'true':
                    return 'true'
                rarg = ground(tree.children[1],level+1)
                if rarg == 'true':
                    return 'true'
                if larg == 'false' and rarg == 'false':
                    return 'false'
                if larg == 'false':
                    return rarg
                if rarg == 'false':
                    return larg
                return f'(or {larg} {rarg})'
            if tree.op == 'and':
                larg = ground(tree.children[0],level+1)
                if larg == 'false':
                    return 'false'
                rarg = ground(tree.children[1],level+1)
                if rarg == 'false':
                    return 'false'
                if larg == 'true' and rarg == 'true':
                    return 'true'
                if larg == 'true':
                    return rarg
                if rarg == 'true':
                    return larg
                return f'(and {larg} {rarg})'
            if tree.op == '~':
                arg = ground(tree.children[0],level)
                if arg == 'true':
                    return 'false'
                if arg == 'false':
                    return 'true'
                return f'(not {arg})'
            if tree.op == '=':
                larg = tree.children[0].op
                rarg = tree.children[1].op
                if (isinstance(larg, AppliedSymbol) and isinstance(rarg, Element)):
                    if larg.ground(quantified_vars=self, function_negative_constant=rarg) == 'false':
                        return 'false'
                larg = ground(tree.children[0],level+1)
                rarg = ground(tree.children[1],level+1)
                if '(' not in larg and '(' not in rarg:
                    if larg != rarg:
                        return 'false'
                    else:
                        return 'true'
                return f'(= {larg} {rarg})'
            if isinstance(tree.op, AppliedSymbol):
                return tree.op.ground(quantified_vars=self)
            if isinstance(tree.op, Element):
                if tree.op.name in self.dict_var_type:
                    return self.dict_var_materialisation[tree.op.name]
                return tree.op.name
            else:
                return tree.op
        for tuple in res:
            self.materialise(tuple)
            grounding_with_tuple = ground(tree)
            if op == 'and':
                if grounding_with_tuple == 'false':
                    return 'false'
                if grounding_with_tuple != 'true':
                    grounding += grounding_with_tuple + '\n  '
            elif op == 'or':
                if grounding_with_tuple == 'true':
                    return 'true'
                if grounding_with_tuple != 'false':
                    grounding += grounding_with_tuple + '\n  '
            else:
                grounding += grounding_with_tuple + '\n  '
        grounding = grounding[:-2] + ')'
        if grounding == '(and \n)':
            return "true"
        if grounding == '(or \n)':
            return "false"
        if op == 'doesntmatter':
            return grounding[:-1]
        return grounding

def make_antecedent_for_normal_form(predicates, bitstring):
    antecedent = predicates[0]
    if bitstring[0] == '0':
        antecedent = Negation(antecedent,'~'+antecedent.decl)
    for i in range(1,len(bitstring)):
        if bitstring[i] == '1':
            antecedent = And(antecedent, predicates[i], antecedent.decl + ' and ' + predicates[i].decl)
        else:
            neg = Negation(predicates[i],'~'+predicates[i].decl)
            antecedent = And(antecedent, neg, antecedent.decl + ' and ' + neg.decl)
    return antecedent


class ExpressionTree():
    def __init__(self, op, children=[], level=0):
        self.children = children
        self.op = op
        self.level = level

    # For debugging reasons
    def __str__(self):
        try:
            s = "  "*self.level + str(self.op) + f" with {len(self.children)} children \n"
            for c in self.children:
                s += "  "*self.level + c.__str__()
            return s
        except:
            return "  "*self.level + str(self.op.decl) + '\n'

    def yield_conjunction_elements_at_base_level(self):
        if self.op == 'and':
            left = self.children[0].yield_conjunction_elements_at_base_level()
            right = self.children[1].yield_conjunction_elements_at_base_level()
            if left and right:
                return left + right
            return False
        # partially interpreted predicate
        if isinstance(self.op, AppliedSymbol):
            name = self.op.symbol_name
            if name in symbols['pred']:
                pred = symbols['pred'][name]
                if pred.partial:
                    return [self]
            return False
        # f(x,y)=c
        if self.op == '=' and isinstance(self.children[0].op, AppliedSymbol) and isinstance(self.children[1].op, Element):
            return [self]
        if self.op == '~':
            neg = self.children[0]
            if isinstance(neg.op, AppliedSymbol):
                name = neg.op.symbol_name
                if name in symbols['pred']:
                    pred = symbols['pred'][name]
                    if pred.partial:
                        return [self]
            if neg.op == '=' and isinstance(neg.children[0].op, AppliedSymbol) and isinstance(neg.children[1].op, Element):
                return [self]
        return False

    def simplify(self):
        something_simplified = True
        while(something_simplified):
            something_simplified = self.simplify_internal()

    def simplify_internal(self):
        something_simplified = False
        if self.op == 'and':
            if self.children[0].op == 'false' or self.children[1].op == 'false':
                self.op = 'false'
                self.children = []
                something_simplified = True
            elif self.children[0].op == 'true':
                self.op = self.children[1].op
                self.children = self.children[1].children
                something_simplified = True
            elif self.children[1].op == 'true':
                self.op = self.children[0].op
                self.children = self.children[0].children
                something_simplified = True
        elif self.op == 'or':
            if self.children[0].op == 'true' or self.children[1].op == 'true':
                self.op = 'true'
                self.children = []
                something_simplified = True
            elif self.children[0].op == 'false':
                self.op = self.children[1].op
                self.children = self.children[1].children
                something_simplified = True
            elif self.children[1].op == 'false':
                self.op = self.children[0].op
                self.children = self.children[0].children
                something_simplified = True
        elif self.op == '~' and self.children[0].op == '~':
            self.op = self.children[0].children[0].op
            self.children = self.children[0].children[0].children
            something_simplified = True
        elif self.op == '~' and self.children[0].op == 'true':
            self.op = 'false'
            self.children = []
            something_simplified = True
        elif self.op == '~' and self.children[0].op == 'false':
            self.op = 'true'
            self.children = []
            something_simplified = True
        for child in self.children:
            something_simplified = something_simplified or child.simplify_internal()
        return something_simplified

    def contains_only_fully_interpreted_predicates(self):
        good = True
        if isinstance(self.op, AppliedSymbol):
            name = self.op.symbol_name
            if name in symbols['func']:
                return False
            if name in symbols['pred']:
                pred = symbols['pred'][name]
                if pred.partial:
                    return False
        elif len(self.children) == 1:
            good = good and self.children[0].contains_only_fully_interpreted_predicates()
        elif len(self.children) > 1:
            good = good and self.children[0].contains_only_fully_interpreted_predicates()
            good = good and self.children[1].contains_only_fully_interpreted_predicates()
        return good

    def fully_interpreted_predicates_mentioned(self):
        if isinstance(self.op, AppliedSymbol):
            name = self.op.symbol_name
            if name in symbols['pred']:
                pred = symbols['pred'][name]
                if not pred.partial:
                    return [self.op]
        if len(self.children) == 1:
            return self.children[0].fully_interpreted_predicates_mentioned()
        elif len(self.children) == 2:
            return self.children[0].fully_interpreted_predicates_mentioned() + self.children[1].fully_interpreted_predicates_mentioned()
        return []

    def make_consequent_for_normal_form(self, predicates, bitstring):
        if self.op in predicates:
            if bitstring[predicates.index(self.op)] == '1':
                self.op = 'true'
            else:
                self.op = 'false'
        for child in self.children:
            child.make_consequent_for_normal_form(predicates, bitstring)
