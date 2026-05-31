import os
import warnings

warnings.simplefilter(action='ignore', category=FutureWarning)
from tree_sitter import Language, Parser, Tree
from fodot_objects import KB, variables, timings
import time
import argparse
import re
from fodot_query import Query_KB, db_manager

# PARSING + INITIALISING DB
start = time.time()
parser = argparse.ArgumentParser(prog='IDP-Z3-DB', description='Grounder and solver for FO[Core] using a database')
parser.add_argument('filename')
parser.add_argument('db_manager')
args = parser.parse_args()

# Manual overrides for debugging
#args.filename = "test_case_manual.idp"
#args.db_manager = "sqlite"

parse_start = time.time()
if args.db_manager == "naive":
    db_manager.naive = True
    args.db_manager = "sqlite"
db_manager.setup(args.db_manager)

with open(args.filename, 'r') as fp:
    test_fodot = fp.read()

# Apply some regex replaces to replace unicode by ASCII
uni_to_ascii = {'∈': 'in', '∀': '!', '⨯': '*', '→': '->',
                '𝔹': 'Bool', 'ℤ': 'Int', 'ℝ': 'Real',
                '∃': '?', '←': '<-', '∧': '&', '∨': '|',
                '¬': '~', '⇒': '=>', '⇔': '<=>', '⇐': '<=',
                '≤': '=<', '≜': ':=', '≠': '~=', '≥': '>='}

for uni, asc in uni_to_ascii.items():
    test_fodot = re.sub(uni, asc, test_fodot)

# Get rid of definitions, by turning them into equivalences (dirty code)
theory_block = re.search(r"theory\s*\{\s*((?:[^{}]|\{[^{}]*\})*)\s*\}", test_fodot, re.DOTALL)
if theory_block:
    theory_block = theory_block.group(1)
if "{" in theory_block:
    warnings.warn(f"This is a naive solver, in which definition inductive definitions have been treated as an equivalence")
    new_theory_block = theory_block.replace("{","")
    new_theory_block = new_theory_block.replace("}", "")
    test_fodot = test_fodot.replace(theory_block, new_theory_block) # potentially slow
    test_fodot = re.sub(r'(\S.*?)\s*<-\s*(\S.*)', r'\1 <= \2\n\1 => \2', test_fodot)
test_fodot = re.sub(r'(?m)^\s*//.*\n?', '\n', test_fodot) # delete comment lines

# Rebuild fodot library
try:
    os.remove('./build/fodot.so')
except:
    pass
Language.build_library('./build/fodot.so',['./tree-sitter-fodot/'])

# Load as a language object
FODOT = Language('./build/fodot.so', 'fodot')

# Create parser, and parse the fodot.
parser = Parser()
parser.set_language(FODOT)
tree = parser.parse(bytes(test_fodot, 'utf8'))

Query_KB = Query_KB()
DB_Manager = db_manager

def traverse_tree_query(tree: Tree):
    cursor = tree.walk()
    reached_root = False
    level = 0
    while reached_root is False:
        if cursor.node.type in ['prop_declaration', 'constant_declaration',
                                'predicate_declaration',
                                'function_declaration', 'type_declaration',
                                #'structure',
                                'formula', 'block_structure']:
            if cursor.node.type == 'prop_declaration':
                Query_KB.create_prop_from_node(cursor.node)
            elif cursor.node.type == 'constant_declaration':
                Query_KB.create_cons_from_node(cursor.node)
            elif cursor.node.type == 'predicate_declaration':
                Query_KB.create_pred_from_node(cursor.node)
            elif cursor.node.type == 'function_declaration':
                Query_KB.create_func_from_node(cursor.node)
            elif cursor.node.type == 'type_declaration':
                Query_KB.create_type_from_node(cursor.node)
            elif cursor.node.type == 'formula':
                Query_KB.add_formula_from_node(cursor.node)
            elif cursor.node.type == 'block_structure':
                Query_KB.apply_interpretation_from_node(cursor.node)
            if cursor.goto_next_sibling():
                continue
            else:
                level -= 1
                cursor.goto_parent()
                if cursor.goto_next_sibling():
                    continue
                else:
                    reached_root = True
        if cursor.goto_first_child():
            level += 1
            continue
        if cursor.goto_next_sibling():
            continue
        retracing = True
        while retracing:
            level -= 1
            if not cursor.goto_parent():
                retracing = False
                reached_root = True
            if cursor.goto_next_sibling():
                retracing = False

traverse_tree_query(tree)
Query_KB.eliminate_conjunctions_from_formulas()
DB_Manager.queries_create_type = Query_KB.queries_create_type
DB_Manager.queries_insert_type = Query_KB.queries_insert_type
DB_Manager.queries_create_func_and_pred = Query_KB.queries_create_func_and_pred
DB_Manager.queries_pred_enumeration = Query_KB.generate_predicate_enumeration_queries()
if not db_manager.naive:
    DB_Manager.queries_update_facts = Query_KB.generate_fact_queries()
DB_Manager.init_database()
if not db_manager.naive:
    for query in Query_KB.generate_quantified_fact_queries():
        DB_Manager.has_facts = True
        DB_Manager.apply_query(query)
        DB_Manager.conn.commit()
    pass
timings["parse"] = time.time() - start
print("done parsing")

# GROUNDING
start = time.time()
with open("log", "w") as log_file:
    log_file.write(Query_KB.smt())
DB_Manager.close()
timings["ground"] = time.time() - start
print("done grounding")

# SOLVING
start = time.time()
Query_KB.model_expand(max_nr_models=1)
timings["solve"] = time.time() - start
print("done solving")

p,g,s = timings["parse"], timings["ground"], timings["solve"]

print(f'Elapsed time: {round(p+g+s, 4)}',
      f' (Parse: {round(p, 4)}',
      f' | Ground: {round(g, 4)}',
      f' | Solve: {round(s, 4)})')

