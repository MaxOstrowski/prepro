"""
 run preprocessor to optimize logic program
"""
from clingo.ast import ASTType, Sign, Transformer, parse_files

from aggregate_equality1 import EqualVariable
from dependency import PositivePredicateDependency

files = ["test.lp"]
prg = []
parse_files(files, lambda stm: prg.append(stm))
pdg = PositivePredicateDependency(prg)
eq = EqualVariable(pdg)
parse_files(files, lambda stm: print(eq(stm)))

# use sympy for simplificaions of mathematical expressions
