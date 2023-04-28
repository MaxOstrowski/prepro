"""
 run preprocessor to optimize logic program
"""
from clingo.ast import ASTType, Sign, Transformer, parse_files
import sys

from aggregate_equality1 import EqualVariable
from dependency import PositivePredicateDependency, DomainPredicates

files = [sys.argv[1]]
prg = []
parse_files(files, lambda stm: prg.append(stm))
pdg = PositivePredicateDependency(prg)
dp = DomainPredicates(prg)
# eq = EqualVariable(pdg)
# parse_files(files, lambda stm: print(eq(stm)))
