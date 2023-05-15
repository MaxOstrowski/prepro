"""
 run preprocessor to optimize logic program
"""
import sys

from clingo.ast import ASTType, Sign, Transformer, parse_files

from aggregate_equality1 import EqualVariable
from dependency import DomainPredicates, PositivePredicateDependency

files = [sys.argv[1]]
prg = []
parse_files(files, lambda stm: prg.append(stm))
pdg = PositivePredicateDependency(prg)
dp = DomainPredicates(prg)
for x in dp.create_domain(("c", 1)):
    print(x)
for x in dp._create_nextpred_for_domain(("c", 1), 0):
    print(x)
# eq = EqualVariable(pdg)
# parse_files(files, lambda stm: print(eq(stm)))
