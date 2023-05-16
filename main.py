"""
 run preprocessor to optimize logic program
"""
import sys

from clingo.ast import ASTType, Sign, Transformer, parse_files

from aggregate_equality1 import EqualVariable
from dependency import DomainPredicates, PositivePredicateDependency
from minmax_aggregates import MinMaxAggregator

files = [sys.argv[1]]
prg = []
parse_files(files, lambda stm: prg.append(stm))
### create general tooling and analyzing classes
pdg = PositivePredicateDependency(prg)
dp = DomainPredicates(prg)

### call transformers
eq = EqualVariable(pdg)
prg = eq.execute(prg)
mma = MinMaxAggregator(prg, dp)
prg = mma.execute(prg)

for i in prg:
    print(i)
