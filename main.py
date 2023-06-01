"""
 run preprocessor to optimize logic program
"""
import sys

from clingo.ast import parse_files

from aggregate_equality1 import EqualVariable
from dependency import DomainPredicates, PositivePredicateDependency, RuleDependency
from minmax_aggregates import MinMaxAggregator

files = [sys.argv[1]]
prg = []
parse_files(files, prg.append)
### create general tooling and analyzing classes
rdp = RuleDependency(prg)
pdg = PositivePredicateDependency(prg)
dp = DomainPredicates(prg)

### call transformers
eq = EqualVariable(pdg)
prg = eq.execute(prg)
mma = MinMaxAggregator(rdp, dp)
prg = mma.execute(prg)

for i in prg:
    print(i)
