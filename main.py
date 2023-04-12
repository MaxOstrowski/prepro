"""
 run preprocessor to optimize logic program
"""
from clingo.ast import parse_files

from aggregate_equality1 import EqualVariable

eq = EqualVariable()
parse_files(["test.lp"], lambda stm: print(eq(stm)))
