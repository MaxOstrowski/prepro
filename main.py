"""
 run preprocessor to optimize logic program
"""
from clingo.ast import ASTType, Sign, Transformer, parse_files

from aggregate_equality1 import EqualVariable
from dependency import positive_body_predicates, positive_head_predicates

# eq = EqualVariable()
# parse_files(["test.lp"], lambda stm: print(eq(stm)))


class Visitor(Transformer):
    def visit_Rule(self, rule):
        print(repr(rule))
        print(list(positive_head_predicates(rule)))
        return
        print(rule)
        for blit in rule.body:
            if blit.ast_type == ASTType.Literal:
                if blit.sign != Sign.NoSign:
                    continue
                if blit.atom.ast_type == ASTType.SymbolicAtom:
                    atom = blit.atom
                    if atom.symbol.ast_type == ASTType.Function:
                        print("found function", atom.symbol)
                elif blit.atom.ast_type == ASTType.BodyAggregate:
                    for elem in blit.atom.elements:
                        print(elem.ast_type)
                        for cond in elem.condition:
                            if cond.ast_type == ASTType.Literal:
                                if cond.sign != Sign.NoSign:
                                    continue
                                if cond.atom.ast_type == ASTType.SymbolicAtom:
                                    atom = cond.atom
                                    if atom.symbol.ast_type == ASTType.Function:
                                        print("found function", atom.symbol)

        return rule


v = Visitor()
parse_files(["test.lp"], lambda stm: v(stm))
