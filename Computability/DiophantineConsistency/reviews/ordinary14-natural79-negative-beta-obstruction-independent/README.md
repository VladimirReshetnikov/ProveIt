# Independent review: negative-beta obstruction

The counterexample reproduces on the exact selected 79-operation source. An
independent checker parses all 79 literal assignments with Python's arithmetic
AST, compares their operands and operators with the pinned candidate, checks
all 14 variable and four port aliases and the graph output tuple, and evaluates
the vector in exact integer arithmetic. For ports `[-1,0,3,0]`, the natural
witness in the author packet has `w=0`, `q=0`, all five factors equal to 1,
and output 0.

The checker also independently evaluates natural positive/negative pairs using
the pinned `Expr.splitNatural` source rules. The two output values are equal;
this is an exact computation of the source-specified splitting algorithm, not
a Lean execution of `InternalZero`. The author's checker and the independent
receipt reproduce.

This refutes an unconditional positive-`w` claim over **arbitrary signed
integer ports**, even with natural witnesses and nonnegative K0. Its beta is
negative and cannot satisfy the represented model-natural beta hypothesis. It
does not show that positive-beta or fixed compact-port graphs have a zero, and
does not determine the consistency of ZFC. It neither elaborates Lean nor
establishes the proposed internal endpoint. No staging or original artifact
mutation was performed.

From the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary14-natural79-negative-beta-obstruction-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary14-natural79-negative-beta-obstruction-independent/result.json
```
