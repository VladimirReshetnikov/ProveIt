# Shared literal circuits for the joint-sign family

All variables below are unrestricted integers. The six fixed coefficient
ports are the complete source34 tuple and determinant scales bound in
../guards/COEFFICIENT_BINDING.json. They are fixed numeral leaves.

| Variables | Exact degree | Live binary gates | Residual-system gates |
| --- | --- | --- | --- |
|19|88|109|96|
|20|32|112|97|
|21|20|115|98|
|22|16|118|99|
|23|12|121|100|
|25|8|127|102|

Each emitted *_dag.json is literally the same integer polynomial as the
corresponding ../joint/*.json sum of squared residuals. This is stronger
than equality of zero sets: no residual normalization, replacement modulo
another residual, finalizer substitution or domain restriction is used.
The 22-variable source already contains its documented auxiliary-row
reduction; its evaluator reproduces that specific polynomial exactly.

The convention charges every live binary addition, subtraction and
multiplication, including squares and multiplication by small integers.
Fixed numeral leaves and reuse of already-computed registers are free.
Unused trial registers are removed by reachability from the single output.
These are delivered upper bounds, not claims of minimum arithmetic complexity.

Reproduce with Python3, standard library only:

    python build.py
    python check.py
    python -O check.py

check.py is independent of the builder. It checks source SHA256 pins,
declarations, all live references, operation counts, each exact residual
identity, and the unchanged sum-of-squares finalizer. For the19–21-variable
factored sources it first checks literal AST equality after complete source
inlining, then performs exact sparse algebra with X,Y,W as validated cut
registers. It never expands the high-degree final sum of squares. For the
other source packets it also checks the lower-degree expanded source rows.

The mathematical and formalization boundaries are inherited from joint/.
This evaluator does not introduce a new consistency proof or alter any
fixed coefficient, source theorem or quantified coordinate.

PROOF.md explains the algebraic cuts. section.tex is a compact report section.
CHECK.json and CHECK_OPTIMIZED.json record all six exact verification results.
