# External binary-gate count for the sign14 candidate

The checker constructs a topologically ordered circuit by exact structural
hash-consing of the five pinned external residual ASTs. With a multiplication
for each square and four additions for their sum, all 98 live gates are 41
additions, 15 subtractions and 42 multiplications. The five residuals alone
use 89 gates. Variables and integer/port leaves are free, each binary
operation costs one gate, and repeated exactly equal ordered subtrees are
shared. The checker validates all 14 variables, four ports, reachability,
topological order and four small assignments against direct AST evaluation.

This is an external upper bound for the pinned JSON candidate under that
convention, not a proof of minimality. Commutative or algebraic rewrites might
reduce it. The JSON is not yet formally bound to the Lean expression; the
binary count is not a Lean theorem and is not an assertion about the current
degree-150 PDF. The author run exited 0.

The [independent external audit](../../reviews/nine-sharing-sign14-operation-count-independent/README.md) passed using a separate ordered-subtree reconstruction and replaying the author's evaluation controls.
