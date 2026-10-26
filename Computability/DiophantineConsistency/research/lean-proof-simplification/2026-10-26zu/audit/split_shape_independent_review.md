# Independent conceptual review of SplitShape.lean

The generic fold theorem is mathematically correct for the pinned raw
`Expr.splitNatural`. Constants produce two constant leaves; variables
produce a variable and a zero leaf, which both map to `leaf`. Addition and
subtraction preserve the paired induction equalities. Multiplication
produces two additions of products, and all four corresponding child fold
values agree by the induction hypotheses. Thus the arbitrary fold's
`add` and `mul` need no associativity, commutativity, idempotence, order, or
semiring laws. This is operation-preserving, ordered tree-shape equality,
not merely equality of total operation counts.

The resource client must assign the SAME base cost to variables and
constants. `NatExpr.depth` and `QuarticCompiler.Gates.count` satisfy that
condition. `GraphRep` depth does too (both leaf representations have depth
one), even though the graph compiler's binary depth fold is asymmetric in
its two arguments. Preserving child order handles that asymmetry.

This theorem does not imply equal values, supports, polynomial degree, or
any resource accounting sensitive to a literal's value or bit length.
Already `Expr.var i` has positive side a variable and negative side zero,
so degree equality would be false. Separate simplification also destroys
the raw shape invariant: `(var i)*(var i)` has raw sides with identical
shapes, but simplification retains `x*x` on the positive side and collapses
the negative side to zero. Any after-simplification claim requires a new,
weaker theorem; it must not be inferred from this result.

No issue found with the definitions or the structural proof sketch.
Compiler status is owned by the parent, who is running this module.
