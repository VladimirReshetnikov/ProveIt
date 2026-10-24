# Independent ordinary review of the height-one compiler

Scope: the mathematical construction in `report/height_one.tex`, the
standard-library producer `research/height_one/build.py`, the separately
written certificate verifier `research/height_one/verify.py`, and the
literal 519-variable source and 7,431-variable output. This is an
AI-assisted independent mathematical/code review, not external peer review
or a proof-assistant certificate. The inherited C222-to-ZFC calibration
was not recompiled by this review.

## Mathematical findings

The central identity is correct:

```
2 B_sigma(m,w)
 = (sum sigma_i*m_i)^2 + (sum sigma_i*w_i)^2
   + sum (m_i-w_i)^2.
```

Expansion gives exactly the proposed coefficients. Consequently the block
is nonnegative over the reals and vanishes precisely at simultaneous
agreement `w=m` and the required signed row equation. This conclusion
does not depend on source variables being nonnegative.

Every occurrence uses two distinct fresh aliases, including repeated old
variables and padded linear/constant terms. Thus all alias products have
degree two before any solution constraints are used. This is essential
for the collision argument: row block monomials involving only aliases
have degree four; the alias/product-port terms have degree three; the
product-port-only terms have degree two. Agreement constraints use only
alias variables at degree two and therefore cannot collide with any of
those terms.

For every old-variable group, a cycle of length at least three has
distinct undirected edges. A two-occurrence group gets a third dummy
vertex, preventing the coefficient -2 that a two-cycle would create.
A singleton needs no agreement equation. Different groups are disjoint.

The unit path has at least two distinct vertices. Its edges are distinct,
its endpoint linear monomials are distinct, and it contributes the only
constant coefficient, namely 1. Its half-square identity is correct and
forces every unit alias to equal one. No hidden collision with another
constant or linear term occurs: the row blocks have no such terms before
applying the agreement constraints.

These observations prove that the fully collected polynomial has
coefficient set exactly contained in `{-1,1}`, constant coefficient one,
total degree four whenever at least one signed monomial occurrence is
present, and individual variable degrees at most two. In the delivered
instance both signs occur, and a quartic term occurs.

The forward map repeats each source value in its aliases, assigns unit
aliases one, and assigns each product port its monomial. The converse
uses nonnegativity to make every block zero. All extra values are uniquely
forced. Thus the asserted bijection on integer zero sets is valid when
every source coordinate occurs. Before coefficient normalization the
forward inverse has degree at most two; the supplied normalization uses
only constant or linear derived wires, so this degree bound persists.

The coefficient-normalization program is also sound. Its new variables
are monically defined in strict dependency order, and its constant/scale
rows recover precisely the intended constant and scalar multiple. Keeping
repeated terms as separate occurrences is legitimate and necessary.
All normalized rows remain quadratic.

## Certificate verifier findings

The verifier imports no producer. It independently:

- checks all normalized definitions are monic and topological;
- substitutes their exact polynomial meanings into every defining and
  source row, comparing collected coefficients;
- reserves each alias, product port, and dummy coordinate exactly once;
- binds every occurrence to its original label and row sign;
- checks every agreement group and the entire unit path;
- reconstructs the complete sum of ordinary squares for `2 H`;
- checks its coefficients are even, divides by two, and compares every
  output coefficient;
- checks degree four, coefficient height one, and constant coefficient one.

This is a substantive independent finite certificate check. Its signed
sample evaluations are supplemental; the exact coefficient reconstruction
and symbolic source pullbacks provide the finite algebraic evidence.

The two corruption checks currently contained inside this verifier are
negative dictionary comparisons. They do not themselves invoke the whole
verifier on modified artifact bytes. They should be described at that
narrow scope, or supplemented with two actual rejected-artifact calls
outside this verifier. This limitation does not affect its exact positive
reconstruction check.

## Instantiated read-check

The independent literal read-check records:

- Source: 519 coordinates, all used.
- Target: 7,431 coordinates, all used.
- Collected monomials: 34,086.
- Coefficients +1: 21,934; coefficients -1: 12,152.
- Maximum individual variable degree: 2.
- Source equation SHA-256:
  `2a7dec9de97fdf80de1fdef4977b6cdf096bff5fc1dc7a586cdb5fede5333016`.
- Output polynomial SHA-256:
  `ff1262a805e6f710bb7b65091b38a76ff954e75277a945e7e282b54fb7c186ee`.

See `height_one_read_audit.json` for the machine-readable receipt. This
review did not repeat the full producer or all verification executions.

## Two exposition corrections requested

1. A nonempty list containing only zero rows need not produce a quartic.
   The generic exact-degree theorem should assume at least one monomial
   occurrence, or explicitly add a harmless nonzero written row. This
   qualification is satisfied by the delivered source.
2. The program uses the literal integer 1 as the base of binary constant
   construction; it does not allocate a separate `C_1` wire. The paper
   should describe that convention to match the delivered counts.

Subject to those wording corrections, no gap was found in the new
height-one construction or its collision proof. Historical priority is
not established by this review. The generic construction and exact data
are mathematically substantive independent of any priority claim.
