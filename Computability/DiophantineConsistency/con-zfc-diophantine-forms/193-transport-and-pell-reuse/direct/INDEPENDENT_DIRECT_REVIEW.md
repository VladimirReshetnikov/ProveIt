# Independent review of the recycled-quotient direct equation

This is an AI-assisted internal mathematical and finite-algebra review. It is
not external human peer review or a new proof-assistant development.

## Principal endpoint

The supplied P83 circuit is an ordinary polynomial in **83 unrestricted
integer variables**, with **exact degree 624**, **31 residual squares**, and
**2,939 live binary arithmetic operations**. Every integer literal in its
live circuit has absolute value at most324. An exact propagated coefficient
norm proves every expanded coefficient has absolute value strictly less than
2^1568; this is a bound, not an assertion that its exact height has1568 bits.

The full source-coordinate restoration uses one additional node not needed
by the final polynomial. Source-coordinate roots are polynomial
abbreviations, not extra quantified variables or constraints. The graph
contains only integer literals, independent input leaves, addition and
multiplication. The reported operation count includes multiplication by
constants and squaring.

## New number-theoretic step

The separate recycled-quotient theorem was reviewed term by term. For every
odd p with p^2|W, the divided Pell ordinate Y_W(W+1)/W is a p-adic unit.
The abscissa c=X_W(W+1) is1 modulo p^6, which is more than enough for the
index increment

    Y_(k+p^a)(c)-Y_k(c) = p^a modulo p^(a+1).

This proves a permutation of every p-power residue ring. Elementary square
root lifting and CRT therefore choose the already-existing odd frame
quotient r so that the same value supplies the center

    A=L^2+2r^2,

with the target residue required by the parent. No extra quantified k or
modular root is introduced. These finite indices and modular roots occur
only in the completeness proof.

The signed W=qW0 branch is valid before q is known positive. At W=-F<0,
the frame equation becomes

    L^2-F^3(F-2)r^2=1,

where F>=6 and r is odd and nonzero. Ordinary Pell classification at base
F-1 shows the index is divisible by F, giving

    A>=L^2>=(F-1)^(2F)>F^F.

Thus the old magnitude arguments may use the positive bound F=|W|. The
positive canonical q in the converse is already a sufficiently powerful
integer in the parent construction, so p^2|W holds for every prime of the
required modulus. The sign bootstrap has no circular use of positivity of
that modulus or of decoded powers.

In the raw source the W and its two frame-product helpers are isolated from
the semantic data used to compute W0. The two deleted center coordinates
occur only in their constructor row. This is an existence-preserving
construction, not a pointwise map from every old choice of two center
witnesses.

## Independent finite replay

The checker `check_independent.py` imports neither the producer nor any
search or verification routine. It authenticates eight frozen parent
artifacts, replays the old projections to the stored parent endpoints, and
replays the two changed arithmetic rows through those same projections.
All shear inverses have unit coefficient; row additions have distinct
source and target; every eliminated coordinate is recovered from its actual
current unit pivot. The resulting source has exactly227 variables and175
rows and matches `source227.json` coefficient for coefficient.

For P83,144 different rows orient144 different coordinates by identities
of the form

    v=R(other coordinates).

The dependency graph is acyclic. The checker authenticates every pivot
against its literal source polynomial and verifies that the83 free
coordinates and31 retained rows are exactly the two complements. Therefore
the definitions give an integral polynomial restoration of all227 source
coordinates. On zeros, its inverse is projection to the free coordinates.
No division or choice of a rational root occurs in this map.

The actual emitted DAG is reflected into a canonical associative and
commutative expression representation. Exact constant folding is allowed;
no random polynomial identity test is used. This reflection checks every
restoration, every retained source row, and the final sum of residual
squares. Every source row is thus accounted for either by an exact pivot
identity or by a retained residual.

## Degree, coefficients, and actual arity

Ordinary degree propagation through the actual DAG proves every residual
has degree at most312. The recorded integer ray gives the leading
coefficient936906 modulo1,000,003 for residual5, so that residual has degree
exactly312. A sum of squares of integer polynomials cannot cancel its
highest homogeneous component: along the same integer ray at least one
leading coefficient is a nonzero integer, and the sum of their squares is
strictly positive. Thus the final degree is exactly624.

Forward dual arithmetic, independently implemented from the producer's
reverse differentiation, verifies all83 stored partial derivatives at the
specified integer point modulo1,000,003. Every value is nonzero. Each input
therefore genuinely occurs in the final polynomial, rather than merely
appearing syntactically in a canceled intermediate expression.

For the coefficient bound, assign1 to each input leaf and |c| to each
integer literal. At an addition gate add the two bounds; at multiplication
multiply them. The triangle and convolution inequalities prove inductively
that these integers majorize coefficient l1 norms. The final integer in
`P83/TIGHT_HEIGHT.json` has bit length1568, and the independent checker
reconstructs it exactly from the literal DAG. It therefore proves the stated
strict bound below2^1568. The earlier coarse3618 exponent in the main
metrics remains a valid, weaker bound.

Three deliberate corruptions were rejected: a false unit restoration, an
output that omits the sum of squares, and an altered multiplication gate.
The normal receipt is `INDEPENDENT_CHECK.json`; the optimized-Python replay
is recorded separately. Additional moderate-degree family profiles were
also replayed, but this review's main conclusion is the P83 equation.

## Proof boundary and remaining limitations

No mathematical defect was found in the new recycled-quotient argument or
the P83 bridge. The finite replay does not establish the inherited C222/ZF/ZFC
calibration by itself. That calibration and the new quantified Pell, CRT,
growth and sign arguments are ordinary proofs intended to be formalizable
in ZFC. The work is not a newly compiled end-to-end Lean or Rocq theorem or
an emitted object-language ZFC derivation.

The conclusion is the equivalence between existence of an integer zero and
existence of a finite syntactic ZFC refutation, at the stated inherited
calibration. Negating it gives the desired equivalence with Con(ZFC). It
does not prove consistency, exhibit a zero, decide unsolvability, or prove a
global minimum among all Diophantine equations.
