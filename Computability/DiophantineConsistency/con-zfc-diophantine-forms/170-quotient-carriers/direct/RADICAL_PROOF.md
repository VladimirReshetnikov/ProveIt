# Composition with the inherited common-quadratic-radical projection

## Attribution

This method, its producer and independently written finite checker are copied
unchanged from `ConZFC_Quadratic_Projection_234_2026-10-25.zip` at ProveIt commit
`536c08e7913e59bd42e8fca66e89944c920884ad`. The archive and exact source hashes
are retained in `inherited_radical/`. We claim a tested composition with our
distinct arithmetic source, not priority for common-Hessian-radical projection.

## The exact integer bijection

Let Q_0,...,Q_(r-1) be quadratic polynomials in n integer variables. Suppose
v is an integer vector in the common kernel of all quadratic Hessians,
v_p=1, and the directional derivative of Q_j along v is a_j. Because the
quadratic derivatives vanish, each a_j is a fixed integer and

    Q_j(y+v*t) = Q_j(y) + a_j*t.

Suppose a_s is +1 or -1. On the coordinate hyperplane y_p=0, set

    T(y) = -a_s*Q_s(y),
    R_j(y) = Q_j(y) - a_s*a_j*Q_s(y),   j != s.

Every R_j is quadratic. If all R_j vanish at an integer y with y_p=0,
then x=y+v*T(y) is an integer common zero of every Q_j, including Q_s.
Conversely, given an integer common zero x, define

    y=x-v*x_p.

Then y_p=0. The equation Q_s(x)=0 forces x_p=T(y), because a_s²=1,
and all R_j(y)=0. These two polynomial maps are inverse on the zero sets.
Thus one variable and one residual are removed, with no positivity,
divisibility, rational-root or existential-completeness premise.

For a sum of real squares, vanishing is equivalent to every residual being
zero. Applying the bijection repeatedly therefore preserves absence of
integer zeros and, through our established arithmetic calibration, the
equivalence to Con(ZFC).

## Literal application here

The source `diagonal238_reduced` has six independent usable radical
directions. Six supplied certificates remove six variables and six rows,
giving `radical238`: 232 variables and 168 quadratic residuals. The source
`diagonal239_reduced` similarly gives `radical239`: 233 variables and
169 residuals. The finite checker derives the projected rows directly as
Q_j-a_s*a_j*Q_s on y_p=0, independently of the producer's shear/substitution
implementation. It checks every Hessian directional derivative, unit slope,
map, coefficient and dimension. Complete modular column-rank certificates
for the final Hessian systems exclude further common-radical directions in
those particular systems; they do not exclude other variable reductions.

The incoming residual-basis optimizer subsequently applies elementary
integer operations Q_i <- Q_i+k*Q_j, i != j. Their inverses use -k in
reverse order, so they preserve the common zero set. They change the
sum-of-squares polynomial and its support/height, with every resulting
coefficient supplied and independently recollected. Prefixes selected for
support/height tradeoffs are checked by the same exact inverse replay.

## Composition on the unchanged incoming pooled-power source

The same inherited radical method applies directly to the incoming
225-variable pooled-power equation, without changing any unbounded semantic
source choice. Its exact original equation is `inherited_pooled/source225.json`;
its unchanged original ZIP is retained there. Five integer polynomial
bijections yield `pooled225_radical`, with 220 variables and 157 residuals.

Six integral coordinate shears from the Factorial-Free Binomial CRT package
then give `pooled220_sheared`. Each shear replaces one old coordinate by that
coordinate plus a fixed integer linear combination of other coordinates.
It is an invertible integer map; its inverse subtracts the same combination.
The six maps are applied in order and inverted in reverse order. Their
literal coefficients and complete inverse identity are independently checked.

Two affine consequences are then exposed. The first has the literal form

    4 + 4*x9 + 8*x10 + 4*x20 - x21 + x34 = 0,

and equals residual 19 minus residual 6 of the sheared 220-variable system.
Solving it for x34 gives an affine integer restoration and the 219-variable
system `pooled219_affine`. The second is residual 80 of that 219-variable
system and has coefficient +1 on coordinate 94. Solving it for that
coordinate gives `pooled218_affine`, with 218 variables and 155 residuals.
All indices here are zero-based; the certificates supply the complete
second affine row rather than an informal ellipsis.

In general, if a fixed integer linear combination of residuals is an affine
polynomial L with a unit coefficient on x_p, solve L=0 for x_p. Substitute
the resulting affine integer polynomial in every residual and omit any one
row with nonzero coefficient in the displayed linear combination. Every
original integer zero projects to a new one. Conversely, restoration makes
L vanish; all retained rows vanish, so the nonzero fixed integer coefficient
times the omitted row vanishes, forcing the omitted row itself to vanish.
Degree remains at most two. This is an exact integer zero-set bijection.

The row-basis endpoints and their selected prefixes alter only the residual
basis. The supplied `verify_compositions.py` checks the source225 byte binding
to its original archive, the inherited projection/checker modules against
their original archive, all five radical steps, all six shears and their
inverse, both affine projections, and every final polynomial coefficient.
The incoming Pooled Powers verifier was also replayed with `--rebuild`;
`POOLED225_PARENT_REPLAY.json` records that successful run. The inherited
unbounded semantic proof and logical calibration remain explicitly identified;
this is not a new proof-assistant certificate.

## Verification commands

## Composition with the qualified diagonal pooled source

The independent strict-horizon and pooled-power construction in
`diagonal_pool/` starts from `diagonal238/equation.json` and
produces the 223-variable source copied here as `pooled223_source.json`.
Its SHA-256 is
`7c95a8dbcba85fe15ccaf33123132b423f2e28aa9068ceed9a3ff86f5eb075c5`.
That separate source package supplies the complete ordinary semantic proof,
an independent checker importing no producer, and normal/optimized-Python
receipts. It explicitly checks all fourteen aggregate request memberships,
the Pell gates, the two aggregate identities at each base, and all thirty-six
affine frame squares covering the seventeen retained requests. No optional
Pell-difference stage is used in this selected chain.

Six common-radical projections now produce `pooled223_radical`, with
217 integer variables and 154 quadratic residuals. The proof is exactly the
polynomial-bijection lemma above. Applying the first 112 recorded elementary
row operations gives `pooled217_height5184`, with 19,112 collected monomials
and coefficient height 5,184. The first 50 operations give a second point
with 18,148 monomials and height 5,888. These are alternative bases of the same
common-zero ideal, each certified by exact forward and inverse row replay.
All 217 variables occur in the collected polynomials. The degree is exactly four.

The arithmetic dependency chain is explicit: inherited factorial-free source;
diagonal q congruent 3 modulo 6 source and its proof; strict-horizon/pooling
source and its proof; common-radical bijections; residual-basis maps. The
218–220-variable companion instead uses the unchanged incoming pooled source
and therefore avoids the new diagonal and strict-horizon semantic links.

## Verification commands

From this directory, the following check the six-step compositions:

    python3 -B inherited_radical/audit_projection.py diagonal238_reduced/equation.json radical238
    python3 -B inherited_radical/audit_projection.py diagonal239_reduced/equation.json radical239

For any `radical238_*` or `radical239_*` residual-basis profile, use its
corresponding `radical238/equation.json` or `radical239/equation.json` as
the source and add `--row-mode`. The tool also works with optimized Python.
The whole source-level proof and its independent audit remain necessary;
this projection checker alone does not establish the imported arithmetic
calibration or Con(ZFC) equivalence.
