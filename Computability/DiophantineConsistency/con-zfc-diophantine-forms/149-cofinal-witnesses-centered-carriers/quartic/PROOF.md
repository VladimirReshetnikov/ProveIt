# Affine-exposure compilation and a degree-three obstruction

## Composition and theorem

First compose the authenticated 252-coordinate common-remainder source
with the separately proved odd-square radix change; see
`ODD_SQUARE_COMPOSITION_PROOF.md`. This gives the 250-coordinate source
`sources/common_remainders250_odd.json`. Every supplied final polynomial is
an exact degree-four polynomial with integer coefficients in independently
unrestricted integer variables. Subject only to the identified ordinary
arithmetic and C222/ZF/ZFC calibration inherited from these sources, ZFC
proves that its integer unsolvability is equivalent to Con(ZFC).

The arithmetic composition is new relative to those two separate incoming
branches. The affine-exposure identities and six initial coordinate shears
are credited to the prior Residual Bases/Denominator Engineering package.
The alternative 76-step coordinate preconditioner is credited to Shared
Residue Bounds. The newly frozen certificates transport those operations
to the stronger source and record additional searched elementary operations.
No search heuristic, sampled zero, or claimed optimizer minimum is a premise.

## Universal compilation lemmas

For integer polynomials R_i, the elementary row replacement
R_i <- R_i+kR_j (i!=j,k integer) has inverse with -k and preserves the
common zero set. The quartic sum of squares generally changes, so equality
of the old and new quartic polynomials is NOT claimed.

A coordinate substitution old x_t=new x_t+L(x), where L is integral
linear and independent of x_t, is an integer-lattice bijection, with
inverse obtained by subtracting L. Our frozen sequences use only such
substitutions and are inverted in reverse order.

If a residual is epsilon*x_t+L(x) with epsilon=+1 or -1, L integral
affine and independent of x_t, delete that residual and substitute
x_t=-epsilon*L everywhere else. Restriction and this unique restoration
are inverse maps of the common integer zero sets. Affine substitution
preserves the degree-at-most-two bound on every residual.

Finally, a sum of squares of integer residual values is zero iff each
value is zero. These three lemmas prove the stated zero-existence
transport without any bounded test or division by a nonunit.

## Four affine consequences in the 250-coordinate source

Use zero-based source indices. After the six credited preliminary
coordinate shears (and also after the new shear old x4=new x4-x0), let Q_i
be the residuals. Literal expansion gives

    Q21-Q6 = 4+4x10+8x11+4x21-x22+x37,
    Q73-Q71-4Q70-8Q68 = 12-6x3-8x84-4x85-x86+x89,
    Q119-Q117 = 3-2x107+2x148-x164+x166.

The old source row Q90 is already affine, with its unique x105 determined by

    x105=x10+x11+4x21+2x24+4x26+2x29+2x31+4x32+2x34
         +2x36+4x39+2x40+2x43+2x47+4x68+2x69.

The first three equations remove x37,x89,x166, giving 247 coordinates and
179 rows. Removing Q90 and x105 as well gives 246 coordinates and 178
rows. The latter substitution is denser: fewer variables does not mean fewer
expanded monomials. For the 76-step preconditioner, the exact affine
replacements differ and are printed in each finite certificate; the checker
verifies each current row before projecting it. Identical row labels or
similar displayed formulas are never used as a substitute for equality.

`RESTORATION.json` in each endpoint gives all 250 original source
coordinates as affine polynomials in the final coordinates. Inverse row
operations identify every pulled-back source residual with its explicitly
reconstructed row. This is a universal polynomial identity, not merely
an implication checked on some tuples. The finite checker imports no producer
and verifies all final quartic coefficients, exact degree, coordinate
liveness, and complete metrics. Five deliberate corruptions must fail.

## A stronger stopping certificate: affine polynomial multipliers

For the 178 residuals R_i in 246 variables, form the integer matrix M
whose 178*(246+1)=43,966 columns are the degree-2-and-degree-3 coefficient
vectors of

    R_i, x0*R_i, ..., x245*R_i.

(The ordering in the audit places R_i last in its block, which is immaterial.)
The independent `macaulay_rank.py` obtains full column rank modulo the prime
1,000,003. Singleton-column elimination is exact, and the remaining sparse
Gaussian elimination uses field arithmetic only. A duplicate-residual
negative control must lose rank. The pinned receipt records the precise
pivot split and equation hash; these are not inferred from floating point.

A full-rank minor modulo a prime is a nonzero integer minor. Therefore M
has full column rank over Q. Consequently there are no affine polynomials
L_i, not all zero, for which sum_i L_i R_i has degree at most one.
This extends the previous constant-multiplier quadratic-rank obstruction to
ALL affine polynomial multipliers, including nonlinear row combinations
x_j R_i. It also rules out affine-coefficient syzygies among these residuals.
It is not a global lower bound for quartic representations. Degree-two or
higher multipliers, semantic transformations, different source circuits,
and different variable encodings remain outside the conclusion.

The matrix ignores residual constants: they contribute only degree zero
or one after multiplication. It is invariant in rank under invertible
integral affine coordinate changes and invertible constant row-basis changes.
No conclusion about Con(ZFC) is obtained from this rank computation.
