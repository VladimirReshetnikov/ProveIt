# Independent review of oriented reciprocal pooling

Reviewed 25 October 2026. This is a separate AI-assisted mathematical and
finite-algebra review, not external human peer review or an end-to-end
proof-assistant check.

## Verdict

The theorem in `proofs/ORIENTED_POOLING.md` is correct with the
stated bounds, including zero bases. The specialization keeps all shared
source polynomials unchanged and restores every deleted private certificate.
Its parity bootstrap is noncircular. The complete emitted residual lists and
all six inherited projections have passed an independently written checker
which imports no producer code.

The parent is package173's `source/anchor221/equation.json` at ProveIt
commit 02a78a08603cbae248c19c23a75907c6c6bd6443. The retained Pell
orientation, bounded-frame theorem, numerical C222 calibration and ZF/ZFC
refutation equivalence are inherited dependencies. This review validates
the new reduction relative to those dependencies.

## Why the arithmetic theorem works

For T_n=2An-n^2-1, the sign of n/T_n is the sign of A whenever n is
nonzero. Its absolute denominator exceeds W^W. When n=0, T_n=-1 and the
weighted reciprocal term is identically zero. This permits the theorem to
authenticate the nonzero blocks without assuming all bases are nonzero.

The exact identity is E_j=sum delta_i^2+T_j sum Y_i^2, with
delta_i=m_i-X_i+(A-n_j)Y_i. The main certificate therefore makes the
weighted sum of squared errors over T_j an integer. Multiplication by
C^2, where C is the product of n_j^b over nonzero blocks and
b=floor(sqrt(W-1)), clears all negative indices in the proof. The canonical
Pell congruence makes the resulting small-error weighted reciprocal sum
an integer too.

For at most five blocks and at most 64 requests, its numerator in absolute
value is at most 4r*b^(12b+1), strictly less than W^(6b+2)<=W^W.
Every nonzero summand has the same sign. Hence the integer sum has absolute
value below one, is zero, and every error vanishes. This proves every
nonzero-base exact power. Unit bases are allowed with signed indices;
nonunit bases force nonnegative indices. No coprimality among the T_j is
required. The apparent product C is proof notation, not a hidden variable
or an operation in the delivered polynomial.

The Pell congruence for negative indices is valid: evaluation of the
norm-one quadratic-ring unit A+s at s=n-A modulo T_n gives n, and n is
invertible because T_n=-1 modulo n. Thus the proof uses a finite-ring
identity rather than an unjustified interpretation of negative powers.

## Bootstrap without changing the parent

The first base is t=128+4h^2 and the growth index is K=t^4. Both are
positive, so the active t block immediately gives F=t^K, which is even.
The encoded index C is literally twice an integer. Consequently the
retained relation B*mu=C+F+1 has odd right side and forces B to be odd and
nonzero, without knowing the sign of C.

The original H is 2+4 times a sum of actual integer representatives. Thus
H is 2 modulo four and |H|>=2, even before signs are known. The BH block
is now active and has a nonunit base. It gives x>=0 and q=(BH)^x.
If x=0, q=1; otherwise q is a nonzero even integer. Thus q is never 0
or -1, and both q and q+1 are nonzero. The theorem now authenticates all
remaining blocks. The temporary case q+1=-1 is harmless: the unit-base
statement already suffices to restore its old polynomial certificates.

This ordering avoids both potential circularities: proving B nonzero by
using an unproved sign of C, or assuming a radix progression to activate
the q+1 block. No new H formula, radix restriction or CRT completeness
argument is needed.

## Exact zero-set maps

From a new zero, restore each singleton modulus T and its quotient
-delta/T. Restore each old same-base pool by L=E/T and
K=2H_j+(2A-n)L. The proof establishes integrality of every restored value.
All old shared coordinates are fixed. This is an existential inverse on
the solution set, not a globally polynomial map on arbitrary assignments.

There is an especially simple polynomial map in the forward direction.
At an old zero, each singleton satisfies delta=-TQ. Therefore
E/T=TQ^2+Y^2. In the five-base construction choose

    z=sum_(first three blocks) n_j(T_j Q_j^2+Y_j^2)
        +q L_q+(q+1)L_(q+1).

For the split construction choose z0 as the first sum and
z1=L_q+L_(q+1). These expressions are integer polynomials in old
witnesses. This forward direction does not require invoking the parent's
full logical interpretation.

## Independent coefficient verification

The independent checker reconstructs the singleton E_j using the alternative
identity delta_j^2+T_jY_j^2+2n_jY_j(Z_j-AY_j), so the crucial cancellations
and actual AY offsets are checked. It verifies each old singleton row up
to its literal sign, including the negative convention for the third
modulus row. It recomputes both old pooled E_j from their complete source
rows, verifies all private-coordinate occurrences and compares every
coefficient of each new reciprocal residual with the emitted raw source.

For each common-radical projection it explicitly expands the integral shear
x_i=u_i+d_i s. It checks that s occurs only linearly with constant slope,
the selected slope is a unit, and the supplied restoration solves the
actual pivot equation. This is independent of the producer's directional
derivative implementation. It then verifies the final affine consequence,
its unit restoration, the repeated omitted row, every final coefficient,
the surviving variable identities and the liveness of all coordinates.

Measured outputs:

| Profile | Variables | Residuals | Exact degree | Residual monomials | Largest residual coefficient |
|---|---:|---:|---:|---:|---:|
| Five-base | 206 | 145 | 24 | 26,146 | 95,232 |
| Split | 207 | 146 | 16 | 1,914 | 95,232 |

The first has 144 quadratic residuals and one residual of exact degree 12.
The second has 144 quadratic residuals, one of degree 8 and one of degree 5.
The sum-of-squares polynomial has exactly twice the largest residual degree:
over the real numbers its nonzero top homogeneous squares cannot cancel.
These residual-coefficient figures are not the coefficient heights of the
fully expanded final polynomials.

The independent checker also recomputed every coefficient of the supplied
207-variable degree-16 expansion: 94,294 collected nonzero monomials and
coefficient height 13,607,065,661. It rejected three actual modified inputs:
a changed pooled coefficient, an omitted retained source row, and a changed
pivot restoration. The 206-variable final sum of squares is specified by
its complete residual list; no full collected expansion of that polynomial
is claimed to have been produced or checked here.

These results trade higher degree for fewer variables. They are not quartic
records, global variable minima or literature-wide priority claims. The
signed orientation idea was anticipated as an open extension in package168;
the active-zero-base theorem, parity activation, and completely emitted
five-base and split specializations supply the completed result here.
