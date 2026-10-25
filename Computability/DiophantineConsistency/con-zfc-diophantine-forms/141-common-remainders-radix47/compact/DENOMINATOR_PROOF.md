# Carrier denominator replacement after staged first-index recovery

This is a mathematical extension of the incoming archive
`ConZFC_Certificate_Reductions_2026-10-25.zip` at repository commit
`55d1f72aedebf892e446c90d35fa1ae37689b0f2`, not a literature-wide novelty claim.
The incoming archive's compact/PROOF.md is the parent proof. Its notation
is retained except that `D` in the carrier is replaced. The first-Pell
base remains `P0=2XY^2+1` and the polynomial `E` remains unchanged.

## General lemma

In the parent construction let `D` be any positive polynomial value such that

    D > 2,  q^4 | D,  D | 4 X Y^2.

Keep every parent definition except the carrier denominator. Put

    M = h D H,
    Z = h D [H(n-LB)+Kpos] - H[DB+h e],
    RG = M^2 G,
    P = Q(Z^2-RG V^2) + RG - Z^2.

This polynomial has a positive zero if and only if the parent native
refutation condition holds. The conditions on D are required for all
positive input assignments, not merely calibrated zeros.

### Soundness

Product-square extraction, Pell folding, and the first norm are unchanged:
`z=Z/M` is an integer, `G=g^2`, and `z=epsilon*g*y`; `c=psi_A(p)`;
`k=2psi_P0(n0)`; `k>=8XY^2+4`; and `b>c`, `V>0`.
Only the rational term rho changes to `e/D`. The identity `b-e>0`
still gives `rho<b/D`. For both original weights `L=V^2` and `L=bV`,
`g*y<L/2`. If B<=-1, then the parent's transport calculation gives

    n < L/2 - L + b/D < 0,

since V>b>1 and D>2. Thus B>=0 and C>0. The same main-index recovery
then gives p=R and 3q<R<q^4-2.

Clearing hH in the integral-carrier identity gives `D | h H e`.
Because q^4|D, gcd(q,h)=1, and H=-1 modulo q, it follows that q^4|e.
The first-Pell congruence gives k=2n0 modulo 4XY^2, hence modulo q^4.
Also P0>A and c=kY+eta force 1<=n0<R by monotonicity. Therefore

    q^4 | 2n0-R-1,    |2n0-R-1| < R < q^4,

so 2n0=R+1. Return to the full Pell congruence to get 4XY^2|e.
The last hypothesis on D now implies D|e: rho is integral.

At this stage the remainder of the parent's soundness proof is literal:
H|hKpos, whole-product projection gives X=2^R, then kappa integral and
h|B, followed by the fixed-minus/rounding/native calibration. No
coprimality of D with h or H is asserted or needed.

### Completeness

Use the parent's canonical outer data and first Pell witnesses. The
recovered first index yields e a positive multiple of 4XY^2. Therefore
e/D is a positive integer. Choose the parent's fresh strong and auxiliary
Pell witnesses and set

    n = g*y + W*t + e/D - kappa.

The parent proves g>kappa, while y>=1, Wt>=0, e/D>=1. Hence n is a
positive integer and gives P=0. This fresh completeness argument avoids
assuming that a rational or integer shear preserves positivity.

## Concrete denominators and exact finite metrics

D=XY satisfies q^4|D because X=wq and Y=q^3s; it divides 4XY^2.
It is computed using the same two multiplication gates as the parent:
replace `Y2=Y*Y; V0=X*Y2` by `D=X*Y; V0=D*Y`. No operation is added.
The carrier uses D, while V0 (and therefore the entire first norm) is
identically unchanged.

D=q^4 satisfies the hypotheses and needs one additional square of the
already-computed q^2. It gives a cost/degree tradeoff.

| Weight | D | Positive unknowns | Live binary operations | Exact degree |
|---|---|---:|---:|---:|
| V^2 | Y^2 (parent) | 10 | 78 | 630 |
| V^2 | XY | 10 | 78 | 626 |
| bV | Y^2 (parent) | 10 | 79 | 468 |
| bV | XY | 10 | 79 | 464 |
| V^2 | q^4 | 10 | 79 | 622 |
| bV | q^4 | 10 | 80 | 460 |

The 79/622 point is dominated by the 79/464 point and need not be advertised
as a frontier improvement.

For exactness, put q0=beta J, k0=eta+zeta, t0=T+alpha. The complete leading
homogeneous forms are inherited from the parent's unique top summand:

* XY, V^2: `2^14 q0^378 w^48 s^110 i^20 k0^64 t0^4 (q0-F-alpha)^2`.
* XY, bV: `-2^10 q0^284 w^36 s^82 i^14 k0^46 t0^2`.
* q^4, V^2: `2^14 q0^378 w^46 s^108 i^20 k0^64 t0^4 (q0-F-alpha)^2`.
* q^4, bV: `-2^10 q0^284 w^34 s^80 i^14 k0^46 t0^2`.

All are nonzero for the authentic beta>0. For V^2 the unique top term is
Q Z^2; for bV it is -Q RG V^2. Degree drops cannot be explained away by
unexamined cancellation.

## Scope

The source package's named unbounded Pell, native, and refutation
calibrations remain dependencies. The finite builder verifies graph
well-formedness/liveness and propagates degrees; it does not constitute
an end-to-end formalized ZFC theorem. A targeted textual search through
the downloaded active source and incoming archives found no earlier
`D=XY` or `D=q^4` version of this staged-index carrier; this is not an
exhaustive mathematical priority search.
