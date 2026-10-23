# Independent mathematical review of the new constructions

This is an ordinary mathematical audit, not a proof-assistant certificate.
The repository baseline is ProveIt at
`ae3007ca4467011e0e051c84acb4a1dd13971b0e`. The audit checks the new
reductions while retaining the explicitly declared inherited compiler,
Pell, Jones-ratio, and K215/refutation calibration theorems.

## Twelve positive unknowns, degree 1097

Reviewed `audit_algebra/COMPACT_NORM12_PROOF.md` and its final sharpening
`SHIFTED_NORM12_PROOF.md`. The accepted construction uses

    h_old=q+h,        W=I(T+I),       L=1+HW.

The weak bootstrap is noncircular. Before any eliminated root is recovered,
transport gives R>3q and R<q^4-2; the index-unit equation and supplied
positive h give h_old>=q+1. The useful exact identity is

    (q+1)EY-q^4(E+Y)=qE(Y-q^3)+Y(E-q^4)>=0.

It follows that c>Ra+(R-1)Y>R(a+5), and therefore
`ac-R Delta` is a strictly positive integer. Since c+R<I^2, the auxiliary
constant b satisfies b<acI^2. Both exact squared comparisons in the norm
proof were independently expanded and checked:

    d I^2 G-Q c^2 D
      =I^2[Delta^2(I^2-c^2)-G]>0,
    d G-Q a^2 c^2
      =(Q-1)+(QH-Delta)c^2>0.

These prove the improved auxiliary-root bound without presupposing a Pell
root, its sign, or consistency. The conjugate argument remains valid when
an auxiliary conjugate is imaginary: it uses `|y'|^2=|y'^2|`. A field
automorphism may change several radical signs simultaneously; the triangle
inequalities bound all those changes, so no independence of square classes
is assumed. The coefficient used to recover f is strictly positive.

The completeness restriction is justified separately. In a genuine source
solution, n=(R+1)/2>=3 and

    k>=2 psi_P(3)=8P^2-2>32E^2Y^2.

Hence old h=(k-R-1)/E>R>q and new h=old h-q is positive. This establishes
existential equivalence without treating a one-way coordinate restriction
as a pointwise polynomial identity.

The stated degree ledger, nonzero leading monomial, and unchanged operation
count are coherent: norm degree 1088, product degree 1097 in 116 binary
operations, shifted three-equation system at 110 operations, and sum of
squares degree 2176 at 118 operations. The final norm parity argument is
unchanged by either the weight or h shift. No unrestricted-integer extension
of this new positive construction was used in this audit.

## Seventeen unrestricted integer unknowns

Reviewed `audit_small_variables/SIGNED17_PROOF.md` and its generator.

The sign guards work because each new Pell factor is 1 modulo 4 and is
coprime to the product of its predecessors. If the product is a square,
unique factorization makes each absolute factor a square; a negative square
cannot be 1 modulo 4. The factors therefore are positive squares. Nonzero
guard parameters then force the six nonnegative coordinates and positive
margin. Conversely, Pell units can be raised to a power whose secondary
coordinate is divisible by any prescribed modulus, giving the guard
parameters without simultaneous-Pell solvability assumptions.

The signed-h proof initially had a potential ordering risk: the packed R
need not be positive for arbitrary large g. The final proof resolves it by
first deriving g<G/8 from the positive margin. Its subsequent estimates
q>1+B+g and q^3>b*ell give R>=2 before C>0 and K>0 are used. The
consecutive-square argument then forces h>=1. The i sign can be normalized
because the relevant ratio predicates depend on i only through its square.

The denominator JF is universally nonzero, independently of guard signs.
For the homogeneous degree-five polynomial obtained from

    Pi(t)=(t^3-t-1)(t^2+23),

nonvanishing follows from the absence of rational roots. Intersectivity
holds at every prime power: the odd unramified cases use the cubic's
Frobenius/discriminant alternative, p=23 uses the simple cubic root 3,
and p=2 uses -23=1 modulo 8. The valuation argument remains valid at p=23;
its additional coefficient valuation only raises the nonleading term.
It forces divisibility of the original dividend by the original denominator.

If the combined denominator S vanished, the final polynomial would become
the nonzero eighth power T^8. This excludes all zero guard parameters and
i=0 together. The three-root norm's weights separate all nonzero sign
patterns, including complex radicals and dependent square classes. A
rational encoded sum therefore forces all three roots to be rational and
then integral. The completeness proof chooses the final integer root
coordinate after imposing divisibility; no unproved sign condition remains.

The finalizer lemma is an existential equivalence in its last coordinate u.
It should not be read as saying that arbitrary u satisfies the polynomial
once the square/divisibility predicates hold. The proof and final theorem
use the correct existential statement.

## Low-degree unrestricted-integer lifts

The accompanying `ODD_SCALE_LIFTS_PROOF.md` gives the independent synthesis
of package 20's low-degree lifts with package 23's odd-scale theorem.
It yields 51 variables at degree 4, 42 at degree 6, and 36 at degree 8.
The exposed-quotient quartic gives both congruences needed by the negative
scale proof directly, so no unchecked division is used to recover T.

All three generated packets select the entire compact 943-tile tuple from
package 19. Its exact compressed/raw coefficient hashes, bit lengths,
mask congruences, and population identity were checked locally. The transfer
argument explicitly recovers the odd canonical scale, square power scale,
and odd auxiliary multiplier. The source 4094-tile binding remains only in
unchanged parent files as provenance.

## Evidence boundary

The audit found no new mathematical gap in the stated reductions. It does
not independently reprove every inherited compiler theorem, rebuild the
Lean/Rocq K215 endpoint, establish a global variable/degree optimum, or
prove Con(ZFC). The claimed equivalences within ZFC compose the new
reductions with the identified ordinary mathematical source theorems.
