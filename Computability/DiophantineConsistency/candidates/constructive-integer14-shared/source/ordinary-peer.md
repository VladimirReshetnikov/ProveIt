# Ordinary review of the constructive fourteen-integer component

**Accepted at the ordinary mathematical level.** The complete equations
have14 unrestricted integer unknowns and160 operations/degree540 or
147 operations/degree568. The first is now dominated by the separately
reviewed148/414 form. The147/568 point saves one operation at higher
degree and remains a different tradeoff. No global optimum is claimed.
This review is confined to `integer14/` in the immutable
`ConZFC_Constructive_Reductions_2026-10-23.zip`, SHA256
`37e6f0e8d46fec88df60eab7d4c4b5106fc321be1736763d5def910b8d0619e0`.
Its direct component is outside this review; nine-positive has a separate
accepted review.

## The changed root-extraction argument is valid at the weak scale

I read the complete104-file component's proof, builder and executed
verification path, comparing the formula to the actual front and norm.
All92 copied upstream files byte-match the previously reviewed root-fusion
subtree in `interpolation-shared-norms/source/inherited/root_fusion`.
All six full coefficient payloads are unchanged. The MF port was already
shifted; no second shift is introduced.

The explicit three-square guard forces v nonzero, G positive and eta*zeta
positive. The unit-product finalizer is valid even when the norm N is
negative: `(1+S)(1+N)=1` with S a square forces S=N=0. The pair lemma
uses nearest integer squares at the positive integer x+y-1; its squared
error is strictly smaller than that integer, which is at most xy.
Its reverse guard representation follows from Legendre applied to4n-3.

The exceptional cases do not create false zeros. For all integer inputs,
the literal residue restrictions give nonzero q and W, q=2 modulo3 and
|q|>=16. The even integer a gives Delta=(a+1)(a+3)>=3 and nonzero odd H.
When c=0 the last rational radicand is exactly1. Otherwise Q>=9,
Df>|c|+1 and V=Df*b-c is nonzero, so its radicand is positive and
delta=Q-1 cannot vanish. Thus multiplying by delta^8 loses no actual zero.

At a zero the guard gives K=|k|>=2 and
K(|Y|-1)<|c|<K(|Y|+1), in particular |c|>30. With |X|>=64,|Y|>=16,
the displayed estimates give d/|H|<|c|/2, tau>2|c| and f>2tau.
I checked the strict inequality used for the last estimate:
`m^2(x-4)-4m(x+2)+9>0` throughout x>=64,m>=16.
The auxiliary root is either between |c| and |c|+1, or exceeds2f,
according to whether b=cT-R is zero. These give the claimed strict
superincreasing orders in both branches. They use only Y=qv, before
any cubic-scale congruence has been recovered.

The signed-sum Galois argument therefore forces each of the four roots
to be rational, even when their square classes are dependent. The three
integral radicands give integral roots. For the remaining root, the
adjacent-Pell descent preserves its reduced denominator b: b^2 divides
Q-1, so the transformed numerator is unchanged modulo b and the new
V remains integral. For |V|>1 the new nonzero absolute V is strictly
smaller. At |V|=1 the root is1, proving integrality. This supplies the
unbounded descent that a finite norm calculation alone would not prove.

## Both CRT recoveries and both directions are justified

After extraction the literal factor equality, together with
gcd(H,4q^2)=1, recovers the odd cubic scale
v=q^2(2v_old+1). Reduction modulo H separately recovers the integral
main-Pell residue gamma=(d-b0)/H. The uncentered companion with modulus
2q^2 gives exactly the same two conclusions. Coprimality holds because
H is odd, H=3 modulo q and q=2 modulo3; it is not assumed of arbitrary
unrelated parameters.

The resulting roots satisfy the entire parent's normalized signed
kernel. I checked the strong-witness restoration identities, including
`c*j_old-R=V`, and the parity of the restored odd strong index. The
private guard witnesses may be regenerated. In reverse, the printed
formula for n is integral from the already known scale and gamma;
substitution makes the selected conjugate factor and the guard vanish.
There is no circular selection of n or the private positivity witnesses.

## Exact degree and independent finite checks

The four centered defect identities give formal root correction degrees
3,5,5,4, all below the center remainder's degree7. The16 factor degrees
are therefore eight25, four17, two13 and two7 in the centered case.
The last pair has nonzero leading forms U0*n and U0*(n+c). Including
delta^8 gives degree484 for N and then540 after the degree56 guard square.
The one-center companion has eight25 and eight17 factors, hence N has
degree512 and the final polynomial568. The explicitly selected leading
coefficients depend on beta alone and are positive at the actual tuple.
Thus the ordinary degree proofs do not presume that generic coefficient
specialization preserves a nonzero leading term.

I ran the complete scoped `verify.py` in normal and optimized Python in
`/tmp/proofs62ff-constructive-integer14-review`; both pass. They rebuild
both actual graphs, reconstruct every fixed integer from the943 tiles,
check495 norm coefficients and all four defects, and check the selected
leading coefficients. Each mode's72 modular transcription controls
include v=0 and c=0 branches. The verifier imports its builder, so I also
wrote an inert independent check: it imports only an earlier peer's
sparse-ring oracle, binds all six norm cut ports, and proves equality of
the entire literal tail with all495 coefficients of the cleared norm.
It authenticates all104 component files, all92 prior files, the whole
six-port tuple, topology and complete liveness. Both normal/-O modes pass.

Reproduce the independent check with `tools/review_constructive_integer14.py`,
an explicitly supplied fresh author `--replay-receipt`, and `--output`.
The separate JSON receipts embed both full scoped author results.
No incoming file, Lean source or canonical PDF/TeX was changed. The named
ordinary native/refutation calibration remains inherited; these checks
do not complete the internal object-ZFC proof or establish consistency.
