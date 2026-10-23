# Independent review of the degree-901 positive carrier

## Verdict

The new ordinary mathematical reduction in `positive/PROOF.md`, Sections
3--8, is sound on independent inspection. The inner multiplier may indeed
be set to one. The exceptional-branch exclusions modulo Q replace the old
large radical separator; they do not hide an assumption that the roots
were already rational. The two new outer bounds are established from the
weak compiler interface before recovery. The claimed exact degrees 892
for the norm and 901 for the product follow from the displayed leading
branches, including the cancellation-sensitive degree-97 branch.

The endpoint remains conditional on the named inherited normalized compiler,
signed-quotient interface, and K215 calibration. This is not a new formal
proof-assistant certificate. This review did not reprove those endpoints.

## Root bounds and the main square

The identity (I sqrt(G))^2-(c sqrt(D))^2=I^2-c^2 is exact. Since I>=c^2
and c>=2, the denominator estimate in Section 3 gives

    I sqrt(G)-c sqrt(D)>I/(8Ec)=ic/(8E)>Y/8>1.

Also b+cf<d follows from the conservative positive estimates in the proof.
In particular b<5E^3I^2 and cf<2EI^2 together are below 6E^3I^2, whereas
d exceeds that last quantity. No decoded root or sign restoration enters
these estimates.

For every complex auxiliary root, the absolute-value estimate with
Z=b+Tcf gives |y|<Z+Z/d. Since Z<=T(b+cf)<Td, it follows that
|y|<b+ITg. Adding the first square root, which is smaller than g, yields
the strict inner-root ceiling b+(IT+1)g. The proposed negative main root
exceeds this ceiling. Actual quadratic conjugation then excludes an
irrational main root and gives a positive integral g and rational x.

## Exceptional branches and rational recovery

When C(x)=0, the factorization gives

    d^2 A^2-d e A+Q^2 v^2 b^2 D=0.

This is obtained by dividing an exact identity by 4 *before* reduction
modulo Q. Since d=e=-1 modulo Q, it implies Q|A(A-1), impossible because
1<A<sqrt(Q). Likewise x=0 implies Q|(A-1)^2, again impossible. Thus every
denominator in the subsequent rational formulas is justified. In particular
Baux>0 and d>0 were proved independently.

The formulas for f' and tau' are algebraically correct and produce rational
square roots of D and A; therefore they are integers. The special Pell
saturation lemma then applies to the rational auxiliary y. It is a genuine
integer-coordinate Pell argument, not a claim that arbitrary rational
Pell points are integral. The recovered gamma is positive because
g>(a+1)c and c>X. The source signed-quotient interface handles a negative
recovered f' by the documented simultaneous sign change of f' and T.

## Completeness

For canonical source witnesses, y>=|vf-b|. The full correction delta is
less than g because ell>2c, and the short correction is smaller still.
Consequently

    t=gamma+(IT+1)g+tau+y-b-delta

is a strictly positive integer. It satisfies the new carrier identity
exactly, without an extra Pell period or divisibility condition. Thus the
construction proves both directions, not merely soundness.

## Independent leading-branch calculation

After matching the sign of f with that of g, use

    delta_full-g = -ell + terms of degree -1,
    tau-ell = k/2 + terms of smaller degree,
    ITg-vf = iT c0/(2E0) + terms of smaller degree.

The four matched branches have degrees 107,107,105,97. The final degree-97
leader contains t+k0/2-iT c0/(2E0); t is independent and prevents it
from vanishing identically for any fixed positive beta. The four unmatched
branches each have degree119. Therefore the exact norm degree is

    4*119+107+107+105+97=892.

Their signed numerical multipliers multiply to -2^14, agreeing with the
stated leading form. The short correction subtracts 2c from the full one;
this changes only the special last branch, to degree101 and multiplier -4,
giving degree896 and multiplier +2^16. The independent nonzero leaders of
Nk and Nt add degrees7 and2. Hence product degrees901 and905 follow
uniformly, not merely for the toy coefficient rays in the finite checker.

The scalar norm evaluator is the same universal trace/remainder identity
already reviewed for the previous norm package, with the inner multiplier
specialized to one. The mod-4 unit guard remains valid for the new carrier.
