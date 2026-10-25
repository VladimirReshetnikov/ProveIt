# Independent audit: spherical digit guards

Status: **the mathematical replacement is accepted**, for the literal coefficient-two
sphere variants, including scaled merging and the odd-square radix refinement
below. The complete named-coordinate transformations for all twelve emitted
endpoints passed independent normal and optimized replay; see
`SIGNED_TRANSFORM_NORMAL.json` and `SIGNED_TRANSFORM_OPTIMIZED.json`. This is an ordinary mathematical audit, not an
end-to-end proof-assistant certificate.

The inspected baseline is round 17 `direct/strict_dimension/guarded.json`, with
its three complete proof notes. Its eleven interval products comprise:

* denominator `pow4.output = q^t`: exact binomial remainder and encoded-index
  range remainder (two);
* denominator `pow6.output = q^(t+1)`: four constructor-parameter ranges and the
  derived-label range (five);
* denominator `pow11.output = q^(y+1)`: the two accumulator ranges (two);
* denominator `pow14.output = q^x`: the two strict beta-quotient ranges (two).

## 1. Precise replacement lemma

For each group with common positive integer denominator D and at most seven
remainders, replace its old product guards by

    D^2 - 2 sum_i r_i^2 = u^2 + v^2 + w(w+1).

All variables here are unrestricted integers. The right side is nonnegative,
because w(w+1) is nonnegative at every integer. Hence 2r_i^2 <= D^2 and
|r_i| <= D/sqrt(2) < 3D/4 for every member. This implication does not depend on any other
remainder already being interpreted.

Suppose the retained digit equation gives r_i = T_i modulo D, where T_i is the
genuine low base-q tail and 0 <= T_i < D/8. Then

    |r_i - T_i| < 3D/4 + D/8 = 7D/8 < D.

The difference is an integer multiple of D, so r_i=T_i. In particular each
remainder is natural and below D. Its old slack, if retained, is consequently
D-1-T_i >= 0. If that slack and its monic definition are projected out, they
can instead be restored with this same integer value.

For completeness, genuine tails satisfy

    2 sum_i T_i^2 < (m/32) D^2 <= (7/32) D^2 < D^2.

Thus the integer D^2-2 sum_i T_i^2 is nonnegative. The inherited universal
ternary representation of every nonnegative integer supplies u,v,w. No
positivity of the new auxiliary coordinates is required.

## 2. Uniform low-tail estimate

Let D=q^k, with q>=2 and k>=1. If 0<=c_j<=q/16 for every j<k, then

    T/D = sum_(j<k) c_j q^(j-k)
        <= (q/16)(1-q^(-k))/(q-1)
        < q/(16(q-1)) <= 1/8.

This is a strict inequality even when the last weak inequality is an equality.
Zero upper arguments cause no exception: binom(0,0)=1 and the higher
coefficients vanish. The coefficient bound must use max(1,a), not a, there.

## 3. Noncircular factorial bootstrap

Retain the round-17 initial guards on factorial remainder r, factorial slack s,
and exact-binomial output slack o. They give B=r+s+1>=1 and q=B+o+1>=2.
The unchanged signed-Pell orientation and power schedule then supplies, before
any remainder is decoded,

    t>=16, F>=1, B>=2, V0=(F^2+1)^t <= FB < B^2,
    x>=2+(t+1)y>=6, H0>=1,
    N=B^x, q=(B H0)^x, N divides q.

For M>=1 and 0<=j<=t,

    binom(M+t,j) <= (M+1)^t.

Proof: induct on t. For j<t, Pascal's identity and the induction hypothesis
bound the two terms by 2(M+1)^(t-1)<=(M+1)^t. For j=t the product formula
gives product_(i=1)^t (M+i)/i <= (M+1)^t. The t=0 case is immediate.

Apply M=F^2. Since x>=6 and B>=2,

    c_j <= V0 < B^2 <= B^x/16 <= q/16.

The factorial tail therefore satisfies T<q^t/8 **without assuming F=t!**.
Its spherical guard identifies its remainder first. The retained exact digit
equation is

    (q+1)^(F^2+t) = r + q^t (B + q z).

After r=T, division by q^t gives B=c_t modulo q. Both B and c_t lie in [0,q):
for B this is the retained output-slack guard, and for c_t it is the estimate
above. Thus B=binom(F^2+t,t). The inherited square-output fixed-point theorem
now gives F=t!.

This order avoids the potential circularity in using factorial-dependent
derived-label estimates before recovering the exact factorial digit. A sphere
shared by the factorial remainder and another still-uninterpreted remainder is
harmless, because each individual squared term is bounded independently.

## 4. Remaining ranges

Only after F=t! is known, retain the round-17 index-congruence argument giving
the separate encoded-index representative C0>=1 and hence H0>=2. Ordinary
upper arguments a>=0 satisfy max(1,a)<=H0, and their lower indices k satisfy
1<=k<=x. Therefore for j<=k,

    binom(a,j) <= max(1,a)^k <= H0^x = q/N <= q/16.

For the derived label h, the inherited constructor ledger and encoded-index
repair give h<=H0^ell, ell=4194304. The already proved factorial and endpoint
bounds give ell(t+1)<x. Its coefficients through k=t+1 are therefore also
at most H0^x=q/N<=q/16. All remaining low tails satisfy the same strict D/8
bound and are recovered from the spheres.

For a range equation `(q+1)^a = r + N D z`, write the exact numerator as
`T + c_k D + q D H`. Since r=T and N divides q, division by D gives
N divides c_k. This is exactly the inherited range-binomial premise; no sign
of z was used to prove it. Since the numerator and its expansion are natural,
the resulting quotient is also natural. All deleted interval signs can thus
be reconstructed, and the old local-range/Horn/calibration argument applies.

## 5. Deliberate failure controls

The coefficient 2 and the small-tail argument are substantive. Replacing 2
by 1 admits D=9,T=1,r=-8, congruent modulo D, with slack 17>=0. Keeping 2
but assuming only T<D admits D=9,T=8,r=-1, with slack 79>=0. Both have a
negative noncanonical remainder. These are not counterexamples to the proposed
construction; they show why its exact inequalities must be documented.

## 6. Merging adjacent denominator levels

The emitted merged variant uses D1=qD0 and introduces two exact multiplication
coordinates z0=q*r0 and zC=q*rC. Its first sphere groups z0,zC with the five
remainders at denominator D1. Its seven true scaled tails are all below D1/8.
The same inequalities therefore prove completeness. For soundness the sphere
gives |q*r0|,|q*rC|<3D1/4, so q>0 gives |r0|,|rC|<3D0/4. The original
modulo-D0 uniqueness argument applies unchanged. The two explicit product
rows keep every residual quadratic.

## 7. Replacing the output guard by an odd-square radix

The `_odd` variants remove only guard2 and impose q=(2z+1)^2 instead. Thus
q>=1, not initially q>=2. The correct noncircular schedule is:

1. The unchanged signed frame, cap and joint coordinate-orientation proof
   supplies canonical signed-index principal pairs without any q sign premise.
   Since t>=16, its already canonical pair directly interprets
   V0=(F^2+1)^t, including the base-one case. The retained factorial
   remainder and slack guards imply F>=1, B>=2 and y>F+2.
2. The actual representative requests have base q+1>=2, so the negative-index
   power lemma forces each representative to be nonnegative. Hence H0>=1.
3. The request at base B*H0>=2 forces x>=0 and q=(B*H0)^x. The two
   unchanged endpoint equations then give x>=F+1>=2 and
   x>=2+(t+1)y. Consequently q>=B^x>B and q>=2.
4. Complete the remaining power interpretations. The old output slack
   o=q-B-1 is now automatically nonnegative. All sphere/factorial arguments
   above apply, with no use of that reconstructed slack in steps1--3.

For completeness choose x even in its beta-CRT class: y=V0(V0-1) is even,
so all beta moduli and their product are odd. Adding the product changes
parity and permits an arbitrarily large even representative. The later
representative modulus N^2 is odd, because F=t! makes each factor
1+F^2/i odd. Their parities can therefore be chosen independently. Choose
a and b with opposite parity as before, so the semantic anchor h is even;
choose one other representative parity so the total of the nine representatives
is even, giving H0 odd. The standard dominant a representative may still be
chosen in [2N^2,4N^2), with its prescribed parity. These choices preserve all
CRT congruences and the previous anchor-size proof. Both B and H0 are odd
and x is even, so the exact integer

    z=((B*H0)^(x/2)-1)/2

supplies q=(2z+1)^2. The zero or negative x cases have already been excluded
in soundness, and no parity assumption was added to arbitrary witnesses.

## Scope

This audit validates the new unbounded guard lemma and its noncircular placement
in the inherited direct proof. It does not independently reprove the inherited
Pell-classification, factorial-fixed-point, Horn-refutation, or numerical
C222/ZFC-calibration theorems. It cannot establish global optimality or ZFC
consistency. Exact coefficient files, compiler transformations and counts require
their own complete finite checks.
