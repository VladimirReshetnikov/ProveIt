# Recovering signed remainders from canonical digit margins

## 1. Result and source boundary

The isolated radius endpoint in `audit261/equation.json` is an ordinary polynomial
equation over **261 unrestricted integer variables**. It is the sum of the squares
of its **185 literal quadratic residuals**. Its total degree is exactly four,
its collected support has **5,377 monomials**, and its largest absolute coefficient
is **128,446**. Every declared coordinate occurs. The adjacent
`expanded_polynomial.json` supplies every collected coefficient.

The input is the fixed `strict_dimension/factored_source.json` from
`ConZFC_Cofinal_Anchors_Height_One_Round17_2026-10-25.zip`, present in the inspected
ProveIt commit `e0c98c629bf10d30b695884f6b1d2ab361bdf513`. The corresponding complete
signed source theorem is stated in the copied `proofs/PROOF_315.md`,
`proofs/ORIENTATION_FIRST_PROOF.md`, and `proofs/STRICT_BUDGET_PROOF.md`.
They identify the retained C222/ZF/ZFC refutation calibration. The new reduction
changes only eleven remainder bounds and their eleven product sign certificates.
Every other source residual is retained exactly, before integral coordinate
projection and translation.

With that explicitly inherited calibration, ordinary mathematics formalizable
in ZFC proves

    P261 has an integer zero  <=>  a finite ZFC refutation exists.

Negating gives the requested ZFC-provable equivalence between integer
unsolvability and Con(ZFC). No consistency assumption, global minimality theorem,
or new end-to-end proof-assistant derivation is asserted. The new contribution is
the uniform small-digit margin before factorial interpretation and its use to
replace eleven interval certificates by four radius certificates.

## 2. The arithmetic available before the removed interval signs

The source first orients its signed Pell pairs and recovers its exact powers.
That part of its proof does not use the eleven delayed interval sign graphs.
The three front sign graphs for the factorial remainder, factorial slack, and
exact-binomial output slack remain untouched. Thus, before any factorial or
binomial interpretation, the following facts are available:

    t >= 16,
    V = (F^2+1)^t,
    B = r+s+1 >= 1,       BF = V+s,       r,s >= 0,
    q = B+o+1 >= 2,       o >= 0,
    y = V(V-1),
    x = F+1+(y+1)u0 = 1+[1+(t+1)y]ut,
    K=x,
    N=B^K,               q=(B H0)^K,
    H0=1+sum(the nine actual CRT representatives).

The source's canonical signed-power lemma first gives x>=0 and then its endpoint
rows give u0>=0, x>=F+1>=2, ut>=1, and

    K=x >= 2+(t+1)y.

Each actual CRT representative is a nonnegative integer, because it is the
exponent of an exact power with base q+1>=3. A stored shifted coordinate may
still equal -1; no positivity of that shifted coordinate is needed.
Consequently H0>=1.

From BF=V+s and V>=1, F>=1. Since V>F^2, B>F and B>=2. Moreover

    V <= BF < B^2.

Put ell=2^22. The retained literal constructor majorant gives, for the derived
label J and n=max(a,b,c,d),

    J <= (max(1,n)+1)^ell <= (2H0)^ell.

This inequality is valid even if all the ordinary representatives are zero; it
does not invoke the later proof that the encoded index is positive.

There is considerable exponent slack **before** proving F=t!. Namely

    V >= 2^t >= 2^16,
    y >= 2^16(2^16-1) > 2^31 > ell,
    K >= 2+(t+1)y > ell*t+4,

and K>=6. These estimates use only F>=1 and t>=16. They are the part that prevents
a circular appeal to factorial semantics.

## 3. A uniform bound for every low binomial coefficient

Set U=BH0>=2, so q=U^K>16. There are eleven numerator requests with positive
lower indices k<=K. They fall into the following four denominator groups:

| Numerator requests | Denominator | Group size |
| --- | --- | ---: |
| factorial upper index F^2+t; encoded row index | q^t | 2 |
| a,b,c,d,J | q^(t+1) | 5 |
| S,Sp | q^(y+1) | 2 |
| u,vq | q^x | 2 |

For every request and every 0<=j<k, we claim

    binom(n,j) <= q/16.                                      (1)

For an ordinary nonnegative representative a<=H0, including a=0, the elementary
bound binom(a,j)<=max(1,a)^j gives

    binom(a,j) <= H0^(K-1) <= q/B^K <= q/16.

For J, its lower index is t+1, so j<=t. Using B>=2 and K>=ell*t+4,

    binom(J,j) <= max(1,J)^j <= U^(ell*t) <= q/U^4 <= q/16.

The special factorial numerator is n=F^2+t. For integers z>=1, h>=1 and
0<=j<=h, the inequality

    binom(z+h,j) <= (z+1)^h

follows by induction on h for j<h using Pascal's identity, and for j=h from
the product formula binom(z+h,h)=product_(i=1)^h(1+z/i). Apply it with z=F^2
and h=t. Then, without assuming F=t!,

    binom(F^2+t,j) <= V < B^2 <= q/B^(K-2) <= q/16.

This proves (1) for all eleven requests.

For D=q^k, define the canonical low residue

    r0 = sum_(j=0)^(k-1) binom(n,j) q^j.

By (1),

    0 <= r0 <= (q/16)(D-1)/(q-1) < D/15,                    (2)

because q>16. In particular all coefficients used here are smaller than q, so
the expression is the ordinary residue of (q+1)^n modulo D. This argument
uses only already recovered exact powers and their raw size margins.

## 4. The radius lemma

Let D>0 and let r_1,...,r_m be arbitrary integers, with m<=5. Suppose each
r_i is congruent modulo D to a known r_i^0 satisfying 0<=r_i^0<D/15. Consider
the single equation, with three new unrestricted integers a,b,c,

    D^2 = 4 sum_(i=1)^m r_i^2 + 1 + a^2+b^2+c(c+1).        (3)

For every integer c, c(c+1)>=0. Hence (3) implies |r_i|<D/2 for every i.
If r_i differs from r_i^0 by a nonzero multiple of D, then

    |r_i| >= D-r_i^0 > 14D/15 > D/2,

a contradiction. Thus every r_i equals its canonical nonnegative residue.

Conversely, for the canonical residues and D>=17,

    4 sum_i (r_i^0)^2 < (4m/225)D^2 <= (20/225)D^2.

Therefore G=D^2-4 sum_i(r_i^0)^2-1 is a nonnegative integer. The classical
three-square theorem gives a,b,c with G=a^2+b^2+c(c+1): since 4G+1 is not of
the excluded shape 4^e(8h+7), write it as three squares. Modulo four exactly
one of the three entries is odd. Put it last, divide the two even entries
by two, and write the odd entry as 2c+1. This proves the stated representation.
Thus (3) has witnesses for all canonical residues.

This is an equivalence on the shared residue coordinates, after existentially
quantifying the new gap witnesses. It is not a test of positivity by a finite
sample, and it is not a claim that an arbitrary small integer is the required
residue without the congruences.

## 5. Exact replacement in the signed source

The old remainder rows and sign certificates were

    D_i = r_i+s_i+1,
    r_i*s_i = a_i^2+b_i^2+c_i(c_i+1).

There are eleven such pairs. Their three-square witnesses are private, and the
slack s_i occurs only in its displayed bound and product guard. The exact
constructor checks these occurrence conditions before deletion.

Retain the exact-power numerator rows. For the ten range requests their form
is (q+1)^n=D_i*N*Q_i+r_i, and for the factorial digit it is
(q+1)^n=D_i*(q*Q_i+B)+r_i. Hence they supply

    r_i = (q+1)^n modulo D_i.

Delete all eleven s_i and all thirty-three old sign witnesses. Group the
remaining r_i by their four identical denominators and impose one copy of
(3) for each group. This adds twelve witnesses and four quadratic rows.

For soundness, Sections 2-3 remain available because no removed interval sign
is used in the earlier Pell and power recovery. Section 4 now gives the
canonical r_i. Restore s_i=D_i-r_i-1>=0; its product with r_i is nonnegative,
so fresh three-square witnesses restore the old guard. Every other literal row
is unchanged. This restores a zero of the inherited complete signed source,
and its C222/refutation theorem applies.

For completeness, start with an old zero, or with its canonical construction
from a finite refutation. Its old interval bounds identify the same canonical
residues. Their uniform bound (2) supplies the four new gaps and their
three-square witnesses. Drop the eleven old slacks and thirty-three old guard
witnesses and retain every other coordinate. This produces a zero of the new
raw quadratic system.

The reverse-map argument also justifies use of the inherited Horn
factorization before this mutation: its certified transformations do not
touch the removed interval rows, and the constructor explicitly verifies that
none of the removed coordinates occurs in another residual.

## 6. Literal polynomial, projections and exact metrics

The retained source has 584 unrestricted coordinates and 408 quadratic
residuals. The radius mutation gives 552 coordinates and 390 residuals.
Every new residual is quadratic. An integral monic projection removes 291
coordinates and 205 residuals, leaving 261 coordinates and 185 residuals.
Each restoration is an integer polynomial, and its exact substitution is
checked to leave all residual degrees at most two. This preserves existence
over the unrestricted integers in both directions.

The final fixed integer translations are copied by coordinate name from the
parent's accepted centering. Translation is a polynomial bijection of the
entire integer lattice. The exact maps and their inverse convention
`old=new+shift` are supplied. Independently expanding the sum of squares gives
5,377 nonzero monomials, exact degree four and height 128,446.

The matched incoming parent has 282 variables, 192 residuals, 5,491 terms and
the same height. The achieved reduction is 21 variables, seven residuals and
114 collected monomials, at unchanged degree and coefficient height. This is
a comparison of these fixed equations; it is not a minimum over all
Diophantine representations.

## 7. Verification and logical limits

Finite checks bind the source bytes, all changed and unchanged rows, the exact
private-coordinate census, each projection restoration, all translations, and
every collected coefficient. Their role is exact algebra and artifact
authentication. The ordinary unbounded proofs above establish the new
arithmetic implications. The retained source theorem and C222/ZF/ZFC
refutation interfaces establish the final logical calibration. No finite
verification run decides Con(ZFC), and no fresh end-to-end formal assistant
build is claimed.
