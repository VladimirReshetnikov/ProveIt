# Independent arithmetic review of the signed-growth report

Reviewed by the alternative-research agent, separately from the report's
author and the direct-quartic emitter. This is an internal mathematical
review, not external peer review or a proof-assistant certificate.

Reviewed file: `report/signed_growth.tex`.

SHA-256 of the reviewed revision:
`5080b8d2163c7bf80667fe8a169b60e68909a721d7ff2a379d360e7aef54de10`.

**Result:** no gap found in the new sign bootstrap, lowered horizon bounds,
or cofinal completeness construction. The finite coefficient counts and
row operations are covered by the direct package's independent exact
checker; this review concentrates on the unbounded arithmetic interface.

## Sign recovery and the square frame

For every integer z, t=2+4z has exact 2-adic valuation one. The retained
equation F=2^19 t(2u+1) therefore gives exact valuation 20 and the signed
bound |F|>=2^19|t| before any Pell classification. In particular both
F/64 and F/128 are integral on every zero, not only on the chosen cofinal
slice.

I compared the retained frame with source216 and its membership checker.
It has 34 actual square atoms, includes F^2 and the actual affine radix
D=2(C+F+1), and covers every base, nominal exponent, and output of the
15 surviving power requests at the 13 principal Pell pairs. Thus
W=2+sum(atom^2)>=2+F^2>258 before signs are recovered. The inherited
odd-frame, anchor-cap, and signed-orientation arguments use this threshold,
|A|>W^W, and |A-1|>4W^3. They do not require t>=16, 4|t, or positivity
of t or F. The separate growth pair at center 4t+1 does not belong to
that common family and requires no additional common-frame atom.

The order D nonzero -> x>=0 -> x>=1 -> |q|>=2 -> t>=2 is valid.
The retained exponent is literally t, not t+1. Recovering y>0 and then
x>=2 gives |q+1|>=3, allowing F+t>=0 and C>=0 to be inferred; |F|>t
then excludes F<0. The anchor excludes C=0. No positive-center growth
estimate is applied on a negative-t branch.

## The numerical replacements at t>=2

The depth-19 square-shell estimate has only leaves below t and constants
0 and 1 as premises. Its bound L=8^(d-1)t^d, d=2^19, is valid at t=2.
For a=4t+1, the congruence Y_n(a)=n modulo 4t together with the exact
2-adic valuation gives n>=dt. The growth ratio needed for

    F >= (8t)^(dt-1) >= L^t

is exactly 8^(t-1)/t>=1. There is no missing large-t estimate.

Since d>=2, L>=t^2, so

    F >= L^t >= t^(2t) >= (t!)^2 >= lcm(1,...,t)^2.

At t=2, L=2^(4d-3), hence F>=L^2>=2^(8d-6)>2^32.
The positive endpoint gives x>=2+(t+1)y and y>=F. Therefore
2+t+y+F<x follows from (t-1)y>t. The inherited local majorant is
consequently below (2x)^(2^23)<2^x. The last inequality holds for every
x>=2^32: if 2^n<=x<2^(n+1), n>=32, then
2^23 log_2(2x)<2^23(n+2)<2^n<=x.

## Cofinal completeness

The progression t=2 modulo 2^23 is cofinal within the new affine horizon,
and bit 20 of t is zero. For n0=dt, y0=Y_n0(4t+1), and
a0=X_n0(4t+1), the quotient b0=y0/(dt) is an odd integer and
a0=1 modulo 4.

The residue-permutation argument is valid, including its r=0 step.
At h=2^r, v2(Y_h(a0))=r, X_h(a0)=1 modulo 4, and the Pell norm imply
X_h(a0)=1 modulo 2^(2r+2). The addition formula makes the two index
lifts produce the two distinct output lifts modulo 2^(r+1).
Periodicity follows from the same formula, providing arbitrarily large
positive odd s in the required residue class. The selected F then satisfies
F=2^20 modulo 2^ell with 2^ell>t. Its binary support is disjoint from
t, so binom(F+t,t) is odd.

The beta-spacing multiplier remains independent and can supply both
prime support and the magnitude required by the finitely many pending
states. Prime support up to t suffices for pairwise coprimality of
1+iy, 1<=i<=t+1. The argument does not incorrectly demand t!|y,
which would be incompatible with fixed v2(y)=20 for large t.
All later choices remain acyclic: beta code, CRT representatives, even
dominant anchor, radix and outputs, then common Pell witnesses.

## Two scope corrections retained in the release

The rejected witness fusion with h=t+1 forces y=F^2/(dh). The correct
capacity obstruction compares a canonical state with its own beta modulus:
every such modulus is at most 1+hy=1+F^2/d, while a state with two
positive labels has weight at least (1+F)^2>1+F^2/d. Requiring each
state to be below y would be unnecessarily strong. This obstruction
invalidates the proposed inherited completion, not every possible future
encoding with fewer variables.

No impossibility theorem for a univariate consistency polynomial is
claimed from mere Con(ZFC). Such an argument would require a stronger
soundness assumption or the external truth of that polynomial's
nonsolvability; consistency alone does not license rejecting every
false existential arithmetic theorem of a theory.

The signed-horizon modification preserves the refutability predicate by
soundness and cofinal completeness. It is not a pointwise polynomial
bijection with the former square horizon. Exact polynomial or integral
zero-set restoration begins only after the changed semantic source is
specified. The inherited C222/ZF/ZFC calibration is an explicit proof
dependency; this review does not replace it with a new formal build.
