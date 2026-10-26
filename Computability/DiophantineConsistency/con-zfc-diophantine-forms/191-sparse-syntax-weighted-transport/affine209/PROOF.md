# Affine horizons for divisibility-forced Pell growth

## Result and exact comparison

The frozen parent is the incoming Pell Growth 210 packet, specifically
`equations/principal210/equation.json`, at repository snapshot
`d123610bc98fef2006bff1c9466bc3f1221003e7`. It has 210 unrestricted integer
variables, 150 quadratic residuals, degree four, 5,282 collected monomials,
and coefficient height 2^40. Its source and inherited proof boundary are
retained by that packet. The present construction changes its horizon and
then deletes one coordinate. This is a source-level existential equivalence,
not an identification of the two old and new zero sets.

Every resulting equation is literally the sum of the squares of the 149
quadratic residuals in its `equation.json`, with all 209 coordinates ranging
independently over Z. There is no inequality, variable exponent, or external
predicate in these final equations.

| Minimum m | Variables | Rows | Degree | Collected monomials | Height |
|---:|---:|---:|---:|---:|---:|
| 16 | 209 | 149 | 4 | 5,486 | 2^50 |
| 8 | 209 | 149 | 4 | 5,485 | 2^48 |
| 2 | 209 | 149 | 4 | 5,486 | 2^44 |

The m=16 version needs no decrease of the parent's positive-horizon
threshold. The m=2 version supplies the additional threshold estimates
below. These improve dimension and row count but spend coefficient height
and a modest number of monomials relative to the parent; dominance in all
metrics is not claimed.

## 1. The only semantic source edit

Fix m in {2,8,16}. Replace the old row

    t=16+4z^2

by

    t=m(2z+1),       z in Z.                            (H)

Retain every other source row. In particular retain the three growth rows,
with d=2^19,

    Z=tF,
    X^2-16Z^2-8ZF=1,
    F=d*t*(2u+1),                                     (G)

the affine radix D=2(C+F+1), the complete square frame, the C-anchor cap,
all 13 retained principal Pell pairs and all 15 exact-power requests.
Among them are q=D^x and the requests q^t and q^(y+1). These notations
describe certified meanings of the source's polynomial equations; they
are not operations in a final polynomial. The beta equations retained are

    y=F(2v+1),
    x=F+1+(y+1)r0,
    x=1+[1+(t+1)y]rt.                                 (B)

Here C is the actual even CRT representative, C=2c. Before sign recovery,
all these witnesses may be signed.

## 2. Recovering t without a positive-horizon assumption

Equation (H) immediately gives t!=0, |t|>=m>=2, and t even. The last
equation of (G), independently of its Pell norm, gives

    F!=0, F even, |F|>=d|t|>=2^20.                    (1)

Thus the existing square frame, which still includes F^2, satisfies its
required W>=258 before t or F is oriented. The parent's C-anchor proof is
valid with signed frame atoms and does not use the discarded quadratic
horizon row. It recovers all retained principal pairs at their canonical
signed nominal indices. Its signed exact-power lemma applies to every
base of absolute value at least two: it forces the requested exponent to
be nonnegative and the output to be the exact integer power.

Because C and F are even, C+F+1 is odd and nonzero. Hence D=2(C+F+1)
satisfies |D|>=2. The retained q=D^x request therefore gives x>=0.
Put g=1+(t+1)y. From (B) and (1), |y|>=|F|. Since |t|>=2,
|t+1|>=1, whence

    |g| >= |t+1||y|-1 >= |F|-1 > 1.

If x=0, the final equation of (B) would give grt=-1, impossible over Z.
Therefore x>=1 and |q|=|D|^x>=2. Apply the retained q^t request. Its
signed exact-power lemma gives t>=0. Equation (H) excludes zero, so

    t>=m.                                             (2)

This order is essential. No classification of the standalone growth Pell
equation at the potentially negative center 4t+1 is used. No unproved
growth estimate for signed t is required. The initial linear divisibility
alone gives the size needed to activate the existing q^t sign certificate.

For m=16, the complete incoming proof now applies at its stated positive
horizon threshold, except that completeness chooses the new cofinal
progression. Sections 3 and 4 justify the smaller m=2,8 profiles as well.

## 3. Growth and source bounds for every t>=2

After (2), set a=4t+1>=9. The norm in (G) is the ordinary Pell equation
X^2-(a^2-1)F^2=1. The parent's classification gives |F|=Y_n(a) for n>0.
Its elementary congruence and valuation identities are

    Y_n(a)=n mod (a-1),    v2(Y_n(a))=v2(n)  (a odd).

Since 4t divides F, it divides n. Since F=d*t times an odd number,
v2(n)=19+v2(t). It follows that the positive integer n/(4t) has valuation
17, hence n>=dt. The recurrence bound Y_n(a)>=(2a-1)^(n-1) yields

    |F| >= (8t+1)^(dt-1) >= (8t)^(dt-1).              (3)

Let L=8^(d-1)*t^d. The actual deepest constructor has depth 19. The
source's four square-shell constructors obey, for 0<=r,s<=M,

    E(M,M)+1=8M^2+14M+8 <= 8(M+1)^2.

Every leaf is a local parameter <t or one of the constants 0,1. For t>=2
each leaf plus one is at most t. Induction on constructor depth therefore
bounds every local label strictly below L. This proof is valid for t=2;
it does not use the rougher threshold-16 estimate.

The ratio (8t)^(dt-1)/L^t is 8^(t-1)/t, at least one for every positive t.
Thus |F|>=L^t. In particular |F|>t. The parent's remaining front bootstrap
uses q^(y+1), the beta endpoints, and the base-(q+1) request of exponent
F+t to derive y>0, x>=2, F>0, C>0, D>0, q>0, and

    x>=2+(t+1)y,     y>=F,     x>=F+1.                 (4)

Those steps use t>=2 and |F|>t and remain valid verbatim. Consequently
F>=L^t with positive F, and the sharp product-separation theorem decodes
the same exact multisets of formula labels.

For clarity, every additional threshold estimate used by the incoming
source is recovered as follows.

* F>=L^t>=t^(2t)>=(t!)^2>=lcm(1,...,t)^2, since d>=2. This directly
  supplies the generalized factorial-free binomial-CRT selector radius.
* At t>=2, L>=2^(4d-3), so F>=2^(8d-6)>2^32. Thus x>2^32. The inherited
  fixed local-polynomial estimate Local<(2x)^(2^23)<2^x is valid at this
  same large-x threshold. To check the first comparison's size premise,
  F>=t^2, y>=F and t>=2 give t+F<ty; hence
  2+t+x+y+F < x+2+(t+1)y <=2x by (4).
* C>F+t>t>=2 follows from the authenticated largest-index cap. The affine
  radix D=2(C+F+1)>2C and q=D^x give exactly the parent's binomial digit
  bound C^x<q/2^x. With x>2^32, all its low-tail margins, including q/32
  and q^k/32, are stronger than required. No bare t>=16 estimate is used.
* All range exponents remain at most x by (4), and every required frame
  atom remains present. No canonical-index or range inequality is dropped.

This identifies the replacement estimates rather than assuming that an
old proof remains valid after lowering a parameter.

## 4. Cofinal completeness in the new progression

Starting with a finite C222 refutation, choose t large enough for all its
steps and local parameters, subject to the following congruence. Write
m=2^r, where r is 1,3 or 4. Choose

    t = m mod 2^(r+22),    t>0.                       (5)

These horizons are cofinal and satisfy (H), with
z=(t/m-1)/2 an integer. They have v2(t)=r and their binary digit at
position 19+r is zero. Let n0=dt, y0=Y_(n0)(4t+1) and a0=X_(n0)(4t+1).
The parent's congruence and valuation calculations give

    b0=y0/(dt) odd,     a0=1 mod4,     v2(y0)=19+r.

Choose L0>r+22 with 2^L0>t. The parent's proved residue permutation
s -> Y_s(a0) modulo powers of two gives an arbitrarily large positive
odd s such that

    (t/m)b0 Y_s(a0)=1 mod 2^(L0-19-r).

Then F=Y_(n0*s)(4t+1)=y0Y_s(a0) satisfies all growth rows with integer
u=(F/(dt)-1)/2, and

    F=2^(19+r) mod 2^L0.

The supports of the binary expansions of F and t are disjoint, so
binom(F+t,t) is odd. This is exactly the parity required for the even
CRT anchor. A positive odd multiplier containing every odd prime <=t
supplies y=F(2v+1); choosing it sufficiently large also bounds all finite
pending-multiset states. The squarefree beta-spacing lemma establishes
pairwise coprimality of the beta moduli without requiring t! to divide F.

Choose the beta code x, then B=binom(F+t,t), N=B^x and the independent
CRT representatives as in the incoming construction. Because N is odd,
C can be even, positive, and arbitrarily large in its residue class,
dominating every requested index. Put D=2(C+F+1), then q=D^x. Finally
choose the shared Pell frame and its private comparison witnesses. The
selection order and every remaining equation are those of the frozen
incoming proof. This constructs a zero of the modified source from each
finite refutation, with no consistency assumption.

## 5. Exact passage to the literal 209-variable equations

At the final 210-variable endpoint, t is coordinate 0, the former horizon
parameter is coordinate 178, and the unique horizon residual is row 125.
Replace that row by t-m-2mz. In every other row substitute t=m+2mz, delete
the replaced zero row, and delete coordinate t. Renumber the other
coordinates in their previous order. The inverse simply restores
t=m+2mz. This is an exact integer bijection for the modified system.

The new source modification commutes with every inherited algebraic
reduction from the 216-variable semantic source: all five common-Hessian
directions have zero t and z components; their omitted equations and
restoration maps do not use the horizon; the following affine projection
uses only local syntax rows; none of the 79 final coordinate or residual
operations changes t, z or the horizon row. The independently implemented
`verify.py` tracks every renumbering and checks those exclusions against
the frozen certificates. It also reconstructs every substituted
coefficient with a binomial formula, independently expands each sum of
squares by unordered term pairs, and checks every final coefficient,
dimension, exact degree, liveness assertion and metric. Both normal and
optimized Python runs give the same results.

Combining Sections 1--4 with the explicitly retained C222/ZF/ZFC
calibration proves, in ordinary mathematics formalizable in ZFC,

    ZFC proves: (there is no integer zero of Q209) iff Con(ZFC).

The result proves the equivalence, not consistency or absence of zeros.
The finite checker authenticates the new polynomial arithmetic and
source binding; it is not a kernel proof of the unbounded inherited
calibration, and no fresh end-to-end Lean/Rocq build is claimed.

## Attribution and further directions

Signed affine horizons are credited to the incoming Signed Horizons and
Residue Carriers packet. Divisibility-forced Pell growth and the affine
radix are credited to the incoming Pell Growth 210 packet. The new step
is their noncircular composition: a linear lower bound from divisibility
activates q^t before the standalone Pell center is oriented. The threshold
extension to t>=2 and its complete coefficient instances are also supplied.
Worldwide priority or global minimality is not asserted.

The new horizon lemma is compatible with a different numerical syntax
provided the replacement constructor majorant is proved. Such a change
could substantially reduce the local arithmetic circuit; it is distinct
from the present one-coordinate reduction and requires its own calibration.
