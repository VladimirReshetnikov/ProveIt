# An 80-operation fixed-index universal certificate

For every recursively enumerable set of positive integers, fixed positive
compiler numerals can be computed so that the system below has positive
integer witnesses exactly for its members. The complete straight-line
certificate takes **80=43M+37A**, with **33 positive existential coordinates
and 21 equations**. Numerals and equality comparisons are free; numeral
multiplication is charged.

This changes the native finite-state compiler in the
[81-operation proof](FIXED_RAW_UNIVERSAL_81_PROOF.md). The machine, exact
helical geometry, two markers, both temporal-alignment operations,
14-operation raw-input bridge and 43-operation Pell kernel are retained.
The new compiler has successor coefficient **DY=1**, removing precisely
the multiplication DY*P. The other two local coefficients remain fixed
positive numerals. This is a mathematical proof with symbolic and finite
checks, not a proof-assistant formalization.

The [complete source](../verification/explore_fixed_raw_universal_80.py)
and [receipt](../verification/explore_fixed_raw_universal_80.json) give the
full arithmetic ledger. The universal alphabet and its potentially enormous
fixed constants are defined effectively below; the checker does not claim
to enumerate that whole machine alphabet or materialize full Pell tuples.

## 1. Keep the actual window structure

Use the fixed stay-step machine and windows S3,E3 of the 81 proof. Its
underlying tile alphabet has some fixed finite size a. In Sections 1--3,
this a denotes the tile count, not the retained Pell coordinate. Enumerate its
allowed 3-by-3 windows as w0,...,w_(k-1), with End=E3 at index0 and
Start=S3 at index1. Here k>=2. Allowed-window membership is a decidable
finite test depending only on the fixed machine, so this enumeration and
all constants below are effective and independent of the raw input x.

The three-site relation is not an arbitrary table: it is precisely

    center[row,col+1] = right[row,col],  row=0,1,2; col=0,1,
    center[row+1,col] = next[row,col],   row=0,1; col=0,1,2.       (1)

All three windows must belong to the allowed alphabet. The exact lift and
helical theorem in the 81 proof already show that a cyclic word with this
relation at offsets0,-1,-h, unique Start at0, and End at x<N exists
exactly when the fixed machine accepts x. This includes the smallest
positive input, the unmarked short strips, and arbitrary h not dividing N.
The new compiler implements this same relation; it does not change it.

## 2. Native selectors and linked tile copies

Each native cell has Boolean selector bits z_i for the k allowed windows.
It also has 9a Boolean copy bits b_(r,c,s), recording whether the tile at
window position(r,c) is symbol s. These copy bits are not unconstrained
successor data: local center clauses force them to agree with the selector.

Choose a power of two A>k+1, with A>=4. Concatenate the following
homogeneous clauses in radix A:

* The selector occupancy e=sum_i z_i, with mask A-2. Since e<A, its
  mask vanishes exactly for e=0 or1.
* For each(r,c,s), the expression
  b_(r,c,s)+sum_{i:w_i[r,c]=s}z_i, with mask1.
  Once e<=1, each term is at most1. Evenness therefore says exactly
  that the copy bit equals the selected tile indicator.

The raw copy-clause values are at most k+1<A even before occupancy is
decoded. Write the concatenation as sum_l c_l z_l and its mask as mu,
where l runs over the selector and copy variables. Every c_l is positive.
Append zero-expression mask1 clauses if needed. They impose no additional
constraint but affect the population balance below.

Thus these center clauses permit either one genuine window with all its
copies correct, or no selector and all copy bits zero. Later horizontal
overlap propagates occupancy from the unique Start to every cyclic cell.
No condition concerning a neighboring selector is used to prove the
center-copy implication.

## 3. A separated layout with successor coefficient one

All positions in this section are exponents of an inner radix R, chosen
after the finite layout has been specified. Give selector i exponent i,
and define the copy exponents

    e(r,c,s) = T0+(2-r)3a+(2-c)a+s,   T0=k+3a.                (2)

The copies occupy the interval T0,...,T0+9a-1. Their reversed row and
column ordering makes multiplication by R^(3a) shift the bottom two rows
onto the top two, and multiplication by R^a shift the right two columns
onto the left two. A source left-column bit that crosses a row boundary
under the latter shift lands in a rightmost column, which is not tested
by the horizontal overlap mask.

Let

    m = popcount(mu)+12a.

Append enough zero-expression center clauses that m+2>=k+9a. Add exactly
m+2-(k+9a) ignored Boolean dummy bits at consecutive exponents above all
copy exponents. Let Emax include every selector, copy and dummy exponent.
The native cell therefore has exactly K=m+2 permitted Boolean positions.
Let their exponent set be E. The selector exponents0 and1 are reserved
for End and Start; every other position will be permitted in Z.

Choose, for example,

    H = Emax+3a+1,
    T = H+2Emax+a+1.                                      (3)

Here H,T are fixed compiler integers, not variable tableau dimensions.
Extend c_e by zero on dummy positions. Choose a power of two R satisfying

    R >= max(K*(sum_e c_e+4), mu)+2,
    B = R^(T+Emax+1) = 2^d.                               (4)

In particular mu<R. This matters when zero-expression clauses make mu
larger than the sum of the nonzero clause coefficients. Define

    DC = R^(3a)+R^(H+a)+sum_e c_e R^(T-e),
    DR = R^H,
    DY = 1,                                               (5)

where the last sum ranges over selector and copy positions. The native
cell word is Ccell=sum_{e in E} bit_e R^e. Define the mixed mask

    MF = mu R^T
         + sum_{r=0,1; c=0,1,2; s<a} R^e(r,c,s)
         + sum_{r=0,1,2; c=0,1; s<a} R^(H+e(r,c,s)).         (6)

The first part checks the center clauses, the second vertical overlap,
and the third horizontal overlap. The native remainder mask is

    MC = B-1-sum_{e in E\{0,1}} R^e.                      (7)

Its two excluded positions are the marker selectors. The native marker
contributions are CS=R for Start and1 for End. These are **selector
contributions**, not full window codes: every selected window also has
nine nonzero copy bits, and the copy bits of both marked cells live in Z.

### Exact isolation of every tested digit

For arbitrary native typed cells Ccell,Rcell,Ycell, put

    Fcell = DC*Ccell+DR*Rcell+Ycell.                       (8)

The following coefficient assertions hold before any local clause is
assumed true:

* At degree T, the coefficient is exactly sum_e c_e bit_e of the
  center cell. Off-diagonal terms in the convolution have degree
  T-e+f with distinct native exponents e,f, so only e=f contributes.
* At degree e(r,c,s), r=0,1, the coefficient is exactly the sum of
  center's(r+1,c,s) copy and next's(r,c,s) copy. These are the two
  terms tested by a mask1 parity check.
* At degree H+e(r,c,s), c=0,1, the coefficient is exactly the sum of
  center's(r,c+1,s) copy and right's(r,c,s) copy.

To check separation, the successor word has degree at most Emax. The
vertical center term has degree at most Emax+3a<H. The horizontal band
ends at H+Emax+a, while every center-clause convolution term has degree
at least T-Emax>H+Emax+a. All the non-clause terms have degree less
than T. Selector shifts remain below the copy masks by T0=k+3a;
shifted dummies remain above them. These inequalities also cover every
ignored native bit, not merely the genuine selector/copy bits.

The total raw coefficient mass of (8) is at most K*(sum c_e+4)<=R-2.
The highest possible degree is T+Emax, below the outer radix exponent.
Hence there are no inner-radix or outer-cell carries, even for multiple
selectors, malformed copies, or arbitrary dummy bits. In particular

    0<=Fcell<=B-2,   0<=Ccell<=B-2.                        (9)

The mask in(6) therefore tests exactly the center clauses and the two
overlaps in(1). Neighbor copy consistency need not be assumed in this
single-cell statement: it is enforced by their own center tests in the
cyclic system. This is why the argument does not repeat the unchecked
successor-plane failure of the omitted-alignment construction.

### Population and parity

The two overlap parts have6a bits each, are disjoint, and do not overlap
the clause block. Thus popcount(MF)=m. The low mask permits exactly
K-2=m native bits, so popcount(MC)=d-m. Moreover

    0<DC,DR,DY<B,  0<MC,MF<=B-2,
    MC odd, MF even, popcount(MC)+popcount(MF)=d.           (10)

All tested copy and clause degrees are positive, giving MF even. The
unit selector is forbidden by MC, giving MC odd. All quantities in
(2)--(10) are fixed numerals computed from the fixed machine alone.

## 4. The full 80 source and soundness

Use exactly the 33 positive existential coordinates and raw positive x
from the 81 proof. Keep all 21 equations, replacing only its transport by

    (DC+B*DR+P)C = F+z(q-1).                              (11)

The seven outer equations are therefore

    (B-1)J=q-1,                    P*v=q,
    (B-1)align=P-1,                C+alpha+d*x=q,
    (DC+B*DR+P)C=F+z(q-1),
    r=(q^2-Z-qF)(q^2-1)+(MC+q*MF)J,
    C=CS+Z+W.                                            (12)

The ten fixed-minus Pell equations and four fixed-base input equations
are literally those in Sections3--4 of the 81 proof. The supplied scale
is still D0=q^3. The checker expands all 21 complete source residuals;
there is no omitted digit, marker, power or period predicate.

Before interpreting powers, the positive-domain bootstrap of81 uses
only its geometry, marker decomposition, raw bound and the fixed bounds
on MC,MF. These are unchanged by(10). It gives

    q>=P>=B, 0<Z<C<q, 0<W<C<q, 0<d*x<q,
    0<F<q, q^2<=r<q^4.

The retained kernel and input bridge then recover, in their existing
noncircular order,

    q=B^N, P=B^h, W=B^x, 0<x<N,
    Z AND(MC*J)=0, F AND(MF*J)=0.                          (13)

Both alignment operations remain present; P is not allowed to be a
within-cell shift. The marker insertion is disjoint: Z has neither
marker selector at any cell, CS inserts Start at0, and W inserts End
at x. Consequently every C cell is typed by the native position set E,
before any consistency or occupancy conclusion is used.

Let Rword,Yword be the exact cyclic shifts C_(i-1),C_(i-h). Then

    Rword=BC-kR(q-1), Yword=PC-kY(q-1),
    Factual=DC*C+DR*Rword+Yword.

The no-carry bound (9) applies to these arbitrary typed words, so
0<Factual<q-1. Positivity uses DC*C>0. Equation(11) gives F congruent
to Factual modulo q-1; with 0<F<q this forces F=Factual.

Every cell's center mask now gives at most one selector and its exact
copy array. The horizontal overlaps force adjacent occupancies equal:
an occupied window has one copy bit at each physical window position,
whereas an empty window has all copies zero. Equality on any of the
six overlapping positions precludes one occupied and one empty cell.
Shift1 is one cyclic orbit, and Start is occupied, so every cell has
exactly one genuine selector. Both overlaps then give the exact fixed
window relation(1) everywhere.

The marker selectors occur exactly once at0 and x. The unchanged81
helical semantic theorem consequently yields a genuine halting run on
the raw input x. Copies cannot create a different marker state because
the selector-to-copy link is exact and the allowed windows are distinct.
This proves soundness for every positive solution.

## 5. Strictly positive completeness at the new constants

For an accepted x, take the padded helical word of the 81 proof, whose
N>=4 cells have unique Start at0 and End at x, with x<N. Use its selector
and nine genuine tile-copy bits at every cell, choosing dummy bits zero.
Set q=B^N, P=B^h, W=B^x and the positive geometry witnesses exactly as
before. Put Z=C-CS-W. This is positive: removing two selector bits leaves
the marked cells' copy bits, as well as all other genuine cells. Its low
mask vanishes and it is even. The field(8) has its mask zero and is positive.

Every genuine cell has a nonzero selector, so C>=J. Its bound (9) gives
C<=(B-2)J. Therefore the same estimates prove

    q-C>=J+1, J>=B^(N-1)>=B^x=2^(d*x)>d*x,
    alpha=q-C-d*x>0.

Both cyclic wrap quotients are positive: kR>=1 and kY>=align>=1.
The transport quotient is now z=DR*kR+kY>0, without a DY factor.
All seven outer equations hold at the newly computed packed index r.
By (10) and the vanishing masks, its binary population is 3dN, and it is
odd since Z is even, MC,J are odd, and qF is even.

The retained fixed-minus kernel supplies all 17 fresh positive kernel
coordinates at this actual r and scale q^3. The unchanged 14-operation
fixed-base bridge supplies positive kappa,mu,delta,phi,rho at its new
parameter, with index d*x. Its hypotheses d*x>=4 and d*x<q are satisfied.
Thus every one of the 33 supplied existential coordinates is positive,
including for x=1. No earlier numerical Pell tuple is reused.

## 6. Exact ledger and evidence boundary

The81 outer source computed kp=DY*P followed by kinner=Kconstant+kp,
where Kconstant=DC+B*DR is a fixed numeral. For this compiler DY=1,
so delete kp and compute kinner=Kconstant+P. This removes exactly one
multiplication and no comparison or supplied witness.

| Part | M | A | Total |
|---|---:|---:|---:|
| Geometry, transport, masks, raw bound register, markers |11|12|23|
| Retained fixed-minus kernel |25|18|43|
| Fixed-base raw-input bridge |7|7|14|
| **Complete certificate** |**43**|**37**|**80**|

No copy-bit population changes this ledger: copies and center clauses
are encoded inside fixed native numerals and the same two paid masks.
The fixed numerals become larger; their size is outside the chosen
complexity measure. All variable powers retain their counted construction.

The checker verifies the full 80 source, all 21 residuals and the inherited
acyclic norm correction. It audits each native input basis bit, including
dummies, against every tested coefficient: together with the proved raw
coefficient bound, this checks the absence of unintended contributions
on the entire typed Boolean cube. It also tests arbitrary malformed
native triples, complete genuine/empty triples on small window alphabets,
center-copy defects, and a larger alphabet requiring zero-expression
padding. The large alphabet's selector-subset sampling is explicitly
distinguished from the small exhaustive cases in the receipt.

The packed arithmetic examples use valid cyclic overlap words and the
same raw x, geometry, marker and transport equations as the complete
source. They check positive outer witnesses, exact mask population and
rejection of corrupted copy bits. Those small window sets are compiler
tests, not claimed enumerations of the actual universal machine alphabet.
The unchanged helical theorem and the effective full enumeration in
Section1 supply that universal step mathematically. Astronomical full
Pell witnesses are proved to exist, not numerically materialized.

Review status: author and independent complete proof/source reviews pass.
Fresh read-only verification matches the saved receipt. Additional
independent checks cover 1,500 malformed, linked and dummy-filled triples
with original tile alphabets of sizes 3 and 5. The default checker compares
its result with the saved JSON; only `--write` regenerates that receipt.
