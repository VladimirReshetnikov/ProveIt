# Sharing the history decoder across centered relator forms

For r>=1, the two centered form producers of each relator can be
computed with5M+5A, after one shared5A history decoder. The current
direct four-coordinate producers cost8M+8A per relator. The resulting
local saving is

    3r M+(3r-5)A, or6r-5 total operations.                (1)

For r=1 this trades three multiplications for two additional additions,
saving one operation. For larger r the shared cost is amortized further.
All coefficient products, including zero and unit products in the
uniform template, and both additions of the existing center are paid.
The signed input polynomials are unchanged for every integer runtime
assignment. This is a local proof/count result, not a complete emitted source.

Root proposed decoding the common histories before applying the sparse
right basis. The five-addition decoder was already available in the
older decoded alternative in the relator-plane note; the new use here
is sharing it across all unselected centered-form producers.

## 1. Existing fixed recipe and runtime cut

For a fixed relator P=[p,q;s,t] in SL2(Z), the inherited right invariant
is w0=(2q,p-t,-2s). If it is nonzero, divide by its positive coordinate
gcd to obtain primitive w, and apply a fixed coordinate permutation so
w1!=0. Choose

    g=gcd(w1,w2)>0, a*w1+b*w2=g,
    u=(w2/g,-w1/g,0), v=(-w3*a,-w3*b,g).                 (2)

Undo the permutation in both rows. The original-order right matrix is
V=[u;v]. As established in the three-form and quotient notes, it is the
same V used to prepare the fixed action matrices E and T. No new basis
change or altered action coefficient is introduced here.

Write

    C=[1,0,0,-1;1,1,0,-2;2,0,1,-4],
    h=(H4,H5,H6,H7)^T,
    ell_1=u*C, ell_2=v*C.                                (3)

The existing shared center W=lambda*D*J has already been paid outside
this cut. The two old output polynomials are

    A1=ell_1*h+W, A2=ell_2*h+W.                           (4)

They are produced once for the relator and used by both of its signed
selector slots. Their direct implementation retains all eight fixed
coefficient products, six dot-product additions and two center additions,
giving8M+8A. This note retains the same ordinary runtime histories and W.

For P=+/-I2, keep the existing convention u=(1,0,0),v=(0,1,0), E=0
and T=I2. Do not normalize a zero invariant. The form polynomials and
their guarded native consumers remain present in the uniform template.

## 2. One common five-addition decoder

Compute the following five records once, independently of the relator:

    c1=H4-H7;
    k=c1-H7;
    c2=k+H5;
    k2=k+k;
    c3=k2+H6.                                            (5)

Thus

    (c1,c2,c3)^T=C*h
      =(H4-H7,H4+H5-2H7,2H4+H6-4H7)^T.                  (6)

Every coefficient2 in this schedule is implemented by the displayed
addition k+k, not an uncharged multiplication. The decoder costs5A
and uses no runtime coefficient products or division. These are signed
computed words; they need not be positive, even when every H_i is
strictly positive. They are not added existential inputs or native lanes.

## 3. Sparse right rows, including every fixed permutation

For a noncentral relator let(i1,i2,i3) be its chosen original-coordinate
indices corresponding to the permuted coordinates in(2). The first
row has possible nonzero entries only at i1,i2; the second has possible
nonzero entries at all three indices. Prepare the five fixed integers

    U1=w2/g, U2=-w1/g,
    V1=-w3*a, V2=-w3*b, V3=g.                            (7)

Every exact division here is fixed integer preparation. The runtime
schedule is

    x1=U1*c_(i1); x2=U2*c_(i2); L1=x1+x2; A1=L1+W;
    y1=V1*c_(i1); y2=V2*c_(i2); y3=V3*c_(i3);
    L2first=y1+y2; L2=L2first+y3; A2=L2+W.                (8)

The first dot product costs2M+1A, the second3M+2A, and the two final
center additions2A. Hence(8) costs5M+5A. The fixed permutation selects
which already computed c register appears in each product; it is a
static register alias, not a supplied permutation or free arithmetic
transformation. The resulting polynomials are u*C*h+W and v*C*h+W
in their original row order, precisely(4).

Negative coefficients and zero coordinates of w cause no omitted
operation or sign charge: all five products use their signed fixed
integers. For the central case use(i1,i2,i3)=(1,2,3) and

    (U1,U2)=(1,0), (V1,V2,V3)=(0,1,0).

Equation(8) then still computes the old central forms. Retained products
by zero make this a valid uniform upper schedule even in degenerate
cases. No claim is made that every such product is semantically needed
or that every fixed coefficient is nonzero.

### A canonical recipe can fix all runtime wire choices

Root also proposed a particular allowed preparation that avoids a
per-relator wire permutation in a future source. For noncentral P,
let k be the first nonzero coordinate of the original primitive w,
and use only the transposition(1,k) before applying(2). Undo that same
transposition afterward. Then the resulting original-order u always
has third coordinate0. If k=1 this is the displayed formula(2). If
k=2, then w1=0 and the permuted row is(0,-sign(w2),0), which becomes
(-sign(w2),0,0) in original order. If k=3, both w1,w2 vanish; the
permuted row is(0,-sign(w3),0), and swapping coordinates1,3 leaves it
(0,-sign(w3),0) in original order. The central row u=e1 also has this
property.

With this canonical recipe the uniform runtime forms can always use
u1*c1+u2*c2 and v1*c1+v2*c2+v3*c3, with all five original-order
coefficients precompiled. This has the same5M+5A cost. It is a valid
choice of the inherited preparation, not a free change to some already
prepared different V. A same-polynomial parent/child comparison using
this option requires ell,E,T, all ell-based guard constants and both
producers to use this same canonical V. The general fixed-permutation
proof above remains valid without this restriction. Examples using only
the identity permutation
would not by themselves audit that general source grammar.

## 4. The positivity recipe continues to use ell, not the sparse roles

For any original-order three-entry row b=(b1,b2,b3), its four history
coefficients are exactly

    b*C=(b1+b2+2b3, b2, b3, -b1-2b2-4b3).                (9)

Continue preparing nminus and pplus from all eight ell coefficients
per relator, exactly as in the guarded two-form note:

    nminus=max(0,all -ell_(j,i)),
    pplus=max(0,all ell_(j,i)),
    lambda=nminus+1, Cg=2lambda+1,
    K>max(Cmass,m,Cg,lambda+pplus), K dyadic.              (10)

The recipe can compute these fixed integers using(9), even though the
eight ell entries are no longer used as runtime multiplication ports.
They must not be replaced in(10) by maxima of the five entries in(7).

The shared decoder may have negative coordinates off or on the guard.
The native theorem uses A1,A2, not c1,c2,c3. Because(8) equals(4) for
every integer runtime assignment and(10) is unchanged, the existing
global guard Cg*(D*J-S)=Ztot+g still proves A1,A2 positive and below
the lane scale before native projection. The former off-guard warning
about A1,A2 also remains unchanged; no unconditional positivity is
being inherited for any signed producer word.

In a complete splice preserving these fixed recipes, all existing
consumers receive the same A1,A2 polynomials. Thus the selected-action,
native-lane, history and ordinary-input arguments transfer by polynomial
identity. This local note does not itself emit or audit that splice.

## 5. Paid boundary, retained schedules and counterexample

The total new producer cost is5r M+(5r+5)A versus8r M+8r A, proving(1).
The existing W producer, its guard and all selected offset recovery
remain outside both compared cuts. There are still52+4r selected fields,
62+6r native lanes and96+6r positive witnesses; no additional supplied
coordinate or comparison has been introduced. For r=0 emit no new
decoder and retain the existing fallback.

At the quotient-action interface the eight ell multiplication roles per
relator can be replaced by five sparse-basis roles, with the fixed
coordinate permutation recorded as recipe data. E and T still come
from the very same V. This suggests6+15r fixed roles instead of6+18r
for that interface, but a full source must authenticate the actual role
set and recipe binding; this is not a claim for arbitrary independent
assignments to old and new fixed coefficient ports.

**Remark 1 (retained valid six-addition proposal, credited to root).**
The initial decoder w=H7+H7,k=H4-w,c1=k+H7,c2=k+H5,k2=k+k,c3=k2+H6
is correct and costs6A. It gives the valid total5r M+(5r+6)A, saving
6r-6 operations against the direct producers. Equation(5) computes c1
first and then k, saving one shared addition. The six-addition schedule
was not false and is retained as a distinct valid comparison.

**Remark 2 (refuted substitution of sparse-coefficient guard bounds).**
For the central convention u=e1,v=e2, all sparse coefficients are0 or1.
Using their negative maximum would incorrectly suggest lambda=1 and
Cg=3, whereas ell_2=(1,1,0,-2). Take H1=...=H6=1,H7=10, so S=16,
and D=17,J=1,Ztot=0,g=3. Then the modified guard3*(17-16)=0+3 holds,
but the second formed input is A2=1+1-2*10+17=-1. Thus those altered
guard numerals do not guarantee native positivity. This is a concrete
counterexample at the local guard/producer interface, not a complete
compiler zero or a failure of the unchanged recipe(10). Its actual
ell-based lambda for this single central relator is3, not1.

**Open question 1 (composition and further sharing, credited to root).**
Emit and independently audit this same-polynomial replacement in the
current complete compiler, including the shared decoder, every fixed
permutation, all five coefficient roles and unchanged guard recipe.
Only that complete source can incorporate the local saving. Further
reuse or special coefficients may give other schedules; five additions
for the displayed decoder and5M+5A per relator are upper bounds here,
not generic arithmetic-circuit lower bounds. No numerical universal
relator list or new whole-compiler bound is claimed.

## 6. Provenance and execution boundary

Root proposed the shared-decoder producer route and its valid6A/5M5A
schedule, and later supplied the canonical-transposition option above.
The author checked the exact identities, reused the earlier five-addition
decoder, derived the final incremental ledger and supplied the local
counterexample to changing the guard bounds. Root read the complete
204-line draft and independently checked its mathematical and paid
interface claims, requesting no correction; he then read and passed the
canonical extension, including all three cases and the same-V correlation.
Aristotle read the complete232-line final mathematical draft and separately
challenged the decoder, sparse supports, permutations, central padding,
counts, signed domains, guard counterexample and canonical extension.
His challenge also passed with no correction. Neither proof challenge
is a complete-source or coefficient-array audit.

All new work is handwritten algebra and paid instruction accounting.
Dependencies were read as inert text. No supplied, archived, committed,
predecessor or frozen helper was run or imported; no saved scientific
source or coefficient array was evaluated or degree-propagated. No
scientific sampling, emitter or build was used. Any companion metadata
is fresh byte/read-span bookkeeping only. New files remain in/tmp;
repository files, Git and all earlier frozen artifacts are unchanged.
