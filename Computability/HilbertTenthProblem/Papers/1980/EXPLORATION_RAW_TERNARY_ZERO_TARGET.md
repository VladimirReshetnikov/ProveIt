# A 77-operation first-plus raw walk from 2x to zero

This is a specialization of the raw numerical two-track history, with
exactly **77 operations: 38 multiplications and 39 additions/subtractions**,
31 positive unknowns, and 21 equations. The sole positive parameter is x.
The input is the ordinary integer 2x, computed by the charged addition x+x.
The final counter value is zero. The first row is required, by the mask,
to increment; all later rows may increment or decrement. Counter values
remain nonnegative.

This is not a universal representation of a nontrivial input predicate.
Every positive x has such a walk: first +1, then -1, then 2x decrements.
The useful output is the typed entire sign history, which a separate
machine-control relation could restrict. No program routing, zero branch,
or halting interpretation is supplied here. In particular 77 is a component
count and does not replace the published universal bound.

The exact fresh source, primitive list, and receipt are in
`../verification/explore_raw_ternary_zero_target.py/.json`. The proof uses
the complete raw-track interpretation from
`EXPLORATION_RAW_TERNARY_MIXED_HISTORY.md` and the fixed plus-sign
general-scale kernel from `EXPLORATION_UNIT_TWO_TERNARY_KERNEL.md`.
All changed bounds, masking, endpoints, and parity hypotheses are checked
below; the proof does not reuse a square-scale or fixed-form assumption.

## 1. The complete system

Use positive outer unknowns

    q,J,W,H,v,T,F0,F1,G0,G1,FKplus,FKminus,alpha,alphaI.

The seventeen kernel unknowns are

    a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,gamma,y_aux.

As before the checker uses Jrep for J and ga for gamma. Define

    S=F0+F1, A=S-2J, delta=FKplus-FKminus, I=2x,
    P=FKplus+qG0+q^2F0+q^3G1+q^4F1+q^5FKminus,
    D0=q^6.

These are mathematical abbreviations for charged expressions, not free
supplied positive registers. The eleven outer equations are

    q=2J+1,                                      (1)
    q=Wv,                                        (2)
    H(W-1)=2J,                                   (3)
    FKplus+FKminus=2J+H,                          (4)
    3T=2J+H,                                     (5)
    F0+F1+alpha=q+J,                             (6)
    G0=F0+T, G1=F1+T,                           (7)
    I+(W-1)A+W delta=0,                          (8)
    I+alphaI=W,                                  (9)
    r=P.                                       (10)

Equation (7) has two comparisons. The zero in (8) is a fixed numeral,
not a positive existential unknown. Its evaluated left side can have
negative intermediate terms; this is allowed under the straight-line
certificate convention.

For the ten kernel equations, put

    U=wD0, Y=sD0, Q=UY^2,
    Delta=(a+3)^2-1=a^2+6a+8, J_pell=2r+1,
    u=J_pell+jc.

Then require

    Q(Q+1)k^2=tau(tau+1),
    c=Yk+eta, k=eta+zeta, k=r+1+hUY,
    a=Y(U+1), d=U+ac+gamma(6a+8),
    d^2=1+Delta*c^2,
    (ic^2)^2=Delta*(f^2-1),
    Delta*(f^2-1)(u^2-y_aux^2)=1-y_aux^2,
    u=c+of.                                    (11)

Here u is computed, not supplied. This is exactly the 43-operation fixed
plus-sign kernel. Its soundness has no assumption that r is even; its
positive converse requires even r, which Section 5 proves for every
canonical witness of the present relation.

The checker constructs all twenty-one source polynomials separately from
the schedule. The only nonidentity comparison is the retained acyclic
norm correction: source((ic^2)^2=Delta(f^2-1)) times u^2-y_aux^2. No field
typing or parity condition is hidden in a residual simplification.

## 2. Independent range and first-plus mask

The positive geometry and shared bound give, before any digit information,

    q>=3, W>=3, J=(q-1)/2, 0<H<=J, 0<T<=J,
    F0+F1<=3J, FKplus+FKminus=2J+H<=3J,
    0<F0,F1,FKplus,FKminus<3J,
    0<G0,G1<4J.

Indeed (3) excludes W=1, and W divides odd q, so W>=3. Neither the raw
track A nor its individual raw summands has yet been assumed nonnegative.
All six packed fields are positive, so P>q^5. The reordered word satisfies

    P=FKplus+q^5FKminus+(q^2+q)F0+(q^4+q^3)F1+(q+q^3)T
     <=(3J-1)q^5+(3J-1)q^4+(4J-1)q^3+q^2+(J+1)q+1
     <3(q^6-1)/2.                               (12)

The final upper-bound gap, with J=(q-1)/2, is

    q^5+q^4/2+3q^3-3q^2/2-q/2-5/2>0

for q>=3. Its expansion at q=z+3 has strictly positive coefficients;
the exact checker verifies that polynomial identity and coefficient list.

Thus D0=q^6,r=P satisfy

    D0>=729>=81, r>q^5>=243>27,
    r<3D0/2<2D0, D0<r^2.

The fixed plus-sign kernel's general soundness recovers U=3^(2r+1) and
D0 dividing binomial(2r,r). This step does not use r even. It follows
that q is a power of three. The independent geometry gives

    W=3^m, q=W^t, H=1+W+...+W^(t-1), m,t>=1.

The direct unit-two mask, in the strict range (12), therefore gives
P<q^6, lowest ternary digit two, and all other digits one or two.

Since FKplus<3J, its lowest native q-chunk forces FKplus<q: an overflow
would leave remainder at most J-2. The adjacent G0,F0 and G1,F1 pairs
then decode by the raw82 carry argument. Explicitly, if G_i>=q, its
native remainder requires G_i>=q+J. The next F_i carries one, but
F_i<3J makes a native next chunk possible only for F_i<=q-2; this gives
G_i=F_i+T<=q+J-2, contradiction. Each base field therefore has no
incoming carry and is below q. The last flag field, bounded by 3J,
also decodes without a carry. All six fields are native.

The first flag's unit digit is two while J's unit digit is one. Thus
the raw Kplus has unit digit one. The typed flag complement equation
then proves that the first row is a plus row. This is a changed and
explicit component semantics, not a free external promise about a
previously arbitrary sign history.

## 3. Ordinary numerical values and zero-target semantics

Subtract J from F0,F1,FKplus,FKminus. The resulting words A0,A1,Kplus,
Kminus are Boolean in radix three. The complement equation says
Kplus+Kminus=H digitwise, so every row has exactly one sign epsilon_j.
The two top guards give T=(W/3)H and force each A_i to be zero at the
highest ternary place of every row. At the least overlap with T, addition
would produce a forbidden zero digit in the native guard. Consequently
every ordinary row value

    a_j=(jth row of A0)+(jth row of A1)

is nonnegative and less than W/3. Digits of a_j may be zero, one, or two;
its numerical value is not a sparse binary reinterpretation.

The time equation expands as

    (2x-a_0)
    +sum_(j=1)^(t-1)(a_(j-1)+epsilon_(j-1)-a_j)W^j
    +(a_(t-1)+epsilon_(t-1))W^t=0.               (13)

The input bound gives 0<2x<W. The unit coefficient has absolute value
less than W, so reduction modulo W proves a_0=2x. The interior signed
coefficients also have absolute value less than W; successive division
by W proves all ordinary updates. The final coefficient is exactly zero.
Thus the system gives a nonnegative +/-1 walk from 2x to zero, of positive
length, and its first step is +1. Every decrement is valid: a decrement
from zero would require the next nonnegative row, or final zero, to be -1.
No intermediate counter is required to be strictly positive.

These arguments also prove the flag sequence and endpoint semantics for
every accepting positive solution. No parity assumption was used in
deriving them.

## 4. Why the smaller kernel is available without a cycle

Let a genuine walk have t steps. Its signed increment sum is -2x, so
t is even. Since W is odd,

    H=1+W+...+W^(t-1)=t modulo 2

is even. Also q is odd, and summing the six packed fields modulo two gives

    P=FKplus+FKminus+G0+F0+G1+F1
     =(2J+H)+2(F0+F1)+2T=H modulo 2.

Hence P=r is even. This is the only parity fact needed to construct the
fixed plus-sign kernel witnesses. It is established from an actual finite
walk in the converse, before any such witnesses are chosen. The soundness
proof in Sections 2--3 used the same kernel's parity-independent direction.
The argument does not infer a pre-mask evenness condition from an unproved
decoding assertion.

## 5. Full positive converse and an innocuous initial prefix

Take any nonnegative finite +/-1 walk from 2x to zero whose first step is
+1. Choose W=3^m large enough that every value appearing before a step is
less than W/3, and set q=W^t. Split each ordinary ternary input-row value
into two Boolean tracks, with digit two split as 1+1 and digit one split
in either order. Add J to form the positive native fields; add the top
mask T for the two guards. The two sign fields are the complementary
Boolean row-head sets, also shifted by J.

Both zero tracks and empty sign sets still give strictly positive native
fields. The whole raw counter word obeys

    A<= (W/3-1)H<=J,

so alpha=q+J-F0-F1>=1. Also alphaI=W-2x>=1. Every outer equation now
holds. The first plus head gives unit digit two in the first packed field;
the direct mask gives D0-divisibility. The range (12) verifies every
general-scale hypothesis. Section 4 proves r even, so the fixed plus-sign
positive converse supplies the sixteen remaining Pell auxiliaries for
the already fixed r,D0. Together with r these are the seventeen kernel
unknowns in (11).

Every nonnegative walk can be prefixed by +1,-1 at its initial value,
without changing its endpoints or violating nonnegativity. This only
establishes that first-plus is an innocuous restriction on bare walks.
A universal-machine use must separately implement and verify the same
prefix in its program controller; no such controller is implicit here.
In particular the explicit walk +1,-1 followed by 2x decrements shows why
the unconstrained existential endpoint predicate accepts every x>0.

## 6. Exact accounting and evidence

Relative to the complete raw82 component, first-plus packing changes
D0=3q^6,r=3P+2 to D0=q^6,r=P, removing two products and one addition.
Fixing the final value to zero removes the qFplus product and output-offset
addition. Loading 2x adds one charged operation, implemented as x+x.
Finally the proven even converse permits the 43-operation fixed plus-sign
kernel in place of the 44-operation parity-free kernel, removing one
product. The total is 82-3-2+1-1=77. The actual histogram, not just this
delta, is verified as 38 products and 39 additions/subtractions.

The receipt verifies all 77 primitives and all 21 expanded source residuals.
Its numerical phase checks 153 positive pre-power tuples, 429 complete
canonical walks with x from one through three and lengths up to twelve,
25 alternative splittings of the same numerical tracks, and 30 prefix/
cleanup families with x from one through thirty. Every canonical case
checks its raw row values, signs, first-plus condition, zero target,
nonnegativity, full field mask, even packed index and exact central-binomial
valuation. It does not materialize the enormous Pell coordinates; their
existence is the general positive converse just applied.
