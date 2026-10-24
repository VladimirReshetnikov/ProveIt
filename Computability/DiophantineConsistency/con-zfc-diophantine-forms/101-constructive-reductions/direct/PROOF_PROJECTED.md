# Projected rule labels with synchronized arithmetic certificates

## Measured endpoint and exact scope

The frozen `equations_v3/cap64/equation.json` defines an ordinary polynomial
as the sum of the squares of 391 displayed quadratic residuals in 495
nonnegative integer variables. `expanded_polynomial.json` lists all 15,377
collected monomials. Its exact degree is four and its coefficient height is
83,867,632. There is no coefficient parameter or arithmetic macro in that
file. The archived synchronized parent has 522 variables, 400 residuals,
20,225 monomials, and coefficient height 83,900,628.

This endpoint combines two inspected earlier developments, rather than
claiming either generic idea as new: the eight-column branch projection of
`ConZFC_Direct_Projection_7617.zip` and the global arithmetic certificates of
`ConZFC_Synchronized_Certificates_2026-10-24.zip`. The new measured composition
uses an independent parameter bound, a certified small-circuit label bound,
common accumulator products, and a cheaper equivalent bundle witness.
The equation is a direct C222 proof-calculus encoding; it does not encode a
K215 execution or invoke a universal Diophantine polynomial.

The ordinary arithmetic proof below composes with the parent's explicitly
identified C222/ZF/ZFC calibration. It is formalizable in ZFC. No newly
compiled end-to-end Lean/Rocq theorem or encoded object-language ZFC proof
object is asserted. In particular, this construction proves neither its
own unsolvability nor Con(ZFC), and does not establish global minimality.

## 1. Project the deterministic rule labels

Use the parent's twelve calibrated C222 branches in their fixed order.
Let I(a,b)=2(a+b)(a+b+1)+4b and A(a,b)=I(a,b)+2. Their conclusion
polynomials are exactly the nine literal constructors in
`code/projected_source.py`. The nine constructor definitions and all nine
conclusion expressions are checked to be identical, after alpha-renaming,
to the inherited constructor code. The inherited compositional polynomial
audit independently binds those definitions to the sealed numerical rules.

For every axiom branch its premise labels are p=q=0 and its conclusion is
the specified h(a,b,c,d); truth has h=0. The other branches are exactly

    modus ponens:   (p,q,v)=(a,I(a,b),b),
    generalization:(p,q,v)=(b,0,A(a,b)).

This is a reparameterization, with both directions explicit: in modus
ponens choose a to be the old p and b the old v; in generalization choose b
to be the old p and preserve the old generalization parameter a. Unused
parameters can be set to zero. Finite existential quantification distributes
over the branch disjunction, so a common local tuple does not require
simultaneous compatibility of parameterizations of different branches.

In the bundle branch the inherited guard is

    g^2=(d_old+1)^2,  g=(c-a)(c-b),  d_old>=0.

Its conclusion is independent of d_old. Replace it by

    g^2=d+1,  d>=0.

Both existential guards mean exactly g!=0. From the old witness take
d=d_old^2+2*d_old. From the new witness g!=0, take
d_old=abs(g)-1. These transformations preserve nonnegativity and do not
alter a,b,c or the conclusion. The rho8 branch still uses its own ordinary
fourth parameter d. As only one branch must hold, the new bundle meaning of
d imposes no restriction on rho8 or on any other branch.

## 2. The complete eight-column row

Fix outer natural parameters t>=1, m>=1, x,y,M0. Put M=M0+1 and
w(j)=1+M*j. For branch b define its signed accumulator residual

    e_b=Sp*w(v_b)-S*w(p_b)*w(q_b).

Let e_0 be the truth residual, e_1,...,e_8 the eight unguarded axiom
residuals, e_MP,e_GEN those of the two rules, and e_B the bundle residual.
Write G=((c-a)(c-b))^2-d-1. The complete local expression is

    [e_0*e_1*...*e_8*e_MP*e_GEN]^2 * (e_B^2+G^2)
      + [x-S-(1+(i+1)y)u]^2
      + [x-Sp-(1+(i+2)y)vq]^2.                       (R)

Every summand is nonnegative over integers. Thus R=0 holds exactly when
the two beta reconstructions hold and at least one calibrated branch's
accumulator identity holds, including its guard when the selected branch
is bundle. This proves the source projection over all naturals, not only
on test values.

The eight quantified row coordinates are

    a,b,c,d,S,Sp,u,vq,

bounded respectively by m,m,m,m,y,y,x,x. The code implements R as a pair
of polynomials with nonnegative coefficients. Its elementary pair rules
are the unchanged parent rules for addition, multiplication and squaring.
The factoring of eleven unguarded residual squares into one product square
is an exact polynomial identity. The common product Sp*M is also exact:
Sp*w(v)=Sp+(Sp*M)*v. Both changes reduce arithmetic wires.

## 3. A certified label bound and an exact carrier

The sealed label-bound certificate evaluates the constructor DAG at
a=b=c=d=m. Let R0=m+2, so R0>=2. Assign exponent 1 to input m, exponent
ceil(log2(c)) to a constant c>=1 (and zero to c=0), use max(e,f)+1 for
addition, and e+f for multiplication. Each assigned exponent certifies
that the corresponding nonnegative value is at most R0 to that exponent.
Monotonicity then bounds every rule label whenever a,b,c,d<=m.
The largest certified exponent is at most the emitted fixed exponent

    D=4,194,304,

so the ordinary polynomial h(m)=(m+2)^D bounds all labels. Its fixed
power uses 22 squarings. This large degree is confined to the semantic
arithmetic expression; its emitted multiplication graph remains quadratic.
Set M=(h(m)+1)^t, using the same positive-power graph as the parent.

For t chosen rule instances let

    A(X)=product_i(1+v_i X),
    C(X)=(1+X) product_i(1+p_i X)(1+q_i X).

The endpoints S_0=M+1 and S_t=1 and the row updates imply A(M)=C(M).
All accumulator entries are positive: S_0>0, all weights are positive,
and each update determines the sign of its next entry.
Since every label is at most h=h(m),

    A(M)<((h+1)M)^t=M^(t+1).

If deg C>t, its nonnegative integer leading coefficient would force
C(M)>=M^(t+1), contradiction. Consequently deg C<=t. Each nonconstant
factor of C has coefficient sum <=h+1, including 1+X because h>=1;
there are at most t such factors. Therefore both A and C have coefficient
sum at most (h+1)^t=M and constant coefficient 1. Every coefficient is
strictly smaller than M. Uniqueness of base-M digits gives A=C.
Comparing multiplicities of the distinct linear factors 1+jX for j>0
gives exactly the calibrated Horn balance with target label 1.
The parent's elementary closure-separation proof turns that balance into
a finite derivation, even in the presence of cycles and repeated premises.

Conversely, expand a finite derivation into a tree. Choose its finite t
and then m large enough for the four parameters of every projected row,
including each newly chosen bundle slack g^2-1. Choose M as above.
The product of the weights of the outstanding proof obligations gives a
positive integral accumulator trace from M+1 to 1. No truth padding or
bound on proof lengths is required; m remains an independent existential.

## 4. Bounds, beta coding, and CRT

Choose y above all accumulator entries and divisible by t!, then choose x
by the ordinary beta/CRT coding of the finite trace. The quotients in
x=S+(1+(i+1)y)u are automatically nonnegative and at most x. Therefore the
displayed heterogeneous row bounds hold. Conversely S,Sp<=y make the
two beta reconstructions canonical remainders because y<1+(i+1)y.
Adjacent rows consequently recover a single trace. The unchanged endpoint
identities recover the required first and last entries.

For the row pair E,F the second certificate computes an exponent majorant
using the same elementary rules, with base 2+t+x+y+m+M0. It proves a
bound for E,F at the upper row bounds and for the index and every bound.
The emitted exponent is 8,388,608. With H equal to this fixed power, set
T=H! and B=product_(i<t)(1+(i+1)T). The parent's fixed-vector CRT lemma
applies verbatim to the eight bounded columns. Since every (bound+1)!
divides T and B is coprime to T, the factorial factors cancel from the
eight binomial divisibility range tests exactly as in the parent.

The new construction has 11 binomial requests and 24 positive-power
requests. Their exponents are syntactically positive. The parent's shared
binomial-radix, common Pell frame, and simultaneous auxiliary-index
theorems apply to any finite family of such requests; changing its size
from 27 to 24 does not change those proofs. There are 19 distinct index
certificates and 10 distinct power bases. In soundness, powers are
identified first, binomial digits second, and semantic factorials/CRT
last; in completeness the acyclic intended values are chosen first and
shared auxiliaries afterward. This preserves the noncircular ordering
proved in the inherited final mathematical review.

## 5. Literal quartic and equivalence in ZFC

The primitive builder emits 823 natural variables and 719 quadratic
residuals after its elementary affine inlining. The independent monic
nonnegative contraction replay removes 328 more variables and residuals,
yielding 495 variables and 391 residuals. Every restoration is an integer
polynomial with nonnegative coefficients, and its occurrences keep every
remaining residual quadratic. Thus contraction preserves existence of
natural zeros in both directions. Exact expansion of the sum of squared
residuals gives the supplied 15,377-term quartic and coefficient height.

Combining the source proof, inherited arithmetic representation theorems,
literal contraction identities, and inherited ordinary C222 calibration
gives a proof formalizable in ZFC that

    exists z in N^495, P(z)=0  iff  there is a finite syntactic ZFC refutation.

Negation gives the requested no-solution/Con(ZFC) biconditional. Here
N includes zero. The nonnegative domain is essential; an unrestricted
integer interpretation requires the separately proved domain conversion.
Finite exact artifact checks are distinguished from this unbounded proof.
