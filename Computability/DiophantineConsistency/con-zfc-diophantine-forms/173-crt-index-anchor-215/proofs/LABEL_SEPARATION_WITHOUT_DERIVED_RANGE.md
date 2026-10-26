# Large polynomial labels without a derived-label range certificate

## Status and exact interface

This is a new ordinary arithmetic argument for the proposed direct quartic.
It is not a newly compiled Lean/Rocq certificate. Its finite expression
majorants are independently evaluated by `schema_audit.py`. The calibrated
logical source remains the original square-shell C222 calculus.

The source parameters a,b,c,d have the already certified strict ranges

    0 <= a,b,c,d < t,   t >= 16.

The two local pending-multiset states lie in [0,y], and the two beta
quotients lie in [0,x-1]. The row index lies in [0,t-1]. Keep the same local
Horn equation and all eight parameter/state/quotient ranges and the index
range. Delete only the separate binomial range of the derived label sum J.

Use the original square-shell constructors

    I(a,b)=2((a+b)^2+a),  M(a,b)=I(a,b)+1,
    A(a,b)=2((a+b)^2+3a+4b+3),  E(a,b)=A(a,b)+1.

Here A is a syntax constructor, not the Pell center. Let J be the same
formal expression formerly passed to the derived-label range: the sum of
the nine axiom-code expressions, a,b,I(a,b),A(a,b), and 1. J is used in this
proof as a mathematical expression only; it need not remain a circuit
register or a power-request index. Every label in a selected local rule is
at most J.

The independent constructor-depth certificate described below gives

    every local label < t^(2^20-1),
    J < 14*t^(2^20-1) < t^(2^20).

It is therefore sufficient to use

    L(t)=t^ell,   ell=2^20=1048576.

Choose a positive integer K with K>=ell*t and set F=t^K. Then
F>=L(t)^t. The principal choice is

    t=128+4z^2,  U=t^2,  K=U^2=t^4,  F=t^K.

Indeed K/(ell*t)=t^3/ell>=128^3/2^20=2. Only two new quadratic
power-index equations, U=t^2 and K=U^2, are required. Their coefficients
are small. The horizon is cofinal and divisible by four.

The alternative affine choice K=ell*t, with t=16+4z^2, also works; its
larger fixed coefficient is a different size tradeoff. These are explicit
constants, not an unspecified degree or an encoded computation.

The final Diophantine system does not contain variable exponentiation:
one retained-style Pell power request has base t, requested index K,
and proposed output F. Both base and index are positive before any
postponed arithmetic signs are used. Every actual changed base, index,
and output must be included in the square frame. In particular K must
be included, as an actual coordinate or its exact affine expression.

### Exact constructor-depth majorant

Let t>=16, e>=1, and 0<=u,v<=t^e. Each of the four constructors is
nonnegative and at most the common upper bound for E:

    8*t^(2e)+14*t^e+7
    <= (8+14/16+7/256)*t^(2e)
    = (2279/256)*t^(2e)
    < 16*t^(2e) <= t^(2e+1).

Treat I,M,A,E as primitive binary syntax constructors, and treat variables
a,b,c,d and constants 0,1 as depth-zero leaves. Set e_0=1 and
e_(d+1)=2e_d+1, so e_d=2^(d+1)-1. Induction on the constructor tree proves
that every positive-depth expression of depth d is strictly below
t^e_d. Trees of unequal child depths use the larger child bound, which is
legitimate since t>=16.

The nine actual source expressions have depths, in source order,

    4, 3, 3, 3, 3, 5, 4, 3, 19.

The other possible local labels a,b,I(a,b),A(a,b),0,1 have depth at most
one. Hence every actual local label is below t^(2^20-1). The former J
expression has exactly fourteen summands: the nine codes and
a,b,I(a,b),A(a,b),1. Therefore J<14*t^(2^20-1)<t^(2^20).

The finite certificate is `CONSTRUCTOR_DEPTH_CERTIFICATE.json`.
`check_constructor_depth.py` creates an independent constructor AST,
lowers it into canonical commutative arithmetic expressions, executes the
exact preserved source `shell_source.py` through an independent symbolic
builder, and checks equality of all fourteen outputs. It checks the source
SHA-256 before execution. The source is the square-shell `xx0` implementation
at pinned commit `953fb4d82d4229f4efc5f9db4cc2bf38ae329bb4`, repository path

    Computability/DiophantineConsistency/con-zfc-diophantine-forms/
    112-powered-saturation-round14/intake/
    ConZFC_Shell_Reciprocal_660_2026-10-24/
    ConZFC_Shell_Reciprocal_660/code/shell_source.py

Its exact byte length is 2955 and SHA-256 is
`59c68a354fe5cdbc04bde33720080db2436cb51ae25e3485ac5ae45ff4230199`.
This binds the finite syntax and depth computation to the actual source;
the induction above is the unbounded mathematical majorization proof.

As a separate cross-check, `schema_audit.py` obtains the larger expression
majorant J <= (n+1)^2790644, n=max(1,a,b,c,d). The main construction uses the
sharper depth bound, not that larger exponent. Even non-strict leaf ranges
a,b,c,d<=t would suffice for the depth induction; the emitted system
retains its existing strict ranges.

## 1. Sharp finite-product separation

**Lemma.** Let t,L,F be positive integers with L>=t and F>=L^t. Let U and V
be finite multisets of labels in [1,L]. Suppose |U|<=t, |V|<=2t+1, and

    product_(j in U)(1+jF) = product_(j in V)(1+jF).

Then U=V as multisets.

**Proof.** First their cardinalities agree. If they differ, put
r=min(|U|,|V|). Since |U|<=t, one has r<=t. The side with more factors is
at least (F+1)^(r+1); the side with fewer factors is at most

    (1+LF)^r <= L^r(F+1)^r.

Equality would imply F+1<=L^r<=L^t<=F, a contradiction. Therefore the two
counts equal m<=t. This argument also includes r=0: an empty product is 1,
whereas every nonempty product exceeds 1.

Replace F by an indeterminate z. For either product and 0<=k<=m, its kth
coefficient is a positive integer bounded by

    binom(m,k)L^k <= m^(m-k)L^k <= L^m <= F.

For m>0 the first inequality follows by counting k-fold products of
labels. The second uses binom(m,k)=binom(m,m-k)<=m^(m-k); the third uses
m<=t<=L. For m=0 both products are 1 and the conclusion is immediate.
Consequently every coefficient of the difference of the two polynomials
has absolute value strictly less than F. The strict bound remains valid
when a coefficient of one product equals F, because the corresponding
coefficient of the other product is positive, not merely nonnegative.

If the difference polynomial were nonzero, let r be its lowest nonzero
degree and c_r the corresponding coefficient. The equality at F, divided
by F^r and reduced modulo F, would give F|c_r. This is impossible for
0<|c_r|<F. The two products are therefore identical polynomials in Z[z].
Their distinct positive labels have distinct roots -1/j; unique
factorization over Q[z] recovers their multiplicities. QED.

The bound does NOT require F>=(L+1)^(2t+1). Recovering the factor counts
first is essential: it lowers the relevant coefficient degree to at most t.
It also shows that equality F=L^t is admissible.

## 2. Application to t Horn steps

For every nonnegative formula label j let w_j=1+jF. In particular w_0=1,
since truth has label 0. A valid single-conclusion Horn row has conclusion
v and two premises p,q, with missing premises padded by truth. The existing
weighted update is

    S_(i+1) w_v = S_i w_p w_q.

After the beta states have been decoded, the source endpoints give initial
state F+1 and terminal state 1. There is one small boundary issue when
using y=F(2u+1): the initial endpoint gives residue 0 if y=F. This case is
impossible, because positivity of every weight would propagate the zero
state through all t rows, whereas the final residue is 1. Therefore y>F,
and the true initial residue is F+1, with 0<F+1<=y. All intermediate states
are positive by induction on the same update equation.

Multiplying the t updates and cancelling the positive intermediate
states yields

    product_(i<t) w_(v_i) = (1+F) product_(i<t) w_(p_i) w_(q_i).

Discard unit factors with label 0. The left side has at most t factors;
the right side at most 2t+1, including the target label 1. All labels are
at most L(t), by their source-polynomial bounds. Section 1 therefore gives

    conclusion_count(j)-premise_count(j) = 1 if j=1, else 0

for every positive label j.

Take the closure of truth under the finitely many instantiated rules in
these t rows. If falsity 1 were outside that closure, each row with an
outside conclusion would have at least one outside premise. Summing its
conclusion count minus premise counts over all outside labels is therefore
at most zero. The displayed balance makes it one. This contradiction
extracts a finite C222 refutation. Cycles and repeated premises are covered
by this argument; there is no assumed ordering of the proof rules.

## 3. The CRT local-value bound survives

Deleting the range of J does not alter the local Horn polynomial. Its
nonnegative local value is a product of nonnegative rule factors, plus
the two squared beta residuals. With

    R0=2+t+x+y+F,

every nonnegative local atom is less than R0. The same independent
expression ledger gives the uniform bound

    0 <= Local(i,a,b,c,d,S,Sp,u,vq) < R0^(2^23).

Its more precise conservative recursive exponent is 5582565. The emitted
constant 2^23 is retained; no improved bound is needed for soundness.

The affine beta sign bootstrap supplies y>=F and

    x>=2+(t+1)y.

Since F=t^K>=t^t>=16^16=2^64, one has x>2^32 and R0<2x.
For x>=2^32 the elementary dyadic estimate

    2^23 log_2(2x)<x

gives Local<2^x. Equivalently, choose k with 2^k<=x<2^(k+1), k>=32;
then 2^23(k+2)<2^k<=x, and the inequality persists when k increases.

The binomial-CRT row selector therefore still converts local congruences
modulo a selected prime power p^(xe) into exact zero rows. No upper bound
on a DERIVED label is needed for this step beyond the fixed polynomial
majorant already used in bounding Local. Only the independent columns
need their range binomials.

## 4. Radius and every-prime completeness

For t>=16, lcm(1,...,t)^2<=16^(t-1)<t^t<=F. Thus the existing generalized
binomial-CRT theorem applies to

    B=binom(F+t,t),   N=B^x,   B | C+F+1.

It is not necessary that F be divisible by 1,...,t. The theorem uses only
F>=lcm(1,...,t)^2. Its two conclusions must both be retained:

1. Every row has a selector p^e||B, with p^e>t and p^e dividing F+i.
2. Every prime power p^e||B has at least one compatible row i.

For completeness choose a finite refutation and a cofinal horizon
t=128+4h^2 larger than its number of steps and every local source parameter.
There is no longer any need to make t larger than the derived formula
labels. Put K=t^4 and F=t^K. Construct the pending-multiset states using weights
1+jF. They are finite integers. Let O be the odd part of t!, choose an
arbitrarily large positive odd multiple u of O, and put y=Fu. Because

    v_2(F)=K*v_2(t)>=2t>v_2(t!),

t! divides y. Choose u large enough that y>F and all states are at most y.
The usual beta moduli 1+(i+1)y are then odd and pairwise coprime, and CRT
provides an arbitrarily large positive beta code x.

At every prime of B assign a compatible row and its genuine local tuple,
at precision p^(2xe). The prime-power moduli have product N^2, and all
remaining range binomials are obtained exactly as in the retained theorem.
There is no missing derived-label range to fill. Soundness and completeness
therefore use the same finite rule instances as before.

## 5. Move the Pell anchor to the encoded index C

The old use of J as an anchor was independent of the range proof except
for constructing an even, dominating nominal index. Once its request is
deleted, use the EXISTING principal pair whose nominal index is C, the
CRT row-index representative. Impose C=2c at the literal arithmetic level.

The signed anchor soundness proof works with an arbitrary nominal signed
index h. Its squared cap forces its anchor ordinate nonzero and
|ordinate|>|h|; the comparison congruences recover the classified index
|h| and exclude h=0. Thus the proof applies with h=C before C's semantic
sign is known. The orientation pool recovers both signed canonical
coordinates as before. Later the base-(q+1) request for C forces C>=0,
so the anchor is positive. No inequality C<t is asserted: C is a global
CRT representative; its least residues, not its global value, lie below t.

For completeness B is odd: v_2(F)>floor(log_2 t) gives
v_2(F+i)=v_2(i) for 1<=i<=t, so the binomial has 2-adic valuation zero.
Consequently N^2 is odd. Choose each of the eight other representatives
positive in its required residue class. At this stage the other fixed
indices x,y+1,t,F+t,K are already determined. Choose C in its required
class modulo N^2, even, and strictly greater than all these indices and
all eight representatives. This is possible because the even members of
any class modulo an odd modulus form a cofinal progression of step 2N^2.
No upper bound on C is required. Only after choosing C do we define the
self-sized radix multiplier H=2+4(C+sum of the eight representatives)
and q=(BH)^x. Thus enlarging C creates no circular modulus choice: B,N,x
and the residue classes were fixed before C,H,q. All digit estimates use
the actual H and lower bounds on it.

The canonical ordinate Y_C(A) therefore dominates the finite sum of
the other ordinate squares exactly as in the old cap completeness proof.
The nominal index C is even, so its canonical ordinate is even and the
odd auxiliary quotient construction applies unchanged. The actual frame
is constructed AFTER these choices, with the changed index K
and every retained request atom included.

## 6. What the finite audit must bind

The compiler must remove exactly the derived-label range's numerator,
quotient and private index pair when no longer used, substitute the C pair
in all anchor equations, retain its orientation term, and include the
F=t^K request with its correct canonical pair and actual index atom.
The same t pair remains needed for q^t. The weighted local rule equations,
the nine remaining range predicates, beta endpoints, every-prime CRT
conditions, and source constants must be retained exactly. Any variable
count saving belongs to the completely emitted and verified polynomial,
not to this semantic proof in isolation.

The companion `C_ANCHOR_THEOREM.md` supplies the complete signed-index
anchor proof and its odd auxiliary witnesses. Its cofinal selection of C
is compatible with the present polynomial-index choice K=t^4.

With those bindings, the ordinary arithmetic proof gives integer
solvability iff a finite C222 refutation exists. The unchanged identified
C222/ZF/ZFC calibration then proves in ZFC that absence of integer zeros
is equivalent to Con(ZFC). This states an equivalence; it proves neither
consistency nor inconsistency.
