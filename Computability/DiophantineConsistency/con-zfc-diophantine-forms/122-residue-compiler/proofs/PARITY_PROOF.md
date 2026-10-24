# Parity padding and modular Pell numerators

## Status and exact statement

The final natural polynomial in `even_modular12/natural/equation.json` is

    P(X_0,...,X_332) = sum_{j=0}^{263} R_j(X)^2.

Its 264 rows are all literal integral quadratic polynomials. Its complete
collected expansion is `expanded_polynomial.json`: degree 4, 4,357 terms,
maximum absolute coefficient 209,508,384. Every variable occurs. The new
ordinary theorem is that this equation has a zero in N^333 exactly when the
fixed C222 calculus derives its falsity code 1. Composition with the inherited
`KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation` gives the required
ZFC-provable equivalence between no natural zero and syntactic Con(ZFC).
This is an ordinary proof formalizable in internal arithmetic, not a new
Lean/Rocq proof object. It does not establish consistency or global minimality.

The exact frozen parent is Round14's derived-label factorial-carrier source,
whose 349-natural endpoint is in the incoming
`ConZFC_Powered_Saturation_Factorial_Carriers_Round14_2026-10-24.zip` at
ProveIt commit 45b399ec51dfbecb891dd51d8a9e4b6b7c361ac6. Its local C222
constructor, Horn-flow proof and eight local witness columns are retained.
The incoming even-index package supplies the parity exclusion lemma, credited
below. The modular-numerator ingredient was independently adapted by the
companion investigation from the older package 108. The new joint construction
changes the semantic source coordinates, its bounds, and all simultaneous
Pell interfaces; it is not claimed to be the same polynomial as those parents.

All witnesses in this proof are NONNEGATIVE INTEGERS. This restriction is
essential in the modular numerator interpretation. Dropping signs of the
modular-only Pell pairs is not justified here.

## 1. The padded front and its strict bounds

Write

    t = 2 t0 + 12,       x = 2 x0 + 2,
    F = 2 f,            y = F + 2 r0 + 2,
    R = 2 + t + x + y + F,       K = 2 R.

Here t0,x0,f,r0 are natural. Thus t,x,F,y,K are even by literal polynomial
identities, before F has been identified as a factorial. The values t,x,y
are already strictly positive, including when the proposed F is zero.

The local columns are (a,b,c,d,S,S',u,v). Their strengthened bounds are

    0 <= a,b,c,d < t,       0 <= S,S' < y,       0 <= u,v < x.

The local polynomial L is exactly the inherited nonnegative Horn branch
product plus its two beta residual squares. Its label expression is

    J = c1+...+c9+a+b+I(a,b)+A(a,b)+1,

using the complete inherited calibrated constructor formulas. In particular
J>=1 at all natural inputs. In the decoded local rows impose J<t. This is
stronger than the inherited J<=t requirement and still bounds every label
that can occur in any actual vanishing rule branch.

The retained endpoints are

    x = F+1 + (y+1) u0,
    x = 1 + [1+(t+1)y] ut.

The definition of y replaces the old nonnegative slack equation y=F+r0+1.
As x>=2, the last equation forces ut>=1. Consequently, even before any
power or factorial meaning is used,

    x >= 2+(t+1)y > y, t, 2t

because y>=2. This inequality will let one existing denominator determine
all modular numerators.

The same source majorant remains valid because the new local bounds are
stronger. Its finite gate certificate proves

    0 <= L(w) < R^E,    0 < J(w) < R^E,    E=8,388,608.

A separate inherited positive-constructor certificate proves, for n>=1,

    J(a,b,c,d) <= (n+1)^ell    if a,b,c,d<=n,
    ell=4,194,304.

No numerical bound here is inferred from a finite search. Those are exact
inductive bounds on the literal finite constructor DAG.

### Completeness of the strict, even front

Given a finite C222 refutation, expand it to a finite proof tree. First
choose an EVEN t>=12 strictly above the finite tree length, every row
parameter and every corresponding full label sum J, including the fixed
truth-padding tuple. This choice does not depend on F or accumulator sizes.
Set F=t!, which is positive and even, and define label weights W_j=1+jF.
Expand the tree backwards and take each accumulator state to be the product
of pending label weights, as in the inherited Horn-flow proof. Add truth
steps to reach exactly t rows. All states are positive and finite.

Choose an even y, divisible by F, strictly larger than every accumulator
state and than F+1. The beta moduli 1+(i+1)y, 0<=i<=t, are pairwise coprime
and odd: common prime divisors would divide an index difference of magnitude
at most t and hence divide F, a contradiction. CRT therefore gives a common
x with the required state residues. Since the product of these moduli is
odd, adding that product changes parity; choose a positive even x. The
standard remainder inequalities ensure all beta quotients are nonnegative.
Their divisors are at least 3, so the local quotients are strictly less than
x. Every state is strictly less than y. Thus the strengthened column bounds
hold. Finally x=2x0+2 and y=F+2r0+2 give natural x0,r0; F=2f gives natural f.

For soundness, the strict bounds imply the old weak bounds, and the same
beta uniqueness and endpoint arguments apply. The shared factorial makes
W_1,...,W_t pairwise coprime, W_0=1. Multiplicative Horn balance therefore
isolates the exact label multiplicities. The inherited closure argument
excludes a balanced rule multiset without a derivation of code 1, even if
that multiset has cycles. No assertion of soundness or consistency of ZFC
is used in this finite syntactic argument.

## 2. Reciprocal CRT and even representatives

After F=t! is recovered, define

    T=F^2,   d_i=1+T/i (1<=i<=t),
    B=binom(T+t,t)=product_i d_i,   N=B^K.

Each d_i is an odd integer >1. Its prime divisors exceed t, and distinct d_i
are coprime. These are exactly the inherited reciprocal-modulus facts.
Oddness follows from even F and i|F: T/i=F(F/i) is even.

Choose the nine independent CRT representatives (eight columns and the
index C) in the syntactically even positive form

    A_j=2(a_j^*+1),       C=2(c^*+1),

and impose their aggregate bound

    C + sum_j A_j + g = 18 N^2.

For completeness, the precision-2K CRT moduli have product N^2, which is odd.
Any residue class modulo N^2 has a positive even representative at most 2N^2:
use its least residue if positive and even, add N^2 if it is odd, and use
2N^2 for residue zero. Therefore the nine independent representatives can
be chosen to satisfy the aggregate bound. Their prescribed residues modulo
all d_i^(2K) are unchanged. This parity requirement costs only a factor two
in the representative bound.

Retain the reciprocal index condition

    C+T+1 = B i_q

and impose the range divisibilities

    N | binom(C,t),
    N | binom(A_j,b_j),          b_j = t, y or x,
    N | binom(2J(A_a,A_b,A_c,A_d),2t),
    N | L(C,A).

The first nine representatives, not the derived expression 2J(A), occur in
the aggregate bound. The derived expression may be enormously larger.

The one-sided prime-power range lemma states

    p^e | binom(a,k)  =>  a mod p^e < k,

for a>=0,k>=1. Its proof counts prime-power factors in the falling factorial:
if [a-k+1,a] contained no multiple of p^e, then all valuation summands at
levels >=e vanish, leaving valuation at most e-1. The case a<k is immediate.
The false converse is never used.

For soundness, take p|d_i and e=K v_p(d_i). The index congruence gives
C=i-1 mod p, while its range gives C=s mod p^e with 0<=s<t. Since p>t,
s=i-1. Each column range similarly produces a local value 0<=w_j<b_j.
The polynomial congruence and N|L give p^e|L(i-1,w). The majorant below puts
that nonnegative value strictly below p^e, forcing zero.

The derived range gives 2J(A)=s mod p^e with 0<=s<2t. Polynomial congruence
gives the same residue for 2J(w). Both numbers are strictly below p^e, so
2J(w)=s and J(w)<t. There is no division modulo a nonunit and no illicit
reverse use of the range lemma.

For completeness, prescribe C=i-1 and each A_j=w_j modulo d_i^(2K).
For any lower index k in {t,x,y,2t}, the relevant represented value is
congruent to an integer w in [0,k-1] modulo p^(2K v_p(d_i)). Its falling
factorial contains a factor divisible by that prime power, unless the
binomial is zero. Dividing by k! loses at most k-1<K in valuation, since
k<=R-2<K. Thus at least K v_p(d_i) remains. This proves every range
divisibility, including the polynomially derived 2J range. The evaluation
congruence and reciprocal index follow directly. All quotient witnesses
are nonnegative because their numerators are nonnegative.

## 3. Factorial bootstrap and radix bounds

The factorial and common radix are

    rho=F t^2,    V=(rho+1)^t,
    D=binom(rho+t,t),    B=binom(F^2+t,t),
    V+D=DF+r+1,     D=r+s+1,
    N=B^K,         q=N(N+V+1)^K.

Initially D,B,V,N are only proposed coordinates, not assumed meanings.
Exact positive-power recovery, justified in Sections 4-5 independently of
any binomial meaning, first gives V>=1. The ceiling rows imply DF=V+s>=1,
so F>=1; since F=2f, F>=2. The raw reciprocal index equation with C>=2
gives B>=1 before B is known to be a binomial. Hence N>=1, and the radix
power gives q>V^2 and q>=9.

As rho=Ft^2>=t, every binomial coefficient through degree t in
(1+z)^(rho+t) is at most binom(rho+t,t)<=V. Thus the first exact digit,
implemented by Section 5, identifies D. The inherited self-bounding
factorial lemma then identifies F=t!: writing G=t!,

    V/D = G product_{i=1}^t (rho+1)/(rho+i),
    G(1-1/(2F)) < V/D <= G,
    F = ceil(V/D),

forces F=G. Completeness sets r=V+D-DG-1 and s=DG-V; both are natural.

The elementary inequality F^2+t<=(Ft^2+1)^2 gives all lower coefficients
of the second exact binomial at most V^2<q. Thus B has its intended value.
Only now infer B>=2 and N>=2^K from the reciprocal-modulus theorem.

The horizon 12 suffices for the fixed growth budgets. One has

    12! = 479001600 > 2^28,
    28E < 2^28,      2E <= 2^28,
    12(3ell+1) <= 12!.

At r=2^28, r^E<2^r. The estimate
(1+1/r)^E <= sum_{j=0}^E (E/r)^j < 2 propagates this strict inequality
by induction to all larger integers. Since R>=F>=12!,

    L(w),J(w) < R^E < 2^R,
    2J(w) < 2^K,        K=2R.

The third base inequality persists because (t+1)! grows by a factor t+1:
t(3ell+1)<=t! implies (t+1)(3ell+1)<=(t+1)!. Therefore

    2t(3ell+1) <= 2F < K.

For every independent representative n<=18N^2 and lower index
k in {t,x,y}, one has k<=R-2 and N>=2^(2R). Hence

    binom(n,j) <= n^k <= 18^k N^(2k)
                     < 32^R N^(2k) <= N^(2k+3) <= N^(2R-1) < q

for 0<=j<=k (with zero coefficients when j>n). The same estimate also
works at k=2t because F>=t gives 2t<=R-2.

For the derived argument, n=max(A_a,A_b,A_c,A_d)<=18N^2 and N>=19 imply
n+1<=N^3. Thus

    J(A)<=N^(3ell),     2J(A)<=N^(3ell+1),
    binom(2J(A),j) <= N^[2t(3ell+1)] <= N^K < q   (0<=j<=2t).

This establishes carry-freeness of every exact and divisibility digit,
without inserting J into the aggregate bound and without assuming a
binomial meaning before its lower-digit bound is available.

## 4. Even-index certificates with no index-gap coordinates

For A>=2 write

    (A+sqrt(A^2-1))^j = chi_A(j) + psi_A(j) sqrt(A^2-1).

The usual minimal-unit reduction classifies every nonnegative integral
solution of X^2-(A^2-1)Y^2=1 as (chi_A(j),psi_A(j)). The minimal nonzero
ordinate is 1 with abscissa A. The addition formulas and recurrence are
polynomial identities and hold over any commutative quotient ring.

The common frame includes every exact-power base, exponent and output,
AND EVERY upper argument n of a modular digit request:

    W = 2 + sum(distinct actual atoms).

Thus W exceeds every tested seed exponent before interpreting any power.
The scale is cofinal:

    L^2-W^3(W+2)Z^2=1,    Z=z+1,
    A=L+s_A.

All coordinates are natural. Pell classification at base W+1 and the
congruence psi_(W+1)(h)=h mod W imply h>=W, and therefore
L>W^W and A>=L>W. The freely larger A will impose the modular root below.

The common auxiliary pair has V_aux=v0+1>0 and

    U^2-(A^2-1)V_aux^2=1,
    V_aux=(product over all seed Y_j^2)(v+1),
    B_aux=1+4V_aux(q4+1),     B_aux=A+U bq.

Each seed exponent e has only the rows

    X^2-(A^2-1)Y^2=1,
    S^2-(B_aux^2-1)R_aux^2=1,
    S=X+U sq,      R_aux=e+4Y rq.

No coordinate or premise Y>=e is present. The product and V_aux>0 force
Y>0 and Y^2|V_aux. Every e is syntactically even and >=2:

- t,x,y,K;
- rho+t and F^2+t;
- the eight even representatives and C;
- the explicitly doubled expression 2J(A).

The parity identities use F=2f, not F=t!, so their use at this point is
not circular. The exact checker follows these literal gate identities.

If Y=1, then X=A. Let U=chi_A(h), V_aux=psi_A(h), h>=1. Classify the
comparison pair at the positive B_aux. Its abscissa congruence gives
chi_A(j)=A mod chi_A(h). The Chebyshev residue lemma forces j odd. One
proof reduces j modulo 2h using alpha^(2h)=-1 mod chi_A(h), reflects the
remainder to [0,h], and uses 2chi_A(h-1)<chi_A(h) to rule out a false
residue. The only reduced index giving +/-A is 1. Since B_aux is odd,
psi_(B_aux)(j)=j mod2; R_aux is odd. But R_aux=e mod4 and e is even.
Contradiction. Thus Y>=2, and Pell classification gives Y>=2A>e.
This is the credited even-index exclusion from the incoming even-indices
packet, applied to even source parameters instead of squaring power outputs.

The rest of the index proof is standard but records its dependencies.
Write (X,Y)=(chi_A(i),psi_A(i)). If psi_A(i)^2|psi_A(h), divide h by i
and use the addition formula modulo psi_A(i) to deduce i|h; expanding the
multiple-index formula modulo psi_A(i)^2 gives Y|h. The abscissa congruence
then yields j=+/-i mod2h. As B_aux=1 mod4Y, the ordinate congruence gives
j=e mod4Y. Hence i=+/-e mod2Y. Since 1<=i<=Y and 1<=e<Y, only i=e is
possible. All pairs therefore have their exact positive intended indices.

Completeness chooses the actual positive Pell pairs at the even exponents,
then a common auxiliary unit congruent to 1 in the finite ring modulo
4 product Y_j^2. Its ordinate is a positive multiple of that product.
CRT between U and 4V_aux chooses a sufficiently large B_aux=A modU,
B_aux=1 mod4V_aux. All comparison pairs and progression quotients are
then nonnegative. V_aux=v0+1 is possible since V_aux>=1. Thus deletion of
all index-gap coordinates does not exclude any valid semantic tuple.

## 5. Six exact powers and one modular root

The six actual power requests are

    V=(rho+1)^t,       N=B^K,       H=(N+V+1)^K,
    d_t=q^t,          d_y=q^y,     d_x=q^x,
    q=NH.

The denominator at the derived label range is d_(2t)=d_t^2. This is an
ordinary quadratic gate; there is no seventh power request.

The indexed-Pell congruence for a genuine power m=n^e is

    X+(n-A)Y = m + (2An-n^2-1)u.

Because W bounds n,e,m, and A>W^W, the modulus is positive and larger
than both m and n^e. The Pell recurrence identifies the left side with
n^e modulo that modulus, so equality follows. Conversely the exact
identity

    chi_A(e)+(n-A)psi_A(e)-n^e
      = (2An-n^2-1) sum_{j=0}^{e-1} n^(e-1-j) psi_A(j)

provides a nonnegative quotient. Bases are positive in the necessary order:
rho+1 is immediately positive; the raw index condition gives B>0; N and H
are then positive; q is positive and, after V is recovered, q>=9. All
exponents are positive before this order begins.

Set b=q+1 and use the ONE common root congruence

    2Ab = b^2+1 + M u_M,        M=N d_x=N q^x.

The last endpoint already proved x>t,2t,y. Therefore M is divisible by
q^(t+1), which is the modulus of both exact factorial/product digit tests,
and by every N q^k with k in {t,x,y,2t}, which are the divisibility digit
moduli. This uses no assumption that a proposed binomial has its intended
value. The exact q powers were already recovered.

The sequence chi_A(n)+(b-A)psi_A(n) obeys the same recurrence as b^n
modulo any divisor of 2Ab-b^2-1, with initial values 1 and b. Thus the
common root row implies

    chi_A(n)+(b-A)psi_A(n) = b^n   modulo M

for every requested upper argument n. Its exactly indexed pair is supplied
by Section 4. The exact digit rows are

    X+(b-A)Y = r + q^t D + (q^(t+1))u,
    0<=r<q^t,  0<=D<q,

and analogously for B. The range digit rows are

    X+(b-A)Y = r + (N q^k)u,       0<=r<q^k.

All these moduli divide M. Carry-freeness from Section 3 makes the former
rows identify D,B, and the latter equivalent to N dividing the respective
binomial coefficients. No exact coordinate for (q+1)^n is introduced.

For completeness, all semantic arithmetic coordinates, and therefore W,L,
are chosen before A. Now F=t! is even, so reciprocal B and N are odd. The
true V=(Ft^2+1)^t is odd; N+V+1, H and q=NH are odd. Therefore M is odd
and gcd(2b,M)=1, since every prime of N divides q and gcd(q+1,q)=1.
Choose A solving 2Ab=b^2+1 modM, and increase A by a multiple of M until
A>=L and A>b. This supplies the natural cofinal slack s_A and root quotient.
The exact-power and shared-index completions then work at that A.

The modular-digit quotients are also natural. For b>=1 the exact identity
above, with n replaced by b, gives

    chi_A(j)+(b-A)psi_A(j) >= b^j

because 2Ab-b^2-1>0. The true b^j has the ordinary nonnegative quotient
and remainder for each valid digit test. The difference is a nonnegative
multiple of M, and hence of its digit modulus. Adding it preserves a
nonnegative quotient. This closes the reverse direction without a signed
quotient assumption or circular choice of A.

## 6. From the arithmetic rows to the printed polynomial

The initial construction supplies 991 named natural coordinates and 922
quadratic rows, including all literal C222 constructor gates. Its exporter
removes affine natural-valued gates and unused gates, leaving a 475-variable,
406-row raw quartic. The complete gate ledger remains supplied. The next
contraction has 142 monic eliminations, each with a nonnegative restoration
polynomial certified as a nonnegative-coefficient remainder plus rational
positive multiples of squares. All final rows remain quadratic.

The independent checker imports no builder. It reconstructs all 922 original
rows after 516 nonnegative gate restorations, checks every further monic
substitution and every nonnegativity identity, and compares all 4,357 final
expanded coefficients. Normal and optimized Python both pass, and deliberate
changes to a restoration and a coefficient are rejected. These are finite
artifact checks; they do not substitute for the quantified proofs above.

Reversing the monic substitutions gives a natural lift of every zero of the
final polynomial to all arithmetic rows. Conversely every valid arithmetic
certificate projects to a final zero. The sum of squares vanishes exactly
when each residual vanishes, so no disjunction or sign constraint is hidden
in the final equation. Composition with Sections 1-5 and the inherited
calculus calibration proves the announced ordinary consistency equivalence.
