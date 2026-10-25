# One semantic Pell anchor and an aligned amplification index

## Result and meaning of the equation

The main new natural-domain construction is the sum of squares of the 179
quadratic integer residuals in `strict_natural229/natural/equation.json`.
It has 229 nonnegative integer variables. Its independently collected quartic
has 9,184 nonzero monomials and coefficient height 83,954,634. The sparse
companion `strict_natural230` has 230 variables, 180 rows, 6,858
monomials and height 83,954,472. An additional exact-projection companion has 228 variables, 178 rows, 9,866
monomials and height 2,445,412,949,744. It trades much greater coefficient
height for one fewer variable and is not the recommended balanced form.
Each coefficient is supplied literally in the
respective `expanded_polynomial.json`; no exponentiation, factorial, binomial,
bounded quantifier, or implicit sequence is a primitive of that polynomial.

The existence claim is unchanged: with the inherited ordinary numerical C222
calculus calibration, the polynomial has a natural zero exactly when ZFC has
a finite syntactic refutation. Consequently ZFC proves that its no-zero
sentence is equivalent to Con(ZFC). This is neither a proof of consistency,
a global minimality assertion, nor a newly checked end-to-end proof-assistant
or object-language ZFC derivation.

There are two new compatible reductions. First, a single bounded-error row
reuses the already required derived-label Pell index as the full anchor. Its
index need not be even and the size frame need not be doubled. Second, the
amplification exponent is the largest required quotient-range index x, rather
than a separate large affine expression. The two beta quotient ranges are
sharpened from u,v<=x to u,v<x, as their defining equalities already permit. The incoming factorial/product
fusion, modular binomial graphs, dominant denominator, consecutive Pell
coordinates, and self-sized radix are explicitly retained and credited.

## A general one-row semantic-anchor lemma

Write X_j(A),Y_j(A) for the ordinary Pell sequences defined by

    (A+sqrt(A^2-1))^j = X_j(A)+Y_j(A)sqrt(A^2-1).

Assume integers W>=3, 2<=H<W, A-1>W^3, r<=W-2 and requested indices
1<=k_i<W. Retain a complete natural indexed-Pell certificate at index H,
with principal pair (U,V), omitting only its separate inequality H<=V.
For each i retain a natural principal Pell norm. Impose the single row

    V = H + sum_i (Y_i-k_i)^2 + (A-1)Q,       Q>=0.             (1)

Then the principal pair is (X_(k_i)(A),Y_(k_i)(A)) for every i. Conversely,
canonical pairs extend to (1) whenever H>=2 max_i k_i. All private witnesses
of the complete indexed-Pell certificate retain their inherited natural
domains. The assertion does not license making any private witness signed.

For soundness, (1) supplies V>=H, so the complete anchor theorem first gives
V=Y_H(A). Since H>=2, V>=Y_2(A)=2A>2W. Classification of each principal norm
gives Y_i=Y_(j_i)(A), j_i>=0. If j_i>=H, then Y_i>=V and

    (Y_i-k_i)^2 >= (V-W+1)^2 > V.

For the last strict inequality, V>=2W gives V-W+1>=V/2+1, whose square is
larger than V. This contradicts (1), which bounds the sum of error squares
by V-H<V. Hence j_i<H<W. The Pell recurrence modulo A-1 gives Y_j(A)=j
modulo A-1. Reducing (1) therefore gives

    A-1 divides E = sum_i (j_i-k_i)^2,
    0<=E<=r(W-1)^2<W^3<A-1.

Thus E=0 and j_i=k_i. In particular, no separate hypothesis k_i<H was used
in soundness. If ordinary coordinates are used, natural X_i supplies the
positive abscissa. Consecutive coordinates are handled below.

For completeness, put s=max_i k_i>=1 and z=Y_s(A)>=1. If H>=2s, then

    V=Y_H(A)>=Y_(2s)(A)=2X_s(A)Y_s(A)>2(A-1)z^2.

As Y_(k_i)(A)>=k_i, each actual square error is at most z^2. Therefore

    V-sum_i(Y_(k_i)(A)-k_i)^2 > [2(A-1)-r]z^2 > H,

where A-1>W^3, r<=W-2 and H<W imply 2(A-1)-r>H. The numerator
V-H-sum_i(Y_(k_i)(A)-k_i)^2 is positive and divisible by A-1. Its quotient
is the required natural Q. The inherited indexed-Pell completeness theorem
supplies fresh private anchor witnesses at this A and H. This proof uses
neither parity of H nor a doubled frame.

## The literal semantic frame and anchor certificate

Let t=t0+12 and take the unchanged positive encoded representatives
C,A_a,A_b,A_c,A_d,A_S,A_Sp,A_u,A_v. The derived nonnegative label polynomial
J is the sum of the nine axiom conclusion polynomials and a,b,I(a,b),A(a,b),1,
with the same Cantor constructors and arithmetic source as the predecessor.
In particular J>=I(A_a,A_b)>=2A_a^2>=2. Use H=J in (1).

The frame is

    W = 15 + sum(distinct exact-power bases, exponents and outputs
                 together with all modular numerator indices).

There are thirteen independent seeds; J itself uses the full anchor pair
and is not also a seed. Thus H<W, every intended index is <W and r=13<=W-2.
The current code computes the offset as the actual seed count plus two,
rather than trusting an unattested hard-coded census.

The scale rows are

    L^2-((W+1)^2-1)(WZ)^2=1,    Z=z+1,    A=L+sigma,

with all coordinates natural. Pell classification gives L=X_e(W+1),
WZ=Y_e(W+1) with e>0. Reduction modulo W gives W|e, so e>=W and
A>=L>=X_W(W+1)>=(W+1)^W. In particular A-1>W^3 and A>W+1, before
interpreting any exact power. The free sigma permits choosing A in the
later common-root congruence class.

The full anchor is exactly the inherited three-norm indexed-Pell graph.
Using private names U1,V1,B1,S1,R1,d,e,f,g,h, it is

    U^2-(A^2-1)V^2=1,
    U1^2-(A^2-1)V1^2=1,
    S1^2-(B1^2-1)R1^2=1,
    B1=1+4V(d+1),                 V1=V^2(e+1),
    B1=A+U1*f,                   S1=U+U1*g,
    R1=H+4V*h.

Its omitted H<=V condition follows from (1). The existing constructive
criterion also supplies the nonnegative oriented congruence quotients:
H>=2 gives V>=2A; B1>1 and B1=1 modulo 4V give B1>A; R1>=H>=2 and
Pell classification at B1 give R1>=2B1, hence S1>U. No unsupported new
indexed-Pell criterion is being substituted.

## Power recovery and modular numerators

Each exact request m=n^k retains

    T_n=2An-n^2-1,
    X_k(A)+nY_k(A)=A Y_k(A)+m+T_n*q_n,

with T_n,q_n natural. The first row excludes n=0. Every requested exponent
is positive from the raw expressions, endpoints and positive representative
offsets. After (1), the ordinary Pell congruence gives m=n^k modulo T_n.
The frame bounds n,k,m by W, while A>=(W+1)^W gives T_n>W^W+W. Thus the
congruence is an equality. Canonical positive powers provide nonnegative
quotients by the inherited positive-power argument.

The six exact requests are

    V0=(F^2+1)^t,       N=B^K,           q=(N*S)^K,
    D_t=q^t,           D_y=q^(y+1),     D_x=q^x,
    K=x,             S=1+C+sum(eight encoded columns).

The extra denominator D_(t+1)=q*D_t is multiplication, not a seventh exact
power. Aligning K with x makes two formerly distinct index requests
literally the same atom. All eleven modular numerator indices remain in W.

The common-root equation is

    2A(q+1)=(q+1)^2+1+M*h0,       M=N*D_x.                    (2)

Once the six powers and endpoints are decoded, x>t+1 and x>y+1; hence M is
divisible by qD_t for the one exact binomial, and by N times every range
denominator. Substituting s=q+1-A into the Pell identity modulo M gives

    X_n(A)+(q+1-A)Y_n(A) = (q+1)^n modulo M.                 (3)

The left side is positive: X_n(A)>(A-1)Y_n(A) for n>0, and every n here
is positive. The literal modular digit equations are the same as the
incoming common-root compiler, with Euclidean remainder r<q^k and, for
the exact binomial only, output B<q. Thus they recover exactly the desired
low digit or binomial divisibility once the carry bounds below hold.

For completeness, N|q, so all prime divisors of M divide q and
 gcd(q+1,M)=1. Hence gcd(2(q+1),M) is one or two. In the latter case
q+1 is odd and (q+1)^2+1 is even, so the linear congruence (2) is soluble.
Choose A in its solution class arbitrarily large after all semantic data
are fixed; both sigma and h0 can be natural. Canonical Pell residues are
positive and congruent to their least nonnegative required residues, so
all modular digit quotients are natural.

## Bootstrap and factorial/product fusion

The factorial/product output B is shared by the two ceiling rows

    V0+B=B*F+u+1,       B=u+v+1.

They imply B>=1 and V0+v=BF. Since V0=(F^2+1)^t>=1, F>=1. Also V0>F^2,
so B>F and V0<=BF<B^2. The raw endpoint x>=F+1 gives K=x>=2. Consequently

    V0<B^2<=N<=q.

For r>=1 and n>=1, every coefficient binom(r+n,j), 0<=j<=n, is at most
(r+1)^n. This follows by Pascal induction for j<n and the product formula
for j=n. Apply this with r=F^2,n=t. All coefficients through t are <=V0<q,
so the exact modular digit really gives B=binom(F^2+t,t), without first
assuming the factorial identity.

The ceiling rows say F=ceil(V0/B). Write T=t! and

    V0/B=T*product_(i=1)^t (F^2+1)/(F^2+i).

Every factor is <=1, so F<=T. Monotonicity in F gives
V0/B>=2^t/(t+1)>t^2 for t>=12, hence F>t^2. The product bound
product(1-a_i)>=1-sum a_i with a_i=(i-1)/(F^2+i) gives

    T*(1-1/(2F))<V0/B<=F.

Thus T<F+F/(2F-1)<=F+1, so T<=F by integrality. Therefore F=t!.
Conversely at F=T the same estimate gives T-1/2<V0/B<=T, furnishing
natural ceiling witnesses. This is the inherited square-radius identity.

For 1<=i<=t, d_i=1+F^2/i is integral and congruent to one modulo F. Any
prime divisor of d_i exceeds t, and the d_i are pairwise coprime, because
a common prime for distinct indices would divide their difference.
Their product is precisely B. This recovers the reciprocal CRT carrier.

## Why x is enough amplification

Retain the literal source majorant with E=2^23 and base
R=2+t+x+y+F, so each nonnegative local source value and local label sum
is strictly below R^E at the prescribed local bounds. The inherited J
majorant has ell=2^22.

After F=t!, the endpoint equations give

    y>=F+1,
    x=1+(1+(t+1)y)*u_t,     x>=F+1>=2.

Thus u_t>=1 and x>=2+(t+1)y. For t>=12, t<y and F<y, so

    R<2+x+3y<2x,
    x>=2+13*(12!+1)>2^32.

At r0=2^32, (2r0)^E=2^(33E)<2^r0 because 33E=276,824,064<2^32.
For r>=r0, the binomial theorem and binom(E,j)<=E^j give

    (1+1/r)^E <= sum_(j=0)^E (E/r)^j
                 < 1/(1-E/r) < 2,

since E/r<=1/512. Induction therefore proves (2r)^E<2^r for all
integers r>=r0. In particular every required local value is

    <R^E<(2x)^E<2^x=2^K.

This proof does not assume a bound on x in terms of y; the arbitrarily
large beta representative x makes the estimate stronger, not weaker.
For the only tightened ranges, the inherited beta equalities in a canonical
finite-refutation witness have u=(x-S)/(1+(i+1)y) and
v=(x-Sp)/(1+(i+2)y), with S,Sp>=0, y>=1 and x>0. Each denominator is
at least two, so u,v<=x/2<x. Thus completeness admits lower index x
instead of x+1 for these two ranges. Soundness only strengthens the old
bounds; all local values still lie in the old majorant's permitted box.

All lower range indices t,t+1,y+1,x are <=K. Equality for x is
permitted: in the completeness valuation estimate division by k!
loses at most k-1<=K-1, which is still strictly less than K.

## The self-sized radix and CRT soundness

Every independently chosen positive representative is <S. For every
such representative n and every 0<=j<=k<=K,

    binom(n,j)<=max(1,n^K)<S^K<q.

The coefficients with j>n are zero. No aggregate upper-bound equation
or slack is required. The literal majorant gives J<=S^ell. At t=12,
3ell(t+1)<2*12!, and this inequality persists with t by factorial growth.
Hence ell(t+1)<F<K, and every required coefficient of J through index
t+1 is also <S^K<q. These bounds apply to arbitrary representatives in
soundness, including the representative deliberately enlarged below.

The modular graphs therefore give all ten intended binomial
divisibilities by N. The inherited prime-power lemma says that
p^e|binom(a,k), k,e>=1, forces a modulo p^e to lie in [0,k-1]. It is
used only in that direction. For row i-1 choose p|d_i and m=v_p(d_i).
The raw B divisibility of C+F^2+1 identifies C modulo p as i-1. Its
range then identifies the small residue modulo p^(Km) as exactly that
index. The remaining ranges recover every local coordinate in its
prescribed interval. The local source divisibility by N, together with
its strict bound <2^K<=p^(Km), forces the nonnegative local source value
to equal zero. The derived-label range similarly forces J(local)<=t.
The unchanged beta consistency and pairwise-coprime weight/Horn-flow
argument then produce a finite C222 refutation.

## Constructive completeness and anchor dominance

Start with a finite refutation, expand to a proof tree and pad a horizon
t>=12 beyond every required local parameter and label sum. The inherited
beta construction supplies x,y and the local source. Set F=t!, B, K=x
and N=B^K. Choose each of the nine positive independent representatives
by CRT modulo d_i^(2K), initially in (0,N^2]. Replace only A_a by
A_a+N^2. This preserves every local polynomial congruence to precision
2K, and leaves every representative <=2N^2.

For each needed range, the falling-factorial numerator contains a term
with at least 2Km p-adic valuation, while division by k! loses at most
k-1<=K-1. The result therefore has at least Km valuation. Polynomial
congruence gives the same conclusion for J. This is the genuine
precision-2K completeness argument, not the false converse of the range
lemma.

Let R=2+t+x+y+F. The endpoint inequalities above give R<2x. More directly,
F,y,t<x, so the remaining nominal indices t,y+1,x,F^2+t are <=x^2+x.
For x>=5, x^2+x<2^x, by the base case x=5 and induction. Since
N=B^x>=2^x, every such index is <N. All other nonanchor indices
are representatives <=2N^2. Thus s=max_i k_i<=2N^2. But

    H=J>=2(A_a+N^2)^2>2N^4>4N^2>=2s,

as N>=2. This supplies the extra completeness hypothesis of (1), at no
additional witness or row cost. Compute S and q afterwards; their carry
bounds hold regardless of the actual representatives' sizes. Then compute
the exact denominators, W, L and a sufficiently large A satisfying (2).
Supply canonical Pell pairs, fresh full-anchor witnesses, Q from (1), and
Euclidean modular-digit witnesses. There is no cyclic choice involving q,
A, the anchor, or the CRT representatives.

## Consecutive coordinates and exact contraction

For every nonanchor seed the chosen endpoint stores natural Y,Z and a
product wire P=YZ, and imposes

    Y^2+Z^2-2A*P=1,       nY=Z+R_n,

where n is an exact-power base or q+1 and R_n is the nonnegative sum in
its actual output row. Each seed is checked to have such an incidence.
The frame gives 1<=n<A. The output row excludes Y=0 because the norm
would force Z=1. It gives Z<=nY<AY, so X=AY-Z>0. Expanding the conic
gives X^2-(A^2-1)Y^2=1; positive Pell classification follows. Thus (1)
applies to its ordinate, and canonical Z=Y_(k-1)(A) supplies completeness.
The full anchor retains ordinary positive coordinates and every private
witness. No anchor norm is silently replaced by an unindexed seed.

Finally the raw polynomial graph is exported and contracted only through
explicit integer polynomial restoration certificates. Their nonnegativity
is witnessed by rational sums of affine squares plus nonnegative monomials.
The independent checker expands these identities, replays each substitution,
checks that rows stay quadratic, and independently collects the complete
sum of squares. Thus both directions of natural existence are preserved.
Finite arithmetic tests and syntax checks complement the ordinary unbounded
proof above; they do not replace it or the inherited logical calibration.

## Fixed-priority 228-variable companion

The 228-variable companion starts from the identical raw semantic equation.
Its contractor uses a fixed, explicitly listed order of row priorities,
bound to the raw equation's canonical SHA-256, rather than the predecessor's
ascending row order. Every elimination is still an integer monic
substitution certified nonnegative by exactly expanded rational squares
and nonnegative monomials. The final certificate has 106 eliminations,
including two restorations with negative expanded coefficients; both have
independently checked positive-square certificates. The target has 228
variables, 178 residuals, 9,866 quartic terms and coefficient height
2,445,412,949,744. No semantic inference or domain relaxation is used for
this extra variable reduction. Independent normal and optimized runs
replay every restoration and all collected coefficients.
