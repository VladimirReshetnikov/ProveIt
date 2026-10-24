# Centered factorial certificates for the direct consistency quartic

This note proves the new arithmetic change. The inherited 407-natural direct
quartic is from `ConZFC_407_888_Quartics_2026-10-24.zip`, present at ProveIt
commit `ec80841c07e91be8956ce6ed4af9a9c0b782d3d9`. The new supplied Python file
constructs the entire changed quadratic system and contracts it to 395
nonnegative variables. No claim of global or literature priority is made.

## 1. A factorial is the unique fixed point of a centered floor

For all natural numbers n,f, put

    R(n,f) = (2f+n+1)^n / (2^n * binom(f+n,n)).

The denominator is positive, including n=0. Then

    floor(R(n,f)) = f  if and only if  f=n!.

For n=0 and n=1 the quotient is exactly 1. Suppose n>=2, let a=n!, and
set m=f+(n+1)/2. Pair the n consecutive positive numbers f+1,...,f+n
around their arithmetic mean m. If d runs through the positive distances
from the mean, then

    R(n,f) = a / product_d(1-d^2/m^2),
    sum_d d^2 = n(n^2-1)/24.

Each factor is in (0,1], so R>=a. Consequently any proposed fixed point
f=floor(R) satisfies f>=a *before* a radius estimate is needed.

The elementary bound n(n^2-1)<=4n! holds for every n>=1. Check n=1,2,3;
for n>=3 its left-side consecutive ratio is (n+2)/(n-1)<=n+1, so induction
proves the claim. Thus at f>=a,

    S = sum_d d^2/m^2 <= a/(6m^2) <= 1/(6a).

The product bound product(1-x_i)>=1-sum(x_i) for x_i in [0,1] gives

    0 <= R-a <= a*S/(1-S) <= a/(6a-1) < 1.

Therefore floor(R)=a whenever f>=a. This both excludes every false fixed
point and proves existence at f=a. The argument uses finite products and
elementary rational inequalities and is formalizable in ZFC without any
assumption about its consistency.

For n=2h+1 this becomes the simpler identity

    f=n! iff f=floor((f+h+1)^n / binom(f+n,n)).

With V=(f+h+1)^n and C=binom(f+n,n), its graph has precisely the natural
remainder rows

    V = C*f+r,
    C = r+s+1.

There is no independently chosen radius and no bound or power for a radius.
All powers and binomials in this explanation are expanded into the inherited
shared Pell and digit graphs in the final polynomial.

## 2. The changed binomial graphs are valid before factorial correctness

For every odd positive n=2h+1 and every f>=0, put m=f+h+1. Then

    binom(f+n,j) <= m^n  for 0<=j<=n.

Here binom(N,j)=0 for j>N. For n=1 the claim is immediate. For n>=3,
f+n<=2m. When j>=4, use binom(f+n,j)<=(2m)^j/j!, 2^j<=j!, and j<=n.
For j=0,1,2 use m>=2 and n>=3. For j=3 and n>=5, use
2^3/3!<=m^(n-3). The only remaining case is n=j=3, where the product
(f+1)(f+2)(f+3)<=m^3 gives the claim directly.

This estimate matters because a Diophantine zero initially supplies an
arbitrary candidate f. One must not assume f=n! when proving that the
binomial digit extraction is carry-free.

## 3. Odd indices cost no proof instances

The direct source uses a finite Horn-rule flow with padding rule
(0,0)->0 and weight w(0)=1. Adding a padding row leaves the accumulator
unchanged, so any finite refutation can be padded to any sufficiently large
odd horizon t. In the new construction t=2*t0+1.

The local polynomial and its majorant certificate are unchanged. Write
R=2+t+x+y+M0 and D=2^23, exactly the parent's emitted majorant exponent.
Instead of H=R^D, use

    Hhalf=R^D,  H=2*Hhalf+1.

This is odd and strictly larger than the old majorant. Thus every local
value remains <H; t,x,y and all local bounds retain the same strict or
nonstrict inequalities required by the CRT theorem. The two factorial
inputs are exactly H and t, with half-indices Hhalf and t0 respectively.

The entire source construction still has eight local coordinate columns,
the exact same C222 axiom/rule polynomials, and the original ordering of
choices: finite proof; odd padded horizon; carrier; finite accumulator;
beta radix and code; arithmetic and Pell certificates. Enlarging the
horizon before choosing the carrier creates no circular bound.

## 4. A noncircular shared radix

Let V_H and V_t be the two centered factorial numerators and B the proposed
CRT product. Choose the single binomial radix

    q = B*(V_H+V_t+1).

The use of their SUM is deliberate. Before factorial correctness, the
second candidate factorial could be arbitrary. Bounding V_t by V_H at
that stage would be invalid.

The unchanged simultaneous Pell theorem first recovers every requested
positive power. The base-modulus row for the power base q excludes q=0,
hence B>=1 and q>V_H,V_t. Section 2 now validates both factorial binomial
graphs independently of their outputs. Section 1 recovers T=H! and F=t!.

It remains to validate the CRT-product binomial and the eight range
binomial divisibilities. Let

    Q=(1+(t+1)T)^t+2.

The unchanged raw remainder rows already imply B<T*Q without needing the
product formula. The unchanged aggregate bound gives every positive encoded
column A_j<=8B. We have R>=4, t<=R, H>=R^4, T=H!>=H>=8, and t+2<=T.
Consequently

    1+(t+1)T <= T^2,
    Q <= T^(2t)+2 <= T^(2t+1),
    Q+t <= T^(2t+2),
    A_j <= 8B < 8TQ <= T^(2t+3).

Every remaining lower binomial index k is at most R. Hence for every
relevant upper argument N (either Q+t or A_j) and 0<=j<=k,

    binom(N,j) <= N^j <= N^k
      <= T^(R*(2R+3)) <= T^H < V_H < q.

The inequality R*(2R+3)<=R^4<=H holds for R>=4. Thus all remaining
lower digits are carry-free. The inherited fused divisibility graph and
CRT-product identity are now valid. There is no circular appeal to the
correctness of B when proving the radix bound.

For completeness, first take the genuine arithmetic values T=H!,F=t!,
the genuine B, and the canonical CRT representatives, then define V_H,V_t,q
from them. All binomial and remainder rows have their usual natural
witnesses. Finally choose the cofinal common Pell frame. This proves the
complete two-way arithmetic replacement, rather than only soundness.

## 5. Composition and exact equation

The unchanged parent proves (in ordinary mathematics formalizable in ZFC)
that its direct bounded-flow source has witnesses exactly when C222 derives
the contradiction label 1. Its inherited calibration is
C222(1) iff ZF has a finite refutation iff ZFC has a finite refutation.
The preceding sections replace only factorial graphs, parity choices, and
the shared radix. The shared-power proof applies to all 21 requested power
graphs, whose positive exponents are independently checked from their
literal producer rows. No machine execution or Jones universal polynomial
is introduced.

The new raw natural source has 663 variables and 581 quadratic residuals.
The inherited certified nonnegative monic contraction gives 395 variables
and 313 quadratic residuals. For the literal residuals r_i in
`centered_output/natural_cap64/equation.json`, the fixed equation is

    P395(x_0,...,x_394) = sum_(i=0)^312 r_i(x)^2 = 0,
    x in N^395.

The fully collected polynomial has degree exactly 4, 8,292 monomials, and
coefficient height 83,843,425. These are literal coefficient measurements,
not syntactic upper bounds. The optional support-16 contraction gives 398
variables, 316 rows, 6,948 monomials, and height 211,184,624.

Taking negations of the source equivalence yields

    ZFC proves (P395 has no natural zero) iff Con(ZFC).

This is an ordinary proof formalizable in ZFC, not an emitted derivation
object for the repository's internal BProv calculus. The finite coefficient
and mutation checks do not replace the unbounded mathematical arguments.

## 6. Scope of improvement

The parent's P407 has 407 variables,323 residuals,degree4,8,420 monomials,
and height83,843,774. P395 saves12 variables,10 rows,128 monomials, and349
in coefficient height. The full power requests fall23->21; the number of
seed Pell indices stays15. This is a concrete improvement of the direct
small-literal-coefficient quartic branch. It does not beat the repository's
few-variable high-degree equations or its machine-derived quartics with
large fixed coefficient payloads. The general centered factorial fixed-point
identity is the new mathematical mechanism; no global minimality claim is
supported.


## 7. The unrestricted-integer quartic

The source polynomial before nonnegative contraction has 663 natural
coordinates and 581 quadratic residuals. Its explicit sign-inference
certificate identifies159 coordinates as seeds and proves the other504
coordinates nonnegative from the actual source equations. Each inference
either isolates a positive multiple of a coordinate as a sum of monomials
known to be nonnegative, or identifies that multiple with an exact square
of an affine expression. The supplied independent checker re-expands each
identity and checks that its premise signs have already been established.

For each seed x insert the single quadratic guard

    x = a^2+b^2+c(c+1),

using three fresh unrestricted integer coordinates. This is equivalent to
x>=0. One direction follows because squares and c(c+1) are nonnegative at
integer arguments. Conversely, the three-square theorem represents4x+1
as a sum of three integer squares: this integer is not of the excluded
form4^u(8v+7). Modulo4 exactly one of those squares is odd and two are
even. Writing their roots as2c+1,2a,2b and dividing by4 yields the displayed
identity.

The guarded source therefore has1140 integer coordinates and740 quadratic
residuals. Every integer zero restores all663 original natural coordinates,
in the certified sign-inference order, and hence a finite C222 refutation.
Conversely every natural zero extends to an integer zero by choosing the
three-square representations for its159 seeds.

Finally, the supplied integer monic-projection certificate removes287
coordinates,183 by affine restorations and104 by quadratic restorations.
At each step a pivot residual is exactly plus or minus x-P, with P an
integer polynomial in the remaining coordinates; substituting P in every
other residual preserves the unrestricted-integer zero set in both
directions. Each substituted residual remains quadratic. Reverse
substitution uniquely restores the eliminated coordinates. No sign
assumption is made until the full guarded source has been restored.

For the453 literal residuals S_i in
`centered_output/integer_cap16/equation.json`, define

    Q853(z_0,...,z_852) = sum_(i=0)^452 S_i(z)^2.

The preceding equivalences prove in ordinary mathematics formalizable in ZFC

    Q853 has an unrestricted-integer zero
      iff C222 derives1
      iff ZFC has a finite syntactic refutation.

Consequently ZFC proves that absence of an integer zero of Q853 is equivalent
to Con(ZFC). The exact collected polynomial has degree4,9,747 monomials,
and coefficient height2,445,790,974,704. There are no external sign
conditions on the final853 integer variables. The proof inherits the
parent's source calibration, the classical three-square theorem, and
the unbounded Pell/CRT graph theorems; the independent finite certificates
check their literal algebraic composition and both projection directions.


 
