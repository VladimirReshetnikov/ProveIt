# Direct source projection and a polynomial factorial bootstrap

This note supplies the new mathematical transformations from the inherited
Synchronized Certificates package to `bootstrap_output/equation.json`.
The inherited source is C222, its ZF/ZFC calibration, finite Horn-flow
criterion, polynomial carrier, beta/CRT compilation, simultaneous powers,
and shared binomial radix. These imports are unchanged. The new source has
781 natural coordinates; its exact nonnegative contractions are listed below.

## 1. A nine-column local rule certificate

Use the original numerical constructors

    I(a,b)=2(a+b)(a+b+1)+4b,   A(a,b)=I(a,b)+2.

Let h_1,...,h_8 be the eight original unconditional axiom polynomials and
h_B the original guarded-bundle polynomial. Their literal constructor
definitions in `hybrid_source.py` agree with `direct_source_factored.py`.
The truth label is zero. The target is label one. Put

    G=((c-a)(c-b))^2-(d+1)^2,
    K=v product_{j=1}^8 (v-h_j),
    B=(v-h_B)^2+G^2,
    w(z)=1+z M,             M=M0+1.

The new local coordinates are

    (v,a,b,c,d,S,S',u,u').

The three kinds of rule residual are

    L_A = S' w(v)-S,
    L_M = S' w(v)-S w(a) w(I(a,v)),
    L_G = S' w(v)-S w(b).

Define

    Q_A=K^2 B+L_A^2,
    Q_G=(v-A(a,b))^2+L_G^2,
    Q=Q_A L_M^2 Q_G.

The local polynomial is Q plus the two beta-reconstruction squares

    [x-S-(1+(i+1)y)u]^2
      +[x-S'-(1+(i+2)y)u']^2.                    (1)

Every factor and summand just displayed is nonnegative on real inputs.
Consequently its zeros have exactly one of these meanings:

* Q_A=0: either truth v=0, one of the eight unconditional axioms v=h_j,
  or v=h_B with G=0. In each case restore the premises p=q=0, and L_A=0
  is precisely the old accumulator equation.
* L_M=0: restore p=a and q=I(a,v). This is exactly a modus-ponens instance
  with conclusion v, and the correct accumulator equation.
* Q_G=0: restore p=b, q=0, and v=A(a,b). This is exactly generalization,
  with its correct accumulator equation.

Conversely every old valid rule row admits this parameterization. For MP
choose the new a to be the old first premise; for generalization choose b
to be the old first premise and retain its independent binder parameter a.
The unused schema parameters can be zero. Axiom parameters and the bundle
disequality witness retain their original values. The two beta rows agree
literally. This proves the existential local equivalence, without requiring
any unselected branch to satisfy its defining equations.

The five local label/schema coordinates v,a,b,c,d are bounded by m>=1.
The restored labels all lie below

    L(m)=I(m,m)+2=8m^2+8m+2=2(2m+1)^2.

Indeed only the MP second premise can exceed m, and it is at most I(m,m).
The carrier therefore changes from (m+1)^t to

    M=(L(m)+1)^t,          t>=1.                  (2)

The inherited carrier argument applies with L(m) in place of m. No bound
on refutation size is asserted: given a finite proof, choose m above all
schema parameters and labels; form this M; then construct the accumulator
path, its beta code, and its CRT witnesses in the original dependency order.
The remaining bounds are S,S'<=y and u,u'<=x, exactly as before.

The nonnegative arithmetic pair E-F in the code implements (1) using
(e,f)(g,h)=(eg+fh,eh+fg) and (e,f)^2=(e^2+f^2,2ef). This is an exact
ring representation. The generic majorant's proof remains coefficientwise
monotonicity of these two nonnegative polynomials.

## 2. A factorial is the unique ceiling fixed point at its squared output

**Theorem.** For any n,F in the nonnegative integers, put

    R=F^2,  C=binomial(R+n,n),  N=(R+1)^n.

Then

    F=ceil(N/C)  if and only if  F=n!.              (3)

The quotient is a rational number with positive denominator. The theorem
supplies the correctness of an ordinary polynomial graph: the displayed
power and binomial are replaced by the explicit inherited finite graphs.

**Proof.** Write K=n! and f=N/C. If F=ceil(f), then F>=1 and F<=K, since

    f=K product_{j=1}^n (R+1)/(R+j) <= K.

For n>=2, the elementary inequality 1-product(1-u_j)<=sum(u_j), with
u_j=(j-1)/(R+j), gives the strict bound

    0 <= K-f < K*n*(n-1)/(2*F^2).                  (4)

For n>=4, every factor (R+1)/(R+j) is increasing in R>=1, as is seen by
cross multiplication. Therefore f>=2^n/(n+1). At n=4 its ceiling is at
least 4. For n>=5 the inequality 2^n>=n(n+1), proved by induction starting
at 5, gives F>=n. Bound (4) now gives K-f<K/2, so F>=f>K/2. Substituting
this stronger lower bound back into (4) yields

    K-f < 2*n*(n-1)/K <= 1,

where the last inequality is K=n!>=2*n*(n-1) for n>=4. Thus
K-1<f<=K and ceil(f)=K.

The remaining cases are exact finite calculations. At n=0 and n=1 the
quotient is identically one. At n=2 and F>=1 it is
2(F^2+1)/(F^2+2), strictly between one and two. At n=3, F<=K=6; for
F=1,2,3,4,5,6 the ceilings are respectively 2,4,5,6,6,6. Hence only
F=6 is a fixed point. These cases prove soundness for every n.

For completeness take F=K. If n>=2, (4) gives
0<=K-f<n(n-1)/(2K)<=1/2, so ceil(f)=K. At n=0,1 it is immediate.
Only finite integer/rational arithmetic, induction, and six explicit
small rational calculations are used; this proof formalizes in PA and
therefore in ZFC.

An exact natural graph for the ceiling introduces r,s and uses

    N+C=C*F+r+1,          C=r+s+1.                 (5)

These imply C(F-1)<N<=CF and hence F=ceil(N/C). Conversely the ceiling
supplies the required natural remainder and slack. Positivity of C,N
also excludes F=0 without any additional positivity witness.

The unusual point is the proved fixed-point uniqueness. The radius is
allowed to depend on its own requested output, and this dependency
replaces a genuine variable-exponent power certificate by one square.
The proof does not silently assume the desired factorial value.

## 3. One square serves both required factorials

The concrete source requests H! first and t! second, with H>=t>=1.
It emits one radius

    R=F_H^2,

and uses (5) with this R for both requests. The theorem first forces
F_H=H!, so R=(H!)^2. For 2<=n<=H the same product bound gives

    0 <= n!-(R+1)^n/binomial(R+n,n)
       < n!*n*(n-1)/(2*(H!)^2)
       <= H*(H-1)/(2*H!) <= 1/2.

The n=1 quotient is exactly one. Consequently the second ceiling is t!.
Conversely the true factorial values and their Euclidean remainders
satisfy all the equations. This also works for H=1, with no n>=2 case.

In the literal builder,

    H=(2+t+x+y+m+M0)^(2^23).

This is represented by 23 ordinary squarings, not a variable exponent.
It is the rounded-up coefficientwise majorant of the local source. Thus
H>=t and H>=2 (indeed H>=4). The first factorial macro receives exactly H,
the second exactly t, and both use the same radius. These exact bindings
are recorded in `equations/parent781/factorial_radius_certificate.json`.

The radius F_H^2 is already required in the base-modulus equation for the
power F_H^t. Common-subexpression elimination shares that square. The
former request (H+2)^(H+2), its distinct base modulus, and its index graph
disappear. No shifted Pell-index construction occurs in the final circuit.

## 4. Soundness and simultaneous completeness

For soundness, start with any natural zero of the literal quadratic system.
The inherited shared power-frame theorem identifies every positive-power
request, regardless of whether its input is a polynomial in other witness
coordinates. This use does not presume that the factorial outputs are
already positive: for each represented power base n the unconditional
natural equation 2*A*n=T+n^2+1 itself excludes n=0. All exponent arguments
are syntactically positive in the literal gate DAG. The common-radix
theorem then identifies all binomial requests.
Apply the factorial fixed-point theorem to F_H and the common-radius bound
to F_t. The remaining CRT, local-source, accumulator, and Horn-flow arguments
are the inherited ones, with the explicit nine-column reparameterization
and the carrier bound (2). Thus a natural zero yields C222(1), then a finite
ZFC refutation by the named inherited calibration theorems.

For completeness, begin with a finite C222 proof. Choose t,m and the
carrier, construct its finite accumulator and beta data y,x, and obtain
the finite H. Set F_H=H!, R=(H!)^2, and F_t=t!, then form the CRT moduli
and choose the encoded local columns and index. All semantic upper
arguments of the deferred binomial requests are now fixed. Choose their
common radix as in the inherited construction, compute every true power
value, and only then choose the shared Pell frame and its auxiliary index
witnesses. This is a finite ordered construction. The self-reference in
the equations does not create a cycle in this completeness construction.
Every actual power base and exponent is positive; in particular H,t>=1
and R+1>=1 (in fact R>=4). Reusing a common factorial radius introduces no
new exponent-zero or base-zero case.

These transformations preserve the ordinary theorem formalizable in ZFC:
absence of a natural zero is equivalent to Con(ZFC). They do not prove
consistency, produce an encoded object-language derivation, or replace the
inherited semantic theorem by finite testing.

## 5. Exact materialized counts

| Construction | Natural variables | Quadratic residuals | Expanded monomials | Height |
|---|---:|---:|---:|---:|
| Inherited synchronized parent | 895 | 773 | 4,863 | 63,908,265 |
| Nine-column parent | 835 | 725 | 4,675 | 63,910,421 |
| Output-linear bootstrap predecessor | 783 | 679 | 4,441 | 63,910,260 |
| Final squared-radius parent | 781 | 677 | 4,434 | 63,910,260 |
| Final cap-64 contraction | 469 | 365 | 12,051 | 83,850,757 |
| Final cap-256 contraction | 468 | 364 | 14,842 | 83,850,989 |
| Retained output-linear cap-256 alternative | 467 | 363 | 18,479 | 83,880,005 |

All listed equations have exact degree four. The contraction is the
inherited certified nonnegative monic substitution algorithm; every
eliminated coordinate has a nonnegative polynomial restoring map, and
independent replay checks all substitutions and every coefficient.
The final source uses 23 positive-power requests, 18 primitive index
certificates, 7 distinct-base moduli, 12 binomial requests and 2 factorial
outputs. The source has nine bounded local columns.

The squared-radius source has fewer raw coordinates than its output-linear
predecessor. The deterministic contraction order gives 468 natural
coordinates versus 467 for that predecessor, while reducing the expanded
monomial count from 18,479 to 14,842. Thus the square radius is simpler
arithmetically; this comparison does not assert dominance in every metric.
The primary source and its contractions use the square radius. The
467-variable output-linear alternative is also delivered, with its own
frozen parent, restoring certificate, and portable radius-mode rebuild.

This advances the direct modest-coefficient quartic construction. It
does not beat the separate nine-positive or ten-integer high-degree forms
on variable count, and no worldwide novelty or global optimality is claimed.

## Appendix: the simpler output-linear bootstrap used during discovery

**Theorem.** For any n,F in the nonnegative integers, put

    R=n^2 F,  C=binomial(R+n,n),  N=(R+1)^n.

Then

    F=ceil(N/C)  if and only if  F=n!.           (3)

Here C and N are positive, including at n=0. Equation (3) is an ordinary
number-theoretic lemma used to prove a finite arithmetic circuit; variable
exponentiation and binomial symbols do not remain in the emitted polynomial.

**Proof.** The cases n=0 and n=1 have N=C=1 and N=C=R+1 respectively.
Assume n>=2. If F=ceil(N/C), positivity gives F>=1. Write K=n! and

    f=N/C=K product_{j=1}^n (R+1)/(R+j).

All the factors lie in (0,1]. For u_j=(j-1)/(R+j), the elementary finite
product inequality 1-product(1-u_j)<=sum(u_j) gives

    0 <= K-f
      <= K sum_{j=1}^n (j-1)/(R+j)
       < K n(n-1)/(2R)
       < K/(2F).                                (4)

There is at least one positive numerator, so the displayed strict bound
holds. Since F>=1, (4) first gives f>K/2, whence F>=f>K/2. Reusing (4)
now gives K-f<1. Since f<=K, its ceiling is precisely K, proving F=K.
Conversely take F=K. The same estimate gives 0<=K-f<1/2, so ceil(f)=K.
This proves both directions. Only finite integer/rational arithmetic and
induction on a finite product are used; the argument formalizes in PA and
therefore in ZFC.

An explicit graph for the ceiling in (3) introduces natural r,s and uses

    N+C=C F+r+1,       C=r+s+1.                  (5)

These equations are equivalent to C(F-1)<N<=CF. They also prove F>=1:
if F=0, the first equation contradicts N>0 and r<C. No extra positive-F
assumption or missing guard is needed.

The point of (3) is that an apparent algebraic cycle is harmless. The
radius is allowed to depend polynomially on the requested output; its
ceiling fixed point is proved unique. Removing a radius bound without this
uniqueness proof would not be valid.


### The retained linear-radius companion

For the optional `--radius linear` builder, the common radius is
R=H^2 F_H. The appendix theorem forces F_H=H!, and H>=t implies
R=H^2 H!>=t^2 t!. The same finite-product deficit estimate is therefore
less than 1/2 at n=t, proving the second factorial output is t!. Its
soundness and completeness have the same dependency order as the square
variant. The literal parent is `equations/parent783/equation.json`, and
`equations/natural467/` is its independently replayed contraction. The
new fixed choice of radius mode depends only on the requested variant,
never on the truth of consistency or on the existence of a refutation.
