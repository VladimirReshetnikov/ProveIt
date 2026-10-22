# Fixed-marker Diophantine construction: arithmetic audit

Pinned source commit: `cdd582bec13f908df3711fa9e05d1ddac368a5db`.

The reusable arithmetic package is `arithmetic/`.
The paper gives the logical equivalence proof and the concrete
finite compiler recipe. The present notes give the exact formulas, source
counts, uniform degree proofs, and audit boundaries.

## 1. Principal system: 16 positive variables and seven equations

The variables are

`J,F,alpha,t,f,h,i,T,s,w,tau,eta,zeta,y,Z,gamma`,

all strictly positive integers. The six fixed numerals are

* `Bm1=B-1`;
* `Kconstant=DC+B*DR`;
* `MC`, the modified half-binomial data mask;
* `MF=MF_native+B-1`, the shifted field-mask coefficient;
* `W0=2^(2*d+b)=R_inner*B^2`;
* `W0plus2d=W0+2*d`.

The finite window/compiler recipe supplies `B=2^d` and odd positive `b`.
The symbols `R_inner` and the packed index `R` below must not be conflated.

Define the following polynomial abbreviations. They are not additional
existential variables:

```
q=(B-1)J+1, X=wq, Y=sq^3, E=XY,
k=eta+zeta, c=kY+eta, a=E+Y,
H=4a+3, Delta=a^2+H=(a+1)(a+3),
Dmain=X+ac+gamma*H, C=Z+W0,
R=(q^2-Z-qF)(q^2-1)+(MC+q*MF)J,
V=c(Tf-1)-Rf^2,
e=q-F-2Z-alpha-(W0+2d).
```

Set

```
N0=tau^2-X*Y^2*(X*Y^2+1)*k^2,
N1=Dmain^2-Delta*c^2,
Ns=f^2-Delta*i^2*c^4,
Na=Delta*(f^2-1)*(V^2-y^2)+y^2,
Nk=k-hE-R,
Nt=(Kconstant+w)C+q-F-t(q-1).
```

The recommended system is

```
N0=N1=Ns=Na=Nk=Nt=1,    e=0.
```

The actual source is `fixed16_system66_degree34.json`:
**66=35M+31A operations, seven equations, 16 positive variables**.
The maximum equation degree is **34**. Signed intermediate registers are
only polynomial abbreviations; no additional witness variables are hidden.
The actual seven comparisons use six already computed factors and the
linear comparison `C_after_alpha=Z+W0plus2d`.

The source is obtained from the literal complete84 source by deleting its
entire ordinary-input Pell bridge, replacing `rho+sigma` by one supplied
positive `gamma`, using a literal fixed marker, and using the reduced
auxiliary coefficient on the strong equation. The half-binomial compiler
and the two ratio slacks remain intact.

At `Ns=1`, the coefficient in `Na` is
`Delta*(f^2-1)=Delta^2*i^2*c^4=(Delta*i*c^2)^2`.
Thus the auxiliary factor is exactly the accepted parent factor. This is
an equivalence on the common strong equation, not an off-zero polynomial
identity.

## 2. One-polynomial variants with 16 positive variables

Put `P=N0*N1*Na*Nk*Nt*Ns` using the reduced unscaled `Na,Ns` above.
Then

```
P*(1+e^2)-1=0
```

has source `fixed16_product76_degree113.json`:
**76=42M+34A operations; exact degree 113**. Integer units force `e=0`.
The strong norm cannot be -1 modulo four, and restores the square auxiliary
coefficient. The first, main, and auxiliary factors then have positive unit
sign. The accepted pre-input rank/ratio proof forces `Nk=Nt=1`, exactly as
in the parent source. The paper cites the source-specific
pre-input argument; the product-to-system implication is not valid for
arbitrary coefficient assignments without the compiler hypotheses.

For a lower degree, take the sum of the squares of the seven displayed
residuals. `fixed16_sos86_degree68.json` has
**86=42M+44A operations; exact degree 68**. Its equivalence to the seven
equations is immediate over the integers and needs no unit-sign argument.

For a lower operation count, retain the parent square coefficient
`Q=(Delta*i*c^2)^2` and scaled strong factor
`Nss=Delta*f^2-Q=Delta*Ns`. Let
`Na0=Q*(V^2-y^2)+y^2` and `P4=N0*N1*Nk*Nt`. Then

```
P4*Na0*Nss*(1+e^2)-Delta=0
```

has **74=41M+33A operations and exact degree 157**. The reduced scaled
version replacing `Na0` by `Na` costs **75=41M+34A** and has degree **125**.
The extra factor `Delta` is positive before any equation is imposed, so its
cancellation is legitimate on the stated positive domain.

## 3. Principal single equation with 15 positive variables

Delete `f` and retain the other 15 positive variables. Keep the earlier
definitions through `R`, and define

```
Q=Delta^2*i^2*c^4,
D=1+Delta*i^2*c^4,
b0=c+R*D, u0=c*T,
A0=Q*(D*u0^2+b0^2)-(Q-1)*y^2-1,
B0=2*Q*u0*b0,
K=A0^2-D*B0^2,
P4=N0*N1*Nk*Nt.
```

The equation is

```
P4*(K+1)*(1+e^2)-1=0.
```

`fixed15_product82_degree295.json` computes it in
**82=46M+36A operations; exact degree 295**. The helper does not separately
compute `B0`; it uses
`D*B0^2=4*(Q*D*u0^2)*(Q*b0^2)`, sharing the products required by `A0`.

The integer-unit argument gives `e=0`. Since `B0` is even,
`K+1=A0^2+1 (mod 4)` cannot be -1. Hence `K=0` and `P4=1`.
Before any equation, `D>c>0`, so `b0=c+RD` is never zero for integral `R`;
therefore `B0` is nonzero. The rational number `f=A0/B0` satisfies
`f^2=D`; a rational square root of an integer is integral. Substitution
restores the strong and auxiliary equations. Its positivity is the one
nontrivial signed-domain step: use the accepted signed-quotient theorem
after the pre-input bootstrap and the fixed-input extension lemma. A
negative `f` can be simultaneously negated with `T`, contradicting that
theorem. The proof is in the paper and `fixed_input_proof_notes.md`.

### 80-operation alternative

Put `P=P4*(1+e^2)`. The equation

```
[P*(A0+1)-1]^2-D*(P*B0)^2=0
```

is `fixed15_outer80_degree346.json`:
**80=46M+34A operations; exact degree 346**.
Reducing modulo `P` gives `P | 1`, so `P=+1` or `-1` and `e=0`.
Now `f=(A0+1-P)/B0` is rational and has square `D`, hence is a nonzero
integer. The restored auxiliary factor equals `P`. It cannot be -1 modulo
four because `Q` is a square. Therefore `P=1`, `f=A0/B0`, and the result
reduces to the 82-operation equation. This argument avoids a separate
appeal to the earlier complete90 theorem.

## 4. Uniform degree proofs

Let `Q0=(B-1)J`, `k0=eta+zeta`,
`T0=wZ-tQ0`, and `L0=Q0-F-2Z-alpha`.
All witnesses have degree one, all six compiler numerals degree zero.
The key retained highest terms are

```
X_top=wQ0, Y_top=sQ0^3, a_top=wsQ0^4,
c_top=k0*sQ0^3, Delta_top=w^2*s^2*Q0^8,
R_top=Q0^3*(Q0-F), V_top=k0*sQ0^3*T*f,
N0_top=-w^2*s^4*Q0^14*k0^2,
N1_top=8*w^2*s^3*Q0^11*k0*gamma,
Nk_top=-h*w*s*Q0^4, Nt_top=T0, e_top=L0.
```

The main norm's leading cancellation is the exact all-ring identity

```
(X+ac+g)^2-(a^2+H)c^2
  =X^2+2Xg+g^2+2acX+2acg-Hc^2,
```

with `g=gamma*H`. Its unique highest term is `2acg`, degree 18.
There are no other hidden degree cancellations in the displayed leading
form computations. In particular `R` has degree 4, not degree 7.

For the reduced 16-variable system the factor degrees are respectively

```
N0:22, N1:18, Na:28, Nk:7, Nt:2, Ns:34, e:1.
```

The degree-68 sum of squares has unique highest component

```
w^4*s^12*Q0^40*i^4*k0^8,
```

from the squared strong residual. Its coefficient at
`J^40*w^4*s^12*i^4*eta^8` is `(B-1)^40`, uniformly nonzero.

The degree-113 polynomial has leading form

```
-8*gamma*h*i^2*k0^9*w^9*s^18*Q0^63*T^2*f^4*T0*L0^2.
```

Its monomial
`J^64*gamma*h*i^2*eta^9*w^9*s^18*t*T^2*f^4*alpha^2`
has coefficient `8*(B-1)^64`, uniformly nonzero.
Multiplying this leader by `Delta_top` gives the degree-125 scaled result.

The degree-157 polynomial has leading form

```
-8*gamma*h*i^4*k0^13*w^13*s^26*Q0^91*T^2*f^2*T0*L0^2.
```

The monomial
`J^92*gamma*h*i^4*eta^13*w^13*s^26*t*T^2*f^2*alpha^2`
has coefficient `8*(B-1)^92`, uniformly nonzero.

For the 15-variable polynomials,

```
P4_top=8*gamma*h*k0^3*w^5*s^8*Q0^29*T0,
Q_top=i^2*k0^4*w^4*s^8*Q0^28,
D_top=i^2*k0^4*w^2*s^6*Q0^20,
A0_top=Q_top*R_top^2*D_top^2.
```

Their degrees are `49,46,34,122`, respectively.
The term `D*B0^2` has degree 214, so `K` has exact degree 244 with
leader `A0_top^2`. Hence the degree-295 polynomial has leader

```
8*gamma*h*i^12*k0^27*w^21*s^48*Q0^177
  *(Q0-F)^4*T0*L0^2.
```

Its monomial
`J^182*gamma*h*i^12*eta^27*w^21*s^48*t*alpha^2`
has coefficient `-8*(B-1)^182`, uniformly nonzero.

The degree-346 alternative has leader

```
64*gamma^2*h^2*i^12*k0^30*w^26*s^56*Q0^206
  *(Q0-F)^4*T0^2*L0^4.
```

Its monomial
`J^212*gamma^2*h^2*i^12*eta^30*w^26*s^56*t^2*alpha^4`
has coefficient `64*(B-1)^212`, uniformly nonzero.

These coefficient proofs establish uniform exact degrees for every valid
fixed compiler slice. The dense modular univariate runs are supplementary
checks of the literal complete circuits, not the reason uniformity holds.

## 5. Domain conversion

For ordinary nonnegative unknowns, replace each positive witness `z` by
`n+1`. This preserves the number of unknowns and every total degree.

If unrestricted integer unknowns are desired, three new integer variables
per positive witness suffice:

```
z=1+a^2+b^2+c(c+1).
```

The expression is positive for all integers `a,b,c`. It covers every
positive integer: represent `4(z-1)+1` by three squares using Legendre's
three-square theorem; modulo four exactly one square is odd and two are
even, giving the displayed form. Thus the principal 15-variable equation
becomes a polynomial in 45 unrestricted integer unknowns, degree 590.
The 16-variable sum of squares becomes one polynomial in 48 unrestricted
integer unknowns, degree 136. Four-square substitution is more familiar
but uses 60 or 64 integer variables and is unnecessary here.

## 6. Arithmetic verification actually performed

`build_fixed_sources.py` reads the exact pinned complete84 JSON as inert
data (SHA-256 `8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf`).
It emits all complete instruction arrays, checks topological order and
liveness of every instruction and free port, verifies literal operation
counts, propagates the justified degree bounds, and evaluates each full
source as a dense univariate polynomial modulo 1000000007. Every stated
degree is attained in that diagnostic. Both normal and optimized Python
replays passed with explicit exception checks.

`verify_closed_forms.py` independently writes the displayed mathematical
formulas and compares them with every complete emitted circuit on twelve
signed-integer and twelve rational assignments each. All seven variants
pass. The diagnostic coefficients deliberately are small noncompiler
fixtures. No full halting tuple or astronomical native Pell witness is
materialized; neither checker proves the semantic equivalence.

## 7. Source-specific dependencies and limitations

Primary files in `Computability/HilbertTenthProblem/Papers/`:

* `1980/FIXED_RAW_UNIVERSAL_75_PROOF.md`: base compiler theorem;
* `1980/FIXED_RAW_UNIVERSAL_81_PROOF.md`: exact stay-step markers;
* `1980/EXPLORATION_HELICAL_UNARY_TABLEAU.md`: helical finite-run semantics;
* `research-wip/native-stream-queue/complete75_half_binomial_compiler.md`:
  modified masks and actual packed-index completeness;
* `research-wip/native-stream-queue/complete85_auxiliary_bezout_projection.md`
  and `review_complete85_auxiliary_bezout_math.md`: pre-input rank and sign
  arguments; the input norm appears only as an additional positive unit
  in the early unit decomposition;
* `research-wip/native-stream-queue/complete85_reduced_auxiliary_degree.md`:
  the strong-equation coefficient replacement;
* `research-wip/native-stream-queue/complete92_norm_unit_guard.md` and
  `complete84_signed_quotient_soundness_scout.md`: signed root restoration.

The large compiler constants must be specified by their actual finite
recipes, not merely said to exist by MRDP. Operation counts treat those
fixed integers as free numerical coefficients and do not measure their
binary description lengths. No globally simplest or smallest polynomial
is proved. The new polynomial bridge is a mathematical proof supported
by exact algebra checks, not a newly checked Lean/Rocq theorem.
