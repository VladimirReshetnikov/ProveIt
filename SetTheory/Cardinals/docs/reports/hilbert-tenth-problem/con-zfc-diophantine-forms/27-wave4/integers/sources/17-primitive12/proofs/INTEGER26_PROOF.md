# Signed primitive-element extension: 26 unrestricted integers

This extends the twelve-positive-variable primitive-element construction.
It inherits the coherent coefficient tuple and signed compiler theorem of
`14-integer29` at ProveIt commit
`f0ae4e0991ca44a7bb4e5671d42e33d775e48035`. It is ordinary mathematics
formalizable in ZFC, not a new assistant-checked formalization.

The final package's default is the reduced T4 tuple in `INSTANCE.json`.
Section 6 of `compiler/PRUNED_T4_PROOF.md` transfers the same positive mask
bounds, odd exponent `d0=5^16`, power-of-five padding and `R=3 mod 4`
canonical tuning. These are exactly the coefficient-dependent properties
needed for the inherited odd-i and square-w completeness argument. The
original `14-integer29` tuple remains a coherent alternative. Ports from
different tuples must never be mixed.

## Domain and arithmetic

Keep exactly `J,F,alpha,z,s,eta,zeta` strictly positive. Let `h,T,t,r,u0`
be arbitrary integers, and substitute `i=2r+1`, `w=u0^2`.
After replacing the seven positive coordinates by independent copies of
`Pos(x,y,z)=x^2+x+y^2+z^2+1`, the construction has `7*3+5=26` unrestricted
integer unknowns.

Use the twelve-variable construction's definitions of q,Cw,X,Y,E,k,c,a,H,
Delta,R,Nindex,Ntransport,ell,A,I,D,Q,d,v,Z,e,B,b,G. In particular

```
A=1+ell(ell+k), ell=EkY,
D=1+Delta i^2 c^4, Q=(Delta i c^2)^2, d=Q-1,
v=cT, Z=c+RD, e=Q(Dv^2+Z^2)-1, B=2QvZ,
b=X+ac, G=Delta c^2+1.
```

At this stage `w>=0` is permitted. Consequently X may be zero, but
Y,k,c,a,H,Delta,D,Q,d are positive, with k,c>=2 and D,Q>1. The outer
transport equation (or its unit version) implies Cw>=0 and R>0, even
before X is known to be positive. This follows directly: if Cw<=-1,
then q-F<=q-1 and z>=1 imply

`(K+w)Cw+q-F-z(q-1)<=-(K+w)<-1`.

Here K>1 for the authentic coefficient tuple. That contradicts the
transport factor being a unit. Thus q-F=Cw+alpha>0,
and the authentic positive mask coefficients imply R>0. In the exact
transport system Cw=0 is impossible as well, but the weaker statement
already suffices below.

## Bounds valid with signed T and h, and with X=0

Set

```
g=c+X,
u=ell+k,
at=2g+1,
S=at*u+g,
C=v^2+D+Z,
ay=Q*C*S+1,
rf=(a+2)(i^2+1)c^2,
C2=c(T^2+1)+c+R*rf,
af=2*ay*C2+S+1.
```

The unknowns eliminated by the primitive element are the roots

```
gamma=(sgn_gamma sqrt(G)-b)/H,
tau=sgn_tau sqrt(A),
f=sgn_f sqrt(D),
y=sgn_y sqrt((e-Bf)/d).
```

Square roots may temporarily be complex; all estimates are absolute-value
estimates in C. The following bounds hold for every one of the sixteen
root choices:

1. `|gamma|<g`. Indeed `sqrt(G)<(a+2)c`, since `c>1`, and
   `(sqrt(G)+b)/H < ((2a+2)c+X)/H < c+X`.
2. `1<=|tau|<u`. The upper bound follows from
   `(ell+k)^2-A=ell*k+k^2-1>0`, including ell=0.
3. `|f|=sqrt(D)>1` and `sqrt(D)<rf`. For the latter,
   `sqrt(1+Delta i^2 c^4)<(a+2)|i|c^2+1`, and the chosen rf is larger.
4. `|y|>1/(Q*C)`. To see this, first
   `|v|sqrt(D)+Z<C` by the elementary arithmetic-geometric mean bound.
   Hence both conjugate numbers `e+B sqrt(D)` and `e-B sqrt(D)` have
   absolute value less than `Q*C^2`: they equal
   `Q(v sqrt(D)+Z)^2-1` and `Q(v sqrt(D)-Z)^2-1`.
   Their product is the integer `e^2-B^2D`, which is nonzero. If B=0,
   nonvanishing follows from `e=Q*(integer)-1`. If B!=0 and the product
   vanished, D would be a rational square and hence an integer square
   f^2; then one would have `Q(vf+Z)^2=1` or `Q(vf-Z)^2=1`, impossible
   for Q>1. Therefore each conjugate has absolute value greater than
   `1/(Q*C^2)`. Dividing by `d<Q` and taking square roots proves the claim.
5. `|y|<2*C2*sqrt(D)`. Since `Q>=4`,
   `|y|^2 <= (Q*(|v|sqrt(D)+Z)^2+1)/(Q-1)` is less than
   `4*(|v|sqrt(D)+Z)^2`, using `Z>1`. Thus
   `|y|/sqrt(D)<2(c|T|+c/sqrt(D)+R sqrt(D))<2*C2`.

No Pell rank theorem, positive main norm, or X>0 premise has been used in
these bounds. This is the feature needed to avoid a circular zero-scale
argument.

## Primitive element and pairwise separation

Use the single retained integer coordinate t to impose

`t=gamma+at*tau+ay*y+af*f`.

The division-free norm polynomial is obtained exactly as in the positive
construction, replacing its tau coefficient 1 by at and its two weights
by ay,af above. Explicitly, work first in
`Q[f,tau]/(f^2-D,tau^2-A)`, put

```
z0=Ht+b-H*af*f-H*at*tau,
K0=d(z0^2+G)-H^2*ay^2*(e-Bf),
E0=K0^2-4d^2*G*z0^2,
N=E0(f,tau)*E0(f,-tau),
P=N(f)*N(-f).
```

Reducing f^2 and tau^2 yields an explicit integer polynomial P in the
twelve mixed-domain coordinates. Because d,H are nonzero, P=0 is exactly
the assertion that at least one of the sixteen displayed radical sums
equals t.

The sixteen sums are distinct. If two tuples first differ in f, their
f-term difference is `2af sqrt(D)`, larger than the sum of all possible
lower-term differences because `af sqrt(D)>ay|y|+S`. If f is fixed and
y changes sign, the y-term difference is larger than `2S` because
`ay|y|>S`. If f,y are fixed and tau changes sign, the tau-term difference
is at least `2at>2g`. Finally, opposite gamma branches differ because G>0.
The lower combined bound used here is
`|gamma+at*tau|<g+at*u=S`.

Let L be the finite splitting field of the radical expressions. If P=0
at integer coordinates, one radical sum equals the rational integer t.
Every automorphism of L over Q fixes t and permutes the sixteen root
tuples. Distinctness forces it to fix the selected tuple coordinatewise.
Thus gamma,tau,y,f are rational. This does not require t to be positive,
odd or nonzero.

Since tau^2=A and f^2=D are integers, tau and f are integers. The rational
auxiliary integrality lemma below shows y is an integer. The defining
integer relation for t then makes gamma an integer as well.

## Rational auxiliary integrality: a complete proof

**Lemma.** If rho>1 is an integer, V is an integer and y is rational, then

`rho^2 V^2-(rho^2-1)y^2=1`

implies y is an integer.

Write `y=a/b` in lowest terms with b>0. The equation implies
`b^2 | rho^2-1`. Put `D0=(rho^2-1)/b^2`. This is a positive nonsquare
integer: if D0 were a square, the factorization
`(rho-b sqrt(D0))(rho+b sqrt(D0))=1` would contradict rho>1. The two pairs

`(rho,b)` and `(rho*|V|,|a|)`

are positive solutions of `x^2-D0 z^2=1`. (V and a cannot be zero.)
Let the least positive unit be `epsilon=x1+z1 sqrt(D0)`, and write

`rho=x_n, b=z_n, rho*|V|=x_m, |a|=z_m`,

where `epsilon^j=x_j+z_j sqrt(D0)`. Since `x_n | x_m`, write
`m=q n+r`, `0<=r<n`. Modulo x_n the identity
`epsilon^(2n)=-1` holds coefficientwise. If q is even, it follows that
`x_m=+/-x_r (mod x_n)`, impossible because `1<=x_r<x_n`. If q is odd,

`x_m=+/-D0 z_n z_r (mod x_n)`.

Here `gcd(D0 z_n,x_n)=1` by the Pell equation, so x_n divides z_r. Since
`0<=z_r<x_n`, this forces r=0. Thus m is an odd multiple of n. Expanding
`epsilon^m=(epsilon^n)^(m/n)` shows `z_n | z_m`. Hence b divides a, and
coprimality implies b=1. This proves the lemma.

In the primitive construction take `rho=|Delta i c^2|`,
`V=c(Tf-1)-Rf^2`. Both are integers after f is restored, and its auxiliary
equation is exactly the lemma's equation. Thus y is integral.

## Completing soundness and completeness

The restored gamma, tau, f, y satisfy the original main, first, normalized
strong, and auxiliary norms. In particular the main norm now excludes
w=0 by reduction modulo H, exactly as in `14-integer29`: if X=0 then
`Dmain=ac+gamma H` and `Delta=a^2+H`, giving `0=1 mod H`.

The signed-domain proof of that package applies to the resulting integer
tuple with seven positive coordinates, odd i, square w and unrestricted
h,T,gamma,f,tau,y. It recovers the same blank K215 halting predicate.

For completeness use the canonical odd-i, square-w witness of
`14-integer29`. Its gamma,tau,f,y are integers. Define t by the displayed
weighted sum; it is an unrestricted integer, so no new parity or sign
requirement arises. The norm vanishes. Therefore the new 26-integer
system represents precisely the same existence predicate.

The system is `Nindex=1`, `Ntransport=1`, `P=0`. A single polynomial can
always be obtained as the sum of squares of its three residuals.
The smaller product finalizer `Nindex*Ntransport*(1+P)-1` is also valid.
Here is the square-modulo-four proof. Write the first quartic expression
as `E0=E00+E01*tau` over `Z[f]/(f^2-D)`. The next norm is
`N=E00^2-A*E01^2=N0+N1*f`. The linear-f coefficient of any square in
this quadratic algebra is even, so N1 is even. Thus
`P=N0^2-D*N1^2=N0^2 (mod 4)`. A product zero therefore gives P=0 and
equal outer unit signs; the preceding primitive proof only used transport
as a unit, and the inherited signed soundness proof forces both remaining
signs positive.

The improvement is from the repository's 29 unrestricted integers to 26.
It costs a substantially larger degree and circuit. The independent
27-integer product in `INTEGER27_PROOF.md` remains a lower-degree
tradeoff. Neither construction claims a global minimum or changes the
classical universal Diophantine bounds.

## Literal sizes and exact degrees

The standalone standard-library generator `build_integer26.py` emits
three fully live circuits. Its comparisons are free, and every binary
addition, subtraction and multiplication, including fixed-numeral
multiplication, is counted.

| Form | Variables | Equations | Degree | Operations |
|---|---:|---:|---:|---:|
| System | 26 Z | 3 | 5248 |225 =132M+93A|
| Product |26 Z|1|5265|229 =134M+95A|
| Sum of squares |26 Z|1|10496|232 =135M+97A|

The exact degrees of the two outer residuals and the norm are 13,4,5248.
After substitution, the bounds g,u,at,S,C,ay,rf,C2,af have degrees
`10,22,10,32,74,196,34,42,238`, respectively. In the quadratic algebra
`Q[f]/(f^2-D)`, whose D has degree 66, the norm computation's final pair
N has constant coefficient degree 2624 and linear-f coefficient degree
2559. Thus P has degree 5248; its second term has smaller degree
`66+2*2559=5184`. The leading constant coefficient is nonzero: successive
unique leading terms come from d times the squared f component of z0,
then its square, then another square. These degrees are uniform for valid
positive fixed compiler coefficients. Products of the three nonzero
leading forms give degree `13+4+5248=5265`; the sum of squares has the norm
as its unique largest-degree residual.

The generator's optional exact univariate modular diagnostic checks all
three degree claims. Validation uses explicit exceptions and remains
active under `python -O`; no successful finite check is represented as a
proof of the compiler theorem, the full enormous coefficients, or ZFC
consistency.

