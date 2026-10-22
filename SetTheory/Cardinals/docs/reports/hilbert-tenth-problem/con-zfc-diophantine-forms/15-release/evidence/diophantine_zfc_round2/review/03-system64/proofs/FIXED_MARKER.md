# Fixed end marker specialization: proof and exact arithmetic artifacts

This is a mathematical specialization of the repository's accepted fixed-program
compiler family. It requires a valid compiler export for the desired machine.
It does not certify arbitrary numerical assignments to the compiler ports.

## 1. Constants and primary sixteen-variable system

Let the valid compiler constants be `B=2^d`, `b`, `K=DC+B*DR`, `MC`,
`MFsource=MF_native+B-1`; the established compiler has odd `b` and `d`.
Set `u=2d+b` and the fixed integer `W0=2^b*B^2=2^u`.

The strictly positive witnesses are

`J,F,alpha,t,f,h,i,T,s,w,tau,eta,zeta,y,Z,gamma`.

All names below are polynomial abbreviations, not further existential variables:

```
q=(B-1)J+1; X=wq; Y=sq^3; E=XY;
k=eta+zeta; c=kY+eta; a=E+Y;
H=4a+3; Delta=a^2+H; Dmain=X+ac+gamma H;
C=q-F-Z-alpha-2d; W=C-Z;
R=(q^2-Z-qF)(q^2-1)+(MC+q MFsource)J;
L=E(kY); V=c(Tf-1)-Rf^2; Kaux=Delta(f^2-1).
```

Seven ordinary polynomial equations are

```
tau^2-L(L+k)=1,
Dmain^2-Delta*c^2=1,
(i*c^2)^2=Kaux,
Kaux*(V^2-y^2)+y^2=1,
k-hE-R=1,
(K+w)C+q-F-t(q-1)=1,
W=W0.
```

The emitted source is `fixed_marker76_system` in
`fixed_marker_systems.json`. Its comparison operands cost 64=34M+30A
operations. In particular, comparing `(ic^2)^2` directly with `Kaux`
deletes the two artificial rows used to turn the strong equation into an
integer-unit factor. There are sixteen witnesses and seven equations,
with maximum total degree 28. Every fixed coefficient multiplication is
charged. Powers with fixed small exponents are computed by multiplication.

The sum of the seven squared residuals has exact degree 56. The emitted
`fixed_marker76_sos` source costs 84=41M+43A operations, including every
residual subtraction, square and sum. Only the auxiliary residual has
degree 28; its leading form is

`(eta+zeta)^2*w^2*s^4*((B-1)J)^14*T^2*f^4`.

Its square cannot cancel with any other squared residual. A distinguished
nonzero coefficient is `(B-1)^28` on
`J^28*eta^4*w^4*s^8*T^4*f^8`.

## 2. Why the input bridge can be removed

The general universal construction must verify an unbounded ordinary input
`x` and thus contains a Pell bridge to the marker `W=2^(2dx+b)`. For the one
fixed instance `x=1`, the marker is the constant `W0` above. Testing the
entire exponentiation graph is unnecessary: the last displayed equation
specifies exactly its required value.

The ordinary kernel/auxiliary proof from
`review_complete86_ordinary_auxiliary_math.md`, or its normalized counterpart
`review_complete85_auxiliary_bezout_math.md`, uses the main quotient only
through `gamma>0` until after it establishes the main Pell index `p=R` and
the index sign. The input norm is only one of the independently +1 factors
at those stages. Accordingly these arguments apply to the seven-equation
system above, giving

`c=psi_A(R), Dmain=chi_A(R), R odd, R>q`, where `A=a+2`.

The marker equality and raw definitions give

`q=F+2Z+alpha+2d+W0>W0=2^u>u`.

Thus `u<R`. Both indices are odd, so `R>=u+2`. The same algebra gives the
positive raw bound needed before kernel decoding. No statement about a
computation or a power-of-two representation of `q` is needed here.

One can now reconstruct the deleted parent coordinates exactly. Put

```
kappa=psi_A(u); mu=chi_A(u);
delta=(kappa-u)/Delta;
rho=(mu-a*kappa-W0)/H;
sigma=gamma-rho.
```

For odd `u`, the standard recurrence gives `psi_A(u)=u mod Delta`.
Since `u>=3`, `psi_A(u)>u`, hence `delta` is a positive integer.
The sequence `E_A(j)=chi_A(j)-a*psi_A(j)` has `E_A(0)=1,E_A(1)=2`
and recurrence `E_A(j+1)=2A E_A(j)-E_A(j-1)`. Modulo `H=4a+3`, it is
`2^j`; for `j>=2` it is strictly greater than `2^j`. Thus `rho` is a
positive integer and the reconstructed input norm and projection hold.

The existing two-step Pell estimate, as proved in
`complete75_gamma_dominance_elimination102.md` section 3, gives

`E_A(R)-E_A(u)>A>X` when `R>=u+2`.

Consequently

`H*(gamma-rho)=E_A(R)-E_A(u)-X+W0>0`,

so `sigma` is a positive integer. Replacing `gamma` by `rho+sigma`
therefore restores the exact positive parent tuple at ordinary input 1.
This proves soundness without assuming that a parent tuple existed in
advance. Conversely, a parent tuple at input 1 has `W=W0`; replace
`rho+sigma` by `gamma` and drop the three bridge witnesses.

This is an equivalence of existential solution sets for the chosen input.
It is not a claim about arbitrary input specializations or arbitrary masks.

## 3. Compact single-polynomial alternatives

For the normalized 84-operation universal polynomial, put
`M=1+(W-W0)^2`, replace the input norm by `M`, fix `x=1`, and replace
`rho+sigma` by the new positive witness `gamma`. The old witnesses
`delta,rho,sigma` disappear. Since `M` is positive, the integer-unit
argument forces `M=1`, which is precisely `W=W0`. The other unit signs and
kernel arguments are unchanged before restoring the input coordinates.

The source transform and count/degree checks are `fixed_marker.py` and
`fixed_marker_variants.json`. All rows are explicit acyclic arithmetic
instructions. The following are the exact counts:

| Source | Witnesses | M | A | Total operations | Exact degree |
|---|---:|---:|---:|---:|---:|
| fixed_marker74 |16|41|33|74|157|
| fixed_marker75 |16|41|34|75|125|
| fixed_marker76 |16|41|35|76|101|
| fixed_marker82 |15|46|36|82|295|

The first three descend respectively from the universal 84/187,
85/155 reduced-auxiliary, and 86/131 ordinary-auxiliary sources.
These are fixed-input bounds, not new universal-input records.

To verify exact degree, put

```
Q=(B-1)J; k0=eta+zeta;
C1=Q-F-Z-alpha; W1=Q-F-2Z-alpha;
Nt1=w*C1-t*Q.
```

The nonzero leading forms for the first three outputs are respectively

```
-8*Q^91*h*gamma*i^4*k0^13*w^13*s^26*Nt1*T^2*f^2*W1^2,
-8*Q^71*h*gamma*i^2*k0^9*w^11*s^20*Nt1*T^2*f^4*W1^2,
 8*Q^55*h*gamma*i^2*k0^9*w^7*s^16*Nt1*T^2*f^4*W1^2.
```

These follow from the original source leaders after removing the input
factor of degree32 and introducing the marker factor of degree2. The main
norm's leading cancellation is the original exact expansion, unchanged by
replacing a sum of two independent variables by one independent variable.
The displayed forms are nonzero for every `B>1`, without imposing any
equation on the witnesses.

## 4. Fifteen witnesses through elimination of f

In the normalized source set

```
Qaux=(Delta*i*c^2)^2;
D=1+Delta*i^2*c^4;
b0=c+R*D; v0=c*T;
A0=Qaux*(D*v0^2+b0^2)-(Qaux-1)*y^2-1;
B0=2*Qaux*v0*b0;
N=A0^2-D*B0^2;
P=Nfirst*Nmain*M*Nindex*Ntransport.
```

The polynomial is `P*(N+1)-1`. This is `fixed_marker82` and has fifteen
positive witnesses, with `f` removed. The arithmetic implementation
shares the two cross-products instead of paying to construct `B0`.
Its degree295 leader is

`8*h*gamma*i^12*k0^27*w^21*s^48*Q^177*(Q-F)^4*Nt1*W1^2`.

As in the accepted parent proof, `B0` is nonzero on the positive retained
domain since `D>c>0` and `c+R*D` cannot vanish for integral `R`.
Because `B0` is even, `N+1` is 1 or2 modulo4 and cannot be -1. Therefore
the polynomial forces `P=1,N=0`; the rational number `f=A0/B0` has square
`D` and is a nonzero integer. The exact auxiliary remainder identities
restore a signed normalized parent zero.

To establish its sign, first suppose `f>0` and permit `T` to be signed.
The accepted signed-T proof's initial rank argument still applies with
`gamma>0` and the marker unit. Restore `delta,rho,sigma` by section2,
then invoke the original signed-T theorem on the actual original source.
It forces `T>0`. If the reconstructed `f` were negative, simultaneously
negating `f,T` preserves every retained polynomial value, giving a
positive-f, negative-T zero, a contradiction. Thus reconstructed `f>0`.

The equivalent six-equation system replaces the outer product by

`Nfirst=1, Nmain=1, Nindex=1, Ntransport=1, A0^2=D*B0^2, W=W0`.

Its literal source is `fixed_marker82_system`: 71=40M+31A operations,
15 positive witnesses,6 equations, maximum residual degree244.

## 5. Evidence boundaries

The script checks complete schedules, source-input hashes, arithmetic
counts, liveness, all retained-register equality on rational fixtures,
complete output factorization, and dense univariate degree diagnostics.
Those diagnostics are not the mathematical proof of soundness or the
uniform degree theorem; the preceding algebra and the pinned repository
lemmas supply those. No accepting ZFC-refutation witness is constructed.
No Lean/Rocq formalization of these new arithmetic specializations is claimed.

## 6. Ordinary integer-variable versions with three coordinates per witness

For unrestricted integer variables define

`Pos(a,b,c)=1+a^2+b^2+c(c+1)`.

Its image is exactly the strictly positive integers. Nonnegativity follows
from `c(c+1)>=0` for every integer c. Conversely, for n>=0, the integer
`4n+1` is 1 or5 modulo8, so Legendre's three-square theorem represents it
as three squares. Reduction modulo4 forces exactly one of the three
square roots to be odd. Writing the roots as `2a,2b,2c+1` gives
`n=a^2+b^2+c(c+1)`.

Substitute this integer polynomial for every positive witness. The
sixteen-witness system becomes seven equations in 48 unrestricted integer
variables, of maximum degree56. Its single sum-of-squares polynomial has
exact degree112. The fifteen-witness single polynomial becomes one in45
unrestricted integer variables of exact degree590. All coefficients remain
integers; there are no divisions, congruence predicates, or additional
existential variables. These are domain conversions, not variable-minimal
claims over the integers.

