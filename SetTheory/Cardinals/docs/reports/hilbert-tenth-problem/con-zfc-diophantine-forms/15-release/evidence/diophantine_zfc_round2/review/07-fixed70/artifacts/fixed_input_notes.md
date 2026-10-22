# Fixed-input compression: 70 operations, 16 positive witnesses

This note supplies the mathematical argument for the literal circuits in
`fixed_input.py` and the complete packets in `fixed_input.json`.
It is a parametric result for **the actual modified75 compiler coefficients**,
not a theorem about arbitrary values passed to the five numeral ports.
The fixed compiler must itself be instantiated for the chosen halting problem.
The arithmetic improvements below do not supply or certify that instantiation.

Pinned repository commit:
`cdd582bec13f908df3711fa9e05d1ddac368a5db`.

Pinned parent:
`Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete84_scaled_strong_output.json`,
SHA-256 `8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf`.
Its exact bytes are included as `parent84_reference.json`.

## 1. What is proved

For every fixed modified75 compiler, the 70-operation polynomial below has a
strictly positive integer zero if and only if that compiler accepts ordinary
input \(x=1\). A 71-operation variant has lower degree. A transparent
eight-equation system provides a separate, simpler interface.

| Construction | Positive witnesses | Equations | Multiplications | Additions/subtractions | Total | Exact degree |
|---|---:|---:|---:|---:|---:|---:|
| Fixed70 | 16 | 1 | 40 | 30 | 70 | 169 |
| Fixed71 | 16 | 1 | 40 | 31 | 71 | 156 |
| Fixed73 baseline | 16 | 1 | 41 | 32 | 73 | 157 |
| Transparent61 | 17 | 8 | 33 | 28 | 61 | maximum residual degree 28 |
| Transparent84 SOS | 17 | 1 | 41 | 43 | 84 | 56 |

Every binary arithmetic operation, including multiplication by a fixed
numeral, is charged. Fixed numerals, named reuse and comparisons are free
in the comparison-system column. No optimality statement is made.
The coefficients are very large; this metric does not charge their bit length.

The underlying fixed-input observation is elementary: the old input bridge
proved \(W=2^b B^{2x}\). At \(x=1\), this is a fixed integer
\[
 W_0=2^b B^2.
\]
A fixed Diophantine equation can place this numeral directly into its marker
\(C=Z+W_0\), eliminating all variable-input Pell arithmetic.

## 2. Explicit Fixed70 polynomial

Use the five fixed positive coefficients
\[
 \beta=B-1,\quad K=D_C+BD_R,\quad M_C,\quad
 M_F=M_{F,\mathrm{native}}+B-1,\quad W_0=2^bB^2.
\]
In particular **\(M_F\) is the shifted source coefficient**, not the native
one-cell field mask. The actual compiler satisfies \(B=2^d\), \(d\ge4\),
\(0<M_C,M_{F,\mathrm{native}}<B-1\), and the complete modified75 layout
and mask contract. Its \(b\) is positive.

The sixteen positive variables are
\[
 J,F,\alpha,t,f,h,i,T,s,w,\tau,\eta,\zeta,y,Z,\gamma.
\]
Define polynomial abbreviations, all evaluated by the paid circuit:
\[
\begin{aligned}
 C&=Z+W_0,& q&=C+F+\alpha,& e&=\beta J,\\
 X&=wq^2,&Y&=sq^3,&E&=XY,\\
 k&=\eta+\zeta,&c&=kY+\eta,&a&=E+Y,\\
 H&=4a+3,&\Delta&=a^2+H,&D&=X+ac+\gamma H,\\
 L&=E(kY),&
 G&=e(q-F)+(q-F-Z),\\
 R&=G(q^2-1)+(M_C+qM_F)J,\\
 V&=c(Tf-1)-Rf^2,&
 K_*&=(i\Delta c^2)^2.
\end{aligned}
\]
The seven factors are
\[
\begin{aligned}
 N_0&=\tau^2-L(L+k),&
 N_1&=D^2-\Delta c^2,\\
 N_e&=q-e,&
 N_a&=K_*(V^2-y^2)+y^2,\\
 N_k&=k-hE-R,&
 N_t&=(K+w)C+(q-F)-te,\\
 N_s^\#&=\Delta f^2-K_*.
\end{aligned}
\]
The equation is
\[
 \boxed{P_{70}=N_0N_1N_eN_aN_kN_tN_s^\#-\Delta=0.}
\]
This is an ordinary polynomial equation with integer coefficients. Its
abbreviations introduce no additional existential variables, exponentiation
with variable exponent, division, or quantifier.

Because \(a>0\), \(\Delta=(a+1)(a+3)>0\). Define only for the proof
\[
 N_s=f^2-\Delta i^2c^4.
\]
There is the exact polynomial identity
\[
 P_{70}=\Delta\bigl(N_0N_1N_eN_aN_kN_tN_s-1\bigr).
\]
Thus the product of the seven unscaled integer factors is one at every
positive zero. Each factor is initially an integer unit.

## 3. Unit signs and bounds before decoding

The first norm is
\[
 N_0=\tau^2-V_0(V_0+1)k^2,\qquad V_0=XY^2>1.
\]
The negative Pell equation at \(V_0(V_0+1)\) has no integer solutions.
For a positive solution with least positive \(k\), multiplication by the
inverse unit \(2V_0+1-2\sqrt{V_0(V_0+1)}\) gives coefficient
\[
 k'=(2V_0+1)k-2\tau,\qquad 0<k'<k,
\]
using \(V_0k<\tau<(V_0+1/2)k\). This contradiction proves \(N_0=1\).

For every integer \(a\), \(\Delta\) is zero or three modulo four.
Consequently \(N_1\) and \(N_s\) cannot equal \(-1\). Since \(K_*\) is a
square, \(N_a\) is congruent modulo four to either \(y^2\) or \(V^2\);
it too cannot equal \(-1\). Hence these four norm factors are \(+1\).
Write
\[
 N_e=\varepsilon,\qquad N_k=\kappa,\qquad N_t=\nu,
 \qquad \varepsilon,\kappa,\nu\in\{-1,1\},\quad
 \varepsilon\kappa\nu=1.
\]

The definitions already give \(C>0\), \(C<q\) and \(F+Z<q\).
Also \(q>W_0\ge2B^2\), so \(q\ge16\); no exact repunit equation is
used for this bound. From \(e=q-\varepsilon\),
\[
 G=q^2-Z-qF+(1-\varepsilon)(q-F).
\]
Since \(F,Z\ge1\) and \(F+Z<q\),
\[
 2q-1\le q^2-Z-qF\le q^2-q-1.
\]
Therefore
\[
 2q-1\le G\le q^2+q-3.
\]
The fixed masks and \(J=(q-\varepsilon)/\beta\) imply
\[
 0<(M_C+qM_F)J<(1+2q)(q+1).
\]
Combining these estimates,
\[
 (2q-1)(q^2-1)<R
 <q^4+q^3-2q^2+2q+4<q^4+q^3.
\]
Thus
\[
 R>3q,\qquad E\ge q^5>R+5,\qquad a>R+2.
\]
These estimates are obtained before knowing that \(q\) is a power of two
or that the repunit sign is positive.

## 4. Restoring the omitted auxiliary coordinates

The normalized strong equation is
\[
 f^2=1+\Delta i^2c^4.
\]
It implies \(f>c^2>2c\). Since \(R<a<\Delta\),
\[
 K_*-(Rf^2+c)
 =(\Delta-R)f^2-\Delta-c>0.
\]
The auxiliary equation is
\[
 K_*V^2-(K_*-1)y^2=1.
\]
It excludes \(V=0\). If \(v=|V|>1\), then
\[
 v^2-1=(K_*-1)(y^2-v^2),
\]
and \(y\ge v+1\) shows \(v\ge2K_*-1\).
On the other hand \(T>0\) gives \(V>-Rf^2-c>-K_*\).
This excludes all \(V<-1\).
The congruence \(V\equiv-c\pmod f\), with \(c>2\) and \(f>2c\),
excludes \(V=\pm1\). Therefore \(V>0\).

Define integers
\[
 o=cT-Rf,\qquad
 j=Tf-R\Delta i^2c^3-1.
\]
The strong equation gives
\[
 of=V+c,\qquad jc=V+R.
\]
Thus \(o,j>0\), and
\[
 V=of-c=jc-R.
\]
These are precisely the positive auxiliary congruences needed by the
repository's generic strong-rank and signed step-down lemmas.
Their use has not presumed an already decoded computation.

## 5. Index recovery does not need the repunit sign

Let \(\Psi_A,\Chi_A\) denote the standard Pell sequences for discriminant
\(A^2-1\), where \(A=a+2\). The first norm gives
\[
 P=2XY^2+1,\quad k=2\Psi_P(n),\quad n\ge1.
\]
The main norm gives \(c=\Psi_A(p)\), \(D=\Chi_A(p)\), \(p\ge1\).
Since \(P>A\) and \(c>k\), one has \(p>n\).
As \(P\equiv1\pmod E\),
\[
 2n\equiv R+\kappa\pmod E.
\]
The bounds \(0<R+\kappa<E\) give \(n\ge(R-1)/2\), so in particular
\(p\ge25\), \(c>A\Delta^2\) and \(c>2p\).
Moreover \(k=R+\kappa+hE\), with \(h\ge1\), gives \(c>2R\).

Apply the retained strong-rank theorem with ordinary strong coordinate
\(i_{\mathrm{ordinary}}=\Delta i\):
\[
 (i_{\mathrm{ordinary}}c^2)^2=\Delta(f^2-1).
\]
Together with the just-restored positive \(o,j\), the signed auxiliary
step-down theorem gives \(p=R\). These are the local arguments of
`complete85_auxiliary_bezout_projection.md`, Sections 3--4; none of those
steps uses the input norm or the exact repunit equation.

Write \(2n=R+\kappa+vE\). The least-positive-residue argument gives
\(v\ge0\); if \(v\ge1\), then \(E>R+5\) yields \(n>R=p\), impossible.
Hence \(2n=R+\kappa\).
If \(\kappa=-1\), then \(p=2n+1\).
Pell duplication with \(Q_2=\Chi_A(2)>P\) gives
\[
 \Psi_A(2n)=2A\Psi_{Q_2}(n)\ge A k.
\]
It follows that \(c=\Psi_A(2n+1)>k(Y+1)\), contrary to
\(kY<c<k(Y+1)\), which follows from \(\eta,\zeta>0\).
Consequently \(\kappa=1\) and
\[
 p=R=2n-1.
\]

## 6. Dyadic recovery precedes repunit recovery

Put \(r=n-1\), so \(R=2r+1\), \(r\ge1\).
The lower Pell ratio argument of
`complete75_asymmetric_scale_tradeoffs.md`, Section 3, gives
\[
 \frac{c}{k/2}>
 \xi=\frac{(X+1)^{2r}}{X^r}.
\]
For clarity, this follows from
\(\Psi_A(2r+1)\ge(2A-1)^{2r}\),
\(\Psi_P(r+1)\le(2P)^r\), and \(6XY^2>a\).
It uses no upper-error estimate and no exact repunit equation.
Since \(c/k<Y+1\),
\[
 Y>\xi/2-1>X^r/3,\qquad a>X^{r+1}/3>2^R.
\]
The main-root recurrence yields
\[
 \Chi_A(R)-a\Psi_A(R)\equiv2^R\pmod{4a+3}.
\]
The definition of \(D\) makes its left side congruent to \(X\).
Both \(0<X<a\) and \(0<2^R<a\), so
\[
 X=2^R.
\]
Because \(X=wq^2\), \(q\) is a power of two, say \(q=2^u\).

Now the negative repunit sign is impossible.
If \(\varepsilon=-1\), then
\[
 2^u\equiv-1\pmod{2^d-1}.
\]
Reducing \(u\) modulo \(d\) would give
\(2^v=2^d-2\) for some \(0\le v<d\).
For \(d\ge3\), however,
\(2^v\le2^{d-1}<2^d-2\).
Thus \(\varepsilon=1\), and the remaining product sign gives \(\nu=1\).

We have recovered
\[
 e=q-1=\beta J,\qquad q=B^N
\]
for a positive integer \(N\). All originally altered packing and
transport identities are now exactly the original ones.
Since \(R>3q>3u\), \(q^3\mid X\), so the original symmetric kernel scale
is restored by \(w_{\mathrm{sym}}=X/q^3>0\).

The physical transport quotient is
\[
 z=t-1+w(q+1)C>0,
\]
because \(X-w=w(q^2-1)\).
Thus the original transport equation
\[
 (K+X)C=F+z(q-1)
\]
holds with a positive quotient.

The retained half-binomial kernel and population argument therefore
recover the two modified75 masks and the exact native helical word.
The fixed marker \(C=Z+W_0\), together with \(C<q=B^N\), gives \(N>2\).
It inserts precisely one End selector at cell 2.
The origin Start, synchronization, marker bijection and same-run theorem
are unchanged. The represented fixed machine accepts ordinary input 1.
No variable-input Pell equations are needed.

## 7. Completeness and the precise maps

Start with any positive zero of the known universal84 source at \(x=1\).
Its proved input bridge gives \(C=Z+W_0\).
Set
\[
 \gamma_{\mathrm{new}}=\rho+\sigma,\qquad
 \alpha_{\mathrm{new}}=q-C-F=Z+\alpha_{\mathrm{old}}+2d>0.
\]
All retained main and auxiliary quantities are unchanged.
The existing decoded kernel gives \(q^3\mid X\) and \(X=2^R\).

For Fixed73, retain the original \(w,t\).
For Fixed71, retain the original \(w,t\) and replace the squared budget
by the now-exact linear repunit factor.
For Fixed70, put
\[
 w_{\mathrm{new}}=X/q^2=w_{\mathrm{old}}/q,\qquad
 t_{\mathrm{new}}=t_{\mathrm{old}}-w_{\mathrm{new}}C.
\]
The first coordinate is a positive integer.
The second is integral because the two transport multipliers differ
by \(w_{\mathrm{new}}(q-1)\).
Its positivity must not be inferred merely from \(t_{\mathrm{old}}>0\):
it follows from
\[
 t_{\mathrm{new}}
 =\frac{(K+w_{\mathrm{new}})C-F}{q-1}+1>1,
\]
since \(w_{\mathrm{new}}=X/q^2>q>F\).
All seven factors have their required values, giving a positive zero.

These arguments establish equality of the represented acceptance
condition. They do **not** claim a bijection with all old input-Pell
witness tuples: several old coordinates have been discarded.

## 8. Exact degrees

For Fixed70 let
\[
 Q=F+Z+\alpha,\qquad k_0=\eta+\zeta.
\]
The exact factor degrees, in circuit order, are
\[
 24,\ 20,\ 1,\ 64,\ 8,\ 2,\ 50.
\]
The main norm's leading cancellation is handled by
\[
 (ac+L_0)^2-(a^2+H)c^2=2acL_0+L_0^2-Hc^2,
 \qquad L_0=X+\gamma H.
\]
The resulting leading homogeneous form of the complete polynomial is
\[
 -8Q^{104}h\gamma i^4 k_0^{13}w^{13}s^{26}T^2f^2
       (Q-\beta J)(wZ-\beta Jt).
\]
It is nonzero uniformly for every \(\beta>0\).
In particular, the coefficient of
\[
 J^2F^{104}h\gamma i^4\eta^{13}w^{13}s^{26}T^2f^2t
\]
is \(-8\beta^2\).
The degree is therefore exactly \(169\), rather than the syntactic upper
bound \(173\).

For Fixed71 the leading form is
\[
 -8Q^{91}h\gamma i^4 k_0^{13}w^{13}s^{26}T^2f^2
       (Q-\beta J)(wZ-tQ).
\]
Its degree is \(156\); the coefficient of
\(JF^{92}h\gamma i^4\eta^{13}w^{13}s^{26}T^2f^2t\)
is \(-8\beta\).
Fixed73 has the analogous squared-budget leader and degree \(157\).

## 9. Transparent alternative

Use seventeen positive variables
\[
 J,F,\alpha,z,Z,f,h,i,j,o,s,w,\tau,\eta,\zeta,\gamma,y
\]
and the same five fixed numerals. Put
\[
\begin{aligned}
 C&=Z+W_0,&q&=C+F+\alpha,&X&=wq^3,&Y&=sq^3,\\
 E&=XY,&k&=\eta+\zeta,&c&=kY+\eta,&a&=E+Y,\\
 H&=4a+3,&\Delta&=a^2+H,&D&=X+ac+\gamma H,\\
 L&=E(kY),&
 R&=(q^2-Z-qF)(q^2-1)+(M_C+qM_F)J,\\
 K_{\mathrm{aux}}&=\Delta(f^2-1),&
 U&=jc-R,&V&=of-c.
\end{aligned}
\]
The eight equations are
\[
\begin{gathered}
 \beta J=q-1,\qquad
 (K+X)C=F+z(q-1),\\
 \tau^2-L(L+k)=1,\qquad
 k-hE-R=1,\qquad
 D^2-\Delta c^2=1,\\
 (ic^2)^2=K_{\mathrm{aux}},\qquad
 K_{\mathrm{aux}}(V^2-y^2)+y^2=1,\qquad U=V.
\end{gathered}
\]
At every solution the strong equation identifies the auxiliary coefficient
with \((ic^2)^2\), and \(U=V\) restores the original auxiliary argument.
The full original kernel then applies, and the fixed-marker argument
above gives input 1. Completeness follows from the known compiler,
or from a normalized zero by restoring positive \(j,o\) and using
\(i_{\mathrm{ordinary}}=\Delta i\).

All derived formerly-positive coordinates are positive:
\(C,q,X,Y,E,k,c,a,D\) by definition, and \(R\) by
\(F+Z<q\) and the exact repunit bounds.
This last point is essential: the weaker choice \(q=C+\alpha\) does
not itself bound \(F\), and therefore does not justify eliminating the
formerly positive packed-index coordinate.

The auxiliary residual has degree exactly 28; all others have degree at
most 26. Its degree-28 leader is
\(\Delta_{\mathrm{top}}f^2c_{\mathrm{top}}^2\ne0\).
The sum of the eight squared residuals consequently has exact degree 56.
Its fully paid evaluation uses 84 operations.

## 10. Verification scope

The script reads and authenticates the exact parent JSON, reconstructs
all five complete circuits, verifies every dependency and liveness, and
records their full row arrays. It performs exact integer checks of
the local identities, packing rewrites and sum-of-squares finalizer.
Two independent modular univariate specializations per polynomial
attain the stated degrees and all factor degrees.

These computations corroborate the symbolic proofs; they do not establish
the generic Pell-rank lemma, instantiate a ZFC machine compiler, check a
machine-level consistency equivalence, or decide whether a positive zero
exists. Those obligations must be recorded separately in the main report.
No predecessor Python source is imported or executed.

Relevant inherited proof notes, all under the pinned commit:

- `Papers/1980/FIXED_RAW_UNIVERSAL_75_PROOF.md`.
- `Papers/1980/PELL_RELAXED_AUXILIARY_PROOF.md`.
- `Papers/research-wip/native-stream-queue/complete75_half_binomial_compiler.md`.
- `Papers/research-wip/native-stream-queue/complete75_asymmetric_scale_tradeoffs.md`.
- `Papers/research-wip/native-stream-queue/complete85_auxiliary_bezout_projection.md`.
- `Papers/research-wip/native-stream-queue/complete84_scaled_strong_output.md`.

Natural and unrestricted integer versions must be distinguished.
The displayed domains are strictly positive integers. Substituting
\(v=1+u_1^2+u_2^2+u_3^2+u_4^2\) for each positive variable gives an
ordinary equation over all integers. Thus Fixed70 has a 64-integer-variable
version of degree at most 338, and the transparent SOS has a
68-integer-variable version of degree at most 112. These are conversions,
not improved bounds for the positive-variable constructions.


