# Independent review of the fifteen-positive-variable degree-24 construction

This is an internal AI-assisted independent review, prepared by a separate agent in the same work session. It is not an external review, peer review, or proof-assistant certificate. It checks the proposed construction against the pinned ProveIt source 53 algebraic proof, the archived squared-modulus proof, and the complete compact coefficient adapter packaged with this submission. It does not independently reprove the inherited K215-to-ZFC calibration.

## 1. Definitions reviewed

The unknowns are the fifteen strictly positive integers

`j,F,alpha,z,f,h,i,T,X,Y,r,eta,zeta,u,gamma`.

On the complete source-44 compact coefficient tuple (d=590069, B=2^590069, padding prime 581197), put

\[
\begin{aligned}
J&=3j+1,&q&=\beta J+1,&C&=q-F-\alpha,\\
E&=XY,&k&=\eta+\zeta,&c&=kY+\eta,\\
a&=E+Y,&H&=4a+3,&\Delta&=a^2+H=(a+2)^2-1,\\
D_0&=X+ac+\gamma H,&&&\\
G&=(q-1)(q-F)+\alpha,
&R&=G(q^2-1)+(M_C+qM_F)J,&&\\
\widehat R&=k-hXY-1,&I&=ic^2,&A_0&=\Delta(f^2-1),\\
\ell&=XY^2k,&V&=f^2(cT-\widehat R)-c.&&
\end{aligned}
\]

The six residuals reviewed are

\[
\begin{aligned}
A&=[q^3(\ell+r)+Y]^2-q^6[\ell(\ell+k)+1],\\
B_1&=[qD_0+XH]^2-q^2(\Delta c^2+1),\\
B_2&=\widehat R-R,\\
B_3&=q[KC+(q-F)-z(q-1)]+XC-q,\\
B_4&=(V+u)^2-A_0u(2V+u)-1,\\
B_5&=I^2-A_0.
\end{aligned}
\]

The equation is \(A^2+B_1^2+\cdots+B_5^2=0\).

## 2. Soundness reduction to the established positive system

Since the complete coefficient tuple has \(B=2^d\) with odd \(d\), \(\beta=B-1\equiv1\pmod3\). Therefore \(q\equiv2\pmod3\).

For every positive integer \(m\), the elementary valuation implication
\(m^2\mid t^2\Rightarrow m\mid t\) is valid without primality or squarefreeness assumptions. Applying it to \(A=0\) gives
\(q^3\mid Y\). Define

\[
s_0=Y/q^3>0,\qquad \tau_0=\ell+r+s_0>0.
\]

Then

\[
\tau_0^2=(XY^2)(XY^2+1)k^2+1.
\]

Also \(q\mid a\), so \(H\equiv3\pmod q\), and \(\gcd(q,H)=1\). From \(B_1=0\), the same valuation implication gives \(q\mid XH\), hence \(q\mid X\). Put

\[
w_0=X/q>0,\qquad \gamma_0=\gamma+w_0>0.
\]

Dividing \(B_1=0\) by \(q^2\) now yields

\[
(X+ac+\gamma_0H)^2-\Delta c^2=1.
\]

The residuals \(B_2=B_3=0\) give the established index and transport equations with both right-hand sides equal to one:

\[
k-hE-R=1,\qquad (K+w_0)C+(q-F)-z(q-1)=1.
\]

Set \(T_0=fT>0\). Because \(\widehat R=R\), the new \(V\) is precisely

\[
c(T_0f-1)-Rf^2.
\]

Finally, \(B_5=0\) gives \(A_0=I^2\); since \(c\ge3\) and \(i>0\), \(I\ge9\). Put \(y_0=|V+u|\). The identity

\[
(V+u)^2-A_0u(2V+u)
=A_0V^2-(A_0-1)(V+u)^2
\]

turns \(B_4=0\) into the established auxiliary norm equation. If \(y_0=0\), it would assert \(I^2V^2=1\), impossible for \(I\ge9\). Thus all recovered coordinates are strictly positive. The established source-53 six-equation soundness theorem applies directly. No advance assertion that \(V>0\) is needed here; that conclusion is supplied in the established theorem.

## 3. Completeness and positive gaps

The inherited compiler can pad a finite refutation to a canonical positive normalized solution with \(q=B^N\), odd \(N\), \(J=(q-1)/(B-1)\), \(R\equiv3\pmod4\), and all norm/index/transport values equal to one. The packaged coefficient adapter, `coefficients/PROOF.md`, takes each relevant dimension to be a sufficiently large power of the odd prime 581197, and explicitly retains odd d and N. Source 53 supplies the general algebraic kernel proof; its different numeric coefficient tuple is not mixed into this construction. Since \(B\equiv-1\pmod3\), odd \(N\) gives \(J\equiv1\pmod3\). Sufficient padding makes \(j=(J-1)/3\) strictly positive.

### First root gap

Let \(v=XY^2\), so \(\ell=vk\). The original first norm gives

\[
\tau_0^2=\ell^2+k\ell+1,
\qquad
\tau_0^2-(\ell+k/3)^2=k^2(v/3-1/9)+1>0.
\]

Hence \(\tau_0-\ell>k/3\). The canonical index equation implies
\(k=R+1+hXY>XY\), and \(X\ge q\ge16\). Consequently
\(k/3>Y/q^3=s_0\). Thus

\[
r=\tau_0-\ell-s_0>0.
\]

### Main root gap

Let \(D=X+ac+\gamma_0H\) be the established positive main root. Since
\(\Delta>(a+1)^2\), \(D>(a+1)c\), and therefore

\[
\gamma_0>(c-X)/H.
\]

The canonical first Pell index is at least three. With \(P_0=2XY^2+1\),

\[
k=2\psi_{P_0}(n)\ge2\psi_{P_0}(3)
=2(4P_0^2-1)>32X^2Y^4,
\qquad c>kY>32X^2Y^5.
\]

Also \(H\le9XY\) for the canonical \(X,Y\ge16\). Thus
\((c-X)/H>X>X/q=w_0\). It follows that

\[
\gamma=\gamma_0-w_0>0.
\]

### Squared-modulus auxiliary reconstruction

Let the canonical normalized strong coordinate be \(i_0\), with
\(f^2=1+\Delta i_0^2c^4\). Choose the new coordinate
\(i=\Delta i_0\). Then \(I=ic^2\) and
\(I^2=\Delta(f^2-1)\).

Write \(R=2t+1\) with odd \(t\). For the integer polynomial \(Q_t\) defined by
\(\chi_Z(2t+1)=ZQ_t(Z^2)\), the standard recurrence gives

\[
Q_t(0)=(-1)^t(2t+1),\qquad
Q_t(1-A^2)=(-1)^t\psi_A(2t+1),
\quad A=a+2.
\]

Choose

\[
V_* =\chi_I(R)/I=Q_t(I^2)>0,
\qquad y_* =\psi_I(R)>0.
\]

Because \(I^2\equiv1-A^2\pmod{f^2}\), \(c=\psi_A(R)\), and \(c\mid I\), the identities give

\[
V_*\equiv-c\pmod{f^2},\qquad
V_*\equiv-R\pmod c.
\]

Furthermore \(f^2\equiv1\pmod c\) and \(\gcd(c,f)=1\). Therefore

\[
T=\frac{V_*+c+Rf^2}{cf^2}
\]

is a strictly positive integer, and it satisfies
\(V_*=f^2(cT-R)-c\). The Pell identity supplies

\[
I^2V_*^2-(I^2-1)y_*^2=1.
\]

Since \(I>1\) and \(R\ge3\), \(V_*>1\). Hence

\[
y_*^2-V_*^2=\frac{V_*^2-1}{I^2-1}>0.
\]

The final gap coordinate \(u=y_*-V_*\) is therefore a strictly positive integer. Every residual vanishes.

## 4. Exact total degree

The six residual degrees are respectively

\[
11,\quad9,\quad4,\quad3,\quad12,\quad10.
\]

The degree-5 homogeneous part of \(V\) is
\(f^2Y[(\eta+\zeta)T+hX]\); the degree-6 homogeneous part of \(A_0\) is
\(X^2Y^2f^2\). The auxiliary residual has the nonzero degree-12 part

\[
-2X^2Y^3f^4u[(\eta+\zeta)T+hX].
\]

It is the sole residual of degree twelve. Therefore the complete sum of squares has exact total degree twenty-four, with leading homogeneous polynomial

\[
4X^4Y^6f^8u^2[(\eta+\zeta)T+hX]^2.
\]

## 5. Review conclusion and scope

No flaw was found in the new existence reduction. It preserves the complete fixed coefficient tuple and does not assume consistency. Its use of canonical witness replacement, rather than a same-assignment bijection, must remain explicit. The mathematical improvement is the new degree/variable tradeoff within the audited repository lineage. The argument does not prove global minimality, and it inherits the original compiler and calibration proof boundary.

For prior operation-count comparisons at degree 44, the appropriate audited best baseline is **44/75**, supplied by `47-sparse-support/minima/gap_minima75.json` and its `README.txt`, rather than 44/76. The 44/76 root-gap equation remains a direct structural predecessor, but it is not the least-cost archived equation at that degree. These are degree/operation pairs, with fifteen strictly positive variables throughout.

Sources checked: pinned repository source 53 `short/PROOF.md` for the algebraic relaxed-rank kernel; the packaged complete compact adapter `coefficients/PROOF.md`, especially its padding and parity sections, for d=590069; archived source-66 `SQUARED_MODULUS_PROOF.md` for the polynomial congruence identity. The former source-53 tuple has d=1064921 and prime 2341; those numerals are not used in the delivered construction.

## 6. Tradeoff variants and independent executable check

For the degree-26 variant, the coupled residual becomes `q*(Nk*Nt-1)` after recovery of `X/q`. Thus the established relaxed kernel receives `Nk*Nt=1`; its proof explicitly handles both initial unit signs and recovers the canonical positive signs. The main and first norm are already one. Canonical completeness supplies all factors equal to one, and the same positive gaps work.

For the degree-30 variant, `X=w*q` is retained and only the first root is used for integral reconstruction. Its paired residual makes `N1`, `Nk`, and `Nt` integer units. The value `N1=-1` is impossible because `Delta=(a+2)^2-1` is zero or three modulo four: in the first case a square would be minus one modulo four, and in the second a sum of two squares would be three modulo four. Hence `N1=1` and `Nk*Nt=1`, exactly as required by the established kernel. Canonical completeness uses the first and auxiliary positive gaps and requires no main-root gamma shift.

The separately written standard-library `code/independent_check.py` imports no project algebra or builder. It authenticates all four packaged gzip and raw payloads, validates circuit topology, liveness, and operation counts, then compares an independent formula implementation against all six primary and degree-certificate circuits. Running from `/tmp` under both ordinary Python and `python3 -O` passed 7,344 scalar residual/output comparisons and 72 exact univariate polynomial ray comparisons over three finite fields. Explicit cancellation formulas give independent upper degree bounds, and nonzero leading coefficients on these rays certify matching lower bounds for the authentic fixed coefficients. The resulting residual degrees are `(11,9,4,3,12,10)`, `(11,9,7,13,10)`, and `(12,15,15,10)` for the degree-24, degree-26, and degree-30 variants, respectively. The deterministic receipt is `certificates/INDEPENDENT_FORMULA_CHECK.json`.

These executable checks verify finite arithmetic claims and transcription. They do not replace the mathematical existence-equivalence proofs or the inherited semantic compiler and calibration theorem.

## 7. Explicit domain translations

The package also supplies `circuits/p15_nonnegative_degree24.json`, using fifteen nonnegative variables with each positive coordinate replaced by `1+x`, and `circuits/p60_integer_degree48.json`, using sixty unrestricted integer variables with each positive coordinate replaced by `1+x_1^2+x_2^2+x_3^2+x_4^2`. The first map is a bijection onto positive coordinates; the second is surjective by Lagrange's four-square theorem. These are standard domain clarifications, with no frontier claim.

The division-free circuits have exactly 105 and 210 binary operations. The separate standard-library builder and checker `code/domain_translations.py` preserves the parent circuit after literal substitution, authenticates the coefficient payloads, and verifies all gate and witness liveness. It passes from `/tmp` under ordinary Python and `python3 -O`. Across the two translations, it checks 594 deterministic modular assignments, comparing all six residuals and the final output. Exact finite differences on the all-equal ray verify degree-24 leading coefficient 36 and degree-48 leading coefficient `36*4^24`, respectively. The corresponding receipt is `certificates/DOMAIN_TRANSLATIONS.json`.
