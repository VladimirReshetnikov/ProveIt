# Twelve integers at degree 2048 {#sec:twelve2048}

A late supplied interpolation theorem permits a further synthesis. The
result is a literal polynomial in twelve unrestricted integer variables,
of exact degree $2048$, evaluated in $233$ live binary operations ($148$
multiplications, $53$ additions and $32$ subtractions). It improves the
supplied twelve-variable $4832/248$ degree--cost point. The supplied
$16000/223$ point remains a cheaper, higher-degree alternative. No
fewest-variable or global optimality claim is made.

The new changes are a coprime homogeneous quintic carrier, a guard Pell
witness divisible by three, fixed prime separation in place of large
size weights, and a doubled auxiliary-root center. The full-residue
interpolation theorem and the direct normalized signed-kernel
calibration are imported from
`ConZFC_Twelve_Integer_Interpolation_2026-10-24`. Its exact proofs,
provenance and notices are retained. In particular, this is not a
literal restoration of the earlier odd-multiplier source chart, nor a
new proof-assistant certificate.

## Complete polynomial specification

The twelve coordinates are $$j,C,z,h,r,v,w,T,c,n,t,s_0\in\mathbb Z.$$
Use the same complete six fixed source-34/source-71 numerals as before.
Define $$\begin{aligned}
 J&=6j+1,&q&=\beta J+1,&W&=12w+4,\\
 X&=qW,&Y&=qv,&E&=XY,\\
 a&=E+Y,&H&=4a+3,&\Delta&=a^2+H,\\
 F&=(K_0+W)C-z(q-1),&&&\\
 R&=(q(q-F)-C)(q^2-1)+(M_C+qM_F)J,&&&\\
 k&=R+1+hE,&\eta&=c-Yk,&\zeta&=k-\eta.
\end{aligned}$$ Put $$\begin{aligned}
 d_g&=(A_{\rm cone}F)(B_{\rm cone}C)
          -(q-A_{\rm cone}F-B_{\rm cone}C)^2,\\
 P&=d_g\eta\zeta-(t^2-d_g-\eta\zeta+1)^2,\\
 s&=3s_0,&D_g&=(3P-4)s^2+1,&I&=src^2,\\
 D_f&=1+\Delta I^2,&Q&=\Delta^2 I^2,&\delta&=Q-1,\\
 V&=D_f(c-R+4IT)-c,&C_y&=QV^2-1,&D_a&=\delta C_y,\\
 \ell&=EYk,&D_\tau&=1+\ell(\ell+k),&D_m&=1+\Delta c^2,\\
 b_0&=X+ac,&M&=2q^2,&L&=MH,\\
 e&=v-q^2,&\widetilde b&=Mb_0+He,&
 u&=LT-\widetilde b,\\
 \widetilde D&=M^2D_m.&&&
\end{aligned}$$ For the fixed intersective quintic
$$\pi(x)=(x^2+31)(x^3+x+1),\qquad
 \Phi_L(x)=L^5\pi(x/L),$$ the following integer polynomials are its
exact quadratic remainder: $$\begin{aligned}
 A={}&u^5+10u^3\widetilde D+5u\widetilde D^2
       +32L^2(u^3+3u\widetilde D)\\
    &+L^3(u^2+\widetilde D)+31L^4u+31L^5,\\
 B={}&5u^4+10u^2\widetilde D+\widetilde D^2
       +32L^2(3u^2+\widetilde D)+2L^3u+31L^4.
\end{aligned}$$ Thus $A+B\widetilde d=\Phi_L(u+\widetilde d)$ when
$\widetilde d^2=\widetilde D$. Finally set
$$S=IL^5,\qquad C_a=(2Q-1)V,\qquad Z=S(n+C_a)-A.$$ With $\mathcal F_5$
denoting the ordinary $32$-sign norm polynomial, the complete equation
is $$\boxed{\mathcal P_{12}
 =\mathcal F_5\bigl(Z;B^2\widetilde D,
 4S^2D_a,36S^2D_f,324S^2D_\tau,2916S^2D_g\bigr)=0.}$$ There is no
denominator clearing in this norm: all five radicands are integer
polynomials. The displayed homogeneous notation is expanded in the
actual DAG. No square root, division, variable exponent or additional
quantified register occurs in the exported equation.

## Exclude the entire zero multiplier branch first

For all integer inputs $q$ is nonzero, even and $2$ modulo three;
$X\equiv2\pmod3$ and $a\in6\mathbb Z$. Hence $\Delta=(a+1)(a+3)\ge3$,
and $H$ is nonzero, odd and divisible by three. Also $H\equiv3\pmod q$,
so $\gcd(H,M)=1$ and $L\ne0$. Thus $D_m\ge1$ and $\widetilde D>0$,
including $v=0$.

The imported elementary quintic lemma says that $\pi$ has no zero in a
real extension of $\mathbb Q$ of degree at most two. The quadratic
factor has no real zero, while the cubic has degree three and is
irreducible by the rational-root test. Consequently
$$A+B\sqrt{\widetilde D}\ne0,
 \qquad A-B\sqrt{\widetilde D}\ne0.$$ If $I=0$, then $S=0$, the last
four norm radicands vanish, and the entire polynomial specializes to
$$(A^2-B^2\widetilde D)^{16}\ne0.$$ Every zero therefore has
$I,S,s_0,r,c\ne0$. This is established before dividing a factor relation
by $S$. Since $Q=(\Delta I)^2$, at such a zero $Q>1$ and $\delta\ne0$.

## Small fixed weights replace all size separators

Modulo three the new carrier has
$$M\equiv2,\quad L\equiv0,\quad b_0\equiv2,
 \quad u\equiv2,\quad\widetilde D\equiv1.$$ Thus
$B\equiv5+10+1\equiv1\pmod3$. Also
$$D_f\equiv D_\tau\equiv D_a\equiv D_g\equiv1\pmod3.$$ For $D_a$ use
$Q\equiv0\pmod9$; for $D_g$ use $s=3s_0$. For $D_\tau$, the
factorization $1+(XY^2)(XY^2+1)k^2$ has $XY^2\equiv0$ or $2$ modulo
three.

Divide a vanishing factor by the already nonzero $S$. The five weighted
roots $$\frac{BMd}{S},\quad 2\widetilde y,\quad6f,
 \quad18\tau,\quad54g$$ have squared three-adic orders respectively
$$-2v_3(S),\quad0,\quad2,\quad4,\quad6,$$ where $d^2=D_m$,
$\widetilde y^2=D_a$, $f^2=D_f$, $\tau^2=D_\tau$, $g^2=D_g$. Each subset
of at least two has a unique even minimum. Normalize its smallest root
by the corresponding power of three and multiply a putative zero sum
over all signs of the other roots. The product is a polynomial in the
rational squared roots and is a nonzero unit modulo three, a
contradiction. Subtracting a Galois conjugate of the rational factor
relation would give just such a forbidden signed subsum. All roots are
therefore rational. The nonzero rational multiplier $BM/S$ causes no
loss: $d$ is rational too. Roots of integer radicands are integral. No
size estimate, radical positivity assumption or bound on $R$ was used
for this extraction. Global monotonicity of the chosen quintic, although
true, is not needed by this new proof: $B\equiv1\pmod3$ already supplies
its nonvanishing.

Now $D_g=g^2\ge0$. Since $s\ne0$, the alternative $P\le0$ would give
$D_g=(3P-4)s^2+1\le-3$. Thus $P>0$, and the joint-positivity identity
gives $d_g>0$ and $\eta\zeta>0$. The rational value
$y=\widetilde y/\delta$ satisfies $$QV^2-(Q-1)y^2=1.$$
Adjacent-coefficient Pell descent makes $y$ integral.

## One monic carrier restores both congruences

After absorbing the factor signs into the integer roots, the norm
relation gives $$S\mid A+BMd=\Phi_L(Md-\widetilde b+LT).$$ In particular
$L^5$ divides this homogeneous monic quintic. For a prime with
$p^a\Vert L$, if its argument had order $b<a$, the monic fifth-power
term would have order $5b$, strictly below every other term. That
contradicts divisibility by $p^{5a}$. Therefore $$L\mid M(d-b_0)-He.$$
Reduction modulo the coprime factors $M,H$ gives
$$M\mid e,\qquad H\mid d-b_0,
 \qquad v=q^2(2v_{\rm old}+1),\qquad
 \gamma=(d-b_0)/H\in\mathbb Z.$$ Thus $Y=(2v_{\rm old}+1)q^3$ is
recovered with its full odd quotient. Moreover the quintic argument
divided by $L$ is exactly $$T+\gamma-e/M.$$ This proves both congruences
without adding a variable or presupposing that $v$ is nonzero.

The late source's direct normalized signed-kernel proof now applies. The
physical coordinates satisfy its first, main and normalized strong Pell
equations, strict guards and native transport/index equations. Its two
auxiliary quotients are restored by $$\begin{aligned}
 o&=f(c-R+4IT),\\
 j_{\rm aux}&=\Delta s^2r^2c^3(c-R)+4srcD_fT,
\end{aligned}$$ so $V=fo-c=cj_{\rm aux}-R$. The normalized rank argument
uses $c^2\mid I$ and does not require $I/c^2$ to be odd. Accordingly, we
do not assert that the old coordinate $(\Delta sr-1)/2$ is integral. The
inherited signed step-down, residue orientation and native compiler then
produce a finite syntactic refutation, with their ordinary theorem
status unchanged.

## Completeness and the exceptional guard value

Start with the late source's canonical native witnesses and set
$v=q^2(2v_{\rm old}+1)$. Choose its nearest-square coordinate $t$ so
$P>0$. A crucial exception must be excluded before forcing $3\mid s$: if
$P=1$, the guard equation would be $g^2+s^2=1$ and no nonzero multiple
of three could serve as $s$.

Here that exception is impossible. Both cone products and $q$ are even,
so $d_g\equiv0\pmod4$. Therefore
$$P\equiv-(t^2-d_g-\eta\zeta+1)^2\equiv0\text{ or }3\pmod4.$$ Positive
$P$ is at least three. Thus $D=3P-4$ is positive and $2$ modulo three,
hence nonsquare. Take a positive Pell pair $g_1^2-Ds_1^2=1$. Modulo
three, $g_1^2+s_1^2=1$, so $3\mid g_1s_1$. Squaring the unit gives
$$g=g_1^2+Ds_1^2,\qquad s=2g_1s_1>0,
 \qquad 3\mid s.$$ Set $s_0=s/3$. No outer coordinate has changed.

Invoke the imported full-residue interpolation lemma with $N=s$. It
supplies a single normalized Pell pair $I,f$, with $4sc^2\mid I$,
*before* a residue is requested, and then realizes every class of $T$
modulo this same $I$ in $$V=f^2(c-R+4IT)-c,\qquad
 (\Delta I)^2V^2-((\Delta I)^2-1)y^2=1.$$ Put $r=I/(sc^2)$. The lemma's
hypotheses include even $a+2$, $R\equiv c\equiv3\pmod4$, all supplied by
the canonical source. Its proof uses the corrected period $4n_0f$ modulo
$f^2$ and the Lucas valuation bound $\gcd(4n_0f,4I^2)\mid4I$; mere
infinitude of Pell solutions would not suffice.

Choose an intersective residue for $\pi(T+\gamma-e/M)$ modulo $I$.
Interpolation supplies $T,y$ in that class, leaving $I,f$ fixed. Hence
$$A+BMd=L^5\pi(T+\gamma-e/M)$$ is divisible by $S=IL^5$. With
$\widetilde y=\delta y$, choose
$$n=\frac{A+BMd}{S}+2\widetilde y+6f+18\tau+54g-(2Q-1)V.$$ This is
integral and makes one norm factor vanish. The witness order is native
data, then $t,s,s_0$, then $I,f,r$, then the intersective residue and
$T,y$, and finally $n$. There is no circular residue choice.

## Exact degree 2048

The relevant polynomial degrees are $$\begin{array}{c|rrrrrrrrrr}
\text{register}&H&\Delta&P&I&D_f&Q&V&D_a&D_g&L\\\hline
\text{degree}&4&8&28&4&16&24&21&90&30&6
\end{array}$$ and $$\deg A=35,\quad\deg B=28,\quad\deg S=34,
 \quad\deg C_a=45,\quad\deg D_\tau=22,
 \quad\deg\widetilde D=14.$$ Pair the two auxiliary signs first. Let
$B_*$ denote $Sn-A$ plus the four signed non-auxiliary radical terms.
Their weights are $35,42,45,49$ for main, strong, first and guard, so
$B_*$ has weight at most $49$. The paired factor is exactly
$$B_*^2+2SC_aB_*+S^2(V^2+4Q-4),$$ because the polynomial identity
$$((2Q-1)V)^2-4(Q-1)(QV^2-1)=V^2+4Q-4$$ holds universally. Its term
bounds are $98,128,110$. Taking sixteen sign choices proves degree at
most $16\cdot128=2048$. The unique leading paired term is
$2SC_a(\mathbin{\pm}54S\sqrt{D_g})$; the eight negative signs cancel.
Thus the full leading form is
$$108^{16}S_0^{32}(C_a)_0^{16}(D_g)_0^8\ne0.$$ More explicitly, the
coefficient of
$$j^{928}w^{288}v^{320}h^{32}s_0^{128}r^{112}c^{224}T^{16}$$ is
$$\boxed{2^{2064}3^{1400}\beta^{928}>0.}$$ The exponent sum is $2048$.
The $h^{32}$ term uniquely selects $ha_0$ throughout the top part of
$k^{32}$; $T^{16}$ then uniquely selects $4I_0T$ throughout
$(4I_0T-R_0)^{16}$. The remaining factors are monomials, so no other
fixed coefficient can cancel this term.

Independent actual-coefficient line certificates modulo $65521$ and
$65519$ also attain degree $2048$. The complete $233$-operation DAG has
no dead gates or hidden input leaves. Independent arithmetic checks use
a separate binomial quintic remainder and full $32$-sign product,
including every intersection of the exceptional slices $s_0=0,r=0,c=0$.
These finite checks do not replace the unbounded interpolation or native
calibration proofs. The resulting consistency equivalence is an ordinary
mathematical theorem composed with those explicitly retained sources,
not a proof of consistency or a completed object-language ZFC
derivation.

## Exact inherited source and reproduction

The imported source is ConZFC_Twelve_Integer_Interpolation_2026-10-24,
archive SHA-256 f44b903de17a70316787ff57562a3d8fe3bdec12791e266318cedb49e7125f72,
reviewing repository snapshot 04a1d79222d55cabe4ba52897863fc33baa8c268.
SOURCE_PINS.json authenticates the copied proof files and notices.

The full-residue interpolation statement and its proof are retained in
inherited/INTERPOLATION12.md, Section 6. The direct normalized signed-kernel
proof is retained in inherited/INDEPENDENT_TWELVE_AUDIT.md, Section 2,
together with its cited signed source proofs. These are ordinary mathematical
proof dependencies, not a claim that the new endpoint has been checked by
a proof-assistant kernel.

Run python build.py, python check.py, and python -O check.py. The independent
checker imports no builder or upstream code. Its two exact univariate
specializations attain degree 2048 with leading coefficients 14607 modulo
65521 and 2944 modulo 65519. CHECKS.json records every slope and the actual
six fixed-coefficient residues. The finite arithmetic checks are not a
bounded search for consistency or a substitute for the unbounded source
calibration.
