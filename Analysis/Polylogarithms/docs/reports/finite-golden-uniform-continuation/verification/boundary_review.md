# Independent audit of the critical-boundary section

**Reviewer:** depth / independent-proof agent.  
**Date:** 2026-10-10.  
**File reviewed:** output/polylogarithms_uniform_continuation_20261010/article/real_boundary.tex.  
**SHA-256:** 4ebe5891bedeedf207700803ded579cef453539ecf5784aee1226d0ba2bc012b.

## Verdict

**PASS.** The uniform local expansion, the two-term crossing asymptotic, the symmetric-point coefficient, the convergence of Jordan parts, and the total-variation exponential law are mathematically sound for each fixed \(b\in(0,1)\). I found no additional correction to the current final section. The root author's correction that the local remainder constant can depend on the radius \(T_0<2\pi\) is already present in the version reviewed.

This review uses the actual final article section and the definitions and proved results in geometry.tex. No article file was edited. The checks below are analytic; no numerical experiment is used to justify a theorem.

## 1. Exact decomposition and Bernoulli coefficients

Write \(p=1-b\), \(a=p+\varepsilon\), so \(a+b=1+\varepsilon\). The scaled representation is

\[
k_\varepsilon(T)=T^\varepsilon\left[-\frac1{\Gamma(1+\varepsilon)}
+\frac{I(T)}{\Gamma(a)\Gamma(b)}\right],\qquad
I(T)=\int_0^\infty\frac{g(s)}{e^{Ts}-1}\,ds,
\]

where \(g(s)=s^{b-1}[1-(1-s)_+^{a-1}]\). With
\(h(v)=(e^v-1)^{-1}-v^{-1}\), subtraction and the subsequent split of \(g\) are legitimate as absolutely convergent integrals. Near zero \(g(s)=O_b(s^b)\); the singularity at \(s=1\) has exponent at least \(p-1>-1\); and at infinity \(g(s)h(Ts)=O_T(s^{b-2})\), integrable because \(b<1\). Thus

\[
I(T)=\frac1T\int_0^\infty\frac{g(s)}s\,ds
+\int_0^\infty s^{b-1}h(Ts)\,ds
-\int_0^1s^{b-1}(1-s)^{a-1}h(Ts)\,ds.
\]

The first integral is \((\varepsilon/p)B(b,a)\). The second equals \(\Gamma(b)\zeta(b)T^{-b}\). The article's continuation argument is valid: splitting the standard Bose integral at 1 and subtracting \(1/v\) only on \((0,1)\) gives an expression analytic for \(\Re b>0\), apart from \(1/(b-1)\). For \(0<b<1\), this term is minus the tail integral of \(v^{b-2}\) over \((1,\infty)\), recovering the fully subtracted integral. Its strictly negative integrand also proves \(\zeta(b)<0\).

The Taylor series

\[
h(v)=-\frac12+\sum_{\ell\ge1}\frac{B_{2\ell}}{(2\ell)!}v^{2\ell-1}
\]

has radius \(2\pi\). The integrated constant term contributes \(+T^\varepsilon/[2\Gamma(1+\varepsilon)]\) to \(k_\varepsilon\), combining with the explicit negative term to give \(-T^\varepsilon/[2\Gamma(1+\varepsilon)]\). There is no missing constant or factor of two.

For \(\ell\ge1\), beta integration gives

\[
-\frac{B_{2\ell}\Gamma(b+2\ell-1)}
{(2\ell)!\,\Gamma(b)\Gamma(\varepsilon+2\ell)}
T^{\varepsilon+2\ell-1}.
\]

After factoring \(T^{\varepsilon-1}\), this is exactly the article's coefficient of \(T^{2\ell}\). Its first two terms are

\[
-\frac{b}{12\Gamma(2+\varepsilon)}T^2,\qquad
+\frac{b(b+1)(b+2)}{720\Gamma(4+\varepsilon)}T^4.
\]

This independently verifies the signs, gamma arguments, and first omitted order. The remaining fractional-power term is \(\zeta(b)T^p/\Gamma(p+\varepsilon)\), also as stated.

### Uniformity

For \(0\le\varepsilon\le\varepsilon_0<b\),

\[
s^{b-1}(1-s)^{p+\varepsilon-1}
\le s^{b-1}(1-s)^{p-1},\qquad 0<s<1.
\]

This beta weight is integrable. The reciprocal gamma factors are uniformly bounded on their compact parameter intervals. Cauchy estimates on any circle \(T_0<T_1<2\pi\) therefore provide the asserted uniform remainder after beta integration. The outside factor \(T\) in the bracket turns the \(O((Ts)^3)\) remainder of \(h\) after its linear term into \(O_{b,T_0}(T^4)\). Uniformity includes \(\varepsilon=0\). No assertion at \(T=2\pi\) is needed.

## 2. Crossing scale and its correction

Pointwise continuity in \(\varepsilon\) follows from a uniform majorant in the scaled integral. The limiting critical kernel is strictly negative at every fixed \(T>0\). Since the interior kernel is positive before its unique crossing, \(T_\varepsilon\to0\).

The equation at the zero is

\[
\frac\varepsilon p
=C_\varepsilon T_\varepsilon^p+\frac{T_\varepsilon}2
+\frac{bT_\varepsilon^2}{12(1+\varepsilon)}
+O_b(T_\varepsilon^4),\qquad
C_\varepsilon=\frac{[-\zeta(b)]\Gamma(1+\varepsilon)}{\Gamma(p+\varepsilon)}.
\]

Here \(C_\varepsilon\) tends to a positive finite constant. The last three terms are \(o(T_\varepsilon^p)\), since \(0<p<1\). Hence \(T_\varepsilon/\tau_\varepsilon\to1\) with precisely the gamma quotient in the article.

For the error hierarchy, put \(y=T_\varepsilon/\tau_\varepsilon\) and \(q=\tau_\varepsilon/\varepsilon\). Direct division gives

\[
1=y^p+\frac p2qy
+\frac{bp}{12(1+\varepsilon)}\varepsilon q^2y^2
+O_b(\varepsilon^3q^4).
\]

Since \(q=O_b(\varepsilon^{b/p})\to0\), the last two terms are \(O_b(\varepsilon q^2)\), uniformly for \(y\) near 1. The mean value theorem first yields \(y-1=O_b(q)\). Taylor expansion then gives

\[
0=p(y-1)+\frac p2q+O_b(q^2),\qquad
y=1-\frac q2+O_b(q^2).
\]

Thus

\[
T_\varepsilon=\tau_\varepsilon-\frac{\tau_\varepsilon^2}{2\varepsilon}
+O_b\!\left(\frac{\tau_\varepsilon^3}{\varepsilon^2}\right).
\]

In particular, the \(bT^2\) term causes no omitted correction of a larger order: after division it is only \(O(\varepsilon q^2)\). The proof works for all fixed \(b\in(0,1)\), including small \(b\), for which convergence of \(q\) can be slow. The leading constant \(K_b\) and the conversion \(1-e^{-T_\varepsilon}\sim T_\varepsilon\) are correct.

## 3. Symmetric point \(b=p=1/2\)

Let \(K=4\pi/\zeta(1/2)^2\). The gamma quotient gives

\[
\frac{\Gamma(1/2+\varepsilon)}{\Gamma(1+\varepsilon)}
=\sqrt\pi\,[1-2\log2\,\varepsilon+O(\varepsilon^2)],
\]

and consequently

\[
\tau_\varepsilon
=K\varepsilon^2[1-4\log2\,\varepsilon+O(\varepsilon^2)].
\]

Also \(\tau_\varepsilon^2/(2\varepsilon)=(K^2/2)\varepsilon^3+O(\varepsilon^4)\), and the general crossing remainder is \(O(\varepsilon^4)\). Therefore

\[
T_\varepsilon=K\varepsilon^2
\left[1-\left(4\log2+\frac K2\right)\varepsilon+O(\varepsilon^2)\right].
\]

This confirms the stated coefficient \(4\log2+2\pi/\zeta(1/2)^2\). Both corrections of the same relative order have been included.

## 4. Jordan parts and the boundary atom

For fixed \(T_0<1\), the local expansion gives

\[
k_\varepsilon(T)
=\frac{\varepsilon}{p\Gamma(1+\varepsilon)}T^{\varepsilon-1}
+R_\varepsilon(T),\qquad
|R_\varepsilon(T)|\le C_bT^{p+\varepsilon-1}.
\]

All the analytic remainder powers are bounded by this power on the fixed interval. The first term is nonnegative, so

\[
k_\varepsilon(T)^-\le |R_\varepsilon(T)|\le C_bT^{p-1}.
\]

This is an integrable uniform bound. Crucially, the proof does not try to dominate the concentrating positive term \(\varepsilon T^{\varepsilon-1}\) uniformly at zero.

Here are explicit details of the common majorant for the scaled integral when \(T\ge T_0\). On \(0<s<1/2\), the numerator is at most \(C_bs^b\), and \(e^{T_0s}-1\ge T_0s\) gives a bound \(C_{b,T_0}s^{b-1}\). On \(1/2<s<1\), use \(C_b[1+(1-s)^{p-1}]\); on \(s>1\), use \(s^{b-1}/(e^{T_0s}-1)\). All are integrable. Therefore \(I(T)\) is uniformly bounded for \(T\ge T_0\), and

\[
e^{-T}|k_\varepsilon(T)|
\le C_{b,T_0}e^{-T}(1+T^{\varepsilon_0}).
\]

Choosing \(T_0\) once justifies writing \(C_b\). Pointwise convergence and these two majorants give convergence of the negative kernels in \(L^1(e^{-T}dT)\), exactly the asserted total-variation convergence under \(u=e^{-T}\).

The limiting negative mass is \(1/p\) by the critical measure theorem. Interior measures have zero total mass, so the positive masses tend to \(1/p\). Their supports lie in \((e^{-T_\varepsilon},1)\), which shrinks to 1, proving weak convergence to \((1/p)\delta_1\). Subtraction gives the asserted weak convergence of the full signed measures. No total-variation convergence of an absolutely continuous positive measure to an atom is asserted.

## 5. Exponential law in total variation

For small \(\varepsilon\), \(T_\varepsilon<1\), and the transformed support is \(y>y_\varepsilon>0\), with

\[
y_\varepsilon=-\varepsilon\log T_\varepsilon
=\frac\varepsilon p|\log\varepsilon|
-\varepsilon\log K_b+o_b(\varepsilon).
\]

This verifies the needed \(O_b(\varepsilon|\log\varepsilon|)\) bound.

On \(0<T<T_\varepsilon\), compare the actual positive measure
\(p k_\varepsilon(T)e^{-T}dT\) with

\[
\frac{\varepsilon}{\Gamma(1+\varepsilon)}
T^{\varepsilon-1}\mathbf1_{0<T<T_\varepsilon}\,dT.
\]

The total-variation error is at most

\[
p\int_0^{T_\varepsilon}|R_\varepsilon(T)|\,dT
+\frac{\varepsilon}{\Gamma(1+\varepsilon)}
\int_0^{T_\varepsilon}T^{\varepsilon-1}(1-e^{-T})\,dT
\le C_bT_\varepsilon^{p+\varepsilon}
+C_b\varepsilon T_\varepsilon^{1+\varepsilon}.
\]

Because \(T_\varepsilon^p=O_b(\varepsilon)\), the bound is \(O_b(\varepsilon)\). The comparison density has exactly the same support cutoff, so no term past the crossing has been lost.

With \(T=e^{-y/\varepsilon}\), the Jacobian has magnitude \(T/\varepsilon\). The pushforward of the comparison measure is therefore exactly

\[
\frac{e^{-y}}{\Gamma(1+\varepsilon)}
\mathbf1_{y>y_\varepsilon}\,dy.
\]

There is no extra factor \(p\) or \(\varepsilon\). The gamma factor differs from 1 by \(O(\varepsilon)\), while the omitted interval contributes \(\int_0^{y_\varepsilon}e^{-y}dy\). Hence its distance from the unit exponential density is at most

\[
|\Gamma(1+\varepsilon)^{-1}-1|
+\int_0^{y_\varepsilon}e^{-y}\,dy
=O_b(\varepsilon|\log\varepsilon|).
\]

Pushforward contracts total variation, so adding the previous \(O_b(\varepsilon)\) error proves the theorem.

If \(m_\varepsilon=\nu_\varepsilon(\mathbb R)\), then

\[
|m_\varepsilon-1|
\le\|\nu_\varepsilon-\operatorname{Exp}(1)\|_{\rm TV},\qquad
\|m_\varepsilon^{-1}\nu_\varepsilon-\nu_\varepsilon\|_{\rm TV}
=|1-m_\varepsilon|
\]

for the full variation norm. This proves the normalization statement with the same rate. Different conventions for TV distance change only an absolute factor.

The interpretation in terms of a typical exponentially small logarithmic distance follows from the limiting distribution. The prose does not incorrectly infer convergence of arbitrary unbounded moments solely from total variation.

## 6. Scope and integration conclusion

The proofs use the single-crossing and critical-density theorems exactly in their established parameter ranges. All results keep \(b\) fixed; the caveats about \(b\downarrow0\) and \(b\uparrow1\) are appropriate. Radius dependence of the local expansion is now explicit. Numerical diagnostics are separated from the proof and add no hidden hypotheses.

**No mathematical revision is required to the reviewed version.**

