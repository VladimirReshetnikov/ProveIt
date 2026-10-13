# Absolute Stieltjes reconstruction, Euler confluence, and consecutive-tail exclusion

13 October 2026 (Pacific). This audit covers the collective manuscript's three new sections:

* [Absolute reconstruction and logarithmic dilations](../chapters/07-stieltjes-logarithmic-dilations.tex), including principal-character centered logarithmic moments.
* [Confluent dilations and Euler differential filters](../chapters/07-stieltjes-confluent-euler.tex).
* [Analytic exclusion of nonalternating consecutive tails](../chapters/07-stieltjes-consecutive-exclusion.tex).

The results below concern the conventional generalized Stieltjes coefficients in
\(\zeta(1+z,a)=z^{-1}+\sum_{n\ge0}(-1)^n\gamma_n(a)z^n/n!\), with positive real shifts. Their all-order validity rests on the written analytic proofs. The exact scripts check finite algebraic instances and normalization; numerical quadratures check independent evaluations and precision refinement. These are distinct kinds of evidence. This audit makes no PDF-build, rendered-layout, publication, Lean-verification, or interval-certification claim.

## Attribution and the new contribution

The scalar balanced-kernel Mellin transform, its shift derivatives, and the general principle of extracting logarithmic moments already occur in the preserved `balanced-stieltjes-moments` report, cited as `stmell:balanced`. They are inputs to these sections. The colored scalar foundation and root-of-unity dictionary are likewise already canonical, with the preserved colored report cited in the preceding chapter. The previous finite-dilation section supplies ordinary moment filters; the previous endpoint reconstruction gives Stieltjes **differences** using a split integral.

The present additions specify a globally integrable digamma kernel for **absolute** coefficients, invert its logarithmic moments at every index, treat repeated filter roots and their minimal support, prove weighted differential confluence, and evaluate explicit ordinary Stieltjes and digamma integrals. The principal-character formulas follow from the classical Euler product and zeta functional equation. The positivity input is the classical Lazarević inequality, attributed to Yang's account (`stce:Lazarevic`) and also proved directly in the chapter. The negative simple roots of Euler--Frobenius numerators are classical, attributed to Janson (`stex:Janson`) and proved by interlacing. The root-disc estimate is the elementary Eneström--Kakeya argument, also included in full. No historical-priority claim is made for these inputs, operators, or resulting special-function formulas.

## Absolute reconstruction and repeated logarithmic moments

For \(a,L,M>0\), write

\[
\begin{aligned}
\mathcal K_{L,M}(x,a)={}&-\psi(a+e^{(L+M)/2}x)
+\psi(a+e^{(M-L)/2}x)\\
&+\psi(a+e^{(L-M)/2}x)-\psi(a+e^{-(L+M)/2}x),\\
N_j={}&\int_0^\infty\log^j(x)\mathcal K_{L,M}(x,a)\,\frac{dx}{x},\\
E_{L,M}(u)={}&\frac{\sin\pi u}{\pi u}
\frac{Lu}{2\sinh(Lu/2)}\frac{Mu}{2\sinh(Mu/2)}
=\sum_{j\ge0}e_{2j}u^{2j}.
\end{aligned}
\]

The exact holomorphic germ and its coefficient identity are

\[
\frac{E_{L,M}(u)}{LM}\sum_{j\ge0}N_j\frac{u^j}{j!}
=u\zeta(1-u,a),\qquad
\gamma_n(a)=\frac{n!}{LM}
\sum_{j=0}^{\lfloor(n+1)/2\rfloor}
\frac{e_{2j}N_{n+1-2j}}{(n+1-2j)!}.
\]

Thus each index is one ordinary integral with an explicit polynomial in \(\log x\). With \(A=\pi^2/6+(L^2+M^2)/24\), the first cases are

\[
N_0=-LM,\quad \gamma_0(a)=\frac{N_1}{LM},\quad
\gamma_1(a)=\frac{N_2}{2LM}+A,\quad
\gamma_2(a)=\frac{N_3}{3LM}-2A\frac{N_1}{LM}.
\]

The kernel is \(O(x)\) at zero and \(O(x^{-1})\) at infinity. Its Mellin integral is therefore holomorphic on \(-1<\Re u<1\), and every fixed logarithmic derivative is absolutely integrable on smaller closed strips. The proof obtains the transform first on \(0<\Re u<1\), then uses these independently proved endpoint bounds to cross zero. The Laurent sign, the nonzero anchor \(N_0\), and logarithmic centering are essential; they are checked separately. No finite-part convention or unproved exchange of an infinite series with a divergent integral is used.

For \(\omega\in\mathbb C\setminus[1,\infty)\), the colored endpoint needs only one centered dilation difference:

\[
\mathcal J_L^\omega(x,a)=\Phi(\omega,1,a+e^{L/2}x)
-\Phi(\omega,1,a+e^{-L/2}x),\qquad
T_j=\int_0^\infty\log^j x\,\mathcal J_L^\omega(x,a)\frac{dx}{x}.
\]

If \(\frac{\sin\pi u}{\pi u}\frac{Lu}{2\sinh(Lu/2)}=\sum f_{2j}u^{2j}\), then

\[
\partial_s^n\Phi(\omega,1,a)
=\frac{(-1)^{n+1}n!}{L}
\sum_{j=0}^{\lfloor n/2\rfloor}\frac{f_{2j}T_{n-2j}}{(n-2j)!}.
\]

The same endpoint bounds and Mellin strip justify all ordinary logarithmic integrals. At \(\omega=-1,a=1,L=\log2\), with
\(f(x)=[\psi((x+2)/2)-\psi((x+1)/2)]/2\) and \(J(x)=f(\sqrt2x)-f(x/\sqrt2)\), the first moments are

\[
T_0=-L^2,\quad T_1=L^2\gamma-L^3/2,\quad
T_2=2L^2\gamma_1+L^3\gamma-\pi^2L^2/3-5L^4/12.
\]

Root-of-unity colors translate into finite generalized-Stieltjes combinations through the existing dictionary.

For repeated roots, take \(G(s)=\zeta(s,a)\) or \(\Phi(\omega,s,a)\), and use the corresponding balanced kernel \(\mathcal C_q\). For \(0\le q\le K\), positive integers \(r_k\), and \(\lambda_{k,\nu}>1\), put

\[
D(s)=\prod_{k=q}^K\prod_{\nu=1}^{r_k}
(1-\lambda_{k,\nu}^{-s-k})=\sum_hc_hh^{-s},\qquad
\mathcal H_q(x)=\sum_h\frac{c_h}{h}\mathcal C_q(x/h,a).
\]

Coincident scales are combined. In the uncolored generating function the scalar Laurent subtraction remains \(D(1)/z\). Every
\(M_{k,\ell}=\int_0^\infty x^k\log^\ell x\,\mathcal H_q(x)\,dx\), for \(q\le k\le K\), is absolutely convergent: the filter cancels all tail indices \(q,\ldots,K\), leaving \(O(x^{-K-2})\), while the origin has at most logarithmic growth. The exact germ is

\[
\sum_{\ell\ge0}M_{k,\ell}\frac{u^\ell}{\ell!}
=(-1)^{k+1}\pi\csc(\pi u)Q_q(k+1+u)D(-k-u)G(-k-u).
\]

Here \(Q_q\) is the scalar Mellin factor already defined in the balanced-kernel chapter. If \(\rho_k\) is the zero order of \(G\) at \(-k\), the first nonzero logarithmic moment is **exactly** at degree \(r_k+\rho_k-1\). This follows because \(Q_q(k+1)>0\), the sine contributes one pole, and no factor assigned to another integer vanishes there. In particular, with

\[
W_k=\prod_\nu\log\lambda_{k,\nu}
\prod_{j\ne k}\prod_\nu(1-\lambda_{j,\nu}^{k-j}),
\]

\[
M_{k,r_k-1}=(-1)^{k+r_k+1}(r_k-1)!Q_q(k+1)W_kG(-k).
\]

For a single root of multiplicity \(r\) at \(-q\) on one scale \(\lambda>1\),

\[
\mathcal H_q(x)=\sum_{j=0}^r(-1)^j\binom rj
\lambda^{-(q+1)j}\mathcal C_q(x/\lambda^j,a),\qquad
\int_0^\infty x^q\log^{r-1}x\,\mathcal H_q(x)\,dx
=(-1)^{q+r+1}(r-1)!(\log\lambda)^rG(-q).
\]

The displayed alternating order-one example \(V=C_1^{-1}(x,a)-2\lambda^{-2}C_1^{-1}(x/\lambda,a)+\lambda^{-4}C_1^{-1}(x/\lambda^2,a)\) has
\(\int xV=0\) and \(\int x\log x\,V=(2a-1)(\log\lambda)^2/4\). At \(a=1/2\), the latter also vanishes because of the intrinsic Lerch zero.

The support bound is a separate exact statement about prescribed filter zeros: total multiplicity \(R=\sum r_k\) requires at least \(R+1\) distinct positive scales. Divide a real exponential sum by one exponential and apply Rolle's theorem inductively; for complex weights, use a nonzero real or imaginary component. A common geometric scale attains the bound and gives uniqueness up to normalization on the prescribed \(R+1\) scales. Intrinsic zeros of \(G\) are not counted as constraints on filter support.

## Principal-character centered logarithms

Let \(d>1\), let \(p_1,\ldots,p_r\) be its distinct prime divisors, and set
\(d_0=\prod p_j\), \(\ell_j=\log p_j\),
\(A_d=(-1)^r\prod\ell_j/2\), and \(c_d=\frac12\log d_0-\log(2\pi)\). Define

\[
K_d(x)=\sum_{h\mid d_0}\frac{\mu(h)}h
[\log(x/h)-\psi(1+x/h)],\qquad
N_j(d)=\int_0^\infty(\log x-c_d)^jK_d(x)\,dx.
\]

These are ordinary absolutely convergent integrals. The exact centered germ is

\[
\sum_{j\ge0}N_j(d)\frac{u^j}{j!}
=A_du^{r-1}\Gamma(1+u)[u\zeta(1+u)]
\sec(\pi u/2)\prod_j\operatorname{sinhc}(u\ell_j/2).
\]

The factor \(u\zeta(1+u)\) takes its removable value one at zero. Consequently

\[
N_j=0\ (j<r-1),\quad N_{r-1}=A_d(r-1)!,\quad N_r=0,
\]

\[
N_{r+1}=A_d(r+1)!\left(\frac{5\pi^2}{24}-\frac{\gamma^2}{2}
-\gamma_1+\frac1{24}\sum_j\ell_j^2\right),
\]

\[
N_{r+2}=A_d(r+2)!\left(\frac{\gamma_2}{2}+\gamma\gamma_1
+\frac{\gamma^3-\zeta(3)}3\right).
\]

The last normalized coefficient is independent of the primes and their number. The proof audit independently checked the sign in zeta reflection, the factorization of \(\prod_j(1-p_j^u)\), cancellation of the linear coefficient in \(\Gamma(1+u)u\zeta(1+u)\), and the quadratic and cubic coefficients. The other factors are even, which explains both the centered zero and the universal cubic coefficient. The kernel is \(O(1+|\log x|)\) at zero and \(O(x^{-2})\) at infinity, giving the required holomorphic strip \(-1<\Re u<1\). Only the radical of \(d\) occurs; prime powers do not change the identities. For example, \(\int K_6=0\), \(\int\log x\,K_6=\log2\log3/2\), and \(\int\log^2(2\pi x/\sqrt6)K_6=0\).

## Weighted Euler confluence and explicit ordinary integrals

With \(\mathcal E=x\partial_x\), define

\[
\mathcal F_{q,r}(x,a)=\prod_{\ell=q}^{q+r-1}(\mathcal E+\ell+1)C_q(x,a)
=x^{-q}\partial_x^r[x^{q+r}C_q(x,a)].
\]

For the preceding geometric filter \(H_{q,r}^{\lambda}\), \(\varepsilon=\log\lambda\downarrow0\), every fixed integer \(M\ge0\), and \(0<\sigma<q+r+1\),

\[
\int_0^\infty x^{\sigma-1}(1+|\log x|^M)
|\varepsilon^{-r}H_{q,r}^{e^\varepsilon}(x,a)-\mathcal F_{q,r}(x,a)|\,dx\longrightarrow0.
\]

This holds locally uniformly in \(a>0\). It follows from the exact cube average

\[
\varepsilon^{-r}H_{q,r}^{e^\varepsilon}(x,a)
=\int_{[0,1]^r}e^{-\varepsilon\sum_{j=0}^{r-1}(q+j+1)v_j}
\mathcal F_{q,r}(xe^{-\varepsilon\sum_jv_j},a)\,d\mathbf v.
\]

The independent proof review checked the fundamental-theorem-of-calculus normalization, commutation of factors, and a uniform integrable majorant. Differentiated Euler--Maclaurin remainders are justified using a right-half-plane sector and Cauchy's formula; each Euler factor kills its designated inverse-power tail. The resulting bounds are logarithmic at zero and \(O(x^{-q-r-1})\) at infinity. This weighted convergence justifies the newly integrable moments, where individual unfiltered terms may diverge.

Put \(A_{q,r}(u)=\prod_{\ell=q}^{q+r-1}(\ell+1-u)\). The Mellin identity on \(0<\Re u<q+r+1\) is

\[
\int_0^\infty x^{u-1}\mathcal F_{q,r}(x,a)\,dx
=A_{q,r}(u)\pi\csc(\pi u)Q_q(u)\zeta(1-u,a).
\]

For \(k=q+j\), \(0\le j\le r-1\), let \(d=r-1-j\), \(S=H_d-H_j\). The ordinary moment and first logarithmic moment are

\[
\int_0^\infty x^k\mathcal F_{q,r}\,dx
=(-1)^{q+1}j!d!Q_q(k+1)\frac{B_{k+1}(a)}{k+1},
\]

\[
\begin{aligned}
\int_0^\infty x^k\log(x/c)\mathcal F_{q,r}\,dx
=(-1)^qj!d!\big[&\{Q'_q(k+1)-(S+\log c)Q_q(k+1)\}\zeta(-k,a)\\
&-Q_q(k+1)\zeta'(-k,a)\big],\qquad c>0.
\end{aligned}
\]

All higher logarithmic moments follow by ordinary differentiation on the same open strip. The audit checked the alternating factorial sign and the harmonic correction by expanding the simple zero of \(A_{q,r}\), before canceling the sine pole.

For the explicit first-Stieltjes expression, let \(L=\log x\) and evaluate every special function in the next line at \(x+1\):

\[
W=3L^2+5L+1-(6L+5)\psi-(6L+2)x\psi'-Lx^2\psi''
-6\gamma_1-6x\gamma_1'-x^2\gamma_1''.
\]

Argument derivatives are intended. This is \(\mathcal F_{1,2}(x,1)\), and

\[
\int_0^\infty xW\,dx=\frac1{12},\qquad
\int_0^\infty x^2W\,dx=0,\qquad
\int_0^\infty x^2\log(x/c)W\,dx=-\frac{3\zeta(3)}{8\pi^2}\quad(c>0).
\]

Its independent signed Laplace density is

\[
\nu(t)=1+\frac{2e^{-t}}{1-e^{-t}}+
\frac{2te^{-t}}{(1-e^{-t})^2}+
\frac{t^2e^{-t}(1+e^{-t})}{(1-e^{-t})^3}-\frac6t,
\qquad
W(x)=\int_0^\infty e^{-xt}\nu(t)(\log(xt)+\gamma)\,dt.
\]

The normalization was audited separately: applying the Euler factors to \(g(t)=(e^t-1)^{-1}-t^{-1}\) gives \(2g-2tg'+t^2g''=\nu-1\). Adding the constant one leaves \(W\) unchanged because \(\int_0^\infty e^{-xt}(\log(xt)+\gamma)\,dt=0\). It improves the density to \(\nu(t)=-t^3/360+O(t^5)\) at zero, making the double Mellin integral absolutely Fubini-interchangeable for \(1<\Re u<4\). This is an exact cancellation, not an omitted boundary term.

The positive digamma kernel

\[
K(x)=2\psi(x+1)+4x\psi'(x+1)+x^2\psi''(x+1)-2\log x-3
=-\mathcal F_{0,2}(x,1)
\]

has Laplace density

\[
\mu(t)=\frac2t-\frac{t^2e^{-t}(1+e^{-t})}{(1-e^{-t})^3}>0.
\]

Strict positivity is equivalent to \(\sinh^3u>u^3\cosh u\) for \(u>0\); the chapter supplies the all-order positive-coefficient proof. Differentiating the positive Laplace integral proves strict complete monotonicity. Its ordinary identities are

\[
\int K=\frac12,\qquad \int xK=\frac1{12},\qquad
\int x^2K=\frac{\zeta(3)}{2\pi^2},
\]

\[
\int\log(x/c)K=-\frac{1+\log(2\pi c)}2,\qquad
\int x\log(x/c)K=\zeta'(-1)+\frac{1-\log c}{12}.
\]

All integrals here run from zero to infinity. Thus \(2K(x)dx\) is a probability measure with mean \(1/6\) and second moment \(\zeta(3)/\pi^2\). The tails \(W=-11/(360x^4)+O(x^{-6})\) and \(K=1/(20x^4)+O(x^{-6})\) show that the next integer moment diverges. The manuscript does not extend these identities to that endpoint by regularization.

## Consecutive-tail exclusion and its remaining boundary

Write \(A_k(w,a)=\Phi(w,-k,a)\). For \(a=b+n\), \(0<b\le1\), \(n\ge0\), the numerator of \(A_k(w,b)\) has only simple negative real roots. Its logarithmic derivative at \(w=e^{i\theta}\), \(0<\theta<\pi\), has imaginary part strictly larger than \((k+1)\sin\theta/4\). The finite shift identity is

\[
w^nA_k(w,b+n)=A_k(w,b)-S_{k,n,b}(w),\qquad
S_{k,n,b}(w)=\sum_{j=0}^{n-1}(b+j)^kw^j.
\]

Consecutive zeros imply equality of both sides' logarithmic derivatives, by
\(w\partial_wA_k=A_{k+1}-aA_k\). For \(n\ge2\), all roots of \(S\) have modulus at most \(\rho=((a-2)/(a-1))^k<1\). Its real power sums give the upper bound
\(|\Im(wS'/S)|\le(n-1)\rho\sin\theta/(1-\rho)^2\). Hence a nonalternating unit-circle pair is impossible whenever

\[
(k+1)(1-\rho)^2\ge4(n-1)\rho.
\]

Equality still excludes the pair because the lower bound is strict. The cases \(n\le1\) need no inequality. The proof review checked the interlacing endpoints, positivity of the pole contribution, coefficient scaling in the root-disc argument, and the use of real power sums in the angular bound. On every bounded positive shift interval this criterion holds for all sufficiently large orders, uniformly.

Two concrete all-order consequences are established:

* **For every \(0<a\le7\) and every \(k\ge0\), there is no consecutive pair \(A_k=A_{k+1}=0\) at \(|w|=1\), \(w\notin\{1,-1\}\).** Orders \(1\le k\le7\) use the previously certified classification through order eight; \(k=0\) is immediate. For \(k\ge8\), the positive rational margin is \(9(1-(5/6)^8)^2-20(5/6)^8=203497798081/313456656384\). Monotonicity in \(k\) completes the infinite range.
* **For every \(0<a\le2\), there is no consecutive pair at any nonreal color, without a unit-modulus assumption.** On the base interval even a single nonreal zero is excluded; after one shift, the finite shift sum is a nonzero constant, while the logarithmic derivative still has strictly positive imaginary part in the upper half-plane.

The additional region \(0<a\le1+2k/3\), \(k\ge1\), follows from the same criterion: \(e^{-3/2}<9/40\) and the exact angular constant \(960/961<1\). These proofs do not extrapolate from a finite search.

On the strip \(0<a\le7\), fixed-shift homogeneous balance is unique at every nonalternating unit-circle color, and a colored kernel has at most one extra ordinary positive-integer Mellin moment. The already certified order-fifteen **single-tail** zero at \(a_*\approx5.94585\) attains that one-moment bound. It does not contradict consecutive-tail exclusion. The alternating color retains the earlier Brillhart/Euler-polynomial classification and golden-shift exception. **The unrestricted nonalternating consecutive-tail problem outside the sufficient regions remains open in this investigation.** The release does not claim global conjecture closure or absence of single-tail zeros.

## Reproducible exact and numerical evidence

The following receipt counts were read from the canonical files. All six current runner SHA-256 values match their recorded LF-normalized digests. Receipts also identify Python/package versions, precision, and optimization level.

| Evidence family | New finite exact checks | Rejected formula controls | Separate replay |
| --- | ---: | ---: | --- |
| Absolute/colored reconstruction and repeated dilation roots | 522 | 5 | — |
| Principal centered logarithms | 115 | 4 | — |
| Euler confluence and explicit kernels | 129 | 4 | Exact-only receipt repeats the same 129/4 |
| Consecutive-tail exclusion support | 146 | 4 | **41 earlier unit-circle certificate checks** |
| Total new finite algebraic evidence | **912** | **17** | Replays are not added to this total |

The 522 checks compare two independent even-germ constructions, reconstruction coefficients through index seven, alternating signs, dilation scale sums, leading derivatives, and confluent matrices. The 115 principal checks cover Euler-product factors, centering, reflection, and low-order coefficients. The 129 Euler checks include Leibniz expansion, signed-density normalization, finite Mellin-germ coefficients, Bernoulli moments, and positivity-coefficient instances. The 146 exclusion checks include independent Stirling numerators, finite shift and derivative identities, exact Sturm diagnostics, angular formulas, and rational boundary constants. Their finite ranges are diagnostics; the chapter's induction, estimates, and holomorphic arguments prove the universal statements.

The **41 replay checks** validate the pre-existing order-eight Bézout certificates used in the small-order part of the strip theorem. They are neither 41 newly discovered identities nor a substitute for the large-order analytic argument.

| Numerical family and receipt | Settings | Comparisons | Maximum recorded absolute residual |
| --- | --- | ---: | ---: |
| `check_confluent_dilations_numeric60.json` | 60 digits; cutoff 64, small order 48, tail order 100 | 29 | 3.1115076389306e-60 |
| `check_confluent_dilations_numeric75.json` | 75 digits; cutoff 80, small order 64, tail order 120 | 29 | 7.9046850784779e-73 |
| `stieltjes-principal-logs50.json` | 50 digits; cutoff factor 32, tail order 90 | 15 | 2.13821176807e-49 |
| `stieltjes-principal-logs70.json` | 70 digits; cutoff factor 48, tail order 120 | 15 | 3.62227163153e-70 |
| `confluent-euler-checks.json`, first run | 45 digits; refined small-density series | 12 | 1.49063124143e-43 |
| `confluent-euler-checks.json`, second run | 65 digits; refined small-density series | 12 | 1.82087248191e-65 |

This is **112 comparisons across two precision settings**, not 112 distinct theorems. The absolute/colored set uses \(a=1,1/3,\sqrt2\) and scale pairs \((2,2),(2,3)\): each run checks six anchors, eighteen absolute coefficients through index two, three alternating endpoint moments, and two alternating order-zero double-root moments. The printed alternating **order-one** bulk formula is proved analytically and checked in its exact leading coefficient; it is not one of those two order-zero quadratures. The principal set checks \(d=2,6,30\), with logarithmic degrees zero through \(r+2\). Its additional numerical sign/centering controls are recorded for each modulus and are not included in the 17 exact controls.

Absolute and principal quadratures evaluate digamma directly, using endpoint Taylor/Bernoulli expansions to avoid large cancellation. Euler moment checks integrate the independent positive/signed Laplace densities, then compare direct digamma or generalized-Stieltjes evaluation at \(x=1/3,2\). The Euler receipt also records **12 confluence-refinement errors separately**, for \(q=0,1\), \(r=2\), and \(\varepsilon=2^{-8},2^{-12},2^{-16}\), at both precisions. Each successive error decreases by more than a factor of eight. These are pointwise refinement diagnostics, not numerical certification of the weighted norm theorem. Floating-point residuals and truncated expansions are not rigorous error intervals.

All finite algebraic suites were run with `-O`; their checks use explicit failures and remain active when Python assertions are disabled. `confluent-euler-exact-replay.json` is an additional exact-only replay with zero numerical checks. The harness deliberately overwrites a stale PASS, observes RUNNING before checks, injects an exception, and verifies FAIL afterward. Thus `confluent-euler-intentional-failure.json` is expected to contain FAIL: it is evidence that the stale-PASS control succeeded, not a failed mathematical identity.

From the repository root, these commands reproduce the canonical receipts (and overwrite only their named output receipts):

```powershell
$v = 'Analysis/Polylogarithms/docs/manuscript/verification'
py -B -O "$v/check_confluent_dilations_exact.py"
py -B "$v/check_confluent_dilations_numeric.py" --output "$v/check_confluent_dilations_numeric60.json"
py -B -O "$v/check_confluent_dilations_numeric.py" --precision 75 --cutoff 80 --small-order 64 --tail-order 120 --output "$v/check_confluent_dilations_numeric75.json"
py -B -O "$v/check_stieltjes_principal_logs_exact.py"
py -B "$v/check_stieltjes_principal_logs.py" --dps 50 --cutoff 32 --tail-order 90 --output "$v/stieltjes-principal-logs50.json"
py -B -O "$v/check_stieltjes_principal_logs.py" --dps 70 --cutoff 48 --tail-order 120 --output "$v/stieltjes-principal-logs70.json"
py -B -O "$v/check_confluent_euler.py" --output "$v/confluent-euler-checks.json"
py -B -O "$v/check_confluent_euler.py" --exact-only --output "$v/confluent-euler-exact-replay.json"
py -B -O "$v/check_confluent_euler_harness.py"
py -B -O "$v/check_stieltjes_consecutive_exclusion.py" --output "$v/stieltjes-consecutive-exclusion.json"
```

The exclusion runner reads the existing `check_stieltjes_unit_circle.py` and `stieltjes-unit-circle-certificates.json`, recording their separate digests. The analytic proofs, these finite receipts, subsequent PDF validation, and publication verification remain separately assessable evidence.
