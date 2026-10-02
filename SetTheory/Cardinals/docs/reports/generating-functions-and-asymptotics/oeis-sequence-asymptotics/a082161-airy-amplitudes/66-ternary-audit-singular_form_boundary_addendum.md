# Boundary audit of the proposed one-step singular-form limit

## Conclusion

Assume the operator is

\[
(T_i u)(j)=U_i(j)u(j-1)+u(j+2),\qquad
U_i(j)=\frac{4(i-j+3)}{2i+j},
\]

from the **single residue class** \(j\equiv i-1\pmod3\), \(0\leq j\leq i-1\), to \(j\equiv i\pmod3\), \(0\leq j\leq i\), with zero extension. In the fixed norm
\(\|u\|_\omega^2=\sum_j\omega(j)|u(j)|^2\),
\(\omega(j)=\ell(j)/(j+1)\), I find no fatal boundary inconsistency in the proposed Dirichlet Airy form or its constants.

There is a material qualification: if the operator is instead taken on **all** indices in the two intervals, it is the direct sum of three residue channels. Then the first three singular values have the first Airy correction \(a_1\), up to lower-order differences; the second singular value is not described by \(a_2\). The single-phase restriction must be explicit.

The formal \(j=0\) energy summand must be declared zero rather than treated as an actual expression involving \(u(-1)/0\).

## 1. Exact critical form

Let \(T\) be the critical transfer with coefficient 2. Since \(u=h f\) identifies \(\ell^2(\omega)\) with \(\ell^2(\pi)\), \(\pi=h\ell\), the one-step Doob probabilities at output site \(j\) are

\[
p_j=\frac{2j}{3(j+1)},\qquad
q_j=\frac{j+3}{3(j+1)}.
\]

The invariant measures transport exactly between the two residue classes. Therefore

\[
\boxed{9\|u\|_\omega^2-\|Tu\|_\omega^2
=\sum_{j\text{ in output phase}}
2\omega(j)j(j+3)
\left|\frac{u(j-1)}j-\frac{u(j+2)}{j+3}\right|^2}.
\]

At \(j=0\), the Doob row is deterministic and its variance is zero.

## 2. An exact identity removes the apparent boundary ambiguity

Let the input residue be \(r\in\{0,1,2\}\), write

\[
g_k=u(3k+r),\qquad H_k=3k+r+1,
\]

and zero extend a finitely supported \(g\). Direct expansion and cancellation yield

\[
\boxed{\sum_{k\geq0}H_kH_{k+1}
\left|\frac{g_k}{H_k}-\frac{g_{k+1}}{H_{k+1}}\right|^2
=\sum_{k\geq0}|g_{k+1}-g_k|^2+
\frac3{r+1}|g_0|^2}.
\]

Interior diagonal coefficients cancel because
\((H_k+3)/H_k+(H_k-3)/H_k=2\). At the initial site the uncancelled diagonal excess is precisely \(3/H_0\).

The critical singular form is

\[
2\sum_{k\geq0}\omega(3k+r+1)H_kH_{k+1}
\left|\frac{g_k}{H_k}-\frac{g_{k+1}}{H_{k+1}}\right|^2.
\]

Since \(1\leq\omega\leq3/2\), it is bounded below by 2 and above by 3 times the boxed elementary Dirichlet form. In particular, there is no free constant trace and no Neumann boundary arising from the missing \(j=0\) variance term.

For a precise interpolation, put \(\varepsilon=i^{-1/3}\), \(x_k=\varepsilon H_k\), and
\(F_\varepsilon(x_k)=g_k/\sqrt{3\varepsilon}\). Interpolate linearly, including the segment from \(F_\varepsilon(0)=0\) to its first value at \(x_0=\varepsilon(r+1)\). Then

\[
\int_0^\infty |F_\varepsilon'|^2\,dx
=\frac1{9\varepsilon^2}
\left(\sum_k|g_{k+1}-g_k|^2+
\frac3{r+1}|g_0|^2\right).
\]

Thus the critical form divided by \(18\varepsilon^2\) uniformly controls an ordinary Dirichlet kinetic energy. This is a direct coercive explanation of the limiting zero trace.

For \(F\in H_0^1(\mathbb R_+)\), Hardy's inequality and integration by parts give

\[
\int_0^\infty|F'-F/x|^2\,dx
=\int_0^\infty|F'|^2\,dx.
\]

The identity should be used on this domain (or a dense compactly supported core), not assumed first for functions of unspecified boundary behavior.

## 3. Exact sub-Markov normalization and column loss

Set

\[
\alpha_i=1+\frac3{2i+1},\qquad
(K_i f)(j)=\frac{T_i(hf)(j)}{3\alpha_i h(j)}.
\]

For \(j\geq1\),
\(U_i(j)\leq U_i(1)=2\alpha_i\). At \(j=0\), the coefficient of the down step is irrelevant since \(h(-1)=0\), and the surviving row sum is \(1/\alpha_i\). Hence every row sum of \(K_i\) is at most one; upper truncation only removes mass.

For an input site \(j\), its column deficit relative to \(\pi=h\ell\) is

\[
\kappa_i(j)=1-
\frac{U_i(j+1)\ell(j+1)+\ell(j-2)}
{3\alpha_i\ell(j)},
\]

where \(\ell(-1)=\ell(-2)=0\). The exact algebraic identity

\[
2\alpha_i-U_i(j+1)
=\frac{12j(i+1)}{(2i+1)(2i+j+1)}
\]

gives

\[
\boxed{\kappa_i(j)=
\frac{2j(i+1)}{(i+2)(2i+j+1)}\frac{\ell(j+1)}{\ell(j)}
+\frac1{2(i+2)}\frac{\ell(j-2)}{\ell(j)}}.
\]

Both terms are nonnegative. In particular \(\kappa_i(0)=0\), which is consistent with a lower bound proportional to \(j/i\), not a uniform positive killing bound at the boundary.

Since \(\ell(j+1)>\ell(j)\), \(j\leq i-1\), and
\((i+1)/(i+2)\geq2/3\),

\[
\boxed{\kappa_i(j)\geq\frac49\frac ji}.
\]

Jensen's inequality for the substochastic rows gives

\[
\|T_iu\|_\omega^2
\leq9\alpha_i^2\sum_j(1-\kappa_i(j))\omega(j)|u(j)|^2.
\]

Consequently the proposed scaled form \(q_i\) satisfies

\[
\begin{aligned}
q_i(u)&=\frac{9\|u\|_\omega^2-\|T_iu\|_\omega^2}{18\varepsilon^2}\\
&\geq\frac{2\alpha_i^2}{9}
\sum_j(\varepsilon j)\omega(j)|u(j)|^2
-\frac{\alpha_i^2-1}{2\varepsilon^2}\|u\|_\omega^2.
\end{aligned}
\]

The last coefficient is \(O(\varepsilon)\). This supplies the proposed macroscopic tail tightness for bounded norms and bounded forms. It is only a coercive lower estimate, not the calculation of the exact limiting potential coefficient.

## 4. Constants in the proposed limit are consistent

Uniformly on a fixed compact macroscopic window, \(j=O(\varepsilon^{-1})\),

\[
U_i(j)=2-3(\varepsilon j)\varepsilon^2+O(\varepsilon^3),
\]

with the error constant depending on the window. A single phase has mesh \(3\varepsilon\), so the normalization is \(u(j)=\sqrt{3\varepsilon}F(\varepsilon j)\).

The critical square difference then contributes
\(18\varepsilon^2\int|F'-F/x|^2\), while the leading cross term from
\(U_i-2\) contributes \(18\varepsilon^2\int x|F|^2\) to
\(\|Tu\|_\omega^2-\|T_i u\|_\omega^2\).
This is consistent with the proposed form

\[
\int_0^\infty (|F'|^2+x|F|^2)\,dx
\]

and denominator \(18\varepsilon^2\).

If this compact form convergence is established, the Dirichlet Airy eigenvalues are \(-a_m\), where \(a_m<0\) are the successive Airy zeros. The algebra

\[
\frac{9-s_m(i)^2}{18\varepsilon^2}\to-a_m
\quad\Longleftrightarrow\quad
s_m(i)=3[1+a_m\varepsilon^2+o(\varepsilon^2)]
\]

has the stated sign and factor.

## 5. What remains unproved here

This audit does not establish the full compact form convergence. In particular, the moving form still requires a proper liminf argument, recovery sequences, comparison of the varying finite-dimensional Hilbert spaces, and a min–max/compactness argument. The exact boundary identity and the column-deficit estimate remove two obvious possible obstructions; they do not replace those remaining steps.

The same exact-arithmetic script as the frozen-block note also verifies the critical one-step identity, the boundary ground-state identity, the column-deficit formula, and the stated tail inequality on finite-phase test vectors.
