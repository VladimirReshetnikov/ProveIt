# Independent intake proof audit

October 12, 2026 (Pacific). This note is maintained separately from the
delivered article, its figures and its historical verification records.
Placement was c0f20fbd88f60d2a0f58c5a8c1377c7de4fbb892.

The conventional proof of Theorem thm:phase and Corollary cor:physical
has been checked. It closes the explicit boundary question at lines
1279–1297 of the preserved predecessor
[article.tex](../Resonant_Polylogarithm_Transseries/article.tex).
The predecessor called the boundary constant unproved; its interior
theorem was not false. No retraction or rewriting of that original is
appropriate. The boundary results are now integrated into Section 1.7 of the
collective Polylogarithms manuscript, with attribution and a full proof.

## Global branch and dominance

For $uv-v^2/2=\operatorname{Li}_s(re^v)$, the fixed-point map is
$\Phi(r,v)=v^2/(2u)+u^{-1}\sum_{n\ge1}r^ne^{nv}/n^s$.
Its nonnegative coefficient iteration stabilizes degree by degree, and
the direct term gives $[r^n]v\ge1/(un^s)>0$. The parametrization
$v=f_u(t)=u-\sqrt{u^2-2\operatorname{Li}_s(t)}$ and
$r=t e^{-f_u(t)}$ uses the root selected at the origin.

The characteristic equation
$u^2=2\operatorname{Li}_s(t)+\operatorname{Li}_{s-1}(t)^2$
has one interior solution precisely in the stated interior regime.
The right side is strictly increasing and tends to infinity for
$0<s\le2$. For $s>2$ its endpoint is
$U_c(s)^2=2\zeta(s)+\zeta(s-1)^2$.

For $u\ge U_c$, set $A=\zeta(s-1)$,
$b=\sqrt{u^2-2\zeta(s)}$, $v_c=u-b$, $R_b=e^{-v_c}$.
The real branch bounds the nonnegative iterates for $r<R_b$.
Their sum therefore converges to that branch, and monotone convergence
at the endpoint gives $\sum a_nR_b^n=v_c$. This establishes convergence
on the entire closed disk before using any coefficient equivalent.

At another point of the circle, strict positivity at every degree makes
$|v(r)|<v_c$; hence $|re^{v(r)}|<1$.
The derivative bound
$|\Phi_v(r,v(r))|< (v_c+A)/u\le1$
gives analytic continuation there by the implicit function theorem.
There are no other dominant points. This argument does not merely
assume that the first positive obstruction is the Taylor radius.

## Normal form and constants

Put $D_s(x)=\zeta(s)-\operatorname{Li}_s(e^{-x})$ and
$K_s(x)=Ax+x^2/2-D_s(x)$. Twice differentiating gives
$K_s''(x)=1+\operatorname{Li}_{s-2}(e^{-x})$ with both initial
conditions zero. Its integral representation is legitimate for $s>2$,
since $x^{s-3}$, and the order-three logarithm, are integrable.
With $d=-\log(r/R_b)$ the selected square-root branch gives exactly

$$
(b+x)d-d^2/2=(b-A)x+K_s(x),\qquad v=v_c+d-x.
$$

The local expansion uses the classical pole-paired polylogarithm
formula, [DLMF 25.12.12](https://dlmf.nist.gov/25.12.E12).
For $b>A$ its noninteger singular coefficient transports to
$\Gamma(1-s)/(b\kappa^s)$ in $v$, where $\kappa=1-A/b$.
Power transfer cancels the Gamma factor. At integer $s=m\ge3$,
the coefficient of $d^{m-1}\log d$ is
$(-1)^m/(b(m-1)!\kappa^m)$; the integer logarithmic transfer
has exactly the cancelling sign and factorial. Both routes give
$b^{s-1}/(b-A)^s$.

At $b=A$, the three leading terms in $K_s/A$ are
$\Gamma(1-s)x^{s-1}/A$ for $2<s<3$,
$x^2\log(1/x)/(2A)$ for $s=3$, and
$(1+\zeta(s-2))x^2/(2A)$ for $s>3$.
Their inverse amplitudes and the Gamma factors reproduce all three
displayed coefficient constants. In particular the marginal inverse
has amplitude $2\sqrt A$, giving $\sqrt{A/\pi}$ after transfer.
The order-three constant inside $K_3$ is $5/2$, including the
quadratic feedback term.

The sectorial inverse argument uses the differentiated convergent
expansions on relative Rouche circles. The model root stays away from
the slit boundaries on each smaller sector, and its derivative does
not vanish. Gluing the local inverses and the compact arcs away from
$R_b$ supplies the dented continuation needed for transfer.
Thus the local nonanalytic terms establish genuine singularity as well
as their coefficient equivalents.

For the physical point $r=-e^{-u}$, the interior criterion is
$\log t_*+\operatorname{Li}_{s-1}(t_*)\ge0$. Its left side increases
strictly from negative infinity to a positive limit, giving the unique
threshold. Above the boundary transition $e^{-u}/R_b=e^{-b}<1$.
This proves the claimed extension to all positive orders without
identifying this general feedback germ with an ordinary Fermi inverse.

## Remaining integration scopes

The seven sections have been read. The low-order, Lambert and
higher-order chart equations follow by explicit substitution into the
normal form, and their displayed base derivatives are nonzero.
Their detailed coefficient formulas, all-order logarithmic transfer,
joint order/feedback chart and uniform lattice theorem remain separate
canonical integration tasks. Reading and successful numerical replay
do not promote those entire branches into the manuscript automatically.

The exact compound-Poisson identity uses $R_b$ on both sides of critical
feedback, although below it the actual Taylor radius is larger.
The local-limit proof fixes $s$ and a compact positive interval of $b$;
its absolute error does not give relative estimates in growing windows.
The complex-fold result concerns local continued normal-form solutions.
Access from the original Taylor germ and global sheet identification
remain open. The report itself states these qualifications.

No new error in the checked phase theorem was found. This is a
conventional analytic proof audit, not Lean formalization, an interval
certificate, or a claim of publication priority. Fresh suite results
are preserved separately under the intake-verification directory.
