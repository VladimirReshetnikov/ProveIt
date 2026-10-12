# Resonant jets and inverse transseries: intake and proof audit

ProveIt Contributors, October 12, 2026.

Five packages from arrival `6207c3d40047` were preserved in placement
`594a660a540e`, published through `1955407685af`. Their 118 members comprise
115 tracked originals and three ignored records recoverable in arrival
history. The ZIPs were deleted in the placement commit. Original texts,
authorship, PDFs, code and recorded evidence remain unchanged. The collective
manuscript author remains ProveIt Contributors.

## Reconciliation

| Package | Relation to the existing work and review status |
|---|---|
| `normalized-resonant-jets` | Continues Lerch order calculus on the uniform-transition spine. The reciprocal-Gamma normalizer and exact pure-logarithm form are audited below. The finite dilation, inverse-support and half-shift tuning results require their own canonical integration. No atomic repository pin is supplied; retain its file-level provenance. |
| `resonant-inverse-folds` | Same pole pairing, followed by primary inverse charts and secondary dilogarithmic folds. Its observed revision qualifies moving reads. The historical bridge supersession was already in the editorial ledger; no new canonical error is established by that note. |
| `sharp-dilog-reversion` | Kept in the Transseries collection beside its inverse-transport antecedents. Positive Laurent sectors, exact radius and endpoint convergence form one proof package; the finite coefficient checks alone do not prove the radius. The Gamma and periodic Borel jets overlap the fifth package. |
| `weighted-resonant-inversion` | Kept in Transseries: weighted endpoint deficits, sharp logarithmic support and global coefficient asymptotics. The global contour argument requires independent review before accepting the claimed external normalization corrections. Its convergent local chart must not be confused with its outer asymptotic expansion. |
| `order-jets-resonant-inversion` | Extends the named R1 of the existing resonance report to fixed complex sectors. Shares the reciprocal-Gamma normalization with the first package and the critical-fold model with the second. The Borel and critical-point claims remain separate analytic review tasks. |

The first, second and fifth packages are under
`reports/uniform-transition-continuation/continuations/`. The other two have
one authoritative copy under `Analysis/Transseries/docs/series-and-transseries/`.
The archive inventory records both destinations explicitly.

## Fixed-sector R1: proof audit

The predecessor asks for complex approach with a fixed logarithm and a common
majorant in `resonance-correlations-nonseparable-jets/sections/07_questions.tex`,
lines 10–16. Its exact cancellation is in `sections/02_resonance.tex`, label
`res:exact`; the real-argument theorem is `res:main`. The fifth package's
`thm:sector` supplies the missing extension.

Set $T=-\operatorname{Log}t+H_k-\gamma$, using the principal logarithm,
and pair the Gamma and Hurwitz-zeta poles before expanding the order.
The exact remainder is

\[
 \mathcal R_k(\epsilon,t,a)
 =\frac{1-e^{-T\epsilon}E_k(\epsilon)}{\epsilon}
  +\zeta(1+\epsilon,a)-\frac1\epsilon+B_k(\epsilon,t,a),
\quad
 B_k=\sum_{\ell\ge1}\frac{k!(-t)^\ell}{(k+\ell)!}
                       \zeta(1+\epsilon-\ell,a).
\]

For compact $a$ in the right half-plane, $|\epsilon|\le\eta<1/2$,
and $t_0<R<2\pi$, Hermite's difference-of-powers integral gives a common
absolute majorant for the series of Hurwitz terms weighted by
$t_0^{\ell-1}/\ell!$. Near its integration endpoint zero, the difference
of powers contributes a factor of the integration variable before absolute
values are taken. At infinity, factorial summation is controlled by
$e^{-(2\pi-R)y}$ times a fixed polynomial. This validates the majorant
also for complex shifts on enlarged compact sets.

Since $k!/(k+\ell)!\le1/((k+1)\ell!)$, the analytic tail is
$O(|t|/(k+1))=O(e^{-\Re T})$, uniformly in every integer $k\ge0$.
The final step uses $H_k-\gamma\le\log(k+1)$. The centered Gamma
coefficients are uniformly bounded because
$|\zeta(j)+(-1)^jH_k^{(j)}|\le2\zeta(j)$ for $j\ge2$.
Taylor expansion with $\epsilon=u/T$, followed by Cauchy estimates on
enlarged compact $u,a$ sets, proves the stated fixed-jet remainder.
On a fixed closed sector $|\arg t|\le\pi-\delta$, $\Im T$ is bounded,
so the exponential tail is smaller than every prescribed inverse power.

This audits the conventional proof of the scoped R1 extension. It does not
resolve growing jet order R3, unrestricted growing transition windows R4,
or arbitrary winding number. A cover version needs an explicit condition
such as $\Re T\ge c|T|\to\infty$. Incorporation into the four canonical
volumes and their next PDF release remains pending.

## Exact normalization and a derived order-lowering identity

The following proof develops an identity from the normalized family. It is
an algebraic consequence of the classical Lerch expansion, with no claim of
literature priority. Let $m\ge0$, $\Re a>0$, $|\epsilon|<\rho<1$,
and $0<|t|<2\pi$ on a fixed slit disk. Define

\[
 D_m(\epsilon)=\frac{\prod_{j=1}^m(1+\epsilon/j)}{\Gamma(1-\epsilon)},
 \qquad C_{m,a}(\epsilon)=D_m(\epsilon)\zeta(1+\epsilon,a)-1/\epsilon,
\]
\[
 \mathcal F_{m,a}=(-1)^m m!D_m(\epsilon)
 \left(e^{-at}\Phi(e^{-t},m+1+\epsilon,a)
 -\sum_{j=0}^{m-1}\zeta(m+1+\epsilon-j,a)\frac{(-t)^j}{j!}\right)
 -t^m C_{m,a}(\epsilon).
\]

Empty sums and products apply at $m=0$. The poles at $\epsilon=0$
cancel. Gamma recurrence gives the exact normally convergent identity

\[
 \mathcal F_{m,a}=t^m\left\{\frac{1-t^\epsilon}{\epsilon}
 +B_{m,a}(\epsilon,t)\right\},\qquad
 B_{m,a}=\sum_{n\ge1}\frac{(-1)^n m!D_m(\epsilon)}{(m+n)!}
                  \zeta(1+\epsilon-n,a)t^n.
\]

Indeed the normalized Gamma term is $-t^{m+\epsilon}/\epsilon$, and
the counterterm leaves $t^m/\epsilon$. This checks the normalizer, the
tail sign and the subtraction, rather than equating a raw order derivative
with its pure-logarithm normalization.

**Order-lowering identity.** For every $m\ge1$,

\[
 \boxed{\partial_t\mathcal F_{m,a}(\epsilon,t)
       =(m+\epsilon)\mathcal F_{m-1,a}(\epsilon,t)-t^{m-1}.}
\]

To prove it, $D_m=(1+\epsilon/m)D_{m-1}$ implies, coefficient by
coefficient and then by normal convergence,
$(m+t\partial_t)B_m=(m+\epsilon)B_{m-1}$.
For $K=(1-t^\epsilon)/\epsilon$,
$(m+t\partial_t)K=(m+\epsilon)K-1$. Multiplication by $t^{m-1}$
proves the formula, including its removable value at $\epsilon=0$.

Writing $J_{m,r,a}=(-1)^r(r+1)\partial_\epsilon^r
\mathcal F_{m,a}|_{\epsilon=0}$, it follows that

\[
 \boxed{\partial_t J_{m,r,a}
 =mJ_{m-1,r,a}-(r+1)J_{m-1,r-1,a}-\mathbf1_{r=0}t^{m-1},}
 \qquad J_{m,-1,a}=0.
\]

Here $J_{m,r,a}=t^m\{(-\operatorname{Log}t)^{r+1}+B_{m,r,a}(t)\}$,
with a holomorphic tail vanishing at zero. Thus the $m=0$ family is
logarithmically singular but integrable at the endpoint.

**Finite antiderivatives of every jet.** For $m,r\ge0$, along a fixed
ray in the chosen slit disk,

\[
 \boxed{\int_0^t J_{m,r,a}(u)\,du
 =\sum_{k=0}^r\frac{(r+1)!}{(r-k+1)!(m+1)^{k+1}}
                 J_{m+1,r-k,a}(t)
 +\frac{(r+1)!\,t^{m+1}}{(m+1)^{r+2}}.}
\]

Differentiate the finite sum using the lowering identity: adjacent jet
terms cancel, leaving $J_{m,r,a}$; the final polynomial cancels the
remaining endpoint term. All terms vanish at zero because
$t^{m+1}\operatorname{Log}^q t\to0$, which fixes the integration constant.
Equivalently, before taking jets,

\[
 \int_0^t\mathcal F_{m,a}(\epsilon,u)\,du
 =\frac{\mathcal F_{m+1,a}(\epsilon,t)}{m+1+\epsilon}
  +\frac{t^{m+1}}{(m+1)(m+1+\epsilon)}.
\]

This supplies exact primitives for the entire normalized resonant jet
family, not just a finite-order experiment. The proof is conventional;
no Lean formalization is asserted. Canonical chapter placement is pending
the combined resonance synthesis.

## Replay and evidence boundaries

Every mathematical suite ran unmodified on an isolated copy with assertions
enabled. `twenty-first-replay/` preserves the fresh outputs and process
receipts. The weighted package initially failed to import `matplotlib`;
the failure is retained. Its rerun with all declared pinned dependencies
passes. The sharp-dilog package also has a passing local NumPy 2.4.4 run;
the accepted replay uses its declared NumPy 2.3.5. No delivered computation
was patched. Plot generation is not a claim of fresh visual PDF review.

The first package has 568 base exact checks, eight extension exact checks,
47 base comparisons, 12 inverse comparisons and 30 extension comparisons,
including nine tuning examples. The second has 150 exact checks and 73
180-digit diagnostics. The fifth has 270 finite symbolic cases, nine lattice,
18 split-root and 12 unfolding samples, plus an independent Bose-integral
principal-sheet diagnostic. Exact case counts and floating-point samples
remain separate; none is a proof of a general inverse-singularity theorem.

`check_resonant_ladder.py` imports no delivered code. It checks 3,780 exact
tail-coefficient basis cases, 72 finite antiderivative cancellations and
24 direct defining-sum comparisons at 85 digits. Controls reject an omitted
endpoint, a flipped lower-jet sign and a wrong jet coefficient. Its finite
checks support the derivation above; the all-order conclusion follows from
normal convergence and the displayed algebra.

The claimed external Bailey–Borwein–Crandall, Krattenthaler–Rivoal,
O'Sullivan and Vepstas corrections are preserved as proposed source-specific
findings. Their exact cited versions and scopes still require an independent
primary-source audit here. The current collective text is not silently
changed on the strength of those claims.
