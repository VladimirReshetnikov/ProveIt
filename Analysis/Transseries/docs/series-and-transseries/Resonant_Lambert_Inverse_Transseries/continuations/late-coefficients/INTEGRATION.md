# Integration proposal

This package is a companion report to *Double Resonance and Nested Stokes Geometry in Polylogarithmic Lambert Inversion*. It proves the two explicit conjectures in that report's §11.1, adds their first correction and parameter uniformity, and resolves the continuation part of §11.2.

The inspected repository snapshot is commit [`8f5afd4d7565df808359f6a0c22f87f79a119bb9`](https://github.com/VladimirReshetnikov/ProveIt/tree/8f5afd4d7565df808359f6a0c22f87f79a119bb9). The principal predecessor is the member `Resonant_Lambert_Inverse_Transseries/article.tex` of [`docs/incoming/Resonant_Lambert_Inverse_Transseries_2026-10-12.zip`](https://github.com/VladimirReshetnikov/ProveIt/blob/8f5afd4d7565df808359f6a0c22f87f79a119bb9/docs/incoming/Resonant_Lambert_Inverse_Transseries_2026-10-12.zip). These are the review anchors, even if `main` subsequently changes. The predecessor's own historical provenance should remain intact.

No existing repository file was changed by this package, and no commit or push was made. The changes below are proposals for maintainer review.

## 1. Suggested destination and links

Copy the complete report package into the proposed directory:

```text
Analysis/Transseries/docs/series-and-transseries/Resonant_Lambert_Inverse_Late_Coefficients/
```

Keep `article.tex`, `article.pdf`, `references.tex`, `sections/`, and the verification code and artifacts under `verification/` together. Preserve relative paths: the article includes its section files and the verification figure by relative filename. Keep `README.md`, `INTEGRATION.md`, and the provenance record with the report. Follow the package README for the actual build and verification commands. The verification results document finite exact checks and numerical diagnostics; they are not substitutes for the proofs and are not proof-assistant certificates.

Add an entry to `Analysis/Transseries/README.md`, using its existing list or table style. Suggested description:

```markdown
[Resonant Lambert inverse late coefficients](docs/series-and-transseries/Resonant_Lambert_Inverse_Late_Coefficients/): proofs of the hyperbolic amplitude conjectures, uniform first corrections, finite-phase amplitude transport, explicit Borel boundary models, and a checked application of nonlinear resurgence to inverse continuation.
```

Add a cross-reference to `Analysis/Polylogarithms/README.md`:

```markdown
[Sharp late coefficients and Borel continuation of resonant Lambert inverses](../Transseries/docs/series-and-transseries/Resonant_Lambert_Inverse_Late_Coefficients/) studies the factorially divergent inverse arising from the Lambert superposition of Li₁. It connects the resonant order-jet and Lambert-moment material with nonlinear reversion, and proves explicit logarithmic and dilogarithmic models for the two nearest Borel singularities.
```

The relevant Polylogarithms manuscript chapters are `01-resonant-jets.tex`, `01-lambert-moments.tex`, and `01-quadratic-feedback.tex` under `Analysis/Polylogarithms/docs/manuscript/chapters/`. A short bibliographic cross-reference from their outlook or related-work material is appropriate. Keep the new report independently compilable; a later editorial decision can select individual results for the canonical manuscript.

If the incoming report is subsequently integrated elsewhere, apply the amendments below to that editable source rather than silently replacing the archived ZIP. Update any research-question index to mark §11.1 as resolved and §11.2 as partly resolved.

## 2. Stable result labels and status

Use the following labels when moving sections or adding internal cross-references. For references from a separate document, cite this report and the theorem's name; a bare `\ref` cannot resolve another document's labels without an explicit external-reference setup.

| Label | Result | Status and intended use |
|---|---|---|
| `thm:main` | Sharp uniform late coefficients | Model-specific proof of the predecessor's conjectures, with an explicit first correction and complex parameter uniformity. |
| `eq:K` | First inverse-index correction | Explicit formula for the two parity corrections; retain the constants and the definition of `z`. |
| `lem:factorial` | Endpoint-preserving factorial bounds | Uniform majorant for the full number of Lagrange factors, including its largest values. |
| `lem:second-endpoint` | Second endpoint contribution | Uniform coefficient estimate that isolates the first quadratic-forward contribution. |
| `cor:relative-two-term` | Relative uniformity down to the resonant endpoint | Valid for every real `0 < u ≤ U`, with no lower bound on `u`. |
| `thm:finite-phases` | Leading amplitudes for finitely many phases | Reusable additive asymptotic law, with the linear forward coefficient determining the exponential amplitude multiplier. |
| `cor:prefix` | Polynomial changes of the forward tail | Changes with no linear term leave the leading amplitudes unchanged. |
| `thm:Borel-models` | Boundary models with controlled remainders | Explicit logarithmic/C⁰ and logarithmic–dilogarithmic/C¹ models; both nearest singularities are genuine for complex `u ≠ 0`. |
| `prop:Sauzin-input` | Nonlinear resurgence and summability closure | Quoted established theory, with hypotheses stated explicitly. |
| `thm:inverse-continuation` | Continuation of the quadratic inverse | A model-specific reduction followed by an application of Sauzin's theorem. |
| `thm:inverse-summability` | Sectorial sums satisfy the inverse equation | Summability off the real directions and an exact equation for its sectorial sums. |
| `prop:Stokes-transport` | Exact-completion inverse transport | Relation to the predecessor's already established forward completion and nested Stokes geometry; preserve its analytic hypotheses. |

The scope of the claimed contribution is the proved project conjecture, explicit model formulas and refinements, the finite-phase synthesis, and the checked nonlinear-continuation application. General Lambert resurgence, the one-large-index asymptotic mechanism, and Sauzin's closure theorems have substantial prior literature and must retain their citations. Worldwide priority for every specialization has not been established.

## 3. Notation that must survive integration

The predecessor uses two related tails:

\[
\mathcal R_0(t)=\sum_{n\ge2}r_n(0)t^n,
\qquad
R(t)=-\frac t4+\mathcal R_0(t).
\]

Its `eq:borel-convention` and `eq:borel0` refer to the tail that begins at degree two. Its `eq:R-all`, and the entire present report, include the linear term in `R`. Accordingly,

\[
\widehat R(\xi)=-\frac14+\widehat{\mathcal R}_0(\xi).
\]

Both use the shifted Borel convention `qⁿ ↦ ξⁿ⁻¹/Γ(n)` and Laplace integration without an additional factor `1/q`. The term `−t/4` is essential: it produces the factors `exp(∓Au/4)` at the two nearest actions. This is a notation reconciliation, not a correction to the predecessor, which already distinguishes the two tails.

Also preserve the following distinctions:

- The coefficient variable `q` and slow parameter `u` are independent before the physical substitution `q = exp(γ − X)`, `u = 1/X`.
- The estimates are locally uniform in complex `u`; relative versions are asserted on the positive real interval. Cancellations at complex values are handled by additive expansions.
- An allowed continuation set `Aℤ` is not an assertion that every lattice point is singular on every sheet. The initial origin is regular; it can be singular after continuation around other actions.
- A continuous or continuously differentiable boundary remainder need not extend holomorphically through an endpoint. The report does not establish a complete local singularity germ or an all-order alien derivative.

## 4. Proposed replacement for predecessor §11.1

The predecessor explicitly calls its amplitudes conjectural and supplies a valid coarser bound. No false theorem was found in the scoped audit. The following replacement records subsequent progress while retaining the existing equation labels, so references to `eq:conj-even` and `eq:conj-odd` remain valid. It uses the new bibliography key `latecoeff2026`, supplied below.

```latex
\subsection{Sharp large-order constants of the inverse sectors: resolved}
The two amplitude formulas conjectured in the original version of this
article are proved in the companion report \cite{latecoeff2026}.
For every $U>0$, uniformly for real $0<u\le U$ as $m\to\infty$,
\begin{align}
 C_{2m}(u)
 &=-\frac{4u\Gamma(2m)}{2mA^{2m}}\cosh(Au/4)
                  \{1+O_U(m^{-1})\},\label{eq:conj-even}\\
 C_{2m+1}(u)
 &=\frac{4u\Gamma(2m+1)}{(2m+1)A^{2m+1}}\sinh(Au/4)
                  \{1+O_U(m^{-1})\}.\label{eq:conj-odd}
\end{align}
There is no positive lower bound on $u$. The proof bounds all numbers
of factors in \eqref{eq:C-formula} by one summable factorial majorant;
it therefore justifies the endpoint summation that produces the
hyperbolic amplitudes. The coarser upper bound in
Theorem~\ref{thm:inverse-gevrey} remains valid.

The companion report also proves a first correction. Put
$b_n=\Gamma(n)/n$, $z=Au/4$, $\Phi_0(z)=\cosh z$, and
$\Phi_1(z)=\sinh z$. Uniformly on every fixed complex disk $|u|\le U$,
\begin{equation}\label{eq:resolved-two-term}
 \frac{(-1)^{n+1}A^n C_n(u)}{4u b_n}
 =\Phi_{n\bmod2}(z)+\frac{K_{n\bmod2}(u)}n+O_U(n^{-2}),
\end{equation}
where a prime means differentiation with respect to $z$ and
\[
 K_\epsilon(u)
 =\left\{\frac{A^2u}{288}+\frac{1+u}{2}z^2\right\}\Phi_\epsilon(z)
       +(2+u)z\Phi_\epsilon'(z).
\]
The quotient at $u=0$ is removable. For odd $n$, the remainder on the
right of \eqref{eq:resolved-two-term} is $O_U(|u|n^{-2})$.
Consequently the relative conclusions remain valid when $u$ tends to
zero at an arbitrary rate as the coefficient index increases.
These statements concern late coefficients; they do not evaluate the
divergent infinite sector series at the physical specialization.

The remaining asymptotic questions include all inverse-index orders,
uniformity for a growing slow parameter, and a sharp remainder theorem
for optimal truncation of the actual inverse.
```

## 5. Proposed replacement for the continuation part of predecessor §11.2

The following replaces the original two-question paragraph. It records both the continuation result and the directly obtained boundary model, then leaves the stronger classification questions open. It uses `R` exactly as defined in the predecessor's `eq:R-all`.

```latex
\subsection{Inverse Borel continuation: resolved part and open classification}
For every fixed $u\in\mathbb C$, the germ $\widehat V_u$ continues
analytically along every path starting at the origin and thereafter
avoiding $A\mathbb Z$. The formal series $V(q,u)$ is $1$-summable in
each direction outside $\pi\mathbb Z$. These assertions are proved in \cite{latecoeff2026}
by checking the hypotheses of Sauzin's nonlinear resurgence and
summability theorems \cite{Sauzin2015}.
The model-specific reduction is
\[
 h(t)=\frac{\sqrt{1-2u^2R(t)}-1}{u},\qquad
 G(x)=x\exp\{-h(1/x)\},\qquad
 V(q,u)=h\!\left(\frac1{G^{-1}(1/q)}\right),
\]
with the square root tending to one and the case $u=0$ filled in by
continuity; $G^{-1}$ is the compositional inverse near infinity.
The closed discrete set $A\mathbb Z$ contains zero and
is stable under addition, as required by the closure theorem.
The resulting sectorial sums satisfy the exact summed form of
\eqref{eq:formal-inverse} on sufficiently small common sectors.

The positive-axis question also has a direct coefficient answer.
With $z=Au/4$,
\[
 \widehat V_u(\xi)
 =\frac{2u}{\xi}
   \left\{e^{-z}\log(1-\xi/A)+e^z\log(1+\xi/A)\right\}
   +\mathcal H_u(\xi),
\]
where the logarithms are their Taylor branches at zero and
$\mathcal H_u$ is holomorphic in $|\xi|<A$ and continuous on the
closed disk. Both $A$ and $-A$ are genuine singularities whenever
$u\ne0$, so the Borel radius is exactly $A$. The first coefficient
correction gives an explicit dilogarithmic refinement with a
continuously differentiable remainder \cite{latecoeff2026}.

The set $A\mathbb Z$ is an allowed singularity set, not a statement
that every lattice point is active on every sheet. In particular, the
origin may become singular on another sheet even though the initial
germ is regular there. Determining the active higher lattice points,
their path-dependent local singularity germs, and the complete Stokes
or alien calculus remains open. Continuous boundary control alone
does not establish that stronger analytic classification.
```

Add the following entries to the predecessor's bibliography if the proposed keys are not already present:

```latex
\bibitem{latecoeff2026}
\emph{Sharp Late Coefficients and Borel Continuation of Resonant Lambert
Inverses}, research contribution prepared for Vladimir Reshetnikov and
the ProveIt project, 12 October 2026. Companion report, especially the
theorems ``Sharp uniform late coefficients,'' ``Boundary models with
controlled remainders,'' and ``Continuation of the quadratic inverse.''

\bibitem{Sauzin2015}
D. Sauzin, \emph{Nonlinear analysis with resurgent functions},
Annales scientifiques de l'\'Ecole Normale Sup\'erieure, S\'erie 4,
\textbf{48}(3) (2015), 667--702, Theorems 3, 5, $3'$, and $5'$.
\url{https://doi.org/10.24033/asens.2255};
\url{https://arxiv.org/abs/1212.4477}.
```

After integration, the companion entry can link to its actual repository path and commit. No URL to an uncreated report directory is asserted here.

## 6. Editorial review boundary

The proposed changes promote proved conjectures and refine valid conclusions. They do not retract an existing theorem, assert ordinary convergence of the factorial sector series, or identify arithmetic averaging with nonlinear median summation. The full lattice and alien-calculus questions, off-resonance transport, deformation of the full complex folds, and certified optimal-truncation analysis remain research topics. Keep those questions visible when updating the predecessor's outlook.

## 7. Ready-to-apply patch and validation

The unified patch [integration/predecessor-status-update.patch](integration/predecessor-status-update.patch) applies exactly the two subsection replacements above and the two bibliography additions to the inspected predecessor's `article.tex`. It preserves the two original conjecture equation labels. The replacement uses `\Phi_0` and `\Phi_1` for its parity functions, avoiding the predecessor's existing hypergeometric kernel `H_ε`.

The expected unmodified `article.tex` has SHA-256:

```text
c36a744b02ccfc2bdbac296088d10cd542291fe2c909153cdfab8f4c8c6ec29b
```

From an editable copy of the extracted predecessor directory containing `article.tex`, run the following, replacing the package path with its actual location:

```bash
git apply --check /absolute/path/to/lambert_inverse_late_coefficients/integration/predecessor-status-update.patch
git apply /absolute/path/to/lambert_inverse_late_coefficients/integration/predecessor-status-update.patch
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

For a different target revision, inspect the hunks against that revision before applying them. The patch changes one file, with 96 inserted and 23 deleted lines; it leaves the rest of the predecessor intact.

Validation was performed on separate scratch copies of the exact original and modified source. The patch passed `git apply --check`, applied successfully, and reproduced the expected modified bytes. Both versions compiled with `latexmk`: the baseline produced 22 pages and the patched version 23. The final logs have no undefined references or citations, multiply defined labels, TeX errors, or overfull boxes. Both retain the same original `amsmath` advisory about `\over` and the same three underfull bibliography boxes. The original fetched source was not modified.

[integration/validation.json](integration/validation.json) records the source and patch hashes, label checks, application checks, page counts, and warning comparison. The complete predecessor source and its compiled PDF are omitted from this deliverable; the patch contains the proposed changes.
