# Claim ledger

All theorem numbers refer to `article.pdf` / `article.tex`.

| Claim | Status and dependency | Boundary |
|---|---|---|
| Theorem 3.1: exact simplex optimizer | Written proof: compactness, boundary improvement, Lagrange equation, tangent second variation, monotonic scalar root. | No claim that all two-order entropy extremal ideas originate here. |
| Lemma 4.1: explicit tangent inverse | Direct substitution on the sum-zero tangent space; independently checked numerically. | Interior formulas; global inequalities extend by continuity. |
| Theorem 4.3: subunit criterion | Written proof using the evaluated block suprema and rank-one Hessian. | The abstract rank-one/block-product method already appears in ProveIt. |
| Corollary 4.4: strong and strict concavity | Written weighted Cauchy--Schwarz and face-restriction proof. | The displayed strong-concavity constant is not claimed optimal. |
| Theorem 5.1: 17 versus 18 symbols | Written proof plus exact polynomial identity and rational curvature data. | Three factors at half order; an arbitrary mixed tuple with one size-18 block need not fail. |
| Proposition 5.2: finite midpoint violation | Exact rational square-root enclosures, with checked positive gap. | Running Python is not a Lean/kernel proof of the checker. |
| Theorem 6.1: rational-order decision | Mathematical algorithm using specified real algebraic roots and exact sign decisions. | The general mixed-alphabet equality branch is not implemented here. |
| Theorem 7.1: convergent large-alphabet expansion | Analytic implicit-function theorem and stationarity of the leading coefficient. | Fixed q, locally uniform away from q=0 and q=1. |
| Theorem 7.2: alphabet-independent threshold | Written consequence of Theta_k < q and Theta_k -> q. | Every particular alphabet is finite; no unrestricted infinite-entropy limit is claimed. |
| Proposition 7.4: varentropy endpoint | Self-contained limiting derivation; the underlying varentropy extremal problem is credited to existing literature. | Not presented as a newly solved classical varentropy problem. |
| Theorem 8.1: Shannon window | Analytic removable-singularity/implicit-function proof with uniform compact-parameter remainder. | Symbolic series checks alone do not prove the uniform theorem. |
| Corollary 8.2: lower boundary | Analytic local implicit-function argument. | No global unimodality or globally unique failure interval is asserted. |
| Theorem 9.2: superunit matrix criterion | Written compression, contraction, and Schur-complement proof. | For 1 < q < 2; q=2 and q>2 are treated separately. |
| Proposition 9.3: remaining orders | Written direct and binary-face arguments. | Binary special cases are recovered prior results, not new claims. |
| Corollary 9.4: upper boundary | Written analytic expansion and local root argument. | Common alphabets, at least two factors, local Shannon neighborhood. |
| Theorem 10.1: quantum extension | Written spectral divided-difference proof; twelve finite-difference diagnostics. | Product-state marginal parameterization only; not a claim about entangled-state geometry. |
| Further research and Lean architecture | Proposed future work. | No implementation or proof is asserted for the proposed open tasks. |

## Novelty and review status

The package resolves the full-categorical-simplex instance of the explicitly
inspected ProveIt Q7 and extends it in several directions. A targeted source
review is not a global priority audit. The manuscript is unrefereed and not
formally verified. The report's exact certificates and numerical scripts
have been run; no entire ProveIt build or external manuscript proof review is
claimed.
