# Source audit and integration notes

## Baseline and purpose

This package contains **Summation and Singularities under Polylogarithmic Reversion: Convergent angular reconstruction, sharp Lambert late terms, and removable inverse endpoints**, dated 12 October 2026.

The repository baseline is **`8f5afd4d7565df808359f6a0c22f87f79a119bb9`** in [VladimirReshetnikov/ProveIt](https://github.com/VladimirReshetnikov/ProveIt). The cited repository files and the current incoming archive inventory were retrieved at that exact commit on **2026-10-12**. `PROVENANCE.json` records the full repository paths, connector-reported Git blob identifiers, pinned URLs, and the inspected archive members.

This is a targeted mathematical source audit. It identifies the statements used, prevents duplication of the newest arrivals, and distinguishes proved results from conjectures and questions. It is not an audit of every file or theorem in the two research programs. Earlier read-only material helped locate relevant reports; the principal cited sources were refreshed at the baseline above. No remote repository file was modified in preparing this delivery.

The mathematical assertions and their hypotheses are those in `polylogarithmic_reversion.tex` and its `sections/` files. This note supplies provenance and proposed status changes; it does not broaden any theorem.

## 1. Precisely identified source material

### Polylogarithms

| Source | Git blob SHA | Inspected material |
|---|---|---|
| [Angular-zero continuation](https://github.com/VladimirReshetnikov/ProveIt/blob/8f5afd4d7565df808359f6a0c22f87f79a119bb9/Analysis/Polylogarithms/docs/reports/angular-zero-continuation/article.tex) | `9c2ec9383debad3b1a1248c13f442a0d850487b5` | `thm:allorders`, `eq:lagrange-coefficient`, `eq:allorder-expansion`, `eq:normalized-zero-equation`, and `rem:not-convergent`: the original multiset coefficients, finite-cutoff theorem, and convergence warning. |
| [Formal reductions: angular divergence](https://github.com/VladimirReshetnikov/ProveIt/blob/8f5afd4d7565df808359f6a0c22f87f79a119bb9/Analysis/Polylogarithms/docs/reports/formal-reductions-continuation/article/sections/angular_divergence.tex) | `87bd27fed0a8b0f6c50e96532a78b2d4131280c1` | `angular:thm:divergence`: divergence even after equal rational exponential bases are combined. |
| [Formal reductions: research questions](https://github.com/VladimirReshetnikov/ProveIt/blob/8f5afd4d7565df808359f6a0c22f87f79a119bb9/Analysis/Polylogarithms/docs/reports/formal-reductions-continuation/article/sections/research.tex) | `dc5d3858548e8155ae13d0eba5938d6a7b2c6395` | Research items 13 and 14: moving optimal truncation and a justified summation procedure. |
| [Real-order threshold](https://github.com/VladimirReshetnikov/ProveIt/blob/8f5afd4d7565df808359f6a0c22f87f79a119bb9/Analysis/Polylogarithms/docs/reports/real-order-threshold/article/real_order_threshold.tex) | `fb8813996c16084014dd3154d4ec299d14996c93` | `thm:double` / `eq:double`, `thm:angular`, and `cor:gaussian`: the positive double kernel, global angular-zero uniqueness, and Gaussian-point sign information used as prior results. |

### Transseries

| Source | Git blob SHA | Inspected material |
|---|---|---|
| [Polylogarithm resonance and inverse transseries](https://github.com/VladimirReshetnikov/ProveIt/blob/8f5afd4d7565df808359f6a0c22f87f79a119bb9/Analysis/Transseries/docs/series-and-transseries/Polylogarithm_Resonance_And_Inverse_Transseries/polylogarithm_resonance_and_inverse_transseries.tex) | `4a3731f5d9ad0ee2ec1272cf756b93889e3457da` | `prop:noninteger`, `lem:univalence`, `lem:cutgap`, `prop:delta`, and further research question 9. The first supplies convergent noninteger charts; the cut-modulus and endpoint-circle statements are proved in an integer-order setting. |
| [Resonant polylogarithm transseries](https://github.com/VladimirReshetnikov/ProveIt/blob/8f5afd4d7565df808359f6a0c22f87f79a119bb9/Analysis/Transseries/docs/series-and-transseries/Resonant_Polylogarithm_Transseries/article.tex) | `d54638582ab147eb4a48a846c3bdc371643aaf39` | The explicitly open quadratic-feedback boundary question under “Further research questions and concrete next steps,” item 1. This is already addressed by later work and is not presented as a new result here. |
| [Quadratic boundary completion README](https://github.com/VladimirReshetnikov/ProveIt/blob/8f5afd4d7565df808359f6a0c22f87f79a119bb9/Analysis/Transseries/docs/series-and-transseries/Quadratic_Polylogarithm_Feedback_Boundary_Completion/README.md) | `4904a66f944d8574268f5f2cd67932d6206041d6` | Existing placement and relationship to the predecessor. |
| [Quadratic boundary completion intake audit](https://github.com/VladimirReshetnikov/ProveIt/blob/8f5afd4d7565df808359f6a0c22f87f79a119bb9/Analysis/Transseries/docs/series-and-transseries/Quadratic_Polylogarithm_Feedback_Boundary_Completion/INTAKE-PROOF-AUDIT.md) | `de53aa45ad6d458e5714d1ba90bfe86abac6acc5` | Its recorded closure of the old boundary question, preservation of the correct interior theorem, and distinctions between checked phase results and other integration tasks. |

### Incoming archives at the baseline

The directory contains the following three archives and its README. All three archives were fetched and extracted before the research targets were finalized. The principal TeX members were read for overlap; the Lambert coefficient theorems and conjecture received a detailed proof-level continuation. This does not claim an exhaustive proof audit of every theorem or a replay of every predecessor verification suite.

| Archive in `docs/incoming/` | Git blob SHA | Inspected TeX member |
|---|---|---|
| `ProveIt_Lambert_Polylog_Order_Jets_2026-10-12.zip` | `cbc18147fad1ae095870e730c6bf02b90ad99490` | `lambert_polylog_order_jets/main.tex` |
| `ProveIt_Quadratic_Polylog_Boundaries_2026-10-12.zip` | `6bb0a65d6bbff7aefef1b445b4c2bb08d565cdc2` | `ProveIt_Quadratic_Polylog_Boundaries_2026-10-12/article.tex` |
| `Resonant_Lambert_Inverse_Transseries_2026-10-12.zip` | `8ccc077fe2609b914d1f2c4ba5590f51c360c4cc` | `Resonant_Lambert_Inverse_Transseries/article.tex` |

The archive blob identifies the repository object. The extracted TeX members are not separately tracked Git objects at this baseline, and this package does not invent independent repository blob identities for them. Archive-member names are recorded exactly, including their wrapper directories.

The incoming README has blob `9956ad83c5ddfa3c75e5f2946481a83082bc81e8`. Its inventory and destination guidance were consulted for this proposal. The archives remain incoming predecessors at the stated baseline; their presence is not a claim of canonical integration or independent publication review.

## 2. Statement-level status changes

| Source target | Status at the baseline | Result in this delivery | Integration scope |
|---|---|---|---|
| Formal reductions, research item 14 | A justified summation method is requested. | `ang:thm:sum` and `ang:thm:Abel` construct the specified radial-Abel/degree summation and prove ordinary absolute convergence of the outer degree sum for every real `a >= 6`, `b > 0`, and `0 < rho <= 1`, with an explicit geometric error. | Mark answered in this stated range. The threshold 6 is sufficient, not optimal; smaller outer orders remain a separate question. |
| Formal reductions, research item 13 | Optimal moving truncation is requested. | `ang:thm:finite` gives an explicit finite frequency-and-degree error bound; `ang:thm:gaussian` gives an attainable `exp(-lambda*a^2 + O_lambda(a))` scale for `0 < lambda < log(3/2)`. | Record partial progress only. The sharp optimum in the original exponential-base ordering, and computational optimality, are not established. |
| Incoming resonant Lambert inverse, `eq:conj-even` and `eq:conj-odd` | Explicitly unproved hyperbolic large-order amplitudes; the source identifies lack of uniform control over the number of factors. | `lm:thm:sharp` proves both amplitudes with a locally uniform complex-coupling error; `lm:thm:first` proves the next relative term. | Mark both displayed conjectures proved by this continuation. Preserve attribution for the source's finite coefficient formula and existing positive-real Borel-radius theorem. |
| Incoming Lambert inverse, nearest Borel singularities | The source proves a sharp radius and a negative-axis singularity for positive real coupling, without both local amplitudes. | `lm:cor:logs` identifies both radial logarithmic amplitudes for every nonzero complex coupling; `lm:cor:dilog` gives an exact log/dilog decomposition in the initial disk with a remainder and first derivative continuous on the closed disk. | Add this refinement. Full analytic continuation beyond the initial Borel disk, further singularities, and alien derivatives remain unproved here. |
| Direct inverse predecessor, `prop:noninteger` | Two convergent local charts and rational/irrational/logarithmic behavior are already given. | `ep:thm:classification` determines the exact minimum local ramification degree and the complete exceptional holomorphic family; `ep:prop:coefficients` gives its finite coefficient formula and support. | Record a sharpening/classification of the existing charts, retaining their attribution. |
| Direct inverse predecessor, research question 9 | Global endpoint-circle geometry beyond integer orders is open; the question mentions the integer cut-modulus argument. | `ep:prop:cut-counterexample` shows that extending the cut-modulus ingredient to all real orders is false for `1 < s < 3/2`, and proves the sharp local threshold `s = 3/2`. | Record a negative result for that proposed ingredient. Do not mark the full endpoint-circle/Taylor-radius question solved or disproved merely from this cut-image comparison. |

No established theorem in the inspected predecessors was found false. In particular, the integer-order cut-modulus theorem is not contradicted. The false statement is its unrestricted all-real-order extension; it had not been proved in the source. A chosen image-cut point may be regular for an analytically continued inverse, so failure of the cut-modulus inequality alone does not locate the true nearest inverse singularity.

## 3. Scope distinctions that should survive integration

### Angular reconstruction

The original multiset transseries remains divergent in the source's stated sense. The new prescription first sums a fixed nonlinear degree at subunit radius, then takes that degree's radial Abel limit, and finally sums the degree blocks. The outer convergence theorem is not a claim of ordinary convergence of the complete flattened family at the boundary, nor an arbitrary rearrangement principle. The proof uses a holomorphic complex norm from the positive kernel; it does not differentiate the boundary Fourier series beyond its justified range.

For integer indices, `ang:cor:algebra` places all degree coefficients in a fixed finitely generated algebra of polylogarithm values. It does not prove minimality of this algebra or algebraic independence of its generators. The elementary depth-reduction identity is credited as an ingredient, not claimed as a new classical identity on its own.

The finite Gaussian-error construction is an attainable upper bound for a specified double cutoff. Its frequency cutoff grows exponentially with the outer order. It does not settle the sharp optimal-truncation problem.

### Lambert inverse

The coupling is an independent formal parameter during coefficient extraction. Physical specialization to the large-target relation comes afterward. The large-order theorem is additive and locally uniform on complex coupling sets, including zeros of one leading parity amplitude. A positive-real ratio formulation alone would lose those cases.

The analytic-core universality theorem, `lm:thm:universal`, concerns leading amplitudes. Nonlinear core changes and higher finite-prefix changes first become visible in later corrections. The explicit first correction retains the quadratic core and the forward coefficient `r_2 = 1/288`.

The exact Borel decompositions are identities inside the initial disk. Their remainder regularity supplies radial endpoint information, not analytic continuation across the disk boundary. General factorial reversion and Lambert resurgence are established subjects; the article credits the relevant literature and claims the explicit project conjecture and refinements.

### Direct inverse endpoint

For `alpha = s - 1 = p/q > 0` noninteger rational in lowest terms, the exact ramification degree is `min(p,q)`. Irrational alpha and integer `s >= 2` admit no finite local ramifying cover. The direct inverse is holomorphic at the endpoint exactly when `s = 1 + 1/q`, integer `q >= 2`. These are local classifications of the branch selected from the real interval; statements about absence of finite ramification should not be expanded into a classification of every global inverse sheet.

The quadratic-feedback arrival treats a different implicit function, `uv - v^2/2 = Li_s(r exp(v))`, and already proves related ramification results for that model. This delivery does not claim those quadratic results anew or identify them with the direct inverse of `Li_s`.

## 4. Suggested integration

Preserve this delivered article and its working layout as a continuation package in the Transseries collection. A suitable proposed directory is:

`Analysis/Transseries/docs/series-and-transseries/Summation_And_Singularities_Under_Polylogarithmic_Reversion/`

This is a proposed destination, not a claim that the directory already exists. If intake establishes a combined host for the incoming Lambert report, the Lambert part can instead be catalogued there as an attributed continuation while retaining a link to this complete article.

Useful cross-references are:

1. The Transseries overview, naming the incoming Lambert inverse report and `Polylogarithm_Resonance_And_Inverse_Transseries` as predecessors.
2. The Polylogarithms project status-of-claims record and the `formal-reductions-continuation` research list: item 14 answered for `a >= 6`; item 13 has the explicit double-cutoff upper bound, with optimality still open.
3. The `angular-zero-continuation` report: link the new summation prescription beside its finite multiset expansion and preserve the divergence warning.
4. The eventual host of `Resonant_Lambert_Inverse_Transseries_2026-10-12.zip`: link `eq:conj-even` and `eq:conj-odd` to `lm:thm:sharp`, and the Borel discussion to `lm:thm:first`, `lm:cor:logs`, and `lm:cor:dilog`.
5. The direct inverse predecessor: link `prop:noninteger` to `ep:thm:classification` and `ep:prop:coefficients`; annotate question 9 with the precise local cut-modulus obstruction and the still-open global scope.

The original integer and interior-fold theorems need no retraction. Already resolved quadratic-boundary questions should remain attributed to their existing completion. Promote particular statements into a collective manuscript after statement-level review; do not promote an entire predecessor archive merely because it was inspected for overlap.

## 5. Evidence, attribution, and metadata limits

Every new theorem in the article has a conventional mathematical proof. Separate internal proof review checked the Lambert factorial estimates, parity amplitudes, first correction, and Borel signs; finite exact and numerical checks are supplied under `scripts/` and `results/`. Numerical diagnostics are not interval certificates, and no theorem is represented as proof-assistant formalized or independently refereed.

The classical kernel identities, Lagrange inversion, factorial-asymptotic framework, Lambert resurgence, Jonquiere expansion, and local Puiseux mechanism are attributed. The proposed contribution is a set of explicit answers and refinements relative to the inspected corpus. The primary-source comparison was targeted rather than exhaustive; worldwide first-priority is not established for every theorem, specialization, or corollary.

Git blob identifiers in the provenance file are source-object identifiers returned by the connector, not new checksum requirements for intake. No independent checksum manifest or archive-wide integrity audit was performed. The exact archive identity plus member name is the provenance for an extracted member. This note does not certify statements elsewhere in those archives, and it does not rely on absence of a search hit as proof of novelty.
