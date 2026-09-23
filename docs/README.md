# The surreal and surcomplex reports

This collection has **56 research reports in five families**. Start with the
reading routes below, use the [notation guide](NOTATION.md) when moving between
reports, and consult the [typeset catalogue](manifest.pdf)
([source](manifest.tex)) for longer descriptions. The
[formalization ledger](FORMALIZATION.md) lists the main sources and maps exact
claims to checked Lean declarations. The [exposition review record](REVIEW.md)
identifies corrected portions and the scope still to review.

These are AI-assisted research drafts. A report's mathematical argument,
finite verification programs, and Lean coverage are separate forms of evidence.
Some statements and prerequisites now have checked Lean proofs; no complete
formal verification of the collection is claimed. Each report records its
hypotheses, limitations and provenance.

## Newest reports

The [omnific Diophantine article](surreal/omnific-diophantine-geometry/)
now assembles five manuscripts, and the
[set-sized quotient article](surreal/set-sized-quotients-of-omnific-integers/)
thirteen. The Diophantine proof review covers the original material in
Sections 1–10 and current Sections 14–15, plus the new elementary
definability and constant-term Sections 11–12. Added material in Sections 6
and 10, Sections 13 and 16–17, and remaining source reconciliation need review;
the [reconciliation](surreal/omnific-diophantine-geometry/RECONCILIATION.md)
records that boundary. Two further Diophantine companions (08–09) and three
quotient companions (17–19) are placed but not integrated. The rectification
addition to [entire functions](surcomplex/entire-functions-at-arbitrary-rank/)
is integrated, but remains outside its earlier review scope.

Two further assembled reports cover
[omnific-preserving automorphisms](surreal/omnific-preserving-automorphisms/)
and [omnific groups and lattices](surreal/omnific-groups-and-lattices/).
Placement `a4dcb91` adds the base texts for
[definable surreals](foundations-and-computation/definable-surreals-and-omnific-integers/),
[omnific notations](foundations-and-computation/omnific-notations/), and
[Hahn–Hilbert geometry](surcomplex/hahn-hilbert-geometry/), with four companions
still to integrate. Their proof review and formalization remain pending.

Batch 23 (placed in `e4f8848`, written in `7af7056`) adds
[Gamma and zeta](surcomplex/gamma-and-zeta-functions/), merged from six
manuscripts on the same questions after a claim-by-claim comparison; its
proof review and formalization remain pending.

Batch 22 (placed in `7b5f934`, written in `68e2960`) adds two reports,
[first-kappa coefficients](surcomplex/first-kappa-coefficients/) and
[single-dilation Hahn support](surcomplex/single-dilation-hahn-support/), and new
sections to the measures, holonomic-rigidity, Euclidean three-space,
entire-functions and trigonometry reports. Their proof review and
formalization remain pending.

Two reports placed in `d4e71b7` and written in `3a2d35d` are catalogued in the
tables below: [surreal fields across universes](foundations-and-computation/surreal-fields-across-universes/)
and [birthday cutoffs and hereditary sets](foundations-and-computation/birthday-cutoffs-and-hereditary-sets/),
both set theory about the surreal field. Their proof review and formalization
remain pending.

Four reports placed in `5fe7f8d` and written in `fb182ea` are catalogued in the
tables below:
[vector and tensor fields](surreal/vector-and-tensor-fields/),
[Euclidean three-space](surreal/euclidean-three-space/),
[finite surreal probability](surreal/finite-surreal-probability/) and
[surcomplex field automorphisms](surcomplex/surcomplex-field-automorphisms/).
The finite-probability main-text review now covers Sections 2–17; remaining
imports and source reconciliation remain pending. The field-automorphism
main-text review covers Sections 1–15 and Appendix B; its remaining imports
and source reconciliation, and review of the other two reports, are pending. Lean coverage is tracked
separately in the ledger. The same batch added
source material to the measures and trigonometry reports; those additions do
not extend their earlier proof-review scope.

## Reading routes

- **For foundations or formalization:** read
  [foundations](foundations-and-computation/foundations/), especially its
  size restrictions and verification boundary, then the current
  [formalization ledger](FORMALIZATION.md). The proposed architecture in the
  article is a plan; the ledger records implementation status.
- **For surcomplex analysis:** read [analysis](surcomplex/analysis/), then the
  four-ring comparison in [analytic geometry](surcomplex/analytic-geometry/).
  Continue to finite deformations, contours, or global divisors as needed.
- **For computation:** read [computer algebra](foundations-and-computation/computer-algebra/)
  for capability levels and prototypes, and
  [computable surreals](foundations-and-computation/computable-surreals/)
  for representations and uniform algorithms.
- **For measures and probability:** read
  [Hahn-valued measures and probability](surreal/hahn-valued-measures-and-probability/)
  first. Its distinction between *strong* and *coefficientwise* countable
  additivity is a prerequisite for
  [Hahn–Herglotz positivity](surcomplex/hahn-herglotz-positivity/), whose
  measures require coefficientwise additivity, with strong additivity optional. "Moment" means power moments there,
  Fourier moments in the Herglotz report, and finite Prony input in
  [Prony reconstruction](surcomplex/prony-reconstruction-at-surreal-scales/).
- **For a particular theorem:** use the report tables below. Read its local
  conventions before importing a definition from a companion report.

## Surreal numbers: twenty reports

| Report | Question or main subject |
|---|---|
| [Hahn evaluation at omega](surreal/hahn-evaluation-at-omega/) | Why increasing-support evaluation `x^a ↦ ω^a` fails, and which exponent maps permit field homomorphisms |
| [Broadcast sums](surreal/broadcast-sum-of-surreal-sequences/) | The sign-truncation game and Lipparini's broadcast-sum question |
| [Product birthdays](surreal/gonshor-product-birthdays/) | Gonshor's bound `b(xy) ≤ b(x) ⊗ b(y)` for specified ordinal-support normal forms |
| [Laurent birthdays](surreal/gonshor-laurent-birthdays/) | The same bound and sharper formulas over `ℝ((ω⁻¹))` |
| [Canonical forms and option graphs](surreal/canonical-forms-need-not-be-subgraphs/) | Why a canonical representative need not occur as a subgraph of a given form |
| [Genetic gaps and primitives](surreal/genetic-gaps-and-primitives/) | A nonconstant genetic indicator with derivative zero |
| [Exponential automorphism rigidity](surreal/exponential-automorphism-rigidity/) | Finite displacement identities, faithful action on the value group and a negative answer to Kaplan–Krapp–Serra Question 5.4 (arXiv v3); "rigidity" here means faithfulness, not triviality |
| [Gamma functions](surreal/gamma-functions/) | Convexity of a family of surreal Gamma extensions and failure of uniqueness |
| [Tail-spans and differential transcendence](surreal/tail-spans-and-differential-transcendence/) | Cofinite spans classify relations among Hahn sums with independent square-root coefficients; continuum many differentially independent surreals and analytic functions; its derivation formula is cited from the surcomplex differential-equations report |
| [Hahn-valued measures and probability](surreal/hahn-valued-measures-and-probability/) | Strong and coefficientwise Hahn-valued measures: atomicity, extension and moment criteria, hidden negative mass; the `ω+1` threshold and the finitely supported standard part hold only in the strong class; a countable-scale density criterion, Hahn-valued integration and conditional expectation; the exact Bernoulli product criterion at interior baselines without uniform separation |
| [Markov generators at every scale](surreal/markov-generators-at-every-scale/) | All-scale resolvent hierarchies of finite positive Hahn rate matrices and their converse realization; divisible value group, no path measures or infinite state spaces |
| [Transcendence over bounded support](surreal/transcendence-over-bounded-support/) | `2^cf(G)` algebraically independent Hahn series over the fraction field of bounded-support series, and linear-disjointness descent; transcendence from the support, not the coefficients |
| [Matrix scaling at surreal scales](surreal/matrix-scaling-at-surreal-scales/) | Fixed-margin diagonal scaling of positive Hahn matrices; the spanning-tree deletion gap is the exact gain; no Sinkhorn convergence claim |
| [Vector and tensor fields](surreal/vector-and-tensor-fields/) | Layered tensor calculus with surreal coefficients in every dimension: Hahn-supported smooth fields, Taylor prolongation, Hodge and Stokes; 3D calculus and Minkowski fields as parts; not a physics claim |
| [Euclidean three-space](surreal/euclidean-three-space/) | Coordinate and spherical geometry of `No³` with finite angles, and the rotation group `SO(3,No)` as a split extension with a perfect infinitesimal kernel; normal subgroups by valuation cuts and the universal set-sized quotient of `SO(3,No)` |
| [Finite surreal probability](surreal/finite-surreal-probability/) | Surreal-valued probability on finite algebras: conditioning on infinitesimal events, log-odds, entropy, scoring rules; compare the measures report for countable additivity |
| [Omnific Diophantine geometry](surreal/omnific-diophantine-geometry/) | Arithmetic and Diophantine equations over the omnific integers; constant-term transfer, rigidity and definability; five-source assembly; reviewed original material in Sections 1–10, new Sections 11–12 and current Sections 14–15; other added material and later review pending |
| [Set-sized quotients of omnific integers](surreal/set-sized-quotients-of-omnific-integers/) | Constant-term factorization of maps to set-sized rings and cardinal/homological thresholds; thirteen-source assembly; three further companions and proof review pending |
| [Omnific-preserving automorphisms](surreal/omnific-preserving-automorphisms/) | Convex-scale stabilizers, definable constants, nondefinable monomials and algebraic-parameter rigidity; four-source assembly, review pending |
| [Omnific groups and lattices](surreal/omnific-groups-and-lattices/) | Algebraic groups, elementary kernels and missing lattice minima over omnific integers; three-source assembly, review pending |

The two birthday reports have different domains. The first allows its specified
ordinal supports but excludes positive powers of `ω`; the Laurent report allows
those powers but uses the integer exponent lattice. Their common part includes
`ℝ[[ω⁻¹]]`. Neither domain theorem subsumes the other. Here `⊗` denotes
**natural ordinal multiplication**, as distinguished in the notation guide.

## Surcomplex numbers: twenty-seven reports

| Report | Main subject and useful prerequisite |
|---|---|
| [Analysis](surcomplex/analysis/) | Hahn-supported calculus, function classes, zero clusters and all-scale rigidity; start here |
| [Analytic geometry](surcomplex/analytic-geometry/) | Coefficient rings, preparation, finite zero geometry and fixed-domain obstructions |
| [Finite deformations](surcomplex/finite-deformations/) | Support-controlled division, multiplicity and residue duality |
| [Contours and Stokes](surcomplex/contours-and-stokes/) | Standard-part Jordan separation, coefficientwise integration and contours representing residue series |
| [Global divisors](surcomplex/global-divisors/) | Plane support obstructions; compact Picard classification, cohomology and Abel criteria |
| [Polynomial algebra](surcomplex/polynomial-algebra/) | Finite-degree factorization and root geometry in modulus and valuation balls |
| [Trigonometry](surcomplex/trigonometry/) | Finite-angle polar representation and geometry at arbitrary surreal scale; the rotation group `SO(2,No)`; period arithmetic of global phases and a partial answer to an Ehrlich–Kaplan question |
| [Differential equations](surcomplex/differential-equations/) | Berarducci–Mantova differential algebra and finite primitives; matrix, regular-singular and autonomous equations; transfinite second-order critical potentials; coherent coordinate equations; its Section 5 on "phase" is a prerequisite |
| [Rank-one Berkovich geometry](surcomplex/rank-one-berkovich/) | Tate algebras, disks and annuli in the fixed field `ℂ((t^ℝ))` |
| [Spectral theory](surcomplex/spectral-theory/) | Finite matrices over real closed fields, singular values and valuation scales; exact matrix-root fields and Hankel splitting fields of squarefree real-rooted polynomials over a nondivisible `Γ` |
| [Dynamics and normal forms](surcomplex/dynamics-and-normal-forms/) | Linearization, periods and quasi-periodic equations; exact scalar and drifting multipliers answer the common-domain question oppositely, and an angular-rank bound covers every exact diagonal multiplier; its convention and threshold tables are prerequisites |
| [Nonabelian support](surcomplex/nonabelian-support/) | Matrix Cousin problems, inverse monodromy, and essential-singularity bundles that stay nontrivial over `Mer((t^Γ))`; its two support criteria test different objects; compare the scalar global-divisor report |
| [Entire functions at arbitrary rank](surcomplex/entire-functions-at-arbitrary-rank/) | Cofinality, factorization, the exact jet image, ideals above canonical products and scalar extension of entire series over one fixed Hahn field; in several variables only the scalar-extension clause is answered; prime ideals above one-simple-node products and their splitting under cofinal extension; formal rectification and its support restrictions |
| [Holonomic rigidity](surcomplex/holonomic-rigidity-for-entire-hahn-functions/) | Entire D-finite series are polynomials, and an order-unit criterion decides which nontorsion dilations admit nonpolynomial entire solutions; this is not the order-unit dichotomy of entire functions at arbitrary rank; first-order algebraic ODEs have only polynomial entire solutions; with no order unit, every nonpolynomial entire series is differentially transcendental in all orders (the order-unit case stays open) |
| [Hahn–Tate uniformization](surcomplex/hahn-tate-uniformization/) | Tate elliptic curves at arbitrary rank: exact Hahn domain `U_q` and `U_q/q^ℤ ≅ E_q(K)`, plus multiscale theta series; the bounded-period quotient itself has a Molcho–Wise precedent |
| [Infinite-dimensional Hahn spectral theory](surcomplex/infinite-dimensional-hahn-spectral-theory/) | Two inequivalent spectra: ordinary normal operators extended to `H((t^Γ))`, and exact diagonalization of row- and column-finite Hahn matrices; Section 3 reconciles their apparently conflicting accumulation statements; Parts III and IV add Drazin halos for any unital algebra and noncommuting compact perturbations |
| [Expanding polynomial dynamics](surcomplex/expanding-polynomial-dynamics/) | Exact itinerary fibers of expanding polynomials over Hahn fields, and the order-unit dichotomy; valuation-expanding is not repelling, and no Julia/Fatou theory is built |
| [Hahn–Herglotz positivity](surcomplex/hahn-herglotz-positivity/) | Matrix Herglotz normalization on halos, a null-ideal positivity criterion, and Toeplitz-positive Fourier moments with no positive measure; it assumes coefficientwise additivity, with strong additivity optional |
| [Prony reconstruction](surcomplex/prony-reconstruction-at-surreal-scales/) | Sharp valuation threshold for recovering `n` weighted nodes from `2n` power moments (no measures); compare polynomial algebra's coefficient threshold |
| [Wick summability certificates](surcomplex/wick-summability-certificates/) | Finite strict valuation inequalities decide strong summability of polynomial Wick diagram families over `ℂ((t^Γ))`, `Γ` divisible; diagramwise only, and a Hahn value is not an integral |
| [Three duals of Hahn vector spaces](surcomplex/three-duals-of-hahn-vector-spaces/) | Algebraic extension, completion and strong closure of `V((t^Γ))`; strong operators; comparison of represented, strong and continuous duals of a Hahn–Hilbert space |
| [Hidden negative Hermitian directions](surcomplex/hidden-negative-hermitian-directions/) | Hermitian forms positive over the finite-lattice-supported subfield yet indefinite over `ℂ((t^Γ))`; a two-scale matrix null-ideal criterion |
| [Hahn–Hilbert geometry](surcomplex/hahn-hilbert-geometry/) | Orthogonal splitting, amplified graphs and Fredholm least squares; placed base, companion integration and review pending |
| [Surcomplex field automorphisms](surcomplex/surcomplex-field-automorphisms/) | Plain, valued, value-fixing and 1-automorphisms of `No(i)`; the real-axis stabilizer `Aut(No)×C₂` and phase twists that move `No`; exponential results are the rigidity report's |
| [First-κ coefficients](surcomplex/first-kappa-coefficients/) | Hahn series with fewer than `κ` terms: omitted types classified by the first `κ` coefficients, completion iff `cf(Γ) ≠ cf(κ)`, never spherically complete |
| [Single-dilation Hahn support](surcomplex/single-dilation-hahn-support/) | One monomial dilation defines coefficients, monomials and the valuation ring; its centralizer among all field automorphisms; undecidability |
| [Gamma and zeta](surcomplex/gamma-and-zeta-functions/) | Finite lifts and RH, strongly summable Dirichlet series at infinity, Stirling and Hurwitz, Gamma and zeta on the horizontal tube for any phase, reflection obstructions at infinite height; six manuscripts reconciled |

Three distinctions recur throughout these reports.

**Specify the topology and the size of the index set.** In the full surreal
fine topology, every set-sized subset is closed and discrete, and a convergent
set-indexed net is eventually constant. In a universe-relative formulation,
these assertions require smaller-universe subsets and index types. Intrinsic
valuation topology on a fixed Hahn workspace behaves differently: `t^n → 0`
in `ℂ((t^ℚ))`. Even there, a strongly summable family need not converge
through its finite subsums; the foundations report gives the example
`Σ t^(n/(n+1))`. Formal support conditions and topological convergence are
separate requirements.

**Name the coefficient ring.** These four constructions impose different
conditions; the table is not a chain of interchangeable rings.

| Construction | Requirement |
|---|---|
| `ℂ{z}((t^Γ))` | Each coefficient is a convergent germ; no common radius is required |
| `O(D)((t^Γ))` | Every coefficient is holomorphic on the specified ordinary domain `D` |
| Common-domain Hahn germ ring `𝓡ₙ` | One neighborhood represents all coefficients, with shrinking allowed |
| `ℂ[[z]]((t^Γ))` | Each coefficient is formal |

A fifth construction, `Mer(D)((t^Γ))`, is not in the table: every coefficient
is meromorphic on the specified domain. It appears in global divisors, in
analysis, and in Part III of nonabelian support, which constructs bundles that
stay nontrivial over it.

For `η > 0`, the family `Σ_{r≥1} t^(rη)/(1−rz)` lies in the radius-free germ
ring but not in the common-domain germ ring: its coefficient poles `1/r`
approach zero. This witnesses that particular strict inclusion. Analytic
geometry gives separate obstructions for fixed domains and explains why
shrinking changes the applicable theorems.

**Keep different operations distinct.** Formal differentiation in `z`, a fine
derivative, and the Berarducci–Mantova scalar derivation act on different data.
A finite angle `θ` for `cis θ` is not an arbitrary primitive of an imaginary
coefficient. Likewise, nonabelian gluing uses supports of normalized **polar
factors**, while monodromy realization uses the **raw** monodromy matrices.
The [notation guide](NOTATION.md) records these distinctions and their local
symbols.

## Surquaternions: one report

[Surquaternions](surquaternions/surquaternions/) develops Hamilton's algebra
over surreal coefficients, its Hahn workspaces, and its exponential and
differential structures. Its convention table distinguishes three
exponentials and four derivative notions. Noncommutative identities need
their own hypotheses: the radial exponential obeys the usual product law on
a common commutative slice, but not on arbitrary pairs of quaternions.

## Physics: one report

[Surreal scalars and spacetime](physics/surreal-scalars-and-spacetime/)
separates exact symbolic identities, conditional mathematics, physical
assessments and imported results. Replacing scalars can encode asymptotic
scales without regularizing a singular metric. For example, with nonzero
Schwarzschild mass `m`, the substitution `r = s^q w(s)`, with integer `q ≥ 1`,
`w ∈ ℝ[[s]]` and `w(0) ≠ 0`,
in `48m²/r⁶` gives a pole of order `6q` and leading coefficient
`48m² w(0)^(−6)`. The recorded special case `w(s) = 1+s` preserves `48m²`;
general substitutions need the factor `w(0)^(−6)`.

## Foundations and computation: seven reports

| Report | Main subject |
|---|---|
| [Foundations](foundations-and-computation/foundations/) | Classes and universes, workspace localization, support recursion, topology and a formalization proposal |
| [Computer algebra](foundations-and-computation/computer-algebra/) | Exact denotation, coefficient access, equality and approximation; three distinct Wolfram prototypes |
| [Computable surreals](foundations-and-computation/computable-surreals/) | Structural names, effective left-finite Hahn names and bounded-denominator Puiseux names |
| [Surreal fields across universes](foundations-and-computation/surreal-fields-across-universes/) | External saturation of an inner model's `No^M` in a same-ordinal outer universe: new ordinal sequences, fresh-sign gaps, first new birthday, nonconjugate surcomplex real forms |
| [Definable surreals and omnific integers](foundations-and-computation/definable-surreals-and-omnific-integers/) | Definability, HOD and finite omnific codes; placed base, companion integration and review pending |
| [Omnific notations](foundations-and-computation/omnific-notations/) | Exact holonomic towers and complexity of equality and support validity; placed base, two companions and review pending |
| [Birthday cutoffs and hereditary sets](foundations-and-computation/birthday-cutoffs-and-hereditary-sets/) | Surreals born below an epsilon number, with birthday, interpret `H_κ`: bi-interpretation, elementary inclusions, axiom spectra, outer models, orientation |

A mathematical closure theorem need not supply a uniform algorithm on the
chosen names. In particular, numerical coefficient access does not supply a
decidable exact support or a leading exponent. The computability report states
which operations need that additional information. The computer-algebra
report separately records each prototype's coefficient field, exponent
lattice, supported operations and known implementation defects.

## Files, provenance and building

Each report has a maintained LaTeX source, its PDF and a local README. Most
also retain verification programs under `code/` and recorded outputs under
`data/`. Those finite checks do not establish infinite theorems. The former
`sources/` archives were retired in `e5791a8`; their tracked originals remain
available in Git history. For example, run
`git ls-tree -r --name-only 608dd23 -- docs` to locate an old manuscript and
`git show 608dd23:<path>` to read it. The computable-surreals originals were
never tracked here; its provenance manifest records their archive identities
and hashes. Reconciliation of every source claim remains a separate audit
obligation.

Build from the report's own directory with a TeX distribution containing its
listed packages:

```sh
latexmk -pdf -halt-on-error -interaction=nonstopmode article.tex
```

If `latexmk` is unavailable, run `pdflatex -halt-on-error
-interaction=nonstopmode article.tex` repeatedly until references and the
contents stabilize. Use `surreal_product_birthdays.tex` in the product-birthday
directory, `surreal_graphs.tex` in the option-graph directory, and `manifest.tex`
for the catalogue. The broadcast-sum report uses its checked-in `article.bbl`.
Inspect the final log for unresolved references and inspect affected PDF pages;
a successful typesetting run is not a proof check.
