# The surreal and surcomplex reports

This collection has **26 research reports in five families**. Start with the
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
- **For a particular theorem:** use the report tables below. Read its local
  conventions before importing a definition from a companion report.

## Surreal numbers: eight reports

| Report | Question or main subject |
|---|---|
| [Hahn evaluation at omega](surreal/hahn-evaluation-at-omega/) | Why increasing-support evaluation `x^a ↦ ω^a` fails, and which exponent maps permit field homomorphisms |
| [Broadcast sums](surreal/broadcast-sum-of-surreal-sequences/) | The sign-truncation game and Lipparini's broadcast-sum question |
| [Product birthdays](surreal/gonshor-product-birthdays/) | Gonshor's bound `b(xy) ≤ b(x) ⊗ b(y)` for specified ordinal-support normal forms |
| [Laurent birthdays](surreal/gonshor-laurent-birthdays/) | The same bound and sharper formulas over `ℝ((ω⁻¹))` |
| [Canonical forms and option graphs](surreal/canonical-forms-need-not-be-subgraphs/) | Why a canonical representative need not occur as a subgraph of a given form |
| [Genetic gaps and primitives](surreal/genetic-gaps-and-primitives/) | A nonconstant genetic indicator with derivative zero |
| [Exponential automorphism rigidity](surreal/exponential-automorphism-rigidity/) | Finite displacement identities and faithful action on the value group |
| [Gamma functions](surreal/gamma-functions/) | Convexity of a family of surreal Gamma extensions and failure of uniqueness |

The two birthday reports have different domains. The first allows its specified
ordinal supports but excludes positive powers of `ω`; the Laurent report allows
those powers but uses the integer exponent lattice. Their common part includes
`ℝ[[ω⁻¹]]`. Neither domain theorem subsumes the other. Here `⊗` denotes
**natural ordinal multiplication**, as distinguished in the notation guide.

## Surcomplex numbers: thirteen reports

| Report | Main subject and useful prerequisite |
|---|---|
| [Analysis](surcomplex/analysis/) | Hahn-supported calculus, function classes, zero clusters and all-scale rigidity; start here |
| [Analytic geometry](surcomplex/analytic-geometry/) | Coefficient rings, preparation, finite zero geometry and fixed-domain obstructions |
| [Finite deformations](surcomplex/finite-deformations/) | Support-controlled division, multiplicity and residue duality |
| [Contours and Stokes](surcomplex/contours-and-stokes/) | Standard-part Jordan separation, coefficientwise integration and contours representing residue series |
| [Global divisors](surcomplex/global-divisors/) | Symmetric-support criteria, Cousin problems and the Picard dichotomy |
| [Polynomial algebra](surcomplex/polynomial-algebra/) | Finite-degree factorization and root geometry in modulus and valuation balls |
| [Trigonometry](surcomplex/trigonometry/) | Finite-angle polar representation and geometry at arbitrary surreal scale |
| [Differential equations](surcomplex/differential-equations/) | Berarducci–Mantova differential algebra, finite primitives and coherent equations |
| [Rank-one Berkovich geometry](surcomplex/rank-one-berkovich/) | Tate algebras, disks and annuli in the fixed field `ℂ((t^ℝ))` |
| [Spectral theory](surcomplex/spectral-theory/) | Finite matrices over real closed fields, singular values and valuation scales |
| [Dynamics and normal forms](surcomplex/dynamics-and-normal-forms/) | Linearization, periods and quasi-periodic equations; its convention and threshold tables are prerequisites |
| [Nonabelian support](surcomplex/nonabelian-support/) | Matrix Cousin problems and inverse monodromy; compare the scalar global-divisor report |
| [Entire functions at arbitrary rank](surcomplex/entire-functions-at-arbitrary-rank/) | Cofinality, factorization and extension of entire series over one fixed Hahn field |

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
| Common-domain germ ring `Rₙ` | One neighborhood represents all coefficients, with shrinking allowed |
| `ℂ[[z]]((t^Γ))` | Each coefficient is formal |

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

## Foundations and computation: three reports

| Report | Main subject |
|---|---|
| [Foundations](foundations-and-computation/foundations/) | Classes and universes, workspace localization, support recursion, topology and a formalization proposal |
| [Computer algebra](foundations-and-computation/computer-algebra/) | Exact denotation, coefficient access, equality and approximation; three distinct Wolfram prototypes |
| [Computable surreals](foundations-and-computation/computable-surreals/) | Structural names, effective left-finite Hahn names and bounded-denominator Puiseux names |

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
