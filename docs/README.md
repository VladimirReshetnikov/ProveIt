# The surreal and surcomplex reports

This collection has **63 research reports in five families**. Start with the
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

Batches 24–29 (placed in `be06fc8`, `cf350b1`, `f4c9504`, `a4dcb91`,
`c6359e4` and `66d7e55`, each followed by its write commits) add nine reports
and extend three earlier ones; most of the new reports also grew by later
additions within the period. Five of the new reports concern Conway's omnific
integers `Oz`:

- [Omnific Diophantine geometry](surreal/omnific-diophantine-geometry/),
  from thirteen manuscripts: constant-term transfer, Pell and norm-form
  rigidity, single quartic equations defining `ℤ` in `Oz`, a Diophantine
  constant term, fractions, and only constant points on smooth affine curves
  other than the affine line, on abelian varieties and on suitable
  logarithmic complements.
- [Set-sized quotients](surreal/set-sized-quotients-of-omnific-integers/),
  from eighteen: every ring map from `Oz` to a set-sized ring factors through
  the constant term; exact cardinal thresholds, homological dimensions, and
  the proper-class Boolean branching of the integral closure.
- [Omnific-preserving automorphisms](surreal/omnific-preserving-automorphisms/)
  (five manuscripts), [omnific groups and lattices](surreal/omnific-groups-and-lattices/)
  (four) and [discrete initial subgroups](surreal/discrete-initial-subgroups-and-omnific-normalization/)
  (two), the last with a proposed affirmative answer to a question of Ehrlich
  and Kaplan.

The others are [definable surreals and omnific integers](foundations-and-computation/definable-surreals-and-omnific-integers/),
[omnific notations](foundations-and-computation/omnific-notations/),
[Hahn–Hilbert geometry](surcomplex/hahn-hilbert-geometry/) and a second
physics report, [quantum and gauge scale reductions](physics/quantum-and-gauge-scale-reductions/).
[Holonomic rigidity](surcomplex/holonomic-rigidity-for-entire-hahn-functions/)
gains theta descent, which makes the order-unit boundary of differential
rigidity exact (Theorem H); [entire functions](surcomplex/entire-functions-at-arbitrary-rank/)
gains rectification by entire automorphisms; and
[Euclidean three-space](surreal/euclidean-three-space/) gains Part V on
compact groups over `No`.

Proof review of this material is recorded in the [review record](REVIEW.md).
The Diophantine report's review covers its original material and Sections
11–15 and 19, plus the Gaussian-fiber and étale-norm additions in Section 6.
Those proofs now include support arguments and boundary examples. Source
07's quartic and the elementary ring/Euler subsections 16.2–16.3 are also
reviewed, with the trivial-exponent-group exception and the meaning of
image inclusions made explicit. Later passes cover the rest of Section 16
and Sections 17.1–17.4: differential rigidity, smooth curves, exact arithmetic
fibers, separated-model descent and projective coordinate ideals. The review now
also covers Section 17.5 and the singular-curve criterion through Section 17.6.5:
conductor certificates, the discrete boundary place and structural consequences.
Later passes review the repeated-root applications and groups and coefficient
algebras and logarithmic applications through Section 18.6. Remaining curve
pointers and neighbouring-report comparisons still await review; Section 20
and Sections 21.1–21.6 now have a scope check, with the exact boundary in its
[reconciliation](surreal/omnific-diophantine-geometry/RECONCILIATION.md); its
remaining geometric arguments and the other new reports and additions await
review. Lean covers the omnific ring and constant-term package, degree
laws, units and finite elements, the exact omnific floor and ordinary
polynomial-root rigidity of the Diophantine report. Its other unmapped
Diophantine results remain pending.

Placement `21375f8` (batch 30) adds two report bases,
[critical-point defects](foundations-and-computation/large-cardinal-embeddings-and-normal-forms/)
and [dilation rigidity](surcomplex/autonomous-dilation-relations/), and
companions to the holonomic, nonabelian-support and omnific-preserving
reports. The first four writes through `1ab41af` integrate those companions
and the dilation report; `de45cee` completes the three-manuscript
critical-point-defects assembly. Its initial 76 standard results were indexed;
independent proof review and Lean formalization remain pending.
That automorphism assembly had nine manuscripts and states automatic
strongness for `Oz` automorphisms; these new claims await proof review.

Placement `9d28e28` adds [independent surreal copies](surreal/independent-surreal-copies/),
a proposed construction of copies sharing a prescribed set-sized Hahn core,
written as a single-source report in `781b19e`. Its eight companions are now
integrated, including theta hierarchies (`1d3f503`) and polynomial
composition (`8bc7994`). The nine manuscripts
placed in `7d04483` are also written through `c315ac9`, expanding eight
existing reports. They add Galois rank, arithmetic sampling, finite symmetry
descent, support-bounded fields, cyclic ramification, measurable first
failures, Chevalley groups and arbitrary-rank coefficient recovery.
Their new proofs remain outside the independent review scopes recorded here.

Placement `aa9c891` retires the next nine archives and adds two main texts:
[omnific continued fractions](surreal/omnific-continued-fractions/) and
[exponential relations over omnific integers](foundations-and-computation/exponential-relations-over-omnific-integers/).
Their 60 standard results are indexed and PDFs supplied; their collection
editions are written in `68db1b5` and `fa54502`. The two dilation companions
are integrated in `1ef6bba`, adding 33 standard results on support rank and
algebraic independence of dilation orbits. The coefficient-observables and
Noetherian-compression companion is now integrated in `76dd876`, adding 11
standard results to the 222-result holonomic report. The discriminant and
étale-unit companion is integrated in `fdedce0`, adding 27 standard results
in Section 19.4 of the Diophantine report. The final three batch-33 companions
are integrated in `19d0b0e`, adding 89 standard results to the 274-result
omnific-automorphism report: formal orbit fields, left-orderable symmetry
groups and formal integration of derivations. All 185 earlier standard
statements in that report are unchanged. Independent proof review remains pending;
assembly alone does not extend any Lean mapping.
A further universal-symmetries and difference-equations archive arrived in
`bbe23a3`, and eight more archives arrived in `a4611ad`. All nine are now
placed in `a7a435f` as additions to six reports, with audits and verification
code supplied. Seven companions are now integrated through `97ff204`: rotation-equivariant
dynamics, Gaussian omnific real forms, beyond-composita obstructions,
infinite simultaneous unitary straightening, universal symmetries and
difference equations, class residue fields, and semialgebraic preservers.
Their 152 new standard results bring the index to 4,550 across 63 reports.
The other two companions await main-text integration; independent review
of all these new claims remains pending.
The Hahn-joins archive from `267b910` is placed in `dec8d56` as a further
companion to independent surreal copies. Its main-text integration and
independent proof review remain pending.
The singular-curve addition
gives a normalization criterion beyond the smooth case; its proof, structural
consequences, repeated-root test and arithmetic applications now have a
manuscript review. The review also covers the closing singular-curve scope
notes and Sections 18.1–18.6 on groups, coefficient algebras, boundary
examples and logarithmic applications. The workspace and question-status
review covers Sections 20–21.6. A subsequent pass checks geometric
pointers and the cited statement scopes in Section 21.7, correcting the
real arithmetic boundary and stale group-report comparison. The independent-copies report and its
class-foundation assumptions remain pending proof review and Lean formalization.

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

## Surreal numbers: twenty-three reports

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
| [Euclidean three-space](surreal/euclidean-three-space/) | Coordinate and spherical geometry of `No³` with finite angles, and the rotation group `SO(3,No)` as a split extension with a perfect infinitesimal kernel; normal subgroups by valuation cuts and the universal set-sized quotient of `SO(3,No)`; Part V: compact groups over `No`, whose universal set-sized quotient exists exactly in the semisimple case |
| [Finite surreal probability](surreal/finite-surreal-probability/) | Surreal-valued probability on finite algebras: conditioning on infinitesimal events, log-odds, entropy, scoring rules; compare the measures report for countable additivity |
| [Omnific Diophantine geometry](surreal/omnific-diophantine-geometry/) | Diophantine equations over the omnific integers `Oz`: constant-term transfer, Pell and norm-form rigidity, quartic definitions of `ℤ`, a Diophantine constant term, fractions, and rigidity of smooth curves, abelian varieties and logarithmic complements; fifteen integrated manuscripts; Section 19.4 reviewed through the root-velocity translation proof and omnific-root corollaries; later étale and matrix proofs await review; exact scope in its reconciliation |
| [Set-sized quotients of omnific integers](surreal/set-sized-quotients-of-omnific-integers/) | Every ring map from `Oz` to a set-sized ring factors through the constant term; exact cardinal thresholds, homological dimensions, integer-valued polynomials, and the proper-class Boolean branching of the integral closure; twenty-two manuscripts |
| [Omnific-preserving automorphisms](surreal/omnific-preserving-automorphisms/) | Which strong automorphisms of a Hahn field preserve its omnific integers: the convex-support criterion, stabilizers, nondefinable monomials, and polynomial coefficient rigidity; fifteen integrated manuscripts; later parts claim automatic strongness, coefficient recovery, formal orbit fields, left-orderable symmetry groups and integration of derivations, pending independent review |
| [Omnific groups and lattices](surreal/omnific-groups-and-lattices/) | Algebraic groups with no new omnific points; `SL_n(ℤ)` as the universal set-sized quotient of `E_n(Oz)` for `n ≥ 3`, but none in rank two; shortest vectors and missing infima in omnific lattices; five manuscripts |
| [Omnific continued fractions](surreal/omnific-continued-fractions/) | Exact digit fibers as translates of a valuation ideal, full Hahn realizations and periodic algebraic fibers; ordinary finite indices only; proof review pending |
| [Discrete initial subgroups and omnific normalization](surreal/discrete-initial-subgroups-and-omnific-normalization/) | A proposed affirmative answer to Ehrlich–Kaplan's question (JSL Question 9.1): every discrete initial subgroup of `No` is isomorphic to an initial subgroup of `Oz`; convex subquotients of initial groups are initially realizable; two manuscripts |
| [Independent surreal copies](surreal/independent-surreal-copies/) | Prescribed common Hahn cores, surreal self-embeddings and transcendence gaps; class assumptions and proof review pending |

The two birthday reports have different domains. The first allows its specified
ordinal supports but excludes positive powers of `ω`; the Laurent report allows
those powers but uses the integer exponent lattice. Their common part includes
`ℝ[[ω⁻¹]]`. Neither domain theorem subsumes the other. Here `⊗` denotes
**natural ordinal multiplication**, as distinguished in the notation guide.

## Surcomplex numbers: twenty-eight reports

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
| [Entire functions at arbitrary rank](surcomplex/entire-functions-at-arbitrary-rank/) | Cofinality, factorization, the exact jet image, ideals above canonical products and scalar extension of entire series over one fixed Hahn field; in several variables only the scalar-extension clause is answered; prime ideals above one-simple-node products and their splitting under cofinal extension; with countable cofinality, radially finite sets in `K^d` are line-rectifiable by entire automorphisms iff `Γ` has an order unit, and fat-point ideals on rectifiable configurations |
| [Holonomic rigidity](surcomplex/holonomic-rigidity-for-entire-hahn-functions/) | Entire D-finite series are polynomials. Without an order unit, nonpolynomial entire series are differentially transcendental in all orders; with one, a theta series has minimal differential order three. Later chapters exclude order two for every value group, exclude order three through total jet degree three, and classify existence of mixed linear differential–dilation equations by relative valuation scales, assuming no quotient of distinct multipliers is a root of unity. These later chapters await independent proof review |
| [Hahn–Tate uniformization](surcomplex/hahn-tate-uniformization/) | Tate elliptic curves at arbitrary rank: exact Hahn domain `U_q` and `U_q/q^ℤ ≅ E_q(K)`, plus multiscale theta series; the bounded-period quotient itself has a Molcho–Wise precedent |
| [Infinite-dimensional Hahn spectral theory](surcomplex/infinite-dimensional-hahn-spectral-theory/) | Two inequivalent spectra: ordinary normal operators extended to `H((t^Γ))`, and exact diagonalization of row- and column-finite Hahn matrices; Section 3 reconciles their apparently conflicting accumulation statements; Parts III and IV add Drazin halos for any unital algebra and noncommuting compact perturbations |
| [Expanding polynomial dynamics](surcomplex/expanding-polynomial-dynamics/) | Exact itinerary fibers of expanding polynomials over Hahn fields, and the order-unit dichotomy; valuation-expanding is not repelling, and no Julia/Fatou theory is built |
| [Hahn–Herglotz positivity](surcomplex/hahn-herglotz-positivity/) | Matrix Herglotz normalization on halos, a null-ideal positivity criterion, and Toeplitz-positive Fourier moments with no positive measure; it assumes coefficientwise additivity, with strong additivity optional |
| [Prony reconstruction](surcomplex/prony-reconstruction-at-surreal-scales/) | Sharp valuation threshold for recovering `n` weighted nodes from `2n` power moments (no measures); compare polynomial algebra's coefficient threshold |
| [Wick summability certificates](surcomplex/wick-summability-certificates/) | Finite strict valuation inequalities decide strong summability of polynomial Wick diagram families over `ℂ((t^Γ))`, `Γ` divisible; diagramwise only, and a Hahn value is not an integral |
| [Three duals of Hahn vector spaces](surcomplex/three-duals-of-hahn-vector-spaces/) | Algebraic extension, completion and strong closure of `V((t^Γ))`; strong operators; comparison of represented, strong and continuous duals of a Hahn–Hilbert space |
| [Hidden negative Hermitian directions](surcomplex/hidden-negative-hermitian-directions/) | Hermitian forms positive over the finite-lattice-supported subfield yet indefinite over `ℂ((t^Γ))`; a two-scale matrix null-ideal criterion |
| [Hahn–Hilbert geometry](surcomplex/hahn-hilbert-geometry/) | Orthogonally split subspaces of `H((t^Γ))` are infinitesimal unitary rotations of ordinary ones; amplified graphs without nearest points, a projection poset that is a lattice only in finite dimension, metric rigidity, Fredholm least squares |
| [Surcomplex field automorphisms](surcomplex/surcomplex-field-automorphisms/) | Plain, valued, value-fixing and 1-automorphisms of `No(i)`; the real-axis stabilizer `Aut(No)×C₂` and phase twists that move `No`; exponential results are the rigidity report's |
| [First-κ coefficients](surcomplex/first-kappa-coefficients/) | Hahn series with fewer than `κ` terms: omitted types classified by the first `κ` coefficients, completion iff `cf(Γ) ≠ cf(κ)`, never spherically complete |
| [Single-dilation Hahn support](surcomplex/single-dilation-hahn-support/) | One monomial dilation defines coefficients, monomials and the valuation ring; its centralizer among all field automorphisms; undecidability |
| [Gamma and zeta](surcomplex/gamma-and-zeta-functions/) | Finite lifts and RH, strongly summable Dirichlet series at infinity, Stirling and Hurwitz, Gamma and zeta on the horizontal tube for any phase, reflection obstructions at infinite height; six manuscripts reconciled |
| [Dilation rigidity](surcomplex/autonomous-dilation-relations/) | Autonomous relations between exponent dilates; three manuscripts, including support-rank bounds and exact finite-support order; proof review pending |

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

## Physics: two reports

[Surreal scalars and spacetime](physics/surreal-scalars-and-spacetime/)
separates exact symbolic identities, conditional mathematics, physical
assessments and imported results. Replacing scalars can encode asymptotic
scales without regularizing a singular metric. For example, with nonzero
Schwarzschild mass `m`, the substitution `r = s^q w(s)`, with integer `q ≥ 1`,
`w ∈ ℝ[[s]]` and `w(0) ≠ 0`,
in `48m²/r⁶` gives a pole of order `6q` and leading coefficient
`48m² w(0)^(−6)`. The recorded special case `w(s) = 1+s` preserves `48m²`;
general substitutions need the factor `w(0)^(−6)`.

[Quantum and gauge scale reductions](physics/quantum-and-gauge-scale-reductions/),
merged from four manuscripts, applies the same claim-tier firewall to finite
quantum operations and gauge models: leading-Gram shadows of rare branches, a
sharp postselection cost, exact elimination of separated virtual sectors,
soft-mode Schur defects, optimal identification of an infinitesimal holonomy,
and Hahn deformations of gauge fields. It claims no departure from ordinary
quantum theory and no measurable infinitesimal.

## Foundations and computation: nine reports

| Report | Main subject |
|---|---|
| [Foundations](foundations-and-computation/foundations/) | Classes and universes, workspace localization, support recursion, topology and a formalization proposal |
| [Computer algebra](foundations-and-computation/computer-algebra/) | Exact denotation, coefficient access, equality and approximation; three distinct Wolfram prototypes |
| [Computable surreals](foundations-and-computation/computable-surreals/) | Structural names, effective left-finite Hahn names and bounded-denominator Puiseux names |
| [Surreal fields across universes](foundations-and-computation/surreal-fields-across-universes/) | External saturation of an inner model's `No^M` in a same-ordinal outer universe: new ordinal sequences, fresh-sign gaps, first new birthday, nonconjugate surcomplex real forms |
| [Definable surreals and omnific integers](foundations-and-computation/definable-surreals-and-omnific-integers/) | The definable surreals form a real closed subfield, elementary in `No` and closed under `exp`, `log` and the omnific floor; `No ∩ HOD = No^HOD`, and `V = HOD` iff every omnific integer in `(0, ω)` is ordinal definable; the maximal initial core |
| [Omnific notations](foundations-and-computation/omnific-notations/) | Holonomic towers, hereditary forms and rational `ω`-terms with decidable equality and floor; raw `d`-block equality is `Π⁰₁`-complete and support validity `Π¹₁`-complete |
| [Birthday cutoffs and hereditary sets](foundations-and-computation/birthday-cutoffs-and-hereditary-sets/) | Surreals born below an epsilon number, with birthday, interpret `H_κ`: bi-interpretation, elementary inclusions, axiom spectra, outer models, orientation |
| [Critical-point defects](foundations-and-computation/large-cardinal-embeddings-and-normal-forms/) | Four manuscripts on the claimed exact support threshold for two transports, defect coefficients, and descent to the target model; proof review pending |
| [Exponential relations over omnific integers](foundations-and-computation/exponential-relations-over-omnific-integers/) | Toric relations and a decidable additive language with algebraic exponential predicates; elementary cores and computability boundaries; proof review pending |

A mathematical closure theorem need not supply a uniform algorithm on the
chosen names. In particular, numerical coefficient access does not supply a
decidable exact support or a leading exponent. The computability report states
which operations need that additional information. The computer-algebra
report separately records each prototype's coefficient field, exponent
lattice, supported operations and known implementation defects.

## Files, provenance and building

Each report has a LaTeX source, a typeset PDF and a local README. Most
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
