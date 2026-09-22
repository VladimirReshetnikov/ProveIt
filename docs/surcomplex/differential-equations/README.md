# Differential Algebra and Differential Equations over the Surreal and Surcomplex Numbers

**The finite-primitive criterion, the phase obstruction, and support-certified
coordinate systems**

A merged research report, 92 pages. Everything in this directory other than
`article.tex` and `article.pdf` is preserved source material.

```
article.tex   the merged report, standalone LaTeX with an internal bibliography
article.pdf   the compiled 92-page report
README.md     this guide
sources/      the seven source manuscripts, unmodified, with their READMEs and audits
code/         the seven source verification programs, unmodified
data/         the seven recorded verification and build records, unmodified
```

## What the report is

Seven independently written manuscripts developed the same theory of the
Berarducci–Mantova derivation `∂` on the surreal class field `No`, normalized
by `∂ω = 1`, and of its unique extension to the surcomplex field `No[i]`.
This report is their **union**, not a selection from them.

The organizing identity is exact:

```
{ ∂y/y : y ∈ No[i]ˣ }  =  No + i·A ,      A := ∂m = ∂O
```

where `O` is the class of finite surreals and `m` its ideal of infinitesimals.
So `∂y = (a + ib)y` has a nonzero surcomplex solution exactly when `b` has a
**finite** surreal primitive. Two things about that identity carry the whole
subject:

* the two printed forms `No + i·∂m` and `No + i·∂O` agree **only through a
  proved lemma** (`∂O = ∂m`), never as notational variants; and
* `A` is a **strict** subclass of `m`. The coefficient `ω⁻¹` is infinitesimal
  while its primitive `log ω` is infinite, so `∂y = i·ω⁻¹·y` has only the zero
  solution. Collapsing `∂O` to `O` would turn the criterion into "`b`
  infinitesimal" and make that equation solvable; all seven sources refute
  exactly that.

From the criterion the report derives: the purely infinite part of the
accumulated phase as an `R`-linear surjection onto the purely infinite
surreals, a complete gauge invariant and the middle term of a four-term exact
sequence; a sharp support threshold over real-exponent Hahn fields with a
counterexample proving it does not globalize by valuation; power and
iterated-logarithm thresholds at `p > 1` at every finite depth; a decision
procedure for rational coefficients (`deg Q − deg P ≥ 2`); the pointwise
maximality of the strip `No + i·O` as the domain of any derivation-compatible
exponential, hence no global one; nonexistence of a nonzero solution of
`∂y = iy` or `∂²y + y = 0`, by three independent proofs; the complete
constant-coefficient and constant-matrix classification, in which only *real*
characteristic roots contribute; a triangular fundamental-matrix criterion with
its insufficient trace test; exact resolvents with factorially divergent Hahn
solutions and exact residual certificates; two different differentially stable
set-sized workspace constructions; and five Picard–Vessiot extensions with
differential Galois tori — at the cost, in the real form, of the `H`-field
ordering rule.

A **deliberately separate** half treats *coordinate* differential equations in
fixed-common-domain Hahn rings `O(U)((t^Γ))`: existence, uniqueness, support
certificates, variation of constants, a Liouville determinant identity,
monodromy valued in `GL_d(K_Γ)`, and a polynomially nonlinear initial-value
theorem, all on strong summability and an **ordered**-word support lemma that
Appendix A proves in full. The two halves share notation and almost nothing
else; several theorems are true for one operator and false for the other on the
same printed equation, and the report keeps their types apart rather than
flattening them.

### Three objects called "phase"

The single most important thing to carry away from the merge. The sources use
the word "phase" for three different objects, one of which is not an angle at
all. The report fixes three names and three symbols and uses them without
exception (Convention 5.1, Table 2):

| Name | Symbol | Lives in | What it is |
|---|---|---|---|
| finite angle | `θ` | `O` | the argument of `cis`; the *whole* angle of a unit, finite by theorem |
| infinitesimal phase residue | `η` | `m` | what remains after factoring out the constant ordinary unit complex number `c` |
| accumulated phase | `B` | `No` | a primitive of the imaginary coefficient; **not** an angle; obstructed exactly when its purely infinite part is nonzero |

`Obs(i) = ω` and `Obs(i/ω) = log ω` are purely infinite surreals, not arguments
of anything. "The phase of the solution is `log ω`" is meaningless; "the
accumulated phase of the coefficient `i/ω` is `log ω`, which is infinite, so
there is no solution" is the theorem.

The report also uses **no symbol `J`** (the sources use that letter for three
unrelated objects), and reserves `U` for an ordinary complex domain, writing
`T` for a transcendental differential generator.

## Where it came from

Seven source archives. Three pairs of archive filenames collided, differing
only by a trailing marker, so the mapping from archive name to manuscript is
recorded here because it is not recoverable from the filenames.

| id | original archive | file in `sources/` |
|---|---|---|
| 01 | `surcomplex_differential_equations` | `01-thresholds-and-galois-tori.tex` |
| 02 | `surcomplex_differential_equations` (second) | `02-word-lemma-and-nonlinear-ivp.tex` |
| 05 | `surreal_differential_algebra` | `05-logarithmic-derivative-image.tex` |
| 06 | `surreal_differential_algebra` (second) | `06-finite-primitive-and-oscillation.tex` |
| 07 | `surreal_differential_algebra` (third) | `07-exact-sequence-and-rational-exponents.tex` |
| 08 | `surreal_differential_equations` | `08-coherent-ivp-and-general-resolvent.tex` |
| 09 | `surreal_intrinsic_differential_calculus` | `09-bm-bridge-and-derived-smallness.tex` |

All seven are pinned to `VladimirReshetnikov/Surreal` at commit
`e260237db9b71da8b74a0c13c8e6355119091100`, and all seven independently prove
the same twelve-item spine (unique complexification, smallness, infinitesimal
exp/log, polar decomposition, normalized primitive, the rank-one criterion, the
obstruction sequence and gauge form, no oscillator, no global exponential, the
constant-coefficient classification, set-sized localization, an oscillatory
Picard–Vessiot extension). Those results are printed **once**.

### What each contributed uniquely

* **01 — thresholds and Galois tori.** The boxed exact image; the gauge
  *uniqueness* theorem and the rank-one tensor corollary; the sharp support
  threshold `min supp(b) > 1` with strictness at exponent 1 and the
  valuation-insufficiency pair `i/(ω log ω)` against `i/(ω (log ω)²)`; the
  upper-triangular criterion with its descending recursion, the Jacobi trace
  test and the `diag(i,−i)` counterexample; the diagonal phase torus with the
  saturated integer lattice and the `(i, 2i)` / `(i, √2 i)` separation; the
  formal oscillator in complex and real rational form; the non-summability of
  the exponential series at `ω`; the phase-independent no-global-exponential
  corollary; the "at most one, not none" warning; the NBG class hygiene; the
  coefficient-domain tiering contract.
* **02 — word lemma and nonlinear IVP.** The entire coordinate half: the
  common-domain ring with its explicit disowning of both the shrinking-radius
  germ ring and the full formal ring; the linear fundamental-matrix theorem
  with uniqueness among *all* Hahn-coherent matrices; the Liouville identity;
  the negative-leading-exponent proposition and the nilpotent counterexample
  bounding it; the nonlinear theorem with no common degree bound; monodromy in
  `GL_d(K_Γ)` and the residue invisible to ordinary monodromy; the two-scale
  noncommuting computation `X₁₁ = z³(NM/6 + MN/3)` refuting the naive
  exponential; `y = t/(1−tz)`, coherent on all of `C` yet poled at `z = ω`;
  the cross-category pair (`ε = ω⁻¹` permitted for `D_z`, prohibited for `∂`);
  the three-promise separation; the strong Laurent resolvent; the
  four-category table; and the from-scratch proof of the ordered-word lemma.
* **05 — logarithmic-derivative image.** The rational decision criterion and
  its raising-rather-than-reporting contract; the order-theoretic structure and
  convexity of the bounded-primitive ideal; the countable-stage differential
  Hahn hull with the monomial criterion, the real-group criterion, the `Q√2`
  counterexample, and "differentiation closure is not integration closure";
  the analytic coefficient interface with coefficientwise linear naturality and
  the total-derivative chain rule.
* **06 — finite primitive and oscillation.** The base skeleton; the strip
  theorem with *pointwise* maximality; the character-independent differential
  defect; products, duals and no finite-order obstruction; the direct-sum
  decomposition; the summary table of distinguishable situations; the
  factorially divergent forced oscillator with its closed residual and
  anti-topological disclaimer; and the theorem that oscillation cannot retain
  the `H`-field rule.
* **07 — exact sequence and rational exponents.** The explicit `C((t^Q))`
  workspace chapter with the exact derivative and logarithmic-derivative
  images, the single resonant coefficient, the resonant normal form, and the
  workspace-versus-ambient discussion; the derivative taxonomy including the
  fine order-field derivative and the `fin`/`pp` proof that a fine derivative
  does not determine an intrinsic one; the change-of-scale observation; the
  two-derivative chain rule with *derived* summability; the Rota–Baxter
  correction to integration by parts; the `ω`-series composition bridge; the
  terminating finite inverse of `∂ − i` on `C[ω]`; the union-of-fields
  anti-lemma; "return a reason, not just a failure flag".
* **08 — coherent IVP and general resolvent.** The resolvent over a general
  real-exponent `K_Γ` with its substantive hypothesis; the beyond-all-orders
  ambiguity of the factorial solution; the valuation test for finite phase; the
  negative-valued coefficient that destroys coherence, and the rescaling that
  resolves it; "the same printed equation under different derivatives"; the
  Riccati example with an entire coefficient family; the oscillatory extension
  proved Picard–Vessiot via the absence of proper differential ideals in the
  Laurent ring; the anti-Banach disclaimer; the certificate table; and the rule
  that a truncation must record the *type* of omitted information.
* **09 — BM bridge and derived smallness.** The derivation of smallness and of
  strict order reversal on the infinitesimals from the `H`-field positivity
  axiom — the provenance this report uses; the theorem that intrinsic
  differentiation preserves common-domain coherence, with the total intrinsic
  derivative and the fixed-contour and moving-pole discussion; the
  bounded-primitive ideal as a named object with its full structure theory,
  including the cut description; the resolvent support certificate and the
  whole-prefix coefficient recurrence; the `Σ ω^(n²) X^n` support
  counterexample; the derivation-aware representation interface.

### How conflicts were resolved

* **Smallness** is *derived* (from `H`-field positivity, with strict order
  reversal as a bonus), not imported. The square-root route used by two sources
  is kept as a remark. `∂m ⊆ m` is recorded as **strict**.
* **The word-counting lemma** is both cited (Neumann, Higman) and proved in
  full in Appendix A, in its **ordered**-word form, which is what noncommuting
  matrix products require.
* **The nonlinear IVP uniqueness class** is printed with the qualifier its
  proof supports and nothing wider: uniqueness among positive-support coherent
  solutions with the specified ordinary reduction, the support containment
  stated as a *conclusion*. The stronger linear statement — uniqueness among
  all Hahn-coherent matrices — is kept separately.
* **"The resolvent theorem"** named four different coefficient rings across the
  batch. It is stated once over `C((t^Γ))` for `Γ ⊆ R` with `1 ∈ Γ`, the
  hypothesis its valuation-shift proof actually needs, with an explicit note
  that the real-exponent restriction is substantive at higher rank; the sharper
  rational-exponent images are kept as the separate statements they are; and
  the sharp threshold theorem is kept separately restricted to real-exponent
  coefficients, with its counterexample, and is **not** merged into the
  resolvent.

## What is NOT claimed

Section 28 of the report is the consolidated register: 52 numbered items
covering the 118 explicit non-claims that the seven manuscripts state between
them. It is part of the result. In outline:

* **Provenance.** The Berarducci–Mantova derivation is imported, not
  constructed and not reproved; no uniqueness of it is claimed and no other
  surreal derivation is classified; every intrinsic statement is relative to
  this one `∂` with `∂ω = 1` and none is derivation-agnostic. The Neumann
  support lemma, Gonshor's normal forms, the `ω`-series composition and
  incompatibility results, and the universal `H`-field results are separately
  imported with their hypotheses intact, and none is strengthened. One source
  records that the Neumann paper was not retrieved in full, which is why
  Appendix A proves the lemma.
* **Novelty and verification.** No priority claim, no solution of a named
  published open problem, no independent refereeing, no proof-assistant
  verification, no Lean source. The literature search was targeted. The seven
  repository audits were targeted, revision-specific and read-only; none
  asserts that any keyword is absent from the repository, and empty or
  truncated search responses were not used as evidence of absence. The
  repository's existing phase decomposition and chosen-exponential obstruction
  are prior coverage, acknowledged as such.
* **Effectivity.** The normalized primitive, the obstruction map and the
  workflow are exact *semantic* operations, not algorithms. A well-ordered
  support is a semantic certificate, not an effective presentation. Only the
  first three of the four result outcomes are decidable, and only for the
  finite exact core; the rational classifier is restricted to `Q(X)` and
  *raises* on unsupported input rather than reporting nonexistence.
* **Scalar scope.** Scalar homogeneous first-order equations only. No
  differential closedness, no general inhomogeneous existence theorem (outside
  the admissible locus the claim is *uniqueness* only), no classification of
  nontriangular matrix systems, no higher-rank differential modules, and the
  constant-coefficient results concern ordinary complex constant coefficients
  only. All nonexistence results are about surcomplex *number* solutions under
  `∂`; they do not deny ordinary oscillatory functions or algebraically defined
  global surcomplex phases, and the Ehrlich–Kaplan constructions should not be
  described as nonexistent.
* **Workspace scope.** Neither localization gives closure under all summable
  families; no Hahn completeness, no birthday bound, no enumeration, no
  termination claim. The hull's minimality holds only among full Hahn fields
  indexed by divisible exponent groups. The support threshold provably does not
  globalize by valuation.
* **Coordinate scope.** Positive support is sufficient, not necessary (the
  nilpotent example). The nonlinear theorem needs a *supplied* ordinary
  background solution on a simply connected `U`, does not continue it past its
  singularities, and does not cover negative-valued perturbations. Monodromy is
  an ordinary-domain construction; monodromy for the nonlinear problem on
  non-simply-connected domains remains future work. No Stokes theory, no
  irregular-singularity classification, no Riemann–Hilbert correspondence.
* **The checks.** The seven suites check finite exact symbolic identities and
  finite jets: 1,395 + 115 + 149 + 258 + 291 + 150 + 259 recorded passing
  checks, all under Python 3.13.5 (six of them with SymPy 1.14.0). They do not
  construct the surreal numbers, do not verify Hahn summability, class-size
  arguments, Higman's lemma, transfinite recursion, or any general nonexistence
  theorem. Declared cutoffs are part of the claim, including a matrix cutoff by
  *total degree* 6 that is explicitly **not** a valuation cutoff. Appendix D
  reproduces each record.

## Relation to the neighbouring reports

* **`docs/surcomplex/trigonometry/`** supplies the finite-angle phase group and
  explicitly declines to choose a derivation. This report reproves the part it
  needs and adds the derivative identity `∂ cis θ = i(∂θ) cis θ`; it states
  precisely what its no-go theorems do and do not say about that report's
  global phase extensions. Those constructions need not be renamed as false;
  their contracts need only be distinguished from the intrinsic differential
  one. **Cross-link both ways.**
* **`docs/surcomplex/analysis/`** already proves a derivation obstruction for
  *one chosen* canonical global surcomplex exponential. **That is prior
  coverage.** This report's Corollary 11.4 — there is no map
  `Ψ : No[i] → No[i]ˣ` with `∂Ψ(z) = Ψ(z)∂z` for every `z`, with no
  homomorphism, continuity, analyticity or normalization hypothesis —
  **strengthens that theorem in phase-independence and does not contradict
  it.** The two are compatible. The coordinate half also reuses that report's
  common-domain coherent-section language and refines its
  germ/common-domain/formal distinction into an explicit table with named
  witnesses.
* **`docs/foundations-and-computation/computer-algebra/`** poses the capability
  taxonomy and the subsection "Differential equations must name their
  category"; **`.../foundations/`** poses the four-interface discipline. The
  operator table, the result contracts, the certificate table and the tiering
  contract in this report answer both directly, and the separation chapter
  sharpens the derivative distinctions. **Cross-link both ways.**

## Build

`article.tex` is standalone: internal bibliography, no external `.bib`, no
graphics, no font files, no shell escape, no network access.

```sh
latexmk -pdf -interaction=nonstopmode article.tex
```

If `latexmk` is unavailable, run `pdflatex -interaction=nonstopmode` three
times so that the table of contents, the cross-references and the `cleveref`
labels settle. The delivered build has zero LaTeX errors, zero warnings, zero
undefined references or citations, zero multiply-defined labels, zero duplicate
destinations, and zero overfull or underfull boxes.

## Re-running the source verifiers

The programs in `code/` are the originals. **Run them on a copy.** Several
write their evidence files beside themselves, so a byte-identity check
performed *after* a run compares two equally modified copies and tells you
nothing. Their recorded outputs are already in `data/`, and Appendix D of the
report reproduces them. Nothing in `sources/`, `code/` or `data/` was modified
to produce this report.
