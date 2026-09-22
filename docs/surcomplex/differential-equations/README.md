# Differential Algebra and Differential Equations over the Surreal and Surcomplex Numbers

**The finite-primitive criterion, the phase obstruction, and support-certified
coordinate systems**

A merged research report, 121 pages. Everything in this directory other than
`article.tex` and `article.pdf` is preserved source material.

```
article.tex   the merged report, standalone LaTeX with an internal bibliography
article.pdf   the compiled 121-page report
README.md     this guide
sources/      the eight source manuscripts, unmodified, with their READMEs and audits
code/         the eight source verification programs, unmodified
data/         the eight recorded verification and build records, unmodified
```

## What the report is

Eight independently written manuscripts developed the same theory of the
Berarducci–Mantova derivation `∂` on the surreal class field `No`, normalized
by `∂ω = 1`, and of its unique extension to the surcomplex field `No[i]`.
This report is their **union**, not a selection from them. Seven of them share
a twelve-item spine of scalar and workspace theory; the eighth joined later and
carries the finite **matrix** stratum — Part III.

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
  infinitesimal" and make that equation solvable; all eight sources refute
  exactly that, and Proposition 16.9 shows the strictness is *sharp*: `A` is
  exactly the class of scalar perturbations that preserve every phase.

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

### The matrix stratum (Part III)

Every `∂y = Ay` with `A` an ordinary finite matrix over `No[i]` is gauge
equivalent to `i·diag(∂P₁, …, ∂Pₙ)` with each `Pⱼ` purely infinite, and the
**multiset** `Ph(A) = {Pⱼ}` is a complete invariant of differential
equivalence (Theorem 15.9). The trace test of Proposition 14.2 sees only its
**sum**, which is exactly why it is insufficient.

For a Hermitian `H` the multiset is computed from ordinary algebra
(Theorem 16.5):

```
Ph(iH) = { Obs(λ₁(H)), …, Obs(λₙ(H)) }
```

— integrate the algebraic eigenvalues, keep the purely infinite parts of the
primitives. **No commutation and no spectral gap is assumed.** The proof does
*not* claim that diagonalization commutes with differentiation: the connection
term `W*∂W` is still there, but a unitary gauge is entrywise finite, so that
term lands in `Mat(A + iA)`, which is precisely the kernel `Obs` annihilates.

Consequences: gap-free finite-primitive perturbation invariance; the exact
kernel count `dim_C ker = #{ j : λⱼ(H) ∈ A }`; existence for *every* forcing;
normalized non-Abelian integration (`∂W = AW` has a unique unitary solution
with `st(W) = I` when `A* = −A` and every entry has a finite primitive); the
complete cone of positive invariant metrics; the real rotation-block descent;
a positive Ermakov–Pinney existence/uniqueness dichotomy; an exact Hahn
expansion for the oscillatory Airy equation; polynomial and rational first
integrals from phase resonance; and the phase-lattice Picard–Vessiot torus of
an arbitrary finite system, which is the diagonal Theorem 21.12 applied through
the normal form rather than new Galois theory.

**Two things are deliberately not claimed.** The non-Hermitian case is *not*
classified, and Example 16.10 is the counterexample that marks the line: a
nonnormal `A` with instantaneous eigenvalues `±i` whose system nevertheless
has a fundamental matrix already in the base field, so that integrating
imaginary parts of eigenvalues would predict `{ω, −ω}` instead of the correct
`{0, 0}`. And Part III rests on a **new imported input** — the splitting of
monic scalar operators into first-order factors and the surjectivity of
nonzero scalar operators, transferred from the transseries field — which the
first seven manuscripts never use. Every inhomogeneous existence statement in
Part III comes from that import and not from the rank-one criterion; the
register of non-claims says so at items N22, N24 and N53.

A **deliberately separate** half treats *coordinate* differential equations in
fixed-common-domain Hahn rings `O(U)((t^Γ))`: existence, uniqueness, support
certificates, variation of constants, a Liouville determinant identity,
monodromy valued in `GL_d(K_Γ)`, and a polynomially nonlinear initial-value
theorem, all on strong summability and an **ordered**-word support lemma that
Appendix A proves in full. The two halves share notation and almost nothing
else; several theorems are true for one operator and false for the other on the
same printed equation, and the report keeps their types apart rather than
flattening them.

### The objects called "phase"

The single most important thing to carry away from the merge. The sources use
the word "phase" for several different objects, one of which is not an angle at
all. The report fixes one name and one symbol per object and uses them without
exception (Convention 5.1, Table 2):

| Name | Symbol | Lives in | What it is |
|---|---|---|---|
| finite angle | `θ` | `O` | the argument of `cis`; the *whole* angle of a unit, finite by theorem |
| infinitesimal phase residue | `η` | `m` | what remains after factoring out the constant ordinary unit complex number `c` |
| accumulated phase | `B` | `No` | a primitive of the imaginary coefficient; **not** an angle; obstructed exactly when its purely infinite part is nonzero |
| differential phase spectrum | `Ph(A)` | multisets in `P` | the `n` accumulated obstructions of a finite matrix system, as a multiset; the complete gauge invariant |

`Obs(i) = ω` and `Obs(i/ω) = log ω` are purely infinite surreals, not arguments
of anything. "The phase of the solution is `log ω`" is meaningless; "the
accumulated phase of the coefficient `i/ω` is `log ω`, which is infinite, so
there is no solution" is the theorem.

The eighth manuscript writes `Ψ` for the map `b ↦ pp(B)` with `∂B = b`. That is
**exactly** the report's `Obs`, so no fourth symbol was introduced; what is new
is the multiset. (Adopting `Ψ` would have collided anyway: the letter already
appears once here, in Corollary 11.4, as a placeholder for a putative
derivation-compatible exponential that is proved not to exist.) The word **"spectrum"** is itself a hazard: `Ph(A)` is a
multiset of purely infinite *surreals* — not the algebraic eigenvalue list that
`docs/surcomplex/spectral-theory/` calls a spectrum, not a set of angles
(`cis` is defined on `O` only, and a nonzero member of `P` is infinite), and
not a prime spectrum of a ring. Warning 5.2 states all three separations.

The report also uses **no symbol `J`** (the sources use that letter for three
unrelated objects, and the eighth uses it for the rotation generator, written
`R` here), and reserves `U` for an ordinary complex domain, writing `T` for a
transcendental differential generator and `W` for a unitary matrix. Convention
15.5 fixes the rest of Part III's alphabet: `H` Hermitian, `G` a gauge matrix,
`M` a horizontal metric, `Π` the additive phase lattice in `P` (because `Λ` is
already the integer relation lattice).

## Where it came from

Eight source archives. Among the first seven, three pairs of archive filenames
collided, differing only by a trailing marker, so the mapping from archive name
to manuscript is recorded here because it is not recoverable from the
filenames.

| id | original archive | file in `sources/` |
|---|---|---|
| 01 | `surcomplex_differential_equations` | `01-thresholds-and-galois-tori.tex` |
| 02 | `surcomplex_differential_equations` (second) | `02-word-lemma-and-nonlinear-ivp.tex` |
| 05 | `surreal_differential_algebra` | `05-logarithmic-derivative-image.tex` |
| 06 | `surreal_differential_algebra` (second) | `06-finite-primitive-and-oscillation.tex` |
| 07 | `surreal_differential_algebra` (third) | `07-exact-sequence-and-rational-exponents.tex` |
| 08 | `surreal_differential_equations` | `08-coherent-ivp-and-general-resolvent.tex` |
| 09 | `surreal_intrinsic_differential_calculus` | `09-bm-bridge-and-derived-smallness.tex` |
| 10 | `surcomplex_phase_spectrum` | `10-hermitian-phase-spectral-integral.tex` |

Members 01–09 are pinned to `VladimirReshetnikov/Surreal` at commit
`e260237db9b71da8b74a0c13c8e6355119091100`; member 10 joined later and is
pinned to the later revision
`aa846271b4dcae2c055b216126a87210292ec19b`. The first seven share a
twelve-item
spine: unique complexification, smallness, infinitesimal exp/log, polar
decomposition, the normalized primitive, the rank-one criterion, the
obstruction sequence and gauge form, no oscillator, no global exponential, the
constant-coefficient classification, set-sized localization, an oscillatory
Picard–Vessiot extension.

All seven prove the first six and the eighth and ninth. The rest are proved by
most but not all: the gauge normal form is absent from three members and the
exact sequence from a fourth; the constant-coefficient classification is absent
from one, which explicitly declines it, and its matrix corollary from two
others; and at least five prove each of the last two. Whatever is shared is
printed **once**, and nothing in the article rests on a member that does not
prove what it is cited for — the provenance appendix records this member by
member.

Member 10 is different in kind. It does not reprove the spine; it cites it,
names the gap this report's own scope ledger had recorded — no classification
of arbitrary nontriangular matrix systems — and closes the Hermitian half of
it. Where it reproves something already here (the convexity and strictness of
`A`, the exact logarithmic-derivative image, the saturation of the relation
lattice), the report records the agreement and cites, rather than printing the
statement twice.

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
* **10 — Hermitian phase spectral integral.** The whole of Part III: matrix
  gauge equivalence and the complete phase normal form, with the differential
  phase spectrum as its complete invariant; the imported splitting and
  first-order surjectivity input with its transfer; existence for every forcing
  and the exact kernel dimension; the canonical phase projectors and the
  refined trace identity `Φ(tr A) = Σ m_P · P`; the complete horizontal metric
  cone with its anti-Lyapunov example (a positive invariant metric of scale
  `e^(−2ω)` for printed coefficients whose ordinary solutions grow) and the
  unitary normal form; the attained min–max, the entrywise Weyl bound and the
  bounded-gauge estimate; the spectral–integral theorem with gap-free
  perturbation invariance and its sharpness; the two deliberate boundary
  counterexamples (the nonnormal `±i` system, and `0 ↦ ω⁻¹` moving the phase
  from `0` to `log ω`) and the coupled unitary example with phases `ω²/2` and
  `log ω`; normalized non-Abelian integration with its cocycle law
  `A ⋆ B = A + W_A B W_A*` and the exact noncommuting Hahn recurrence; the real
  rotation-block descent and the real metric cone with its parity; the positive
  Ermakov–Pinney dichotomy and the canonical amplitude–phase reduction; the
  exact Airy Hahn expansion with Wronskian `−2i`, amplitude jet and truncation
  residual; the resonance algebra with Dickson finiteness and the singular
  three-phase invariant algebra `C[U,V,W]/(UW − V²)`; the phase lattice as a
  Galois torus with its group algebra and real form; and the set-sized
  witness-closed reading of the proper-class arguments.
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
* **Where member 10 strengthened a hedge**, the hedge was amended rather than
  removed and the new hypothesis was named. Item N22 now records that
  first-order inhomogeneous existence holds, but only through the imported
  splitting/surjectivity theorem and not through the rank-one criterion — the
  "at most one, not none" witnesses are untouched, and what changed is that
  their uniqueness is now known to be accompanied by existence. Item N24 now
  records the Hermitian case settled and the non-Hermitian case open, keeping
  the counterexample that marks the line. Nothing is strengthened beyond what a
  source proves.

## What is NOT claimed

Section 31 of the report is the consolidated register: 64 numbered items
covering the 130 explicit non-claims that the eight manuscripts state between
them (118 from the first seven, 12 from the eighth). It is part of the result.
In outline:

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
* **Scalar scope.** Part II is scalar homogeneous first-order equations only.
  No differential closedness; no general inhomogeneous existence theorem there
  (outside the admissible locus its claim is *uniqueness* only); no higher-rank
  differential modules; and the constant-coefficient results concern ordinary
  complex constant coefficients only. All nonexistence results are about surcomplex *number* solutions under
  `∂`; they do not deny ordinary oscillatory functions or algebraically defined
  global surcomplex phases, and the Ehrlich–Kaplan constructions should not be
  described as nonexistent.
* **Matrix scope.** Part III settles the Hermitian case and *not* the
  non-Hermitian one, and Example 16.10 refutes the obvious candidate
  extension. Its inhomogeneous existence rests entirely on an **imported**
  splitting/surjectivity theorem, which is not a consequence of the scalar
  criterion and is flagged at every use. Still open: which nontriangular
  differential modules admit a filtration whose rank-one factors carry
  *computable* obstructions — that needs genuine module-theoretic information,
  not the eigenvalues of an instantaneous coefficient matrix — and higher-rank
  differential modules. `Obs` and the normalizing gauges are exact *semantic*
  operations, not algorithms; certified effective computation on
  support-certified input languages is posed as an open problem, not solved.
  The spectral theorem does **not** remove the connection term `W*∂W`; that
  term is present and merely invisible in the quotient by `A`. The metric
  theorems make no Lyapunov or uniform-equivalence claim. Member 10's novelty
  assessment is provisional, narrowed to three statements, and based on a
  targeted search; no named published open problem is claimed solved, and in
  particular no new solution of the Boshernitzan conjecture. All of Part III is
  relative to the one fixed `∂` with `∂ω = 1` and to no other derivation.
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
* **The checks.** The eight suites check finite exact symbolic identities and
  finite jets: 1,395 + 115 + 149 + 258 + 291 + 150 + 259 + 62 recorded passing
  checks. The first seven ran under Python 3.13.5 (six of them with SymPy
  1.14.0); the eighth records SymPy 1.14.0 and a status of PASS but no Python
  version. They do not construct the surreal numbers, do not verify Hahn
  summability, class-size arguments, Higman's lemma, transfinite recursion, or
  any general nonexistence theorem; the eighth adds that it verifies none of
  the arbitrary-support Hahn arguments, none of the published model-theoretic
  inputs, and no existence of a gauge for an arbitrary surreal matrix. Declared
  cutoffs are part of the claim, including a matrix cutoff by *total degree* 6
  that is explicitly **not** a valuation cutoff. The eighth suite's deliberate
  counterexamples are asserted **as** counterexamples, so a run that passed
  while those assertions failed would report the opposite of what it appears to
  report. Appendix D reproduces each record.

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
* **`docs/surcomplex/spectral-theory/`** supplies the finite algebraic spectral
  vocabulary Part III uses, and its "spectrum" is the **algebraic eigenvalue
  and singular-value list**. That is *not* the differential phase spectrum;
  Theorem 16.5 is the bridge between them for Hermitian coefficients, and
  Example 16.10 shows there is no bridge in general. Each report should name
  its own sense of the word on first use. **Cross-link both ways.**
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
write their evidence files beside themselves — and member 10's program writes
to a `data/` directory it creates one level *above* its own, overwriting the
delivered `verification.json` — so a byte-identity check performed *after* a
run compares two equally modified copies and tells you nothing. Their recorded outputs are already in `data/`, and Appendix D of the
report reproduces them. Nothing in `sources/`, `code/` or `data/` was modified
to produce this report.
