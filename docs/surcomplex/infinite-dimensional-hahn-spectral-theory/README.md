# Infinite-Dimensional Hahn Spectral Theory

**Part I: infinitesimal thickening and range defects in Hahn–Hilbert spaces.
Part II: exact synthesis and algebra-relative spectra for row- and
column-finite Hahn matrices. Part III: Drazin halos and ramified spectral
mapping in arbitrary Hahn operator algebras. Part IV: Fredholm windows for
compact self-adjoint operators under noncommuting Hahn perturbations.**
Four research manuscripts, all dated 22 September 2026, assembled as one
report in four parts: Parts I and II arrived together, Parts III and IV in a
later batch.

```
article.tex   the report, standalone LaTeX with an internal bibliography
article.pdf   the compiled report, 98 pages
README.md     this guide
03-infinite-spectral-PROVENANCE.md      Part II's delivered provenance record
04-drazin-halos-RESEARCH_AUDIT.md       Part III's delivered audit record
05-fredholm-PROVENANCE.md               Part IV's delivered provenance record
code/         02-hahn-hilbert-spectral-{verify.py,build.sh}   (Part I)
              03-infinite-spectral-{verify.py,build.sh}       (Part II)
              04-drazin-halos-verify.py                       (Part III)
              05-fredholm-{verify.py,build.sh}                (Part IV)
data/         02-hahn-hilbert-spectral-{requirements,verification}.txt
              03-infinite-spectral-{build_verification,verification}.json,
              03-infinite-spectral-requirements.txt
              04-drazin-halos-{build_report,verification}.json
              05-fredholm-{build_report,verification}.json,
              05-fredholm-requirements.txt
```

Every label in `article.tex` carries the prefix `ihs:`; Part I labels continue
with `ihs:hh:`, Part II with `ihs:rf:`, Part III with `ihs:dz:` and Part IV
with `ihs:fr:`. Shared front and back matter uses `ihs:sec:`, `ihs:tab:`,
`ihs:app:`, and the shared proposition `ihs:prop:unify`. The files
under `code/` and `data/` keep the local source numbers `02` (Part I), `03`
(Part II), `04` (Part III) and `05` (Part IV). The delivered audit and
provenance records are kept as delivered; their stale statements are
corrected in Appendices C and D of the article, not in the records.

## Why one report, and why four parts

All four manuscripts continue the same sentence of the finite-dimensional
[spectral-theory](../spectral-theory/) report, which closes by listing what it
does not contain: "There is no theorem here about infinite-dimensional Hilbert
spaces over No[i], bounded-operator spectra, compact or trace-class operators,
or spectral measures." Parts I and II supply the first two of those items and
the compact half of the third. Part III adds the algebra-relative spectrum of
every constant bounded operator, normal or not. Part IV adds noncommuting
perturbations of compact self-adjoint operators and a coefficientwise trace
and Fredholm determinant. **No general trace-class theory and no
topologically countably additive spectral-measure theorem is supplied.**
Part II provides a complete Boolean algebra of projections with vectorwise
strong Hahn additivity. Their failure to form an operator-valued Hahn sum
does not itself exclude a spectral measure: the classical definition uses
strong-operator additivity on each vector. Remark 19.4 instead gives an
explicit failure of pointwise valuation convergence, even over rational
exponents, distinguishing the established Hahn calculus from that
topological requirement.

The parts are **not** one theory with one hypothesis paragraph. The word
*spectrum* means different things on different vector spaces and in
different algebras. There are two kinds: a *bijectivity spectrum* (failure of
bijectivity on a named vector space) and an *algebra-relative spectrum*
(failure of invertibility in a named algebra). Table 1 of the article records
all of them:

| | Part I | Part II | Part III | Part IV |
|---|---|---|---|---|
| Vector space | `H((t^Γ))`, `H` an ordinary complex Hilbert space | `C^(I)((t^Γ))`: each Hahn coefficient has finite coordinate support | none needed | `H((t^Γ))`, `H` infinite-dimensional separable |
| Operators | Hahn series of **ordinary bounded** operators | Hahn series of **row- and column-finite** matrices, no boundedness | **constant** elements of `𝔄((t^Γ))`, `𝔄` any nonzero unital complex algebra | `T+E`, `T` injective compact self-adjoint, `E=E*` of positive order, **not commuting** with `T` |
| "Spectrum" | failure of bijectivity on the space (`σ^alg`); also failure of invertibility in the adjointable algebra (`σ^adj`) | failure of invertibility **inside the named algebra** `𝒜_I` | failure of invertibility inside `𝔄((t^Γ))`: `σ^adj` for `𝔄 = B(H)`, `σ_{𝒜_I}` for `𝔄 = RCF_I(C)` | both Part I spectra, proved equal here; also an algebraic Fredholm spectrum |
| `Γ` | nonzero, set-sized, **not assumed divisible**; only Section 12.1 assumes `Γ ⊆ R` | nonzero, set-sized, **not assumed divisible** | nonzero, set-sized, **not assumed divisible** | nonzero, set-sized, **divisible** |
| Accumulation | accumulation points of `σ_C(T)` thicken into whole infinitesimal monads | accumulating residues `d_i` do **not** enlarge the spectrum beyond the labeled eigenvalues | every point of the Drazin spectrum gets a whole halo; in a Banach algebra, the accumulation points and the isolated non-poles | `0` keeps the whole monad, with no eigenvalues in it; each nonzero eigenvalue becomes a finite Hermitian cluster |

Quoted without their categories, the Part I and Part II accumulation
statements read as a contradiction. They are not one; Section 3 works the
apparent conflict out on a single operator, and Proposition 3.1 shows that
Part III's single formula produces both conclusions once the algebra is
named. No theorem of Part I is used in Part II or conversely. Part IV works
in Part I's space and algebra and uses Part I's range-defect Theorem 7.1.
The main theorems of Part III use no theorem of the other parts. Parts I and
IV take inner products linear in the first variable; Part II takes them
conjugate-linear in the first; Part III uses none. Translate a pairing by
conjugating its value (or exchanging its arguments), including the linearity
of variational functionals.

## What Part I claims

The proof review removes the source's standing divisibility assumption.
A nonzero squared norm has leading exponent `2δ`, so its root already
lies in the original field. The scalar moduli and near-one binomial roots
used in Part I need no larger group; ordinary positive operator square roots
are taken before Hahn extension. General positive scalars have a square root
exactly when their leading exponent lies in `2Γ`.

For `K = C((t^Γ))` with arbitrary nonzero set-sized ordered `Γ`,
and `𝓗 = H((t^Γ))` with the
coefficientwise-convolution inner product:

1. **Automatic structure.** Every everywhere-defined adjointable `K`-linear
   operator is a Hahn series of ordinary bounded operators with one common
   well-ordered support (Theorem 6.1). No continuity or support condition is
   assumed.
2. **Exact spectrum of constant normal operators.** For ordinary bounded
   normal `T`, `σ_Γ(T) = σ_C(T) ∪ (σ_C(T)' + m_K)`, where the prime is the
   ordinary accumulation set and `m_K` the infinitesimals (Theorem 8.2). No
   new eigenvalues appear (Theorem 8.3), and isolated points do not thicken.
3. **Range defects persist.** If `S` is injective, every endomorphism-valued
   Hahn perturbation `E` of strictly positive order leaves
   `coker(S+E) ≅ W((t^Γ))`, where `V = Ran S ⊕ W` (Theorem 7.1). No
   commutation hypothesis is needed.
4. **A coercive operator that is not onto.** For `D e_n = e_n / n` and
   `η > 0`, `C = D² + t^(2η) I` is bounded, positive, self-adjoint, coercive
   and injective, yet its cokernel has dimension at least the continuum
   (Theorem 11.3). Its range is closed and proper at every rank, with zero
   orthogonal complement (Theorem 12.2): it is the kernel of the continuous
   defect projection. Section 12.1 also proves metric completeness when
   `Γ ⊆ R`.
5. **Least norm bounds.** The extension of an ordinary bounded `T` has a least
   field-valued norm bound exactly when `T` attains its ordinary norm
   (Theorem 13.2).

Section 15.2, "What would require a different theorem", now records which
parts of that question Parts III and IV answer, and that spectra of general
Hahn operator series remain unclassified.

## What Part II claims

For arbitrary nonzero set-sized `Γ`, the algebra
`𝒜 = RCF_I(C)((t^Γ))` acting on `C^(I)((t^Γ))`, and `A = D + B` with
`D = diag(d_i)` of pairwise distinct ordinary real entries and `B = B*` of
globally well-ordered positive support:

1. **Exact infinite diagonalization.** There is a unique near-identity
   normalized Hahn-unitary `U` with `AU = UΛ` (Theorem 18.2). All correction
   exponents lie in the monoid generated by `supp B`, so the value group is
   never enlarged.
2. **Synthesis, commutants, projections.** Exact vectorwise spectral
   synthesis, and a classification of every commuting operator and spectral
   projection.
3. **The algebra-relative spectrum.** `σ_𝒜(A) = {λ_i}`, even when the real
   residues accumulate, with a coherent resolvent at every noneigenvalue
   (Theorem 20.2). This is a spectrum relative to a specified unital
   `K`-algebra, not a Banach-algebra spectrum. The coherence proof is
   essential: the diagonal `diag(tⁿ)` has coherent support but its scalar
   inverses do not form a Hahn operator. For a finite index set the diagonal
   algebra is all `K^I`; its strict inclusion in `K^I` requires an infinite
   index set and nonzero value group.
4. **Walks and finite sections.** Closed weighted walks control every
   eigenvalue coefficient; a change outside a finite section is first seen only
   through a walk that leaves the section and returns; the order `2r+2`
   finite-section threshold is sharp for one-scale locally finite graphs.

The coefficient and Hahn algebra statements hold for every nonempty `I`.
The closing zero-divisor assertion of `ihs:rf:prop:algebra` requires two
distinct indices: the constant matrix units `E_ii` and `E_jj` are nonzero
with product zero. For a singleton `I`, the algebra is the Hahn field `K`.
This bounded correction is separate from the Part III review recorded below;
the Fredholm main-text review remains pending.

## What Part III claims

For any nonzero unital complex algebra `𝔄` (no norm, no normality) and any
nonzero set-sized ordered `Γ` (no divisibility), with `Σ^𝔄_Γ(T)` the set of
`λ ∈ K` at which `T − λ1` has no two-sided inverse in `𝔄((t^Γ))`, for
constant `T ∈ 𝔄`:

1. **Inverse descent.** For `0 ≠ ε` infinitesimal, `S − ε1` is invertible in
   `𝔄((t^Γ))` exactly when `S` is finite-index Drazin invertible, and the
   inverse is then a finite-tail Laurent series in `ε` (Theorem 31.3). The
   proof straightens `ε` to a monomial by a strong automorphism that adjoins
   no fractional exponent, and projects onto a cyclic support.
2. **Halo formula.** `Σ^𝔄_Γ(T) = σ_𝔄(T) ∪ (σ_{D,𝔄}(T) + m_K)`, with
   `σ_{D,𝔄}` the Drazin spectrum (Theorem 32.1). At a Drazin point of index
   `ν` the shifted inverse has exact valuation `−ν v(ε)` (Theorem 32.2).
3. **Banach algebras.** The Drazin spectrum is the accumulation set plus the
   isolated non-poles. For bounded normal `T` this gives
   `σ_C(T) ∪ (σ_C(T)' + m_K)` (Corollary 33.1). Since `B(H)((t^Γ))` is Part
   I's adjointable algebra, this recovers the adjointable-algebra half of
   Part I's Theorem 8.2 by a second route. The general halo theorem drops
   **normality** and the Hilbert and Banach structure (Remark 33.2).
   This recovery does not establish the
   bijectivity spectrum or Theorem 8.3. `Σ ⊆ C` exactly when `T` is
   algebraic (Corollary 33.3).
4. **Ramified spectral mapping.** After subtracting its ordinary value, a
   polynomial germ of ramification index `e` maps a halo onto zero and exactly
   the nonzero infinitesimals with valuation in `eΓ`
   (Theorem 34.5), so `Σ(p(T)) = p(Σ(T))` exactly when every relevant
   Drazin-spectral fibre has a point whose index acts surjectively on `Γ`
   (Theorem 34.7), with an explicit missing value otherwise. In a Banach
   algebra, Drazin indices of `p(T) − b` follow a ceiling formula when its
   nonempty spectral fibre consists of finite poles (Proposition 34.8).
5. **Examples.** The Volterra operator has ordinary spectrum `{0}`, no
   accumulation point, and `Σ(V) = m_K`, with genuine vector nonsurjectivity
   (Section 35.2); `V²` over `Γ = Z` misses every odd valuation in its image
   (Section 35.3); increasing nilpotent Jordan blocks with norm-convergent
   nilpotent finite sections still acquire the whole halo (Section 35.4).
   The same fixed vector witnesses nonsurjectivity for every nonzero
   infinitesimal displacement of the block operator, including nonmonomial
   ones; its bijectivity spectrum is also the whole monad.
   Theorem 36.1 transfers the halo formula to actual surcomplex parameters.

The Part III main-text review covers Sections 28–37 and their summaries. It
expands the Drazin corner and Laurent-recurrence calculations, distinguishes
cyclic Laurent tails from general Hahn supports, and spells out the local
germ's preservation of valuation. The pole-order proof now uses each Riesz
corner's own identity. Volterra's exact range retains the square-integrable
derivative condition, and the scalar-power summaries retain zero in the
image. The block nonsurjectivity proof now treats every nonzero infinitesimal
directly: its `n`th block forces a nonzero coefficient at `−n v(ε)`.

The [collection review record](../../REVIEW.md#drazin-spectral-main-text-review)
states the targeted primary-source checks and validation. This is a
main-text review and source-level extension, with no new Lean coverage or
priority claim. Remaining foundational imports, original-source
reconciliation and the Part IV main-text review remain separate.

## What Part IV claims

For `H` infinite-dimensional separable, `Γ` **divisible**, `T` ordinary
injective compact self-adjoint, and `E = E*` a Hahn series of bounded
operators with positive valuation that need not commute with `T`:

1. **Exact spectrum.** `σ^adj(T+E) = σ^alg(T+E)` is the whole monad `m_K`
   together with, over each nonzero eigenvalue `c` of `T`, a cluster of
   `dim ker(T − c)` real Hahn eigenvalues (Theorem 42.1). The clusters are
   the point spectrum; at every point of `m_K` the operator is injective with
   a cokernel of dimension at least the continuum. The algebraic Fredholm
   spectrum is `m_K` (Corollary 42.2). Enlarging `Γ` keeps the eigenvalues
   and enlarges the monad (Corollary 42.3). For `E = 0` this is a case of
   Part I's Corollary 9.2. This is the case Part I's Section 15.2 set aside
   as needing a different theorem.
2. **No global assembly.** For `D = diag(2^−n)` plus `t^η` times a
   trace-class weighted path, no Hahn unitary with bounded coefficients
   diagonalizes the operator, whatever its exponents (Theorem 43.1); the
   eigenvalue list is not a bounded coefficient (Proposition 43.2).
3. **Hahn Fredholm determinant.** On the nonnegative-valuation part of
   `S_1(H)((t^Γ))`, a coefficientwise determinant satisfies an exact Fredholm
   alternative decided by one finite matrix (Theorem 44.4). For the example,
   the coefficientwise trace is `1` but the eigenvalue sum diverges at the
   second coefficient (Theorem 45.1), and the determinant's `s²` coefficient
   is negative while the eigenvalue product diverges (Theorem 45.2).
4. **Accumulation boundary.** The finite-coupling determinant detects every
   eigenvalue (Theorem 46.1), but no nonzero coherent Hahn analytic function
   vanishes exactly on the spectrum near `0` (Theorem 46.4).

## What the report does not claim

- No part claims to solve a named published open problem, and **priority is
  not certified** for any part. All four literature comparisons were
  targeted searches, not exhaustive ones.
- Classical inputs are credited, not claimed: the spectral theorem, Baire
  category, the closed-graph theorem, Hahn–Neumann support lemmas, Higman's
  lemma, Rayleigh–Schrödinger perturbation, the row- and column-finite
  algebra of Ara, Goodearl and O'Meara, Drazin inverses and their resolvent
  poles, Banach Drazin spectra and polynomial spectral mapping (Drazin,
  Boasso), the generalized Drazin inverse (Koliha, a different condition),
  Riesz projections and isolated-cluster perturbation (Kato), the direct
  rotation of two projections (Simon), trace-class determinant identities
  (Bornemann), Hahn-field closedness (Poonen), and non-Archimedean Fredholm
  theory in Serre's different category. The failure of non-Archimedean
  orthogonal decomposition is known in other models (Aguayo–Nova,
  Aguayo–Nova–Shamseddine).
- "Compact" in Parts I and IV describes the original operator on the
  ordinary Hilbert space. Nothing is asserted about compactness or
  compactoidness in the Hahn valuation topology.
- The Part I spectral formula concerns **constant normal** operators. Part
  III concerns **constant** elements and **algebra-relative** spectra only:
  it classifies no nonconstant operator and no bijectivity spectrum beyond
  its worked examples, and its algebraicity criterion needs a Banach
  algebra. Part IV needs an injective compact self-adjoint residue, a
  self-adjoint perturbation, a separable infinite-dimensional `H` and a
  divisible `Γ`; it says nothing without divisibility or for a residue with
  kernel. Spectra of general Hahn operator series remain unclassified.
- The Part II hypothesis of distinct real labels forces `|I| ≤ |R|`.
- **No general trace-class theory or topological spectral-measure theorem**
  is provided. Parts I–III have no trace-class theory; Part IV's determinant
  lives on the nonnegative-valuation component of the coefficientwise
  trace-class ideal and is not a determinant for negative-valuation series,
  not a nuclear or compactoid theory, and does not exclude every regularized
  spectral product. Part II's projection calculus is vectorwise Hahn
  additive. No part supplies a positive spectral measure.
- Part IV's local clusters do **not** assemble into a global
  bounded-coefficient spectral theorem; its counterexample concerns bounded
  coefficients only, not Part II's algebra or unbounded frameworks.
- Independent refereeing is not certified. Lean covers the row- and
  column-finite algebra lemma `ihs:rf:lem:rcf` and the algebra, action,
  involution and order-inequality clauses of `ihs:rf:prop:algebra`, together
  with its conditional zero-divisor assertion. The singleton identification
  has no separately mapped Lean equivalence, and the spectral theorems remain
  unformalized; see [the formalization ledger](../../FORMALIZATION.md) for
  the precise scope.
- The four programs check finite algebraic identities only. They do not
  establish Baire category, arbitrary support well-ordering, an infinite
  cokernel dimension, the spectral formulas, the Volterra or block halos,
  the absence of global unitaries, or any infinite-dimensional theorem.
- The Part I and Part II suites both report exactly **218 checks** and both
  recorded runs used Python 3.13.5 with SymPy 1.14.0. This is a coincidence
  of two independently written programs. The counts are of entirely
  different assertions. Parts III and IV report 484 and 1,268 checks.
- The manuscripts audited the repository at three pinned revisions,
  `608dd23` (Part I), `a3124af` (Part II) and `048b72c` (Parts III and IV).
  No audit was repeated against another's pin when they were assembled.
  The Part III source says Part I assumes divisibility; that was true at
  `048b72c` and was removed from Part I by `6e34651` before Part III was
  placed (Appendix C.3). The Part IV source says the report excludes a
  trace-class theory; that remains true of Parts I–III only (Appendix D.3).

## Relation to the neighbouring reports

**[spectral-theory](../spectral-theory/)** is the finite-dimensional sibling:
determinantal matrix theory over real closed fields, in which every dimension
is an ordinary integer. This report is not a continuation of it.
Part II's source proved Higman's lemma in an appendix. That proof is not
reprinted here, because the identical argument is already written out there as
`spec:lem:words` and `spec:lem:neumann`. Its `spec:ex:monoid` is the finite
example behind Remark 18.4, and Part IV's Section 47.2 is an
infinite-dimensional instance of the same repeated-residue phenomenon.

**[hahn-herglotz-positivity](../hahn-herglotz-positivity/)** bears on the
missing spectral measures only negatively: its `herg:cor:unitary` gives a
cyclic algebraic unitary with no positive coefficientwise spectral measure.
It supplies no spectral-measure theory.

**[three-duals-of-hahn-vector-spaces](../three-duals-of-hahn-vector-spaces/)**,
placed in the same batch as Parts III and IV, identifies strong endomorphisms
of `V((t^Γ))` with `End_C(V)((t^Γ))`, a larger algebra than Part I's
adjointable `B(H)((t^Γ))`; nothing here depends on it.

## Build

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The current reviewed build has 98 pages, zero errors, zero undefined references and
citations, zero multiply defined labels and zero duplicate PDF destinations.
It retains the baseline underfull box in the novelty table. The title and
status note are on the first page and the abstract on the second.

For the bounded zero-divisor correction, baseline and revised sources each
completed three `pdflatex` passes with those same diagnostics. All 404 source
labels and their numbering were preserved. A rendered comparison of all
97 pages found only physical page 38 changed; that page and its neighbours
were visually checked. The 20 historical code, data and provenance files
were unchanged, and no verification script was rerun for this correction.

For the subsequent Drazin review, baseline and revised sources each passed
three LaTeX passes, at 97 and 98 pages, with the same single underfull-box
notice. All 93 numbered result statements (including Part III's 19), all
404 source labels and their numbers, and all 20 historical files are
unchanged. The copied Part III verifier passes all 484 finite checks under
Python 3.13.14; its full JSON differs from the historical record only in
the Python version. These checks do not prove the arbitrary-support,
infinite-dimensional or new nonmonomial vector-surjectivity assertions.
All 24 pages with changed text or pagination were visually inspected, with
no layout issues; the 15 Part III numbered references in this README agree
with the final auxiliary file.

To rerun the checks, copy this directory and run the scripts in `code/` on
the copy: the Part II script writes `data/verification.json` in the directory above `code/`,
and the Part IV script writes `data/verification.json` in the working
directory unless `--output` is given. SymPy 1.14.0 is pinned in `data/` for
Parts I, II and IV; the Part III script needs only the Python standard
library. The delivered `build.sh` wrappers refer to their source packages'
original unnumbered file names (`article.tex`, `code/verify.py`) and do not
run as placed. In the earlier assembly review, the Part III and Part IV scripts were rerun
under Python 3.14.4 with SymPy 1.14.0 and again passed 484 and 1,268 checks.
