# Infinite-Dimensional Hahn Spectral Theory

**Part I: infinitesimal thickening and range defects in Hahn–Hilbert spaces.
Part II: exact synthesis and algebra-relative spectra for row- and
column-finite Hahn matrices.**
Two research manuscripts, 22 September 2026, assembled as one report in two
parts.

```
article.tex   the report, standalone LaTeX with an internal bibliography
article.pdf   the compiled report, 54 pages
README.md     this guide
03-infinite-spectral-PROVENANCE.md   Part II's delivered provenance record
code/         02-hahn-hilbert-spectral-{verify.py,build.sh}   (Part I)
              03-infinite-spectral-{verify.py,build.sh}       (Part II)
data/         the recorded outputs and pinned requirements of both suites
```

Every label in `article.tex` carries the prefix `ihs:`; Part I labels continue
with `ihs:hh:` and Part II labels with `ihs:rf:`. The files under `code/` and
`data/` keep the source numbers `02` (Part I) and `03` (Part II) of the batch
they arrived in.

## Why one report, and why two parts

Both manuscripts continue the same sentence of the finite-dimensional
[spectral-theory](../spectral-theory/) report, which closes by listing what it
does not contain: "There is no theorem here about infinite-dimensional Hilbert
spaces over No[i], bounded-operator spectra, compact or trace-class operators,
or spectral measures." This report supplies the first two of those items and
the compact half of the third. **No trace-class theory or general
topologically countably additive spectral-measure theorem is supplied.**
Part II provides a complete Boolean algebra of projections with vectorwise
strong Hahn additivity. Their failure to form an operator-valued Hahn sum
does not itself exclude a spectral measure: the classical definition uses
strong-operator additivity on each vector. Remark 19.4 instead gives an
explicit failure of pointwise valuation convergence, even over rational
exponents, distinguishing the established Hahn calculus from that
topological requirement.

The two parts are **not** one theory with one hypothesis paragraph. The word
*spectrum* means different things on different vector spaces. Both now allow arbitrary nonzero set-sized ordered value groups:

| | Part I | Part II |
|---|---|---|
| Vector space | `H((t^Γ))`, `H` an ordinary complex Hilbert space | `C^(I)((t^Γ))`: each Hahn coefficient has finite coordinate support |
| Operators | Hahn series of **ordinary bounded** operators | Hahn series of **row- and column-finite** matrices, no boundedness |
| "Spectrum" | failure of bijectivity on the space; for constant normal operators, equivalently failure of invertibility in the adjointable algebra | failure of invertibility **inside the named algebra** |
| `Γ` | nonzero, set-sized, **not assumed divisible**; only Section 12.1 assumes `Γ ⊆ R` | nonzero, set-sized, **not assumed divisible** |
| Accumulation | accumulation points of `σ_C(T)` thicken into whole infinitesimal monads | accumulating residues `d_i` do **not** enlarge the spectrum beyond the labeled eigenvalues |

Quoted without their categories, the two accumulation statements read as a
contradiction. They are not one; Section 3 works the apparent conflict out on a
single operator. No theorem of Part I is used in Part II or conversely. Part I
takes inner products linear in the first variable; Part II takes them
conjugate-linear in the first. Translate a pairing by conjugating its value
(or exchanging its arguments), including the linearity of variational
functionals.

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
   well-ordered support. No continuity or support condition is assumed.
2. **Exact spectrum of constant normal operators.** For ordinary bounded
   normal `T`, `σ_Γ(T) = σ_C(T) ∪ (σ_C(T)' + m_K)`, where the prime is the
   ordinary accumulation set and `m_K` the infinitesimals. No new eigenvalues
   appear, and isolated points do not thicken.
3. **Range defects persist.** If `S` is injective, every endomorphism-valued
   Hahn perturbation `E` of strictly positive order leaves
   `coker(S+E) ≅ W((t^Γ))`, where `V = Ran S ⊕ W`. No commutation hypothesis is
   needed.
4. **A coercive operator that is not onto.** For `D e_n = e_n / n` and
   `η > 0`, `C = D² + t^(2η) I` is bounded, positive, self-adjoint, coercive
   and injective, yet its cokernel has dimension at least the continuum. Its
   range is closed and proper at every rank, with zero orthogonal complement:
   it is the kernel of the continuous defect projection. Section 12.1 also
   proves metric completeness when `Γ ⊆ R`.
5. **Least norm bounds.** The extension of an ordinary bounded `T` has a least
   field-valued norm bound exactly when `T` attains its ordinary norm.

## What Part II claims

For arbitrary nonzero set-sized `Γ`, the algebra
`𝒜 = RCF_I(C)((t^Γ))` acting on `C^(I)((t^Γ))`, and `A = D + B` with
`D = diag(d_i)` of pairwise distinct ordinary real entries and `B = B*` of
globally well-ordered positive support:

1. **Exact infinite diagonalization.** There is a unique near-identity
   normalized Hahn-unitary `U` with `AU = UΛ`. All correction exponents lie in
   the monoid generated by `supp B`, so the value group is never enlarged.
2. **Synthesis, commutants, projections.** Exact vectorwise spectral
   synthesis, and a classification of every commuting operator and spectral
   projection.
3. **The algebra-relative spectrum.** `σ_𝒜(A) = {λ_i}`, even when the real
   residues accumulate, with a coherent resolvent at every noneigenvalue.
   This is a spectrum relative to a specified unital `K`-algebra, not a
   Banach-algebra spectrum. The coherence proof is essential: the diagonal
   `diag(tⁿ)` has coherent support but its scalar inverses do not form a
   Hahn operator. For a finite index set the diagonal algebra is all `K^I`;
   its strict inclusion in `K^I` requires an infinite index set and
   nonzero value group.
4. **Walks and finite sections.** Closed weighted walks control every
   eigenvalue coefficient; a change outside a finite section is first seen only
   through a walk that leaves the section and returns; the order `2r+2`
   finite-section threshold is sharp for one-scale locally finite graphs.

## What the report does not claim

- Neither part claims to solve a named published open problem, and **priority
  is not certified** for either. Both literature comparisons were targeted
  searches, not exhaustive ones.
- Classical inputs are credited, not claimed: the spectral theorem, Baire
  category, the closed-graph theorem, Hahn–Neumann support lemmas, Higman's
  lemma, Rayleigh–Schrödinger perturbation, and the row- and column-finite
  algebra of Ara, Goodearl and O'Meara. The failure of non-Archimedean
  orthogonal decomposition is known in other models (Aguayo–Nova,
  Aguayo–Nova–Shamseddine).
- "Compact" in Part I describes the original operator on the ordinary Hilbert
  space. Nothing is asserted about compactness or compactoidness in the Hahn
  valuation topology.
- The Part I spectral formula concerns **constant normal** operators. It is
  not a classification of spectra of general Hahn operator series.
- The Part II hypothesis of distinct real labels forces `|I| ≤ |R|`.
- **No trace-class theory or general topological spectral-measure theorem**
  is provided; the vectorwise Hahn-additive projection calculus is explicit.
- The proofs have not been independently refereed or checked by a proof
  assistant.
- The two programs check finite algebraic identities only. They do not
  establish Baire category, arbitrary support well-ordering, an infinite
  cokernel dimension, the spectral formulas, or any infinite-dimensional
  theorem.
- Both suites report exactly **218 checks** and both recorded runs used
  Python 3.13.5 with SymPy 1.14.0. This is a coincidence of two independently
  written programs. The counts are of entirely different assertions.
- The two manuscripts audited the repository at different pinned revisions,
  `608dd23` (Part I) and `a3124af` (Part II). Neither audit was repeated
  against the other's pin when they were assembled.

## Relation to the neighbouring reports

**[spectral-theory](../spectral-theory/)** is the finite-dimensional sibling:
determinantal matrix theory over real closed fields, in which every dimension
is an ordinary integer. This report is not a continuation of it.
Part II's source proved Higman's lemma in an appendix. That proof is not
reprinted here, because the identical argument is already written out there as
`spec:lem:words` and `spec:lem:neumann`.

**[hahn-herglotz-positivity](../hahn-herglotz-positivity/)** bears on the
missing spectral measures only negatively: its `herg:cor:unitary` gives a
cyclic algebraic unitary with no positive coefficientwise spectral measure.
It supplies no spectral-measure theory.

## Build

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The reviewed build has 54 pages, zero errors, zero undefined references and
citations, and zero duplicate PDF destinations. It retains the baseline
underfull box in the novelty table. The status note is printed with the
abstract on one title page. To rerun the checks, run the scripts in
`code/` on a copy of this directory; SymPy 1.14.0 is pinned in `data/`.
