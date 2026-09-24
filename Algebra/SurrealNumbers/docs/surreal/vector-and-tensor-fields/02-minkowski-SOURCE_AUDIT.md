# Source audit and claim scope

## Repository baseline

Repository: https://github.com/VladimirReshetnikov/Surreal

Pinned revision: `d22a5b35d5b3040e870c3cfd6d1c8f7259e094b0`.

Inspected on 22 September 2026 through the connected GitHub reader.
The recursive repository tree supplied the pinned revision and directory
structure. The review was targeted, not an exhaustive audit of the repository.

## Repository material actually inspected

| Path or operation | Scope and use |
| --- | --- |
| Recursive tree at the pinned revision | Repository structure and commit identification. The large tool response was truncated; no claim of a fully read file inventory is made. |
| `README.md` | Large returned excerpt of the root overview, including the formalization layers and mathematical distinctions. The full response was truncated. |
| `docs/README.md` | Lines 1–160, covering reading routes, report families, coefficient rings, topology and summation distinctions, and the physics report summary. |
| `docs/physics/surreal-scalars-and-spacetime/README.md` | Lines 1–170, including the report's scope, conditional and exact claim distinctions, bounded-frame scale information, and the warning against confusing scalar extension with regularization. |
| `docs/NORMAL_FORM_BRIDGE.md` | Lines 1–95, including the 22 September assessment stating that the infinite normal-form ordered-field bridge and additional algebraic transfers have been constructed. |
| Directory listings for `docs` and the physics report | Locating the relevant source material. |
| Repository search for `Minkowski tensor` | Returned no matches. This is not evidence that every topic in this article is absent from the repository. |

The full physics article, all other report manuscripts, and every Lean source
were not read line by line. No upstream Lean build was performed. This article
therefore does not certify the repository's formalization, and it does not
state that the already documented infinite normal-form bridge is missing.

## External primary and author-hosted sources

The article's internal bibliography contains complete source attribution.
The principal public sources checked during preparation include:

- Mantova and Matusinski, *Surreal numbers with derivation, Hardy fields and
  transseries: a survey*, arXiv:1608.03413v2; the arXiv HTML text and bibliographic
  record, with the published 2017 reference.
- Berarducci and Mantova, *Surreal numbers, derivations and transseries*,
  JEMS 20 (2018), 339–390; the EMS publisher record and arXiv:1503.00315.
- Bär, *Linear wave equations on Lorentzian manifolds*, arXiv:1006.2354;
  the Cauchy and finite-propagation framework.
- Bär, Ginoux, and Pfäffle, *Wave Equations on Lorentzian Manifolds and
  Quantization*, EMS 2007, DOI 10.4171/037, arXiv:0806.1036;
  publisher and author/preprint records.
- David Tong's author-hosted *Electromagnetism* notes, the relativity and
  radiation chapters. Relevant PDF pages were viewed to check conventions
  and the retarded-kernel sign, rather than relying on lossy parsed formulas.
- Madarász, Stannett, and Székely, the 2022 Review of Symbolic Logic paper on
  relativity over arbitrary ordered fields, via the authors' institutional
  manuscript record. The published record, not a differently dated search
  duplicate, supplies the bibliographic year and pagination.
- Neumann's 1949 paper *On ordered division rings*: bibliographic identification
  and DOI, with the support calculus also discussed through the surreal survey.
  This is not a claim to have reread every page of the 1949 paper.

Conway and Gonshor are cited as foundational monograph sources; the article's
normal-form background was cross-checked against the author survey rather
than represented as a fresh cover-to-cover reading of both monographs.

## What is proved and what is imported

Imported: Conway normal forms, real closedness of the stated Hahn fields,
the classical Neumann support lemma, and the stated ordinary real Cauchy and
Green theorems.

Proved in the article: the displayed finite Lorentz and tensor identities;
the bounded-group reduction and logarithmic kernel description; the
valuation-sensitive causal stability estimate; the specified coherent
calculus, halo and coefficientwise lifting statements; Maxwell energy
and scale identities; positive-order retarded inversion and cubic-wave
recursion; and the explicit frequency and infinite-time obstructions.
Some finite facts are standard identities rederived in the chosen conventions.
No exhaustive claim of new literature priority is made.

Physically interpreted only: any proposal to identify surreal coefficients
with measured quantities or physically attainable observers. The article
constructs a mathematical framework, not an experimentally validated model.

## Verification

All 42 tests in `verification/check_identities.py` passed using SymPy 1.14.0.
The record is included. These are finite exact symbolic checks. They are
independent of, and do not replace, the proofs of summability, real analysis,
or the infinite coefficient constructions. No Lean verification is claimed.

The final PDF was compiled with pdfLaTeX, cross-references were stabilized,
and its pages were rendered for visual layout inspection. Build auxiliary
files and rendered inspection images are intentionally excluded from the ZIP.
