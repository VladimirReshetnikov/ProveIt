# Source and verification audit

Review date: 23 September 2026.

## 1. Principal mathematical source

Philip Ehrlich and Elliot Kaplan, *Number systems with simplicity hierarchies:
a generalization of Conway's theory of surreal numbers II*.

- Version used for numbering: arXiv:1512.04001v1, 13 December 2015.
- Versioned entry: https://arxiv.org/abs/1512.04001v1
- HTML: https://arxiv.org/html/1512.04001v1
- Journal publication: *The Journal of Symbolic Logic* 83(2) (2018), 617–633.
- DOI: https://doi.org/10.1017/jsl.2017.9

The manuscript uses the following parts of the preprint:

1. Section 3: Conway normal forms, truncations, and their relation to the
   simplicity hierarchy; Proposition 6 identifies the Hahn normal-form model.
2. Lemma 3: classification of initial additive subgroups of the real numbers.
3. Theorem 1 and its proof: the necessary and sufficient Hahn-group conditions,
   including the initial exponent tree, initial coefficient groups, and dyadic
   coefficients at right ancestors. The sufficiency proof constructs the
   specified canonical normal-form image and proves it initial.
4. Proposition 9: a comparison point for the form of the least positive element;
   the manuscript supplies its own truncation-based argument.
5. Section 9, Question 2, printed page 18: the discrete initial subgroup question
   and the motivating two-level example immediately preceding it.

The PDF pages containing Theorem 1, Proposition 9, and the question were also
inspected as page images. Journal metadata was checked separately. The preprint's
internal numbering is retained throughout; no equivalence of numbering between
versions is assumed.

## 2. Additional primary sources

- Elliot Kaplan, *Initial Embeddings in the Surreal Number Tree*, Ohio University
  honors thesis, 2015. Title page and the relevant text were inspected. Sections
  6.2 and 7.1 provide omnific-integer context and the initial-group question.
  https://etd.ohiolink.edu/acprod/odb_etd/ws/send_file/send?accession=ouhonors1429615758&disposition=inline
- *Mini-Workshop: Surreal Numbers, Surreal Analysis, Hahn Fields and Derivations*,
  Oberwolfach Report 60/2016, especially printed pages 3355–3356. This gives a
  further record of the question and the concrete initial-subgroup criterion.
  https://ems.press/content/serial-article-files/46663
- Vincent Bagayoko and Joris van der Hoeven, *Surreal substructures*, author-hosted
  manuscript, first version 8 June 2019, corrected version 16 April 2022. Used for
  sign-sequence and concatenation context, not as a source for the proposed
  normalization or its exact range theorem.
  https://www.texmacs.org/joris/sss/sss.html

The source PDFs and font files are not redistributed in this package.

## 3. Repository provenance and its limits

Repository: https://github.com/VladimirReshetnikov/Surreal

The review used the GitHub connector to read repository entry points and
metadata. The repository changed during the review. To avoid attributing all
reads to one snapshot, the identifiers are separated here.

### Initially read files

- `README.md`, requested lines 1–230; returned blob:
  `391afd7c64cebd48b47fbe43dae26c27e8ee8047`.
- `docs/FORMALIZATION.md`, requested lines 1–200; returned blob:
  `6a89497cb1de3e5c7a346201f7fc006d85082426`.

A recursive tree overview and the `docs/surreal` directory listing were also
inspected. These large metadata responses were partially truncated; they were
not treated as a complete source inventory or as proof of absence.

### Later observed commit

A later `commits/main` metadata read reported:

`173eb522fdf5d4bf201c097f76b38273eb4f95e1`

with timestamp `2026-09-23T19:01:14Z`. This identifies that later metadata read;
it is not claimed to identify the two earlier file contents. The commit message
reported repository build results, but no repository Lean build was run for this
article, and no such result is counted as verification of the new mathematics.

### Targeted search

Targeted repository searches included `discrete initial` and an earlier
candidate-direction query, `Picard projective completion cohomology`. No matches
were returned by those searches. Search-index coverage was not certified.
These negative results are not a proof that the proposed construction is absent
from every repository file or prior manuscript.

The reviewed entry points describe sign sequences, cuts, normal forms, strong
Hahn summation, and a ledger distinguishing source-level claims from checked
Lean results. Those are relevant infrastructure for a possible future
formalization. This article does not treat their descriptions as a formal
certificate of its new constructions.

## 4. Original contribution versus imported material

The proposed new contributions are the explicit minimum-to-zero sign-tree map,
the exact predecessor identity with its exceptional minimum, the resulting
normalization and inverse/spine classification, and the structural deductions
proved in the article. General Conway normal forms, the Ehrlich–Kaplan
criterion, and the motivating two-level example are imported and cited.

The existence of a question in a 2015/2018 source does not by itself establish
that the question remained unresolved on the review date. Targeted searches did
not locate an earlier resolution or this exact construction, but were not an
exhaustive priority search. The article therefore labels its answer a proposed
solution and does not claim independently established novelty or acceptance.

## 5. Reproducible finite checks

`verify.py` uses exact rational arithmetic and the Python standard library.
The recorded output is `verification_report.json`.

- 450,862 assertions: PASS.
- Finite source word lengths at most seven.
- All 677 prefix-closed trees through depth three, including the empty tree.
- Inverse exponent-spine and coefficient-spine checks in the stated finite
  ranges.
- 1,500 randomized finite rational series pairs; seed 20260923.
- Negative regression tests reject unrestricted inversion and the false
  right-ancestor identity at the old minimum.

These checks do not verify ordinal-limit cases, arbitrary set-supported Hahn
summability, the imported theorem, or any Lean declaration. The transfinite
claims depend on the written proofs. The independent-review checklist in
Appendix B isolates the highest-risk points.

## 6. Document validation

The supplied article was compiled with three final pdfLaTeX passes. It has 24
pages, including the cover and references. Cross-references are resolved; the
final build has no overfull boxes. All pages were rendered and visually reviewed,
including the central predecessor theorem at higher resolution. No page-boundary
overflow or unresolved-reference markers were detected. These checks concern
presentation only.
