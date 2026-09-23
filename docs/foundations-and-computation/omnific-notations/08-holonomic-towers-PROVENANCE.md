# Provenance and review boundary

Date: 23 September 2026.

## Repository

Repository: https://github.com/VladimirReshetnikov/Surreal

Inspected main-branch commit:
`a45d72292a46dac13300d395101df188efb84eef`

Directly inspected material:

- Main repository README and directory metadata.
- `docs/README.md`, report catalogue and provenance statements.
- `docs/foundations-and-computation/computable-surreals/article.tex`, source
  lines 1–230, covering the abstract, representations, reconciliation, and
  opening prior-work statements. Blob:
  `0c2ebbe7ea056fb39dc6e9d0ce180b1050413bc6`.
- `docs/foundations-and-computation/computer-algebra/README.md`, source lines
  1–180, including capability contracts, existing exact monomial prototypes,
  current zero-test references, implementation boundaries, and non-claims.
  Blob: `a6e530b30554b6d685e418d68fd86b9fac7a5917`.

This was a targeted source inspection, not an exhaustive review of all
repository manuscripts, companion drafts, source history, or Lean proofs.
The repository's own formalization status is not transferred to this article.
No modifications or commits were made to the remote repository.

## Literature

The bibliography includes classical surreal normal forms, Stanley's D-finite
series theory, L'Innocente–Mantova's omnific/generalized-series factorisation
work, Ershov's hierarchy, the well-founded-tree index-set theorem recorded by
Cenzer–Marek–Remmel, Bancerek's Cantor-normal-form treatment, and the 2026
Chen–Fang–van der Hoeven D-algebraic transseries zero-test. The user-specified
ordinal-notation Wikipedia page is an introductory motivation, not the
technical foundation of the new proofs.

Searches combined omnific integers or surreal notation with equality,
holonomic/D-finite representations, and Ershov/finite mind-change levels.
No matching published statements of the proposed combined tower theorem and
the exact omnific d-layer positivity classification were located. Search
failure cannot establish mathematical priority. The article's novelty ledger
separates these proposed formulations from their established ingredients.

## Verification

The article was developed with direct mathematical arguments. No Lean proof
was produced or run. The delivered Python suite uses exact rational/SymPy
arithmetic and performs finite checks. It does not decide actual nonhalting,
validate arbitrary infinite trees, or prove the completeness theorems by
experimentation.

During development, the finite order-embedding audit detected a reversed
neighbor selection in the first version of the test implementation. That
implementation was corrected; the final all-pairs order test passes. The
mathematical lemma states insertion in the required reversed order and did
not rely on the erroneous code. The final report records only the final
reproducible test run, not an assertion that no intermediate test failed.

The typeset PDF was rebuilt after reference and layout changes, checked for
unresolved references and overfull lines, and inspected through rendered
page images. This is document-quality checking, not a proof of mathematical
correctness.
