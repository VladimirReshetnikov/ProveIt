# Source and repository audit

Inspection date: 21 September 2026.
Repository: https://github.com/VladimirReshetnikov/Surreal
Pinned revision: e260237db9b71da8b74a0c13c8e6355119091100

## Repository material consulted

The GitHub connector supplied the recursive tree and the following files at
that revision. The tree response was truncated, so it was not treated as a
complete inventory independently of the catalogue.

1. `docs/README.md`: full catalogue and package map.
2. `docs/surcomplex/analysis/README.md`: full README.
3. `docs/foundations-and-computation/foundations/README.md`: full README.
4. `docs/foundations-and-computation/computer-algebra/README.md`: a long
   excerpt covering capabilities, scope, implementation distinctions, and
   the beginning of reproduction instructions; its response was truncated
   near the end. Not represented as a complete code audit.
5. `docs/surcomplex/trigonometry/README.md`: full README, especially its
   stated exclusions of an intrinsic derivation and of a differential-equation
   interpretation of the phase-extension classification.
6. `docs/surcomplex/analysis/article.tex`: source lines 1–180, containing
   the notation and opening field/size foundations.

A connector search for “derivation” returned no results. That search result
was NOT used as evidence that the term or subject is absent. No complete
full-text scan of all manuscripts was performed. A direct network clone was
unavailable; the usable evidence came from connector reads.

The gap assessment is therefore a scoped documentation-interface assessment,
not a claim that the repository contains no prior derivation-related material.
No repository files were edited and no repository code was reported as run.

## Primary literature and its role

- Berarducci–Mantova, “Surreal numbers, derivations and transseries,”
  arXiv:1503.00315v3; JEMS 20 (2018), 339–390.
  Consulted the theorem statements and relevant derivative/integration
  passages. The normalized strongly additive, exponential-compatible,
  surjective derivation is a deep imported result; its construction is not
  reproved or formally verified in this package.
- Berarducci–Mantova, “Transseries as germs of surreal functions,”
  arXiv:1703.01995v3; Transactions AMS 371 (2019), 3549–3592.
  Consulted the omega-series definition, composition/fine-derivative/Taylor
  statements, and the specific global compatibility obstruction. These are
  separate imported results, not hypotheses hidden inside our phase criterion.
- Bournez–Guilmant, arXiv:2211.08396.
  Consulted as contextual literature on stable surreal subfields. No theorem
  from it is used to justify the independent monomial-support localization
  proof in Section 10.
- Singer, arXiv:0712.4124v2.
  Consulted for differential Galois/Picard–Vessiot background. The rational
  constant-field computation and nonembedding example are proved explicitly
  in the article over the set-sized base C(X).
- Gonshor (1986), *An Introduction to the Theory of Surreal Numbers*.
  Standard book reference for normal forms and the surreal exponential. Its
  publisher catalogue was identified; the whole book was not downloaded or
  audited in this session.
- B. H. Neumann (1949), “On ordered division rings.”
  Standard source for the positive well-ordered support lemma. The publisher
  page did not provide accessible full text in this session. The article
  explicitly imports the standard lemma rather than claiming to reprove or
  re-audit the original paper.

The literature consultation was targeted, not an exhaustive novelty search.
No priority claim or assertion of resolving a named open problem is made.

## Verification of the new deliverables

Only the newly supplied `verify_examples.py` was executed for this package.
It passed 291 exact finite checks. The mathematical nonexistence and
infinite-support theorems rest on their written proofs, not on these tests.
The standalone LaTeX source was compiled, all 27 pages were rendered, and
contact sheets plus full-size selected pages were visually inspected.
