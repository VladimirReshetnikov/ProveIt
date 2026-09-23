# Source and claim audit

Date: 23 September 2026.

## Repository provenance

Repository: https://github.com/VladimirReshetnikov/Surreal

Snapshot: `b895e8672990e8b5a56f97dd7246f9dd5f86c771`.

The snapshot was obtained from the repository tree through the connected GitHub reader. Files were read through that connector; no clone or Lean build was completed. No repository write was made.

Relevant inspected material included selected ranges from:

- `README.md` and `docs/README.md`;
- `docs/manifest.tex`;
- `docs/surcomplex/single-dilation-hahn-support/article.tex`;
- `docs/surcomplex/dynamics-and-normal-forms/article.tex`;
- `docs/surcomplex/entire-functions-at-arbitrary-rank/article.tex`.

The central overlap is the existing S_2 monomial recognizer and the distinction between strong Hahn summability and ordinary convergence. These are credited, not presented as newly invented. The inspected material did not provide the article's autonomous algebraic support classification. This observation is not an exhaustive repository-wide absence certificate.

## Published and preprint literature

The article's bibliography supplies stable URLs and bibliographic details. The principal mathematical inputs are classical:

1. Neumann's support lemma for ordered series. The bibliographic record was checked against the American Mathematical Society source; the lemma is explicitly stated in the article.
2. Newton–Puiseux factorization. The Mannaa–Coquand paper was consulted; the article proves the individual selected-branch denominator bound and spells out its evaluation in a Hahn field.
3. Formal Böttcher coordinates. Salerno–Silverman was consulted, including the formal coordinate statement. The article includes its own explicit construction and uniqueness proof so the subsequent Hahn evaluation has no unstated convergence requirement.
4. Omnific arithmetic and prior examples. L'Innocente–Mantova was consulted for the published normal-form/factorization setting. Their primality result for omega^(sqrt(2)) + omega + 1 is explicitly credited; the new claim under discussion concerns algebraic dependence with a dilate, not primality.
5. Mahler equations. Chyzak–Dreyfus–Dumas–Mezzarobba, Faverjon–Roques, and Gontsov–Goryuchkina provide prior context. The decreasing-denominator series pattern is credited rather than claimed new.
6. Exact polynomial-system solving. Basu–Pollack–Roy is cited for the standard algorithmic real-algebraic machinery needed after reduction to a finite system.

The Nishioka–Nishioka paper, *Autonomous equations of Mahler type and transcendence*, was located and its abstract-level scope checked. Its full text was not available through the retrieval route used. It is not used as a proof premise. Its full comparison remains a specific priority before making a publication-level novelty claim.

The late-2025 preprints *Computing basis of solutions of any Mahler equation* (Faverjon–Poulet) and *A purity theorem for Mahler equations* (Faverjon–Roques) are cited from their abstracts for current context, not as detailed proof inputs.

The user-specified Wikipedia page was consulted for orientation only. None of the main proofs uses it instead of a primary mathematical source.

## Claim boundaries

**Established inputs, not proposed novelty:** Hahn arithmetic, Neumann summability, Newton–Puiseux factorization, formal Böttcher conjugacy, the repository's d=2 recognizer, resultants, and exact algebraic-system methods.

**Proposed research contribution:** the arbitrary-rank, characteristic-zero first-order autonomous support-collapse theorem with its branch-degree bound; the finite-profile and coefficient-descent formulation; the resulting exact omnific classification, sharp relation degree, and finite-shape solvability reduction. The higher-order constructions are presented with explicit prior-example attribution and newly proved order claims.

The ordinary polynomial field identity is a consequence and consistency check, not a claim of priority over classical polynomial decomposition theory. The twelve research questions are proposed next problems; they are not represented as twelve previously published open conjectures.

## Proof and computational checks

The proof audit explicitly checks the distinction between a selected Puiseux branch denominator and a common splitting denominator; choice of the actual root matching S_d z; composition and dilation under strong evaluation; descent to a nondivisible original value group; and the support bounds needed to pass from Laurent series to omnific polynomials.

The exact Python suite checks finite instances only. Its output is in `verification_results.json`. It does not implement the entire decision procedure, arbitrary infinite Hahn arithmetic, or a proof assistant.

No Lean proof has been added or checked. No refereeing or independent verification is claimed. Novelty has not been established by an exhaustive literature search.
