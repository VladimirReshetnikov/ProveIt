# Research audit

Date: September 22, 2026.
Repository: VladimirReshetnikov/Surreal.
Pinned snapshot: 4cf691c7d951e037739d32d9f5c387dcce724f3c.

## Material actually inspected

The GitHub connector was used to read the repository README, the complete
report catalogue docs/README.md, the opening scope and implementation portion
of docs/FORMALIZATION.md, directory and recursive tree listings, and the names
of the archives under docs/new. The catalogue listed 26 main reports.
Indexed repository searches for "Kolmogorov" and "probability" returned no
matches. These searches are not certificates of absence.

The binary ZIP archives under docs/new were not unpacked. Historical retired
manuscripts were not exhaustively read. The general repo clone could not be
obtained in the working container, so no claim of a complete local grep or
full archive audit is made.

## Literature and originality

Primary material consulted included Benci, Horsten and Wenmackers,
Non-Archimedean Probability (arXiv:1106.1524 and journal metadata); Brickhill and
Horsten, Popper Functions, Lexicographical Probability, and Non-Archimedean
Probability (arXiv:1608.02850); and the bibliographic record of Kakutani,
On Equivalence of Infinite Product Measures (1948).

The full positive-support Neumann lemma was identified in the repository's
Hahn documentation and is treated as a classical imported result, not a new
claim. The scalar Riesz–Markov representation theorem is also an explicitly
imported classical input. The paper does not claim discovery of lexicographic
probability or of square-summability phenomena in ordinary product measures.

Additional keyword searches were attempted but often returned irrelevant or
inadequate material. They do not support an exhaustive negative literature
claim. The justified originality statement is that equivalent main theorem
formulations were not found in the reviewed material. Candidate originality
requires further expert and bibliographic review.

## Verification boundary

The text gives detailed proofs of its coefficientwise extension criteria,
positivity arguments, strong atomic classification, and applications.
No Lean compilation or independent peer review is claimed. The exact Python
checks verify finite rational identities and estimates only. The program
cannot establish Riesz representation, arbitrary-rank Neumann support,
infinite L2 convergence, or positivity on all Borel events.
