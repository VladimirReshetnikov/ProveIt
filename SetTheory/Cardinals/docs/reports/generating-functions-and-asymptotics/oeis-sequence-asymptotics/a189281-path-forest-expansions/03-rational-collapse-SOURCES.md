# Sources and contribution boundary

Inspection date: 3 October 2026.

## Repository source

Repository: https://github.com/VladimirReshetnikov/ProveIt

Path:
`SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a189281-path-forest-expansions/article.tex`

Fetched file blob: `5b60a1ad447afe7dce58534fba447b05e401f172`.
Repository tree response: `d68b65ea064084fb121df9bb431b21d086f7be81`.
The report includes two parts and is explicitly AI-assisted, unrefereed,
and nonformalized. It proves stable tiling formulas and all-orders
asymptotics, but leaves its `spf:conj:collapse` open. Its conditional
integrality consequence is `spf:prop:collapse-implication`.

The present report proves that conjecture for all h and generalizes it
to all r,s. The previous stable tiling proof is reproduced with credit;
it is not presented as a new invention. The present asymptotic transfer
is proved directly from the new rational formula.

## OEIS

- https://oeis.org/A189281/internal
  Definition of directed (2,2) avoidance; displayed corrections through
  n^-10 and the observed integer pattern; specific degree-11/order-8
  recurrence remains labeled conjectural in the inspected entry.
- https://oeis.org/A189281/b189281.txt
  Exact validation data. The entry credits n=0..35 to Vaclav Kotesovec,
  36..39 to Christoph Koutschan, and later computations to Rintaro Matsuo.
  Only n=0..30 are included in this archive.
- https://oeis.org/A189282
  Directed (3,3) avoidance, displayed asymptotics through n^-2.
- https://oeis.org/A189283
  Directed (4,4) avoidance, displayed asymptotics through n^-2.
- https://oeis.org/A189284
  Directed (5,5) avoidance, displayed asymptotics through n^-2.

Missing proofs or terms on an OEIS page are not evidence that no proof
exists in the literature. The firm novelty comparison is with the
explicitly open conjecture in the inspected repository report.

## Primary literature and reference

George Spahn and Doron Zeilberger, *Counting Permutations Where The
Difference Between Entries Located r Places Apart Can never be s
(For any given positive integers r and s)*, arXiv:2211.02550 (2022).
https://arxiv.org/abs/2211.02550
The paired tiling enumeration is credited to this framework. The authors'
PDF was also inspected, including its tiling derivation.

Manuel Kauers and Christoph Koutschan, *Guessing with Little Data*,
arXiv:2202.07966 (2022).
https://arxiv.org/abs/2202.07966
Context for recurrence guessing, not an assumption in the proofs.

NIST Digital Library of Mathematical Functions, section 5.11.
https://dlmf.nist.gov/5.11
Logarithmic Stirling expansion and remainder statements, used only in
the optional-to-the-main-theorem index reconstruction section.

## New results developed in the article

- Single-sum stable moment identity for arbitrary directed r,s.
- Universal rational-collapse identity and the conjectured A189281 product.
- Integer correction polynomials at every order; sharp eventual degree law.
- Inverse-factorial hypergeometric kernel and auxiliary coefficient recurrence.
- Entire Borel-transform composition, with explicit caveats about summability.
- Simplified parameter-dependent discrete-index reconstruction formula.

No exact recurrence for the original A189281 sequence is claimed proved.
No complete beyond-all-orders expansion or Lean formalization is claimed.
The external search is not an exhaustive priority review.
