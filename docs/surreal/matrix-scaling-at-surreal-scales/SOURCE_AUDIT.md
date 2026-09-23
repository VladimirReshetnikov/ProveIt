# Source and novelty audit

Audit date: 22 September 2026 (America/Los_Angeles).

## Repository snapshot

Repository: https://github.com/VladimirReshetnikov/Surreal

Pinned commit: `048b72cf7cbfc8ab246e4f73788c10460cb3f6e0`.

The GitHub connector supplied this commit as the main-tree SHA. The audit used:

1. The recursive repository tree and the `docs` directory listing.
2. The complete `docs/README.md` catalogue, identifying 36 reports.
3. The detailed `docs/surreal/markov-generators-at-every-scale/README.md` guide,
   including its theorem descriptions, limitations, and neighboring-report comparison.
   The connector's displayed final build-instructions tail was truncated.
4. `docs/surcomplex/spectral-theory/README.md`, requested and read through line 180.
5. The directory listing for `docs/new`, which contains only `README.md` at this pin.
6. The first 20 lines of `Surreal/Algebra/MarkovResolvent.lean`, fetched at the
   pinned commit to confirm the positive-control filename and its resolvent scope.

This was NOT a full-text review of every report, every Lean declaration, or the
entire Git history. No repository file was modified.

### Search reliability limitation

Connector searches for `Sinkhorn` and `spanning` returned empty results. However,
the positive-control search `MarkovResolvent` also returned empty despite the
recursive tree including `Surreal/Algebra/MarkovResolvent.lean`. The indexed search
was therefore treated as unreliable. Its empty results are not evidence that a
term or theorem is absent.

### Closest existing repository subjects

The Markov-generator report describes positive forest formulas, normalized
resolvent hierarchies, and uniform relative stability of resolvent entries. The
spectral report describes positive Cauchy–Binet identities, spectral valuation
scales, and exact support-field descent and ramification. These mechanisms and
topics are relevant precedents. They are not claimed again as new.

The present manuscript concerns nonlinear fixed-margin diagonal scaling, a
whole-relative-infinitesimal surcomplex branch, sharp tree-deletion gains at all
Taylor orders, and exact propagation under a localized chain perturbation.
Those formulations were not identified in the catalogue and relevant guides
actually inspected. This is a targeted comparison, not a certified absence result.

## Published sources compared

### Matrix scaling and its generalized series

Martin Idel, *A review of matrix scaling and Sinkhorn's normal form for matrices
and positive maps*, arXiv:1609.06349 (2016).

- https://arxiv.org/abs/1609.06349
- HTML version read: https://arxiv.org/html/1609.06349v1
- Relevant: prescribed-margin support criterion, Theorem 3.1; continuity material.
- No novelty claim is made for real scaling existence, uniqueness, or continuity.

Meisam Sharify, Stéphane Gaubert, Laura Grigori, *Solution of the optimal assignment
problem by diagonal scaling algorithms*, arXiv:1104.3830, version 2 (2013;
first version 2011).

- https://arxiv.org/abs/1104.3830
- https://arxiv.org/html/1104.3830v2
- Relevant: Theorem 2.6 gives generalized Dirichlet expansions for the scaled
  Hadamard deformation, convergent in a punctured disk; Corollary 2.7 gives an
  exponential convergence rate.
- This is a direct precedent for generalized-series methods in matrix scaling.
  The article explicitly does NOT claim the first such connection.

Marvin Eisenberger, Aysim Toker, Laura Leal-Taixé, Florian Bernard, Daniel Cremers,
*A Unified Framework for Implicit Sinkhorn Differentiation*, arXiv:2205.06688 (2022).

- https://arxiv.org/abs/2205.06688
- https://arxiv.org/html/2205.06688v1
- Relevant: weighted constraint-matrix inverse and implicit Sinkhorn derivatives;
  error analysis of approximate inputs.
- The derivative formula is credited, not proposed as new. The manuscript's
  candidate novelty is the exact nonlinear valuation law and support-controlled
  arbitrary-rank extension, not the mere use of implicit differentiation.

### Spanning-tree and foundational inputs

Robert Burton and Robin Pemantle, *Local Characteristics, Entropy and Limit
Theorems for Spanning Trees and Domino Tilings via Transfer-Impedances*,
Annals of Probability 21 (1993), 1329–1371.

- https://arxiv.org/abs/math/0404048
- Used as a transfer-current precedent. The specific tree interpolation identity
  used in the article is proved directly with Cauchy–Binet and Cramer's rule.

Alessandro Berarducci and Vincenzo Mantova, *Surreal numbers, derivations and
transseries*, JEMS 20 (2018), 339–390.

- https://arxiv.org/abs/1503.00315
- https://arxiv.org/html/1503.00315v3
- DOI: https://doi.org/10.4171/JEMS/769
- Relevant: Hahn and surreal normal-form preliminaries. No theorem about their
  derivation is used or claimed as new here.

Graham Higman, *Ordering by Divisibility in Abstract Algebras*,
Proceedings of the London Mathematical Society (3) 2 (1952), 326–336.

- https://doi.org/10.1112/plms/s3-2.1.326
- Publisher record verified. The standard word-ordering theorem is an imported
  input; the positive-support and finite-generator consequences are proved.

Alfred Tarski, *A Decision Method for Elementary Algebra and Geometry*,
RAND R-109 (1951).

- https://www.rand.org/pubs/reports/R109.html
- Imported real-closed-field transfer is used only for the positive global
  interpretation, not for the main local normalization theorem.

The standard reference H. Gonshor, *An Introduction to the Theory of Surreal
Numbers*, Cambridge University Press (1986), is also cited for normal forms.

## Targeted web searches

Search phrases included:

- `"matrix scaling" "Hahn"`
- `"Sinkhorn" "Puiseux"`
- `"matrix scaling" "spanning tree" perturbation`
- `"Sinkhorn" "non-Archimedean"`
- `"Sinkhorn" "transfer current"`
- Searches for the exact primary-source titles above.

Several topical searches produced mostly irrelevant results. Those results were
not treated as proving absence. Concrete primary-source comparison is the basis
for the limited novelty assessment.

## Priority conclusion

The whole-infinitesimal-polydisc theorem, sharp nonlinear tree/basis-gap laws,
and exact chain propagation formulas are proposed as **candidate original**
formulations. The manuscript supplies proofs. It does not certify publication
priority, exhaustive repository absence, or independent expert validation, and
it does not claim to resolve a named long-standing open conjecture.
