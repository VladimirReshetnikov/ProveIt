# Targeted source audit

Research date: October 2, 2026.
Repository snapshot: `928ea97017a25ebe56d240c84f27d2275d818c75`.

## Repository reads

The GitHub connector was used to inspect the repository tree and these sources:

1. `Computability/HilbertTenthProblem/README.md`
   https://github.com/VladimirReshetnikov/ProveIt/blob/928ea97017a25ebe56d240c84f27d2275d818c75/Computability/HilbertTenthProblem/README.md
   Used for project context and its stated fixed universal 87-operation bound,
   not as a proof of the new results.
2. `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/imported_substrate_review_20261002.md`
   https://github.com/VladimirReshetnikov/ProveIt/blob/928ea97017a25ebe56d240c84f27d2275d818c75/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/imported_substrate_review_20261002.md
   Read for the full review and its warnings about horizon-dependent arity,
   witness uniqueness, conditional nonnegativity, and uninstantiated universality.
   Blob SHA returned for this file: `8bd07142c8b4298fb636e47b40d2d84e993a40ce`.
3. The combined report README:
   https://github.com/VladimirReshetnikov/ProveIt/blob/928ea97017a25ebe56d240c84f27d2275d818c75/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/probabilistic-quantum-and-continuous-computation/README.md
   Used to avoid simply repackaging previously covered contraction, matrix,
   equilibrium, quantum, and bounded-certificate topics.

This was NOT an exhaustive re-reading of every manuscript in the combined report
or a rebuild/audit of all repository proofs. A direct container download attempt
was blocked by DNS/network restrictions; the actual source reads used the GitHub
connector. No source files from the repository are bundled as if newly authored.

## Primary public sources

- Julien Cassaigne, Vesa Halava, Tero Harju, François Nicolas,
  *Tighter Undecidability Bounds for Matrix Mortality, Zero-in-the-Corner Problems,
  and More*, arXiv:1404.0644v3, September 5, 2014.
  https://arxiv.org/html/1404.0644v3
  The full HTML was consulted, especially the explicit mortality bounds and the
  definition of reducibility. Its 2014 open-status tables are not presented as a
  current classification in the report.

- Victor Miller, MathOverflow question 511960, *Decidability of a matrix product
  being rank 1*, June 2, 2026, and the June 2-4 discussion with Benjamin Steinberg.
  https://mathoverflow.net/questions/511960/decidability-of-a-matrix-product-being-rank-1
  The June 3 comment isolates no common invariant line. The discussion supplies
  the research question and credit for the direct-sum/affine suggestions; the
  answer under that restriction is proved independently in the article. It is
  not treated as a peer-reviewed theorem source.

- Yannick Forster, Edith Heiter, Gert Smolka,
  *Verification of PCP-Related Computational Reductions in Coq*,
  arXiv:1711.07023v2, July 18, 2018.
  https://arxiv.org/abs/1711.07023v2
  https://doi.org/10.1007/978-3-319-94821-8_15
  The authors' abstract explicitly describes a reduction from string rewriting
  generalizing Turing halting to PCP. Used as a primary source for the external
  classical reduction interface; their proof scripts were not replayed here.

- Yuri V. Matiyasevich, *Hilbert's Tenth Problem*, MIT Press, 1993.
  Author-hosted preface:
  https://logic.pdmi.ras.ru/~yumat/H10Pbook/preface.htm
  Consulted for the stated equality of Diophantine and recursively enumerable
  sets. The report does not claim to re-prove DPRM.

## Priority audit boundary

Targeted searches included rank-one product undecidability, positive/stochastic
matrix mortality, exact consensus, and no-common-invariant-line restrictions.
They did not identify a source proving precisely the full tensor-guard package
presented here. This is limited evidence, NOT a proof of first publication.
No theorem is called an established major conjecture or a settled broad entropy
problem. The affine lift and standard computability consequences are explicitly
separated from the proposed new guard construction and certificate compression.
