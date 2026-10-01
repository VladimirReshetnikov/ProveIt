# Sources and novelty boundary

Inspected 1 October 2026.

Repository report: https://github.com/VladimirReshetnikov/ProveIt/tree/29e52fcdf8bfa99d52a76d3de380f58c24584b1e/SetTheory/Cardinals/docs/reports/enumerative-combinatorics/adjacency-bounded-132-avoiders

Combined source blob: 0b7cb2f2e63ad60760ddce0916d287e731d413f4. Its text ends at Part V. Parts III and IV supply the finite endpoint counts, the threshold parser, and the Catalan word identities. They are rederived in this manuscript as needed.

Incoming Polynomial Rarity archive: https://github.com/VladimirReshetnikov/ProveIt/blob/a866ff9a2/docs/incoming/ProveIt_Polynomial_Rarity.zip

Archive Git blob: cf18b47515f793c49d82cce5928967234e5a362f. The full source was inspected. Its local subcritical bounds and tilted small-letter suppression are credited and rederived. It explicitly leaves exact amplitudes and limiting crossover functions open. Batch68 commit 29e52fcdf8bfa99d52a76d3de380f58c24584b1e includes the addition07 ancillary files; the article/README were not staged in that integration. The version distinction is deliberate.

model.py is copied from that incoming package, whose header credits its adaptation of the Mayama-Akita endpoint recurrence and ProveIt code/05-macroscopic-deficits-model.py, blob f0248e0d6181200257e2949c1a8fa8f9fecf5617. The new verify.py independently generates all avoiders through size eight, checks the exact parser, and checks finite word coefficients. It uses the credited recurrence only for numerical data.

Primary public records inspected:

1. Nathaniel Nadler, On 132-Avoiding Permutations with an Adjacency Constraint, arXiv:2604.22135v1, 24 April 2026. https://arxiv.org/abs/2604.22135
2. Teruki Mayama and Dai Akita, Finite-state enumeration of adjacency-constrained 132-avoiding permutations, arXiv:2605.23519v1, 22 May 2026. https://arxiv.org/abs/2605.23519
3. Celine Kerriou and Peter Morters, The fewest-big-jumps principle and an application to random graphs, Bernoulli 31(3), 2525-2543 (2025); arXiv:2206.14627. https://arxiv.org/abs/2206.14627

Targeted public searches for 132-avoiding largest jumps, adjacency bounds, half-size thresholds, and crossover functions did not locate the exact result proved here. The search was limited and does not establish universal priority. No external paper is redistributed.

New mathematical content relative to these inspected repository sources: exact three-piece endpoint weight eight; uniform n^-1-scale exclusion of mesoscopic words and small terminal children; first sub-half-size integral constant; its value six at one half; and the limiting ramp 6+12 t_+/sqrt(pi). Higher reciprocal windows remain research questions in this manuscript.
