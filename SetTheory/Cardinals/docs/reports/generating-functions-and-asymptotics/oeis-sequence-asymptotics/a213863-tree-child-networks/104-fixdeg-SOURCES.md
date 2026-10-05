# Source provenance and attribution

Checked 2 October 2026. The report uses original combinatorial definitions and exact normalizations from the primary sources below.

## Main combinatorial source

Yu-Sheng Chang, Michael Fuchs, Hexuan Liu, Michael Wallner and Guan-Ru Yu, *Enumerative and distributional results for d-combining tree-child networks*, Advances in Applied Mathematics 157 (2024), 102704.

- DOI: https://doi.org/10.1016/j.aam.2024.102704
- Author version, 25 March 2024: https://web.math.nccu.edu.tw/mfuchs/d-comb-journal-rev.pdf
- arXiv 2209.03850v2: https://arxiv.org/abs/2209.03850

Definitions 1.1–1.3 fix simple rooted DAGs, labelled leaves, tree vertices, d-parent reticulations, and the tree-child condition. Definition 3.1 and Remark 3.3 give the constrained words and wall tableaux. Theorem 3.4 gives the exact network/word normalization; recurrence (17) and Lemmas 3.10–3.11 give the exact enumeration recurrence and prior transformation. Theorem 1.8 establishes the complete Airy Theta scale. Corollary 1.11 establishes the total/maximal ratio limits. Remark 1.12 explicitly distinguishes those from a first-order equivalent.

The d = 3 rate O(n^(-1/2)) used in the report is a quantitative consequence of the *proof* of Lemma 3.24 and the deficit summation in the proof of Theorem 1.9(ii); it is not claimed as a separately stated theorem in that paper. The uniform product is indexed by m = n-1 letters, and the paired class sums contain the constant factor two explained in the report. No corresponding rate is asserted for d >= 4.

Appendix A Tables 3–4 agree with the maximal-network prefixes derived from the recurrence. The one-component results in the paper count a distinct subclass.

## Binary context

Michael Fuchs, Guan-Ru Yu and Louxin Zhang, *On the asymptotic growth of the number of tree-child networks*, European Journal of Combinatorics 93 (2021), 103278. https://arxiv.org/abs/2003.08049

The fixed-d theorem specializes to the binary word family A213863. The present report includes the proof needed for every fixed d rather than relying on a binary analogy.

## Focused newer-source screening

The following newer primary sources were inspected for overlap with the fixed-d >= 3 maximal-reticulation problem:

- Lin, Liu, Liu, Liu and Xin, *Proof of a conjecture on Young tableaux with walls*, arXiv:2601.09551v3, 6 September 2026. https://arxiv.org/abs/2601.09551
- Liu, Wallner and Yu, *A combinatorial framework for the Pons–Batle identity: Young tableaux, lattice paths, and limit laws*, final AofA 2026 Article 13, 13 July 2026. https://doi.org/10.4230/LIPIcs.AofA.2026.13
- Yu and Zhang, *Asymptotic counting of binary phylogenetic networks*, arXiv:2605.23126v2, 13 June 2026. https://arxiv.org/abs/2605.23126
- Fuchs and Yu, *A cube-root phase transition in tree-child networks and the enumeration threshold for galled networks*, arXiv:2608.20860v1, 21 August 2026. https://arxiv.org/abs/2608.20860
- Yu and Zhang, *A short combinatorial proof of the Pons–Batle identity for counting tree-child networks*, arXiv:2609.04979v1, 4 September 2026. https://arxiv.org/abs/2609.04979
- Liu, *Trident tableaux for tree-child networks with one reticulation node: A bijection with two-wall tableaux*, arXiv:2609.28892v1, 24 September 2026. https://arxiv.org/abs/2609.28892

Their exact binary identities, fixed/bounded/sparse-reticulation regimes, or one-reticulation class do not supply the all-order fixed-d >= 3 maximal-count result proved here. No prior positive-amplitude equivalent or all-order expansion in that regime was located in this focused check. This is bounded search evidence, not exhaustive novelty certification.

## Sequence identity cautions

- https://oeis.org/A213863 identifies the d = 2 word count
- https://oeis.org/A213864 is not d = 3: its first terms 1,1,19,1075 differ from 1,1,25,2305, and its prefix exception differs
- https://oeis.org/A213275 varies multiplicity with a different fixed prefix convention
- https://oeis.org/A167484 counts ranked networks, a different object

No OEIS ID was established for the exact d = 3 or d = 4 word or unranked-network count. Direct OEIS JSON search endpoints were unavailable during the focused check, so no claim that an entry does not exist is justified.

## Reproduction and rights

The exact-check inputs are newly derived finite algebraic certificates and recurrence values, not downloaded papers. Source snapshot SHA-256 digests are recorded in `provenance/sources.json` when a local inspected PDF was available. Third-party PDFs are not included in this package. The TeX is standalone and needs no access to those snapshots or to any prior report to compile.
