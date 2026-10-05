# Sources, provenance, and contribution boundary

## Repository source

Repository: https://github.com/VladimirReshetnikov/ProveIt

Inspected revision: `d1680cdfa40c44abf0825416b6f36a3e9ec2662c`

Report:
`SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a189281-path-forest-expansions/article.tex`

Article blob SHA: `73a53d9784260c2f0d083f2baa62a5535f6d6105`

The GitHub connector supplied the report's README, article ranges covering the model, exact profile formula, stable tilings and moment bound, the existing inverse method, and the further-research questions. In particular, the inspected article's lines 2260–2325 contain Section 22 and the questions about growing gaps and sharp short-path effects.

The inspected report has Parts I–III. Part III already proves the directed rational-collapse and integrality result that earlier parts had left conjectural. The present manuscript neither reclaims that result nor assumes a particular guessed recurrence. It uses the repository as a source of the research questions and as a prior-work comparison, re-proving the exact combinatorial inputs used in its new arguments.

## Public primary sources inspected

1. R. Spahn and D. Zeilberger, *Counting Permutations Where The Difference Between Entries Located r Places Apart Can never be s (For any given positive integers r and s)*, arXiv:2211.02550v3, 6 December 2022.
   https://arxiv.org/abs/2211.02550
   https://arxiv.org/pdf/2211.02550
   The matching-of-tilings formula was checked in the paper, including the rendered page containing the formula. This formula is credited prior work, not a novelty claim.

2. R. Tauraso, *The dinner table problem: the rectangular case*, Integers 6 (2006), A11; arXiv:math/0507293.
   https://arxiv.org/abs/math/0507293
   Used for the fixed-gap dinner-table context and comparison with known fixed-gap asymptotics. No theorem in the new local-cluster proof depends on importing an unchecked result from this paper.

3. OEIS A189281.
   https://oeis.org/A189281
   The directed gap-(2,2) permutation avoidance sequence. Initial values were used for twelve small checks jointly with A110128. Its fixed-gap expansion is not the new target here.

4. OEIS A110128.
   https://oeis.org/A110128
   The absolute gap-(2,2) permutation avoidance sequence. The same provenance distinction applies.

5. NIST DLMF, Section 5.11.
   https://dlmf.nist.gov/5.11
   Standard Stirling expansion and fixed-order remainders for the inverse section.

6. NIST DLMF, Section 4.13.
   https://dlmf.nist.gov/4.13
   Definition and asymptotic context of the Lambert W function.

## What the manuscript adds relative to the inspected report

- Arbitrary-forest uniformity, including linearly many bounded components and vanishing leading density.
- The exact finite locality cutoff at each inverse-n order, a finite coefficient formula, and a constructive proof that the cutoff is necessary among actual forests.
- Highest-path sensitivity, reciprocal-integer correction boundaries, and an explicit cancellation at sqrt(2)-1.
- The leading absolute-model difference produced by one fixed short path, plus the directed cancellation and exact one-target-path shape-independence formulation.
- A moving-ray specialization of index inversion, exact moving-ray coefficients, and reproducible certificates.

The exact profile identity, the elementary factorial-moment bound, the use of formal connected graph expansions, Stirling's formula, and Lambert-W inversion are not advertised as newly invented tools.

## Non-claims and remaining scope

This was a targeted source audit, not an exhaustive bibliographic or priority search. The manuscript supplies ordinary mathematical proofs of its stated results, but historical novelty remains subject to independent expert assessment. The source report and this article are AI-assisted and unrefereed. No Lean or Rocq proof was produced, and no repository-wide build was run.

The logarithmically growing shortest-path problem, a full exponentially improved transseries, the particular guessed OEIS recurrence operators, and general multigap constraints are not solved here. The directed fixed-short-path theorem only proves cancellation at the displayed absolute-model order; its first nonzero general term is explicitly proposed as further research.

No full third-party paper or sequence b-file is bundled. No OEIS submission or GitHub modification was made.
