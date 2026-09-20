# Claim and verification status

## Proposed established result

For the fixed point of `0->01, 1->02, 2->0`, the proportions of integer lengths with additive complexity 3, 4, and 5 have the three explicit natural densities in the article. The count at **every** integer cutoff has error `O(N^theta)`, with `theta=log(7/5)/log(beta)`. The article also gives exact rational generating functions for counts at Tribonacci cutoffs, a mean-value limit, fixed-prefix limits, and an interval-count corollary.

The infinite proof is presented in full. The finite computational hypotheses were reproduced and checked exactly by the included verifier. This is therefore a **proposed complete solution of the stated question**, not merely a numerical conjecture or a result only along a subsequence.

## Credit and scope

The possible values and the existence of a 76-state output automaton are already in Popoli–Shallit–Stipulanti (2024), Theorem 18. Their Remark 19 explicitly asks the proportion question.

Abelian co-decomposition and its usefulness for the Tribonacci word are prior work of Turek. The article supplies a specialized independent proof and implementation of the needed recursion. The 76-state machine is independently reconstructed; no identity with the authors' original state numbering or serialized file is asserted.

The package is original work generated for this task; no third-party repository code is bundled.

## Checks actually performed

- Reconstructed all 277 co-decomposition sets and all 56 paired words.
- Reconstructed all 296 reachable legal-language product states.
- Checked the full output-preserving quotient diagram, yielding 76 live states.
- Verified closed-component connectivity and reachability from every live state.
- Verified the exact left and right algebraic eigenvector equations.
- Evaluated the degree-76 integer polynomial at the 76-by-76 matrix and checked all 5776 entries are zero.
- Verified the rational spectral separation inequality at 7/5.
- Independently enumerated all factor sums for every length 1–2048 via the five legal pair images; 93,070,336 windows.
- Compared exact prefix counts with individual evaluations through 100,000 at 301 cutoffs.
- Checked 61 Tribonacci cutoffs against matrix powers.
- Verified cutoff generating functions with recurrence-supported coefficient certificates and exact residue identities.
- Repeated the verifier under optimized Python, where ordinary `assert` statements would be disabled. This verifier uses explicit checks instead.

## Remaining uncertainty

This draft has not been independently refereed or checked in a proof assistant. The implementation and interpreter remain part of the trusted computation. The finite certificates and complete algorithms permit independent reproduction.

The literature audit found no later resolution in the checked sources, but is not a proof of global priority. The selected problem does not match any of the 71 packages in the supplied manifest, as assessed from that manifest's actual descriptions.

## Not claimed

- Optimality of the error exponent or an explicit optimal error constant.
- Solutions for all weight assignments or all substitutive words.
- A general theorem that every additive-complexity sequence has natural densities.
- A solution to the general regularity conjectures discussed in the source papers.
- A proof-assistant formalization, external peer review, or guaranteed historical novelty.
