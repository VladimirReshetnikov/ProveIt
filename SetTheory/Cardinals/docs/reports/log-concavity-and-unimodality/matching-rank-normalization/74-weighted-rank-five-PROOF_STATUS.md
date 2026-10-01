# Proof status

## Universal results established

1. The rank-(q+2) left marginal is Lorentzian for every bipartite graph with a displayed 2+q vertex cover and fixed positive right activities
2. Every minimum cover meeting a shore in at most two vertices gives weighted rank-normalized ULC
3. Every weighted matching-support polynomial of rank at most five is rank-normalized ULC; nonnegative activities are handled by deleting zero-activity vertices and using the surviving degree
4. The first unrestricted weighted failure rank is exactly six; explicit counterexamples exist at every higher rank
5. The forced-two-left residual is ULC_q; the all-core constant 2q/(q-1) is sharp
6. Both star-core transfer arguments and quantitative strict-scaling results hold with their stated hypotheses
7. First-gap equality for positive weighted graphs is exactly a union of stars with equal weighted edge totals

## Proof inputs

The central external input is the published Lorentzian theorem for matroid basis polynomials and its substitution, derivative and closure properties. The independent transfer appendix also uses the published homogeneous stability-preserver theorem. The geometric corollary uses Davis–Kohl Theorem 3.10 and Lemma 3.11, with the augmented graph and unit-activity hypotheses stated explicitly. The smaller-shore and singleton-cover reductions are proved in the report.

The full lift is an explicit transversal matroid. Its six disjoint basis categories are verified symbolically in the proof and independently checked by Boolean basis enumeration. The rank-five quartic appendix uses a finite exhaustive exact coefficient table plus displayed sums of squares; its complete verifier and data are included.

## Verification scope

Exact tests supplement universal proofs. Finite-field basis realizations, fixed-seed weighted examples and finite population grids are not claimed as universal proofs on their own. The mathematical arguments and final source were independently reviewed; no substantive gap was found. The results have not been Lean-certified or peer reviewed.

No global priority claim is made. The report does not settle unrestricted higher-rank unit-weight or one-shore-only weighting questions, and it does not identify arbitrary matching-support polynomials with arbitrary Ehrhart h-star polynomials.
