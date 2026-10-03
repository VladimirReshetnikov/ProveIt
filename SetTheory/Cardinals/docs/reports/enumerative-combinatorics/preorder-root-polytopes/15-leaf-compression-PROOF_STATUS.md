# Proof status

## Established in this note

1. Exact weighted leaf compression (Lemma 2.1): an elementary support bijection with a sum of alternative leaf activities
2. Rank-normalized ULC for every minimum-cover split 1 + (r - 1) (Theorem 2.2): compression followed by the published weighted smaller-shore theorem
3. Arbitrarily weighted matching rank at most three (Corollary 2.3): Kőnig's theorem plus Theorem 2.2
4. Nonnegative activities in the preceding small-rank theorem: delete zero-activity vertices and reapply the positive theorem
5. Weighted real-rootedness for a mixed three-vertex cover (Theorem 3.1): exact coefficient formula, two nonnegative algebraic identities, and a rational interlacing argument

## Imported mathematical input

- Kőnig's matching-cover equality for bipartite graphs
- Matroid basis polynomials are Lorentzian
- Positive coordinate scaling and nonnegative linear specialization preserve the Lorentzian property
- Bivariate degree-D Lorentzian polynomials give binomially normalized log-concavity of order D

The weighted smaller-shore specialization is reproduced explicitly. The real-rootedness proof does not rely on the repository's unrefereed block-stability assertions. Those assertions are cited only to identify the real-rootedness consequence as already obtainable in the repository.

## Exact verification

`verification.json` records all passing checks. The checker independently enumerates supports rather than individual matchings. It checks the weighted polynomial identity, rank-normalized margins, the cubic coefficients and the nonnegative interlacing expressions with integer arithmetic.

## Remaining questions

- General rank-four graphs with minimum cover split 2 + 2
- Whether the first weighted failure is rank four, five or six
- General unit-weight and one-shore rank normalization
- A universal rank-only normalization order for arbitrary weighted support polynomials
- Machine-checked formalization

No global novelty or priority claim is made. The inspected incoming source explicitly leaves arbitrary weighted rank three open; the new theorem resolves that stated local question.
