# Audit of the cited Anthropic formal proof

## Snapshot and scope

- Repository: https://github.com/anthropics/formal-math
- Requested PR: https://github.com/anthropics/formal-math/pull/31
- Requested and actual PR head: `1a6eee293b9e00cb432eef6018a21f523623a9af`.
- PR state: merged at 2026-10-27 03:07:22 UTC (2026-10-26 20:07:22 America/Los_Angeles).
- Merge commit: `16a5ce41304fcdaea4e0be7c132e1c361dc26da5`.
- PR title: Add eth: paper and Lean 4 formalization of "A 2^o(n) Time Algorithm for 3-SAT".
- 1,063 changed files, 153,191 added lines; do not present this audit as a complete manual proof review.
- Source acquired through the selected GitHub plugin, followed by a public archive of the exact SHA for local read-only inspection. The archive is retained locally. GitHub/raw open through the web-search tool returned DisabledError; the GitHub plugin and archive access succeeded.

## What the top-level propositions actually say

`eth/MainResults.lean` imports only Mathlib and defines the statements without proofs. Its top-level counting proposition is

    exists (M : TM2ComputableAux Bool Bool) (C : Nat),
      (forall i, Finite (M.tm.Gamma i)) and
      forall (k n : Nat) (phi : CNF n),
        1 <= k -> IsKCNF k phi -> 2 <= phi.length -> 4 <= n -> AllOccur phi ->
        CountsWithin M k phi (timeMin C k phi.length n).

The time is floor(2^{C min(km/sqrt(log_2 m), k^2 n log_2 log_2 n/sqrt(log_2 n))}). For the user's exclusive scope k=3, this gives a uniform, deterministic exact #3-SAT algorithm, hence 3-SAT decision, in

    2^{O(min(m/sqrt(log m), n log log n/sqrt(log n)))}.

The machine and constant precede k and the formula; this is genuinely uniform, stronger than just for every delta there exists a different 2^{delta n} algorithm. All stack alphabets must be finite. Time counts steps of Mathlib's deterministic finite-stack machine, not an arbitrary unbounded arithmetic operation. Input and output are explicitly binary words.

`IsKCNF` means every clause has length at most k and the clause list is duplicate-free. A clause itself may repeat a literal, be empty, or contain a variable and its negation. Different literal orderings count as different clauses. For k=3 the number of distinct clause lists is at most (2n+1)^3, ensuring input length polynomial in n. Removing duplicate clauses costs polynomial in the input length; a bound in n alone cannot include reading arbitrarily many repeated input clauses. MainTheorem is a promise theorem for n>=4,m>=2, every variable occurring; elementary special cases and the frontend of NamesInOrder cover arbitrary names/unused variables with polynomial overhead. Unused variables multiply exact counts by 2^{N-n} but do not affect decision.

`ETHIsFalse` is not s_3>0, where s_3 is the infimum over exponents admitted by machines. `Solution.lean` proves it by deriving it from the uniform main theorem, and separately states the exact main theorem as an alias for `CountedRoute.mainTheoremHolds`.

## Proof route and accounting

`Solution.lean` lines 40 and 44 are the closed theorems; `CountedRoute/Main.lean` lines 86--92 close the counted-recursion chain. The route is

1. ExplicitCost.cliqueMachine on the Appendix B pieces;
2. CountedInstance: the recursion meets the quantitative clique hypothesis;
3. CountedToPadded and QueryMachines bridge counted operations to padded machines;
4. ThmVariables and MainRoute transfer the clique rate to variable/clause #SAT bounds;
5. MinOfBounds alternates the two exact counters;
6. NamesInOrder gives the general formula frontend;
7. Wrap derives a 3-SAT decider and the refutation of ETH.

The sharp numeric constant of a word-RAM exponent is NOT certified by the final statement. Appendix E pp.43--44 and Solution.lean explicitly say that one intermediate step may be a polynomial-time computation on its state, state size is bounded by operation budget, and the final simulation can introduce an unspecified constant power. Alternation and choice also cost a constant power in this particular formal proof. These change the unspecified C, while preserving the claimed asymptotic order. Do not use this proof to validate a different proposal's claimed leading constant (for example 29.8116).

## Verification evidence and limits of this audit

The exact requested SHA has successful GitHub Actions run
https://github.com/anthropics/formal-math/actions/runs/40440389861
and job
https://github.com/anthropics/formal-math/actions/runs/40440389861/job/121979112896 .

The API reports success for `verify (eth)`, including both steps
- `lake build (no sorry outside the comparator challenge files)`;
- `Palomar bar (comparator accepts every declared configuration)`.

Metadata is in `ci_evidence.json`; step evidence is in `job_steps.json`. A local source scan finds `sorry` only in the two deliberately unproved Challenge.lean declarations; no other `sorry`, `axiom`, `admit`, or `unsafe` occurrences were found in Lean source. That is a static check, not a kernel rebuild. Lean/lake are unavailable locally, so no fresh rebuild was performed. The README prescribes Lean and Mathlib v4.33.1 plus `lake build` and PrintAxioms. Appendix E reports leanchecker and nanoda verification. The local audit checks the statement and important proof interfaces, not every one of the 1,050 Lean modules.

## Where the quantitative losses arise

Appendix A derives e_l = Theta(rho^l) and log K_l = Theta(2^l). Consequently e(K)=Theta((log K)^{-alpha}), alpha=log_2(1/rho). Appendix B uses partition-graded Heisenberg operators to get rho=1/sqrt(2), hence alpha=1/2.

Appendix D uses a different #SAT network from the naive clause-node one. After sparsification with maximum occurrence Delta, it has U=O(k n log Delta). The logarithm pays for O(n) marked clause/check incidences selected from O(n Delta log Delta) possibilities. Delta is polynomial in 1/e for fixed k, so log Delta=Theta(log log n), giving the extra loglog factor. Merely changing constant cutoffs or selecting checks randomly does not remove that cost. Even reducing count precision to one bit leaves Theta(n) parity checks in the existing union-bound scheme, so it does not automatically reduce the mark budget to o(n).

A promising but still unproved route exposed by Appendix H is a replacement graded-operator decomposition with log(dim V_E)=Theta(E^alpha) for alpha<1/2, while retaining polynomially many pieces, effective two-direction factorizations, and the required scalar identity. Its formal cost balance would give rho=2^{alpha-1} and clique exponent (log K)^{-(1-alpha)}, stronger than 1/2. No such construction is established here.

## A rigorous obstruction to a tempting replacement

One cannot obtain that improvement simply by retaining only Heisenberg modes in a sparse set, such as square-indexed modes, while reusing the locality proof of Lemma 9. The following elementary lemma pinpoints the failure.

Let S be a subset of the positive integers. Set a_0=0 and a_n=n*1_S(|n|) for n!=0 (so a_-n=-a_n). Define the scalar formal distribution

    C_S(z,w) = sum_{n in Z} a_n z^{-n-1} w^{n-1}.

If for some integer H>=0 one has (z-w)^H C_S(z,w)=0, then S is either empty or all positive integers.

Proof. The coefficient of z^{H-m-1} w^{m-1} in the product is the Hth finite difference

    sum_{j=0}^H (-1)^j binom(H,j) a_{m-j}.

Vanishing for every m says that the doubly infinite rational sequence a_m is a polynomial in m of degree less than H (the standard finite-difference/Newton interpolation identity). If S has infinite complement, this polynomial has infinitely many positive integer zeros, so it is zero and S is empty. If S has finite complement and is nonempty, a_m=m for infinitely many m; hence the polynomial is m identically and S is all positive integers. This also treats every nonempty finite S. QED.

The commutator of the truncated/sparse Heisenberg current is exactly C_S. Lemma 9's proof uses clearing by a finite power of z-w, so it cannot survive any proper mode deletion unchanged. Passing to modes divisible by a fixed d permits multipoint locality (z^d-w^d)^H instead, but just rescales partition weights: log p(E/d)=Theta(sqrt(E/d)), with the same doubling ratio sqrt(2). This obstruction is scoped to this direct truncation, not a lower bound against all possible decompositions or SAT algorithms.

## Pinned citation targets

- Main statement: https://github.com/anthropics/formal-math/blob/1a6eee293b9e00cb432eef6018a21f523623a9af/eth/MainResults.lean
- Closed proofs: https://github.com/anthropics/formal-math/blob/1a6eee293b9e00cb432eef6018a21f523623a9af/eth/Solution.lean
- Main chain: https://github.com/anthropics/formal-math/blob/1a6eee293b9e00cb432eef6018a21f523623a9af/eth/proof/maintheorem/CountedRoute/Main.lean
- Paper (Appendices A, B, D, E, H): https://github.com/anthropics/formal-math/blob/1a6eee293b9e00cb432eef6018a21f523623a9af/eth/paper.pdf
- README/build instructions: https://github.com/anthropics/formal-math/blob/1a6eee293b9e00cb432eef6018a21f523623a9af/eth/README.md
