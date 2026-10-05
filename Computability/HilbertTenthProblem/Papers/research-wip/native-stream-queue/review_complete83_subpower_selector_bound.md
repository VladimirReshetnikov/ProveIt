# Independent proof-only review of the subpower selector bound

**PASS.** The complete five-section note was read and independently challenged; no correction is requested.

Reviewed author file: `complete83_subpower_selector_bound.md`, 6657 bytes, SHA256 `3c52050218676fa59fdd83f60699e0d884b1e885e16cc3864146d6dd66010eb4`.

The two cited dependencies were independently authenticated against immutable Git bytes at commit `006b3beab45d94d748da52f3a3b9b1c529240b2c`, under `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/`. They also match the inert local copies:

| File | Bytes | SHA256 |
|---|---:|---|
| complete83_fixed_prime_quotient_carries.md | 13710 | 53ed811331899dba52536c9946cfe370888ac8826376351800d785f87549cd46 |
| complete83_source_coupled_input_lifting.md | 14049 | 822d192578f379e1e81a00caafbb3612db24989902411748f35ee23343d5934f |

For N>1, invertibility of the affine slope makes each squarefree divisibility condition one residue class. Its interval count has error strictly less than1. Inclusion-exclusion therefore has total absolute error less than2^omega(N). The proposed length `floor(N*2^omega(N)/phi(N))+1` gives a main term strictly larger than that error bound. N=1 is correctly treated separately with length1.

The comparison with the preceding five-free square-root bound is exact. In the prime-power expression for `phi(N)/(2^omega(N)*sqrt(N))`, every prime at least7 contributes at least1, while the possible prime3 contributes at least1/sqrt(3). Taking floors preserves the resulting length inequality. Thus the new index range is no larger than the old one; it preserves all original congruences, exact depths, explicit positive-slack threshold and subsequent odd input budget. This argument does not assume the new selector is itself below Q.

For every epsilon>0, the product `N*2^omega(N)/phi(N)=product_(p|N)(2p/(p−1))` is at most `C_epsilon*N^epsilon`: absorb finitely many small primes into the constant and compare every remaining factor with p^epsilon. Prime powers cause no problem because the product depends only on the prime support and the radical is at most N. This uses no prime-distribution or unproved short-gap estimate.

With the compiler fixed, the inherited modulus satisfies `M=O(Q*n³)` and `N=A_out<2Q`. Hence `z<=M*L(N)=O_epsilon(n³*Q^(1+epsilon))`; multiplication by fixed K yields the same bound for F. Choosing epsilon=delta/2 and absorbing the fixed constants and n³ into the remaining exponential factor proves the stated eventual `z,F<=Q^(1+delta)` on either inherited unbounded subsequence. It is an upper bound only, equivalently a limsup at most1; no matching lower bound or asymptotic equality is used.

The unchanged binary criterion for enlarged z remains open. The result does not establish an actual complete source zero, a rejected-input example, a circuit saving or universal83. The previous source/native/Pell conclusions are inherited at their accepted scopes; this review does not repeat a full83 source audit.

Only fresh read-only byte and hash checks were performed. No supplied, archived, frozen, committed or copied predecessor program was run or imported. No numerical sample, source-array evaluation or huge binomial/Pell construction is used as proof evidence.
