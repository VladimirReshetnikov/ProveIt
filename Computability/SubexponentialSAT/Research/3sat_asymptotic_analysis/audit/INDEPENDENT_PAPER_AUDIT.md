# Independent source audit: ETH preprint, 2026-10-27

## Scope and provenance
Pinned repository commit: `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`.
Paper source root:
https://github.com/openai/math/tree/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build

This is a source-only mathematical audit, not a complete proof verification, Lean build, executable benchmark, or proof of ETH's status independent of the supplied preprint.

## Baselines that must not be conflated
1. Paper Theorem 1.1, arbitrary fixed-width CNF: polynomial(n,m) times 2^{O_k(n loglog n / sqrt(log n))} bit operations and polynomial space.
2. Same theorem, fixed density m <= Dn: polynomial(n,m) times 2^{O_{k,D}(n / sqrt(log n))}.
3. Rational interpolation in Sections 3--6: exponent rho(n)=n(loglog n)^2/sqrt(log n).
4. Lean endpoint `SqrtLogSpace.exact_count_and_sat` and `compiled_exact_count_and_sat`, as read from source, use `SqrtLog.Statement.runtimeBound`. The exact expansion in `SqrtLog/StatementCanonical.lean` is
   C*(formulaBitLength+1)^d * 2^{A*n*(log(log(n+16)))^2/sqrt(log(n+16))}.
   Thus this reviewed formal endpoint still uses baseline 3, not the paper's stronger Appendix D bound.

Relevant Lean URLs:
https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/Final.lean
https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/StatementCanonical.lean
https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/Main.lean

These are source statements; transitive dependencies and printed axioms have not been kernel-checked by this audit.

## Appendix D proof and actual bottleneck
Theorem D.1 (Boolean tensor contraction) handles O(s) Boolean wires, degree <= ceil(s^{9/10}), precision and truncation <= Cs, and implicit entries computable in polynomial(description size) * 2^{A s^{9/10}} time and polynomial space. Its bound is polynomial(description size) * 2^{O(s/sqrt(log s))} bit time.

Lemma D.2 encodes sparse polynomial queries with s=O(n loglog n); this extra wire count causes the dense-input loglog factor.
Lemma D.3 is collision packing.
Lemma D.4 is the integral Cauchy deformation.
Lemma D.5 is tapered Hermite recovery.

At depth d, there are M<=Cs*8^{-d} wires and u=floor(epsilon*ceil(log2 s)/2^d) retained valuation levels. Each mode weight j has at most 6M/D variables, where D=L/2^{v2(t)}. Tapering gives precision p_t=O(MD/u). Weighted tuple enumeration therefore costs exp(O(sqrt(Mp_t/D)))=exp(O(M/sqrt(u))). Summing along a branch gives exp(O(s/sqrt(log s))).

Checked structurally:
- The complete residue grid makes derivative normalizations have uniform 2-adic valuation.
- Hermite basis inverse power series has integral coefficients; its only dangerous denominators are bounded explicitly.
- Immutable creation-precision tensor descriptions avoid illegitimate precision extension and avoid recursive composition of entry evaluators.
- The initial ring embedding and eventual extraction of base coordinates are compatible with contraction as a polynomial in entries.
- Child graphs retain the maximum-degree invariant and shrink wires by at least 8.
- Depth-first traversal can retain polynomial space despite many branches.
No immediate algebraic counterexample was found in these local checks. This is not certification of all lemmas.

## Barrier for routine mode-count tightening
This is a lower bound for an enumeration family, NOT for SAT or all tensor-contraction algorithms.

Let a mode inventory have at least K variables of each integer weight j in [1,B], with budget P. If K*B*(B+1)/2 < P, then every 0/1 selection of these KB variables is feasible, so there are at least 2^{KB} feasible tuples. The same remains true with an ordinary-degree bound at least KB.

In the parameter regime K=Theta(M/D), P=Theta(MD/u), and D/sqrt(u) sufficiently large, choose B=floor(cD/sqrt(u)) for a sufficiently small fixed c. Then KB=Theta(M/sqrt(u)), while K*B*(B+1)/2 <= P and KB <= M. Thus the simple weighted-tuple universe contains 2^{Omega(M/sqrt(u))} candidates even after enforcing ordinary mode degree <=M. The paper supplies an upper inventory bound, not a lower one on every actual network; therefore this is a warning against deriving an improved universal bound from the same numerical envelope, not a worst-case runtime lower bound for the actual source.

Consequences:
- Merely replacing the partition upper bound by a sharper estimate cannot generally improve the exponent's log-power.
- Adding the global ordinary-degree condition (the product has only M affine factors) alone cannot eliminate this obstacle.
- Faster polynomial-time arithmetic can improve polynomial overhead, not this dominant exponent.
- A stronger universal exponent needs a new precision bound, stronger mode-weight sparsity, or non-enumerative compression/cancellation.
- Raising u beyond Theta(log s) while keeping explicit polynomial packet descriptions is not justified by the current construction.

## Quantitative implementation warning
Appendix D.4.2 fixes epsilon=1/(128*1024)=2^{-17}. Therefore u_0=floor(ceil(log2 s)/131072). When ceil(log2 s)<131072, u_0=0 and the active-call hypotheses u>=1 cannot hold. The proof handles a fixed exceptional range by direct summation. The displayed root condition u>=lambda^{4/5} requires at least lambda>=2^{85}, before accounting for floors or deeper calls. This is emphatically an asymptotic theorem, not evidence of a practical speedup at conventional sizes.

## Safe improvement statements
An implementation of Appendix D would improve the reviewed Lean loglog-squared *certified upper bound* by one loglog factor in the exponent in the general case and two for fixed density, conditional on implementing/proving the paper algorithm. This is an implementation/formalization upgrade to an already published bound, not a new asymptotic theorem beyond the paper.

For arbitrary density, direct clause-network contraction also gives exponent O((n+m)/sqrt(log(n+m))). Racing or deterministically switching between this and the sparse-query algorithm gives the envelope
min{(n+m)/sqrt(log(n+m)), n loglog n/sqrt(log n)}
up to polynomial input factors and appropriate fixed-width constants. This is already implicit in the paper's last paragraph, not novel.

Connected-component or treewidth preprocessing can provide rigorous structural improvements without changing the unrestricted worst-case bound. Such results must state the structural parameter explicitly and cannot be advertised as a globally improved n-only exponent.

## Bit model and parameter cautions
- n is the declared-variable count, not necessarily the number of occurring variables or the encoded input length.
- m counts input clauses, including redundancy before normalization.
- The count has up to n+1 output bits; exact arithmetic is not a unit-cost ring oracle.
- Width k is fixed. Constants may depend on k (and D in the fixed-density theorem), not on growing n or m.
- Explicit polynomial precision and tensor descriptions are essential; materializing truth tables of high-degree implicit tensors would invalidate the claimed running time.
- Bounds of the form 2^{O(f(n))} are upper bounds. A smaller f demonstrates a sharper certified complexity guarantee; it does not by itself prove that a concrete new implementation is pointwise faster than the old one or prove a lower bound for the old code.

