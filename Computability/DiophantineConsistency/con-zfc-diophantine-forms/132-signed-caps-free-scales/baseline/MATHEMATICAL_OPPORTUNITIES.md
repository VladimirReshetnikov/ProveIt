# Precise mathematical opportunities and proof cautions

All paths below are relative to an extracted incoming package's inner root.

## 1. Pool all requested Pell indices behind a single cap

Source: Shared Pell Bound 261, `portable/CAP_THEOREM.md`.
For W≥3, A−1>W³, distinct requested positive indices k_i<W with m≤W−2, retain one full index certificate V=Y_W(A), and only the principal norms for the other pairs:

x_i²−(A²−1)y_i²=1,
V=W+1+s+Σ_i y_i,
Σ_i(y_i−k_i)²=(A−1)q,

with all witnesses nonnegative. Classify y_i=Y_{j_i}(A); the cap gives 0≤j_i<W. Since Y_j(A)≡j modulo A−1, the last row makes A−1 divide E=Σ(j_i−k_i)², but E≤(W−2)(W−1)²<W³<A−1. Therefore E=0 and every index is correct.

Completeness is not just individual index existence. Canonical values satisfy ΣY_{k_i}≤mY_{W−1}; Y_W>(2A−1)Y_{W−1} ensures the aggregate slack is nonnegative. The single full cap certificate must be preserved, including its condition W≤V, here supplied by the aggregate row. Its comparison/congruence witnesses cannot be omitted merely because the other seeds are pooled.

Most promising combination: use this cap in the six-exact-power plus modular-numerator architecture. The cap theorem needs only a lower bound on A, not that A itself be the abscissa of the scale Pell equation. Thus the cofinal scale A=L+σ from the residue compiler can replace the old fixed A scale. W must contain every independent modular index as well as the exact-power atoms; otherwise j_i/k_i bounds have not been proved. A bound on requested semantic outputs alone is insufficient.

## 2. Six exact powers, with all numerator powers replaced by Pell residues

Sources: Residue Compiler, `proofs/MODULAR_NUMERATORS_PROOF.md`; Shared Binomial, `direct/PROOF.md`, §§4–5.
Let b=q+1. Choose a common modulus M divisible by every exact digit modulus q^(k+1) and divisibility-digit modulus Nq^k. Impose

2Ab=b²+1+Mh.

Then R_n=X_n(A)+(b−A)Y_n(A)≡b^n modulo M. It is strictly positive for n>0, since X_n>(A−1)Y_n and b=q+1. Consequently the Euclidean quotient witnesses in natural digit rows stay nonnegative.

Completeness requires choosing A in a residue class after q and M have been fixed. Use
L²−W³(W+2)Z²=1, Z≥1, A=L+σ.
Pell classification gives L>(W)^W, while σ supplies a cofinal A. Since gcd(b,M)=1, gcd(2b,M) is 1 or 2; in the latter case b is odd and b²+1 even, so the linear congruence for A is still soluble. Choose A sufficiently large in that class, then regenerate all private Pell certificates. Do not freeze the original A and assert its congruence can always be imposed.

For Shared Binomial, six exact powers are V=(F²+1)^t, N=B^K, q=N^K, D_t=q^t, D_y=q^(y+1), D_x=q^(x+1), with D_{t+1}=qD_t. Its printed M=qD_{t+1}D_xD_y is conservative. Residue Compiler proves before factorial/binomial semantics that raw endpoint and ceiling rows force x>t+1 and x>y+1, allowing M=Nq^(x+1). That dominant-denominator reduction is a promising cross-combination. Recheck it for any changed signed source or changed y definition.

## 3. Reuse the same binomial for factorial and reciprocal CRT

Source: Shared Binomial, `direct/PROOF.md`, §§2–3.
For t≥6 and F≥1,
F=ceil((F²+1)^t / binom(F²+t,t)) iff F=t!.
The binomial B=binom(F²+t,t) is also the reciprocal CRT product. Its single exact-digit certificate can serve both roles.

A noncircular radix is essential. One delivered construction takes B=b_0+2, R=2+t+x+y+F, K=2R, N=B^K, q=N^K, V=(F²+1)^t. It proves q≥2^(4R²) and binom(F²+t,j)≤(R²+R)^t<q before assuming F=t! or interpreting B. The ceiling rows V+B=BF+r+1 and B=r+s+1 then force F≥1 and the factorial fixed point. Assuming B has its intended value before proving the carry bound would be circular.

Another delivered approach selects actual CRT representatives first, puts S equal to their sum, and uses q=N(V+1+S)^K. It removes the former S≤9N² row. Its carry proof uses binom(J,j)≤(S+1)^(ell*k)<q, not an unproved bound on each representative. This can be combined only after specifying the correct choice order: outer semantic values, CRT representatives, q, then A and private Pell witnesses.

## 4. Even-index savings are source restrictions, not free domain weakening

Source: Residue Compiler, `proofs/PARITY_PROOF.md`; Unified Binomial / Even Indices, direct proof and source.
The sparse source arranges each tested exponent even and positive through literal identities and parity-compatible CRT choices. This can eliminate Y≥k slack coordinates by ruling out the fundamental Pell pair Y=1. The common comparison ordinate must still be positive and divisible by every seed Y², not merely Y. A product witness that can vanish does not establish this.

For signed variants, prove sign and nonzero facts before using any Pell interpretation. The delivered 442-integer source is a strong existing benchmark, not a newly available round-16 improvement. Positive, nonnegative and unrestricted-integer domains must be reported separately.

## 5. Compact integer carriers: combine proven ideas, preserve signs

Source: Shared Binomial, `lowops/PROOF.md`; Unified Binomial, `norm_weak/DEGREE_PROOF.md`.
The 111-operation single product equation has the form
δ Z²−S² P D_f C_y=0,
where P,D_f,D_a=δC_y are pairwise coprime and P≡1 modulo 4. A nonzero rational square equals P D_f D_a; extracting absolute squares and using mod-4 then recovers P>0. Only afterward may D_f>0 and D_a>0 be inferred.

The strong ordinate is saturated using a square root p_0²=P: I=U p_0 and T_old=p_0 T. In completeness choose the guard first, one fixed strong pair next, and the auxiliary residue last. The supported-modulus interpolation theorem must apply to that fixed strong pair; silently changing it afterward invalidates the argument.

A shorter first-index modulus 4q^4 replaces XY in the 112-operation degree-882 variant. The proof requires 4q^4 | 2XY² and 4q^4>3R+1. It restores the old h only after signed rank folding. Neither modulus divides the other in general. Swapping the literal h expression without re-proving the negative orientation exclusion is not justified.

Attribution and bound: current best measured incoming weak centered norm is already degree416 at125 operations, and ordinary centered is464 at119. A new440/126 or464/122 claim is therefore not frontier progress. Combining shorter-index support with the weak carrier may still be useful, but needs its own leading-form and signed-folding proof.

## 6. Universal reporting cautions

- Fixed coefficient ports are fixed numerals, not quantified variables; retain and authenticate the entire matching tuple, including already-shifted MF.
- Circuit operations, degree, monomials, coefficient height and coefficient bit length are different objectives. One does not subsume the others.
- A DAG degree propagated by maxima can overestimate because of cancellation. Preserve exact leading-form proofs at the authentic fixed coefficients, not just random modular rays.
- Independent finite expansions check literal syntax. They do not prove the unbounded Pell, CRT, factorial, calculus/refutation or Con(ZFC) interpretations.
- All imported consistency conclusions remain composed with the named ordinary calibration. No new proof-assistant endpoint or proof of consistency has been established by this review.
