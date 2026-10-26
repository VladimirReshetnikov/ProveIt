# Arithmetic findings at 9d9d1123b39927d30363f1dcd53c23f0575c30ee

## A. Replace quantitative dummy safety by exact cancellation of equal boundary carries

**Status:** rigorous mathematical adaptation; all four standalone Lean core lemmas compiled successfully without `sorryAx`. No full production overlay has been built. The new idea is the deletion of the quantitative no-wrap proof dependency, not telescoping or generic update linearity themselves; those are assumed available from earlier packets.

### Existing targets

- `CurrentDummySafety2011.lean`: `kernel_upper_bound` (38), `safe_increment_bound` (84), `safe_increment_div_bound` (110), `nonwrap_of_short` (121), `normalized_nonwrap_of_safe` (139), `safe_normalized_increment` (154), `exists_safe_normalized_increment` (169), `safe_rank_decrement` (193).
- Existing source mutation: `CurrentDummyMutation2011.source_increment` (113) and `normalized_increment` (126). The latter currently needs `hnowrap : F + (K+2^W) delta < rho^m-1`.
- Existing boundary result: `CurrentWordTopBounds2011.top_carry_digits` (190) and `last_top_val` (212): the actual outgoing carry at the canonical last index is zero for every Boolean assembled word, independently of high masks/matching/controller premises.
- Literal stencil identity: `CurrentKernel2011.convolution_terms` (494), with `K = rawWord radix` (105-106).

### Exact mathematics

Write m=2011N, rho=2^47, W=47*2011*s, p=977+2011*j.val, and delta=rho^p. Let raw,d,k and raw',d',k' be the old/new raw, normalized-digit and carry arrays. The physical update changes one initially-zero dummy to one. Booleanity is retained, so the existing top-carry theorem applies to both arrays.

For a finite carry sequence q_0,...,q_m and equations a_i+q_i=d_i+rho*q_(i+1), exact weighted summation gives

    sum(a_i rho^i)+q_0 = sum(d_i rho^i)+q_m rho^m.

In a cyclic normalization q_0=q_m=k(-1). For this actual assembled word, k(-1)=0, and likewise for k'. More generally only equality of the two boundary carries is needed. Consequently, any exact raw-word increment is the same exact normalized-word increment.

The perturbation polynomial is a monomial times the fixed kernel plus the temporal monomial. All kernel exponents e satisfy e<=2020. From j.val+1<N and j.val+s<N,

    p+e <= 977+2011*j.val+2020 < 2011N,
    p+2011*s = 977+2011*(j.val+s) < 2011N.

Therefore none of the perturbation monomials wraps around m. Its ordinary folded evaluation is exactly

    rho^p (K+rho^(2011s)) = delta (K+2^W).

This is valid even when the original unperturbed stencil crosses the cyclic boundary; only the DIFFERENCE has to be supported below m. Convolution is additive. Apply `rotation_whole` separately to the two Boolean assemblies to reduce each phase-zero rotation to an ordinary shift; do not assert binaryRotation is globally additive on arbitrary numeric arrays. Thus

    word(raw') = word(raw)+(K+2^W)*delta.

Boundary-carry cancellation now yields F'=F+(K+2^W)*delta directly. No numerical estimate of K, F or the increment enters this proof.

### Integration without a circular proof

1. Add the exact folded perturbation equality below the current safety endpoints, using `convolution_terms`, update-as-addition, and the two exponent inequalities.
2. Instantiate the assumed finite telescoping contract, or a small exact (not modulo) version, with incoming carry q_i=k((i:ZMod m)-1). `q_(i+1)=k(i)` is cast normalization; q_0=q_m=k(-1).
3. Apply `top_carry_digits` at j=N-1 to old and new normalization facts. `last_top_val` identifies the canonical last index.
4. Derive `safe_normalized_increment` directly. Do NOT invoke old `normalized_increment` or `normalized_nonwrap_of_safe` in this derivation.
5. Obtain a normalization of the updated Boolean word and derive a nonwrapping consequence WITH `hj : dummy j = 0`. The existing public `normalized_nonwrap_of_safe` omits `hj`, so its unchanged broader statement does not follow directly this way. All three actual mutation/existence/rank consumers have `hj`; the stronger compatibility theorem must be retained separately or re-proved independently.
6. Existing `exists_safe_normalized_increment` and rank-decrement endpoints then consume the exact equality.

### Public theorem compatibility correction

The existing `normalized_nonwrap_of_safe` has no unused-dummy premise. Do not advertise automatic deletion of its proof: if the original dummy is already 1, updating it to 1 does not create the required increment. All three current real mutation/rank clients have `hj`, so the narrower exact argument still removes the numerical chain from their proof dependency. Quantitative helpers also occur in `CurrentDummySafety2011Checks` and require an explicit API/check decision.

An optional independent proof of the broader theorem uses a fresh identically-zero dummy map and its 0-to-1 update. Exact conservation gives F1=F0+Delta, hence Delta<=F1<rho^(m-1). Together with the original F<rho^(m-1), a sum-of-two-short-words bound gives the original inequality for rho=2^47. This requires two auxiliary normalizations and has not been compiled or measured.

### Scope, limitations, and likely payoff

This retains the existing interior conditions, Boolean controls, whole-field temporal displacement, original raw kernel, ordinary rank formula, and no-new-equation policy. It does not claim arbitrary dummy positions, arbitrary fractional phases, or arbitrary normalized words have equal boundary carries. If boundary carries change, the missing term is a multiple of rho^m-1 and ordinary increment can fail.

The numeric safety chain contains approximately 100 source lines, but no net line-saving claim is made without implementing the cyclic adapter and exact perturbation proof and deciding which exported quantitative bounds to keep. The robust benefit is removal of an entire family of numerical proof obligations from the mutation/rank endpoint. Do not count multiple dummy batching as another idea: the newest additional-certificates packet already advertises generic batching.

### Novelty screen

- Packet j already proposes exact cyclic telescoping and canonical carries: assumed applied.
- Incoming `lean-proof-simplifications-2026-10-26.zip`, section C, already proposes local carries between zero boundaries: assumed applied.
- Incoming `proveit-lean-additional-certificates-2026-10-26.zip`, section C, explicitly retains `F+A*delta < modulus` for normalized transport.
- None of those derives this actual nonwrapping conclusion from equal boundary carries plus no-wrap perturbation support. Independent novelty audit accepted this precise residual deletion.

## B. Replace the shifted-numerator chain by one discrete endpoint envelope

**Target:** `FreeCarrierRatio.shifted_Q_bounds`, starting at line 275. Exact original hypotheses and conclusion retained. Standalone exact-signature Lean proof in `ShiftedNumerator.lean` compiled successfully with Lean 4.32.0; its printed axioms are only `propext`, `Classical.choice`, and `Quot.sound`. See `ShiftedNumerator.log` and `ShiftedNumerator.json`.

Let

    Qstar=J(W^2+1)+Q, J=4A-5, Q=3WC-2(W^2-1),
    T=8D^2-4D-1.

The 39-line original theorem makes separate estimates Q<3D, Qstar<(4A+3)D, 9D<=kT, 9DA<=kTG, kTG<=kTGH and a final comparison. Replace this with the tighter envelope

    Qstar <= (4A-4)D+1.

Indeed W>0 and W<A with A^2<=D imply W^2+1<=D over the integers. Also C^2<D and (W-C)^2>=0 imply WC+1<=D. The coefficient 4A-7 is nonnegative because A>=2. Since

    Qstar=(4A-7)W^2+3WC+4A-3,

substituting both upper endpoints gives the envelope. Positivity follows immediately from the same expression.

The sole scalar denominator certificate is

    3T-4D = (D-1)(24D+8)+5.

Thus, for D>=1 and A>=2,

    (4A-4)D+1 < 3TA <= kTGH.

The final inequality is ordinary monotonicity using k>=3, G>=A, H>=1 and T>=0. The prototype uses explicit nonnegative product witnesses, so `nlinarith` is not asked to discover the factorization or nonlinear products.

This is a source-specific endpoint argument, not a claim of new general polynomial-majorant automation. No helper/API or executable expression is added. Independent audit found no exact Qstar/shifted-numerator proposal in the placed or incoming corpus. The old positive quadratic margin theorem concerns a different proof obligation and remains assumed available.

### Checked patch accounting for B

The original complete theorem occupies 39 physical lines; the replacement occupies 29. A patch preserving file whitespace changes FreeCarrierRatio from 501 to 491 lines, with zero helper or production import overhead. This is static patch accounting, not a whole-module validation claim. The interval envelope is tighter than the existing one; no optimality claim is made.

### Validation outcome

Both standalone Lean files completed with exit code 0 using Lean 4.32.0 and the existing Mathlib cache. Neither uses `sorry`, `admit`, `axiom`, `native_decide`, or trusted external algebra. The boundary file validates four generic lemmas; production ZMod/raw-convolution adapters remain proposed. The shifted-numerator file validates the exact theorem signature and complete replacement proof; the complete production module was not rebuilt. After the successful check, a documentation comment in the latter changed from “sharp” to “discrete”; no proof code changed.
