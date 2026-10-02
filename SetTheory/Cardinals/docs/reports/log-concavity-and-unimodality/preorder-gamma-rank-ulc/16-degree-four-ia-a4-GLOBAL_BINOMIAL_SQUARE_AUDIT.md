# Global integer-population gap-two certificates for templates 10 and 34

## Verdict

APPROVED: the second order-four Newton inequality 4γ_2²−9γ_1γ_3≥0 holds for every nonnegative integer population of both fifteen-type templates 10 and 34.

These two proofs cover respectively 6,298 and 4,672 previously outstanding representative-face tasks, a total of 10,970. Their third Newton gaps remain open. They therefore do not increase the number of fully approved four-attachment templates beyond the separately approved 33 small legal-type families.

## 1. Meaning of the certificate

Write B_q(n)=∏_i binom(n_i,q_i). A listed square is

B_m(n) · (Σ_q c_q B_q(n))².

It is averaged uniformly over all recorded variable actions of the template and multiplied by its listed positive rational weight. The final identity adds a nonnegative linear combination of binomial terms B_q.

This is an unscaled identity for the exported gap 4γ_2²−9γ_1γ_3. There is no factor 36, 576, or 720 in this certificate family. Its multiplier B_m is a binomial polynomial, not an ordinary monomial.

For n∈N^15, every B_m(n) is nonnegative; the squared expression is nonnegative; positive weighting and averaging preserve nonnegativity. The remainder is also nonnegative. This argument is specific to integer populations. A binomial multiplier need not be nonnegative at arbitrary fractional populations, so no whole real-orthant conclusion is asserted.

## 2. Independent exact multiplication and averaging

The checker `audit_global_binomial_squares.py` reads the complete previously audited unscaled gap arrays. Their hashes, and the symmetry-action hashes, must agree with the prior face-orbit receipt.

To multiply binomial basis polynomials, the checker does not use the producer's factorial formula. It enumerates all ordered subset pairs A,B of a t-element set with prescribed cardinalities a,b and A∪B equal to the full set. Their integer count W(a,b,t) gives the exact identity

binom(x,a)binom(x,b)=Σ_t W(a,b,t)binom(x,t).

Tensor products give the multivariate multiplication. The verifier expands each complete root square in this basis and then multiplies by B_m. It explicitly applies every variable-action image and divides by the group order. No orbit-aggregated linear-programming equation or floating-point residual is substituted for the full coefficient identity.

All root coefficients and outside weights are parsed with exact unbounded-integer rational arithmetic. Every square weight is strictly positive; every remainder weight is nonnegative. Exponent domains and total degrees are checked. The complete final sparse coefficient map, including exact cancellation of zeros, must equal the entire integer gap array.

The target gap's invariance under each variable action is also rechecked directly. Positivity of each image is valid in its own right because a coordinate permutation preserves the integer population domain.

## 3. Exact counts and remaining scope

Template 10 has group order six and 321 positive square orbits. Template 34 has group order eight and 220 positive square orbits. The checker expands all 3,686 individual square images, together with every nonnegative binomial remainder term. Both full rational coefficient identities pass.

This proves gap two on every face of these templates at once, including zero populations. Actual-degree rank-ULC for either entire template still requires its third gap, with the already established first-gap and lower-degree conventions. The audit does not turn a global one-gap certificate into a complete-template theorem.

## 4. Reproduction

Run `audit_global_binomial_squares.py` with the two immutable files `global_integer_gram_zeroaware_10.json` and `global_integer_gram_zeroaware_34.json`. The checker uses only the Python standard library and imports no producer code.

`global_binomial_square_audit.json` records exact counts, every formerly outstanding face mask now covered, all source hashes, the checker hash, and runtime. Input hashes are compared before and after execution. An immutable copy of this two-identity receipt is retained as `global_gap2_templates10_34_receipt.json` so later incremental runs cannot erase its record.

## 5. Additional approved global gap: template 2

The same independent checker subsequently verified template 2's unscaled global second Newton gap. Its averaging group has order two and its certificate has 85 positive square orbits, together with the nonnegative binomial remainder. The complete exact coefficient identity passed. This covers all ten outstanding gap-two faces, including face 127. Its gap-three inequality remains pending. The aggregate immutable receipt is `global_gap2_templates2_10_34_receipt.json`; the earlier two-template receipt is preserved.

## 6. Later incremental approvals and authoritative scope

Sections 3–5 record the initial checkpoint, not the current completion status. Later independently checked whole-gap certificates include every still-needed large-template middle gap and numerous last gaps. Immutable `global_gap*_receipt.json` files retain each exact approval. The current union, combined with the small/medium face ledgers and independently reviewed ordinary proofs, is calculated by `refresh_progress.py` and recorded in `incremental_progress.json`. A template is complete only when every originally required face task is covered. Subsequent whole-gap replays use exactly the same unscaled integer-binomial identity, including certificates found using shifted search bases; only their final unshifted identities are trusted.

The balanced complete 2+2 core also now has an independently approved ordinary full real-rootedness proof, including arbitrary nonnegative role activities, in `balanced-core-gamma-research/independent-audit/balanced_real_rootedness_audit_receipt.json`. This is stronger than its earlier last-gap proof and does not imply real-rootedness of arbitrary degree-four templates.

## 7. Core-correction certificate extension

The separate checker `audit_global_core_correction.py` reconstructs its target directly from the SHA-pinned, Hall-audited gamma quota arrays. Write F2 for the quota-total-two part of gamma2, B for its quota-total-zero/one part, F3 for the quota-total-three part of gamma3, C for its quota-total-two part, and F4=gamma4. It checks the allowed support degrees, independently builds

E=6 F3 C+3 C²−8 B F4,

and verifies the full exported last gap is exactly

3 gamma3²−8 gamma2 gamma4 = (3 F3²−8 F2 F4)+E.

The first parenthesis is nonnegative by the separately and independently proved exterior-only Lorentzian theorem at core-cover order four. The checker pins that theorem's exact proof hash. It then applies the same complete Fraction/subset-union square-orbit replay to E, with degree bound five. Thus a successful E certificate proves the full last gap globally on integer populations and covers every face of its template. It is not mistaken for a direct identity with the whole sextic gap. Immutable receipts explicitly identify the E target and the ordinary-proof dependency.
