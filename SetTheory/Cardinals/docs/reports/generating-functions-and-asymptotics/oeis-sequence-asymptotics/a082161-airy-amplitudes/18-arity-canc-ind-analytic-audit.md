# Independent audit: compacted–DFA logarithmic cancellation

Date: 2026-10-02. Scope: the corollary in `../proof.md`, using the approved fixed-arity relaxed and signed all-finite-orders theorems. This is an independent mathematical audit of the cancellation argument, not a new audit of all the inherited analytic machinery.

## Verdict

**Approved for each fixed integer k≥3.** With q=k−1 and the source conventions, including the DFA exceptional seed, specified in the signed theorem, the limits u∞,v∞ are strictly positive and

log(u_n/u∞) − 2 log(v_n/v∞)
= −q^(k−1)/k^k · n^(−q) + O_k(n^(−q−1/3)).

All preceding fractional powers vanish. The k=3 and k=4 coefficients are respectively −4/27 and −27/256. There is no surviving nonlinear, endpoint, amplitude, or finite-order remainder obstruction. The result is safe for the unified report. This approval does not establish uniformity in k, convergence of an infinite expansion, explicit amplitudes, or literature novelty.

The initial reviewed producer file had SHA-256 `0990d7d24aa8001e380434f5ba3b20ec487d3bd8a540091820b77add19020dcc`. Its introductory conditional status was stale, not a mathematical gap: the signed theorem has already been independently approved. See `verdict.md` for the final reviewed version and hash manifest.

## 1. The inherited theorem is strong enough

The signed theorem `../../fixed-arity-airy-research/signed-extensions/general-signed-all-orders.md`, SHA-256 `e50fc94256b8dfefd6320991b2f00b12b7b60cce540183b366413bc9d9f10f60`, is exactly the version approved in its independent audit. It supplies all finite expansion orders, with the same strictly positive amplitude at every order, for C and B. The relaxed companion does so for R. Therefore quotient and logarithm expansion about their positive limiting amplitudes are legitimate.

The factor 2^(n−1) rather than 2^n changes v∞, but no coefficient of a positive inverse power. In particular it disappears exactly after dividing v_n by v∞. No source-seed modification is made in the cancellation proof.

## 2. Why the nonlinear feedback is genuinely too late

Work in the exact common gauge A_m(0)=B_m(0)=0 with ε=i^(−1/3), and let d=3q≥6. The order-m profile enters the recurrence two orders later. Since the delay begins at ε^d, triangular uniqueness first gives δσ=O(ε^d) and δΦ=O(ε^(d−2)). At its first affected stage the delay forcing is a constant times f. The gauged polynomial inverse absorbs precisely that forcing into δσ_d and produces zero new profile. Thus the improved bounds are

δσ=O(ε^d), δΦ=O(ε^(d−1)), δQ=O(ε^d).

The last bound follows by expanding each of the k inverse scalars around its nonzero leading value k. Substitution ε↦ετ_l preserves the valuation; fixed shifts and dilation of x also cannot lower an ε valuation because their Taylor series contain no negative powers.

Writing Q=Q_0+δQ and Φ=Φ_0+δΦ, the omitted nonlinear terms are δσδΦ, βQ_0SδΦ, βδQSΦ_0, and the still higher βδQSδΦ. Their minimum valuations are respectively 2d−1, 2d−1, 2d, and at least 3d−1. Each is strictly greater than d+3. Therefore the equation is exactly linear in the model perturbations through the required scalar order. This does not assume the response is globally linear.

## 3. Exact cancellation of the delay coefficient and pure-f scalar extraction

At active Airy-window inputs, the original delay coefficients differ by

β_C−2β_B = [(m−1)−m] q^(2k)/(X)_k = −q^(2k)/(X)_k.

Using X=(qε^(−3)+xε^(−1)−1)/k gives

β_C−2β_B = −q^(2k) k^k ε^(3k) / product_(j=0)^(k−1)[q+xε²−(1+kj)ε³]
= −q^k k^k ε^(d+3) + O(ε^(d+5)).

There is no ε^(d+4) coefficient in this particular rational difference. After multiplication by Q_0 and the shifted relaxed profile, an O(ε^(d+4)) remainder is allowed and is all that is needed. There are k inverse scalar factors because the equation is divided by H_(i−1); using k+1 here would produce the wrong constant.

The combined response is ΔΦ=Φ_C−2Φ_B+Φ_0 and Δσ=σ_C−2σ_B+σ_0. Its first forcing is +q^k ε^(d+3)f in the left-hand equation. Every preceding combined stage is zero by triangular uniqueness. At stage d+3,

k L_q Δφ_(d+1) − Δσ_(d+3)f + q^k f = 0.

The unique gauged solution is Δφ_(d+1)=0 and Δσ_(d+3)=q^k. Thus ΔΦ=O(ε^(d+2)). The sign is positive for the scalar step and will reverse when summed to a decaying normalization correction.

## 4. Scalar logarithms and the three-order integration shift

Each individual δσ starts at ε^d. Expanding log(σ_0+δσ) about σ_0 therefore introduces quadratic terms only at ε^(2d), strictly later than d+3. The combined scalar logarithm is consequently

log σ_C−2 log σ_B+log σ_0 = (q^k/k)ε^(d+3)+O(ε^(d+4)).

For H_i=G_i exp(sum h_r i^(−r/3)), a single h_r contributes

h_r[i^(−r/3)−(i−1)^(−r/3)]
= −(r/3)h_r ε^(r+3)+higher powers.

The scalar-log to h matching is linear and triangular. The absence of combined scalar-log terms below d+3 therefore implies the absence of combined h terms below d; at d the coefficient is −q^k/(kq)=−q^(k−1)/k. There is no logarithmic integration resonance because r=d>0. There is no free constant contaminating this operation because all H have leading constant exactly one and the true model amplitudes are removed by u∞,v∞.

At i=kn this gives exactly −q^(k−1)/k^k n^(−q). Common factorial, growth, and Stirling factors cancel before this calculation.

## 5. Endpoint order is different from scalar order

Every profile coefficient vanishes at x=0 and is smooth there. Hence any finite profile difference of valuation ε^a, evaluated at x=ε, is O(ε^(a+1)). The leading endpoint profile equals εf′(0)(1+O(ε)), with f′(0) nonzero. Dividing the difference by the common endpoint profile therefore returns order ε^a; there is no loss of one power.

Consequently the individual relative endpoint perturbations a_C,a_B are O(ε^(d−1)), while a_C−2a_B=O(ε^(d+2)). Their logarithmic combination is

log(1+a_C)−2log(1+a_B)
= O(ε^(d+2)) + O(ε^(2d−2)).

Both terms are O(ε^(d+1)) or smaller. The endpoint thus cannot affect the coefficient at ε^d. This checks the correct endpoint target d, rather than incorrectly asking the endpoint remainder to clear the scalar target d+3. The cutoffs are exactly one at this endpoint for sufficiently large i.

## 6. Borderline k=3

For k=3, d=6. The first individual scalar perturbation is ε^6 and the first possible individual profile perturbation is ε^5. The equation's first nonlinear perturbation is ε^11, later than the required scalar order ε^9. The scalar-log quadratic starts at ε^12. At the endpoint the individual relative differences begin at ε^5, so the logarithmic quadratic begins at ε^10; the combined linear endpoint difference begins at ε^8. Both are later than the required endpoint order ε^6 and its ε^7 error threshold. Thus the borderline case passes without a hidden quadratic correction to −4/27.

## 7. From formal cancellation to a rigorously bounded remainder

Choose the inherited all-orders expansion through M=d in each model. Its relative error is O(n^(−(d+1)/3)), which is precisely O(n^(−q−1/3)). Quotient and log composition preserve this bound since the normalized leading terms tend to one. The formal coefficients computed above identify the coefficients in those expansions by the common normalization and exact recursion.

Equivalently, in the inherited norm-to-endpoint transfer choose p>3/2+(d+1)/3, and perform sufficiently many formal stages to achieve its defect bound. This produces a relative endpoint error smaller than the claimed one. There is no differentiation of an uncontrolled remainder, no assertion of convergence of the infinite formal series, and no need to cancel three independent O terms more accurately than their existing order.

## 8. Reproducible checks and their limits

The producer's `check_cancellation.py` was read and replayed successfully. It keeps the Airy parameter symbolic and verifies both polynomial f/f′ residual equations at all affected stages for k=3,4. The response coefficients at the final scalar stage are 8 and 81 after taking C−2B+R, and all combined profile coefficients through the requested stage vanish. Its use of a linearized response is justified by the preceding valuation proof. Truncating the base scalar at order four and base profiles at index three suffices: the potentially earlier response at index d−2 is identically zero.

The independent script `check_independent.py` imports no producer code. For k=3,…,12 it derives the exact delay difference directly from the original source-coordinate formula, checks its leading coefficient and missing next power, checks the scalar-to-normalization sign and conversion, and verifies all nonlinear thresholds against the proper scalar or endpoint target. Output is in `independent-output.json`. These finite checks corroborate the all-k algebraic argument; they are not a substitute for it.
