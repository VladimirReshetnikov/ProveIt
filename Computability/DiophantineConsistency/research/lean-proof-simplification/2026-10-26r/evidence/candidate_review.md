# Follow-up independent review of residual Pell proposals

Reviewed against ProveIt `9bd29079d5e1c6cc1c0bcaee6cb57d59b835cba9` and the complete directly audited six-packet/five-ZIP corpus. Source paths below abbreviate `Computability/DiophantineConsistency/Lean/DiophantineConsistency/` as `DC/`, and `Computability/HilbertTenthProblem/Lean/Diophantine/` as `H10/`.

## 1. Quantitative relative error before tolerance specialization

### Novelty decision: retain

No earlier proposal found for factoring these two Pell ratio proofs through a quantitative relative-error theorem. The closest exact earlier mention is in incoming `lean-proof-simplification-review-2026-10-26.zip`, member `lean-proof-simplification-review/evidence/arithmetic/findings.txt`, section 8, lines 169 onward. It recommends only replacing artificial trivial existential bindings of xi, X, Z, epsilon with `set ... with ...`. That readability change can be assumed applied without affecting the new proposal.

The concrete targets are `DC/NativeHalfBinomial.lean:18-108`, `upper_estimate_scaled`, and `H10/Paper1980/PellRatio90.lean:222-312`, `upper_estimate'`. Both prove the same quantitative bound up to their final tolerance specialization; the bodies explicitly contain the same intermediate `h1'`.

### Mathematical check

Write `xi = (U+1)^(2r)/U^r` and `epsilon = 9/(Y(U+1))`. The common proof establishes

`c <= k * xi * (1 + 2*r*epsilon)`.

Since `k > 0`, it follows that

`c/k - xi <= 18*r*xi / (Y*(U+1))`.

This theorem is independent of the later assumed bound `xi < Y+1` or `xi < 2*(Y+1)`. It is the actual common estimate, rather than an abstract record hiding two entire proofs. From it, any tolerance `delta` follows under

`18*r*xi < delta * Y*(U+1)`.

The existing common conditions `Y>=1` and `72*r < U+1` prove

`18*r*(Y+1)/(Y*(U+1)) < 1/2`.

Therefore `xi < Y+1` gives tolerance `1/2`, while `xi < 2*(Y+1)` gives tolerance `1`. The latter is precisely the bound used before dividing the actual doubled Pell denominator by two. A uniform coefficient `lambda > 0`, `xi < lambda*(Y+1)`, gives tolerance `lambda/2` under the same hypotheses; however the exact relative-error inequality is more reusable than only the lambda-specialized result.

The power-estimate stage only needs `r*epsilon <= 1/2`. Under positive `Y*(U+1)`, this is equivalent to `18*r <= Y*(U+1)`. One may keep `72*r<U+1` on a compatibility wrapper, but the quantitative core can expose this weaker threshold. The original `upper_estimate'` binder `hYr : U^r <= Y` is not used in its proof body; the new core does not require it. Keep the old public theorem signature if compatibility is desirable, deriving it from the stronger helper.

### Integration and claims

Put the shared quantitative theorem below both consumers, naturally beside `upper_key` and `one_add_pow_le` in `PellRatio90` or a small parent module. `NativeHalfBinomial` already imports `Diophantine.Paper1980.PellRatio90`; no new dependency cycle is needed. The improvement is one analytic comparison proof and two short numerical specializations. Do not claim the precise net source saving before counting the helper and wrappers. The two old theorem regions total 182 physical lines, but that is an opportunity size, not a measured deletion budget.

The theorem remains an ordinary real-inequality result. It does not by itself eliminate Real from the half-binomial recovery proof. Keep that latter proposal separate, and do not double-count the shared reduction if a combined implementation eventually proves the estimate in a more general ordered field.

## 2. Compare Pell bases directly

### Novelty decision: retain; strongest immediate pilot

No proposal for monotonicity of the Pell pair in its base was found in the complete audit corpus. Earlier sign relations, Pell parity reuse, source-row decoding, natural/integer cast cleanup, and ratio estimates concern different mathematical arguments. This idea remains useful after all of them are applied.

The source target is `DC/NativePellBootstrap.lean:309-333`, `main_index_gt_first`. Its current proof compares four exponential bounds, introduces `p-1` and `n-1`, and excludes index 1. None of that is required if the actual Pell sequences are compared directly.

### Complete ordinary proof of the new helper

For integer bases `1 < A <= B`, define the standard Pell coordinates `(x_A(n),y_A(n))`. The pinned Mathlib source provides

`x_A(n+1) = x_A(n)*A + (A*A-1)*y_A(n)`,

`y_A(n+1) = x_A(n) + y_A(n)*A`.

At `n=0`, both pairs equal `(1,0)`. Assume both coordinates for base A are at most the corresponding coordinates for base B. The coefficients are all nonnegative, `A<=B`, and `A*A-1<=B*B-1`; monotonicity of natural addition and multiplication gives both inequalities at `n+1`. Thus, by one simultaneous induction,

`x_A(n) <= x_B(n)` and `y_A(n) <= y_B(n)` for every `n`.

This first-order positive recurrence is essential. Trying to compare the second-order recurrence `y(n+2)=2*A*y(n+1)-y(n)` directly is awkward because the subtracted term goes in the wrong monotonicity direction.

### Stronger index comparison

Suppose only that `A<=P`, `c=y_A(p)`, `y_P(n)<=k`, and `k<c`. If `p<=n`, then

`c = y_A(p) <= y_P(p) <= y_P(n) <= k < c`,

contradiction. The middle step uses the existing index monotonicity theorem `Pell.strictMono_y` and its `.monotone` consequence.

Consequently `n<p`. The helper needs neither `p>0`, `n>0`, nor `c>1`; those are consequences or irrelevant. It also requires only `A<=P`, weaker than the old `2*A<2*P-1`. The old public theorem is a short wrapper: infer `A<=P` from the old condition, infer `y_P(n)<=k` from `k=2*y_P(n)`, then apply the stronger comparison. For actual source clients this can also avoid proving the stronger base separation if no other caller needs it, but that is a separate dependency audit and should not be assumed.

### Primary-source check

Pinned Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`, `Mathlib/NumberTheory/PellMatiyasevic.lean`, was inspected through GitHub. `xn_succ` is at line 133, `yn_succ` at line 137, and `strictMono_y` at line 375. The relevant recurrence API exists. No base-monotonicity theorem was found in that file's named declarations/search, though an exhaustive Mathlib-wide search was not performed. If a suitable library theorem exists elsewhere, reuse it instead of adding a duplicate.

### Acceptance conditions

The simultaneous monotonicity proof should compile using the exact pinned `Pell.d`, `xn_succ`, and `yn_succ` APIs. Then compile the stronger index theorem and the unchanged-header production wrapper. Count helper overhead: the old 25-line proof is short enough that the first application might chiefly improve explanation/hypotheses rather than net bytes. Further base-comparison clients would amortize the helper, but do not invent them or claim a project-wide reduction without inspection.

## Additional candidate recommendation

I would prefer a portfolio of four substantial directions (the three Pell mechanisms above/in the arithmetic agent's notes, plus single-source typed rule schedules) over padding the list with overlaps. The direct Pell comparison is the best immediate pilot; the quantitative ratio theorem is the most certain repeated-proof consolidation; exact integer binomial recovery is the larger mathematical reorganization; the rule-schedule compiler is a distinct architectural investment.

No additional fourth/fifth arithmetic headline is presently justified by an independently verified source-level payoff. In particular, aligned-cell subgroup/AddEquiv, signed residue relations, exact decoder graphs, generic fragment assembly, and cyclic algebra homomorphisms are all already represented in the corpus and should remain excluded.

## 3. Stronger refinement: an entirely natural-number error kernel

### Decision: mathematically sound and survives the novelty audit

This refines proposal 1 rather than adding another independently counted idea. It is a more concrete replacement for the shared Real epsilon proof: perform its entire quantitative comparison in natural numbers and convert only in compatibility wrappers. Searches of the entire prior text corpus for perturbation, Bernoulli/power error, upper estimate/key, and related terms found only the already noted cosmetic `set` suggestion. Earlier exact Euclidean and cyclic-carry identities do not subsume this finite-power estimate.

### Natural perturbation lemma

For `H b r : Nat`, assume `2*r*b <= H`. Then

`H * (H+b)^r <= H^r * (H+2*r*b)`.

At `r=0` this is equality, including `H=0`. For the successor step, the new bound implies the old one. Multiply the induction hypothesis by `H+b`, then use

`(H+2*r*b)*(H+b) <= H*(H+2*(r+1)*b)`.

After distributing products, the last inequality reduces exactly to

`b*(2*r*b) <= b*H`,

which follows from the old bound by monotonicity. This proof uses no division, inverse, logarithm, real number, or asymptotic estimate. Positivity of H is not required for the lemma itself. The final application requires H positive for cancellation.

### Composition with the existing Pell growth and key inequality

Put

`H = Y*(U+1)`, `D = U^r`, `N = (U+1)^(2*r)`,

`Z = (2*(H+2))^2*U`,

`Q = (2*(2*U*Y^2+1)-1)*(U+1)^2`.

The existing natural-number `upper_key` gives

`Z*H <= Q*(H+9)`.

The existing Pell power bounds give `c*D <= Z^r` and `Q^r <= K*N`. Raising the key inequality to r and combining gives

`c*D*H^r <= K*N*(H+9)^r`.

Multiply by H and apply the perturbation lemma with `b=9`:

`c*D*H^(r+1) <= K*N*H^r*(H+18*r)`.

Since `H>0`, cancel `H^r`, obtaining the exact common majorant

`c*D*H <= K*N*(H+18*r)`.

All terms and all order reasoning are in Nat. The scale assumption needed for the perturbation step is `18*r <= H`, which follows from the existing `Y>=1` and `72*r<U+1` assumptions. `upper_key` separately retains its `16<=H` hypothesis.

### Direct integer tolerance projections

If `K>0` and `18*r*N < D*H`, then

`c*D*H <= K*N*H + K*(18*r*N) < K*(N+D)*H`,

so canceling positive H yields `c*D < K*(N+D)`. This is the tolerance-one ratio estimate without division.

If instead `36*r*N < D*H`, multiplying the majorant by 2 gives `2*c*D < K*(2*N+D)`, the tolerance-one-half estimate. These inequalities are exact cross-multiplied forms of the existing Real conclusions.

The coefficient bounds `N < 2*(Y+1)*D` and `N < (Y+1)*D`, respectively, combine with `72*r<U+1` and `Y>=1` to discharge these two strict error tests. Thus the refactor can preserve both old public endpoints and serve the integer binomial recovery directly.

### Scope and accounting

The report should count this as the quantitative-error proposal's stronger implementation, not a fifth idea beside it. The separate binomial recovery proposal then composes with this natural-number majorant. Their combined integration can remove Real from a larger proof path, but a compiled perturbation lemma alone does not prove that the full production path has been migrated. Retain that distinction in the evidence table.


## Final source-reuse correction

The natural binomial certificate is already available in the imported `Jones1980.Ratio90.binomial_floor_two` (Paper1980/PellRatio90.lean:367). Under the native bound it returns T=Q*D+v, 4*v<D, Q=choose+w*X. Use it directly with existing parity and the checked integer rounding theorem. No new binomial-sum formalization is needed. `Jones1982.lemma_2_24` at Paper1982/Ratio.lean:44 is another existing natural certificate. The new contribution is the integer-window interface and removal of the real rounding adapters.
