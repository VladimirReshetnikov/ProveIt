# Independent semantic review

Pinned target: `9f35798db4a63c25e435fca14d75931144657d7e`.
This review is a mathematical and source-contract inspection; Lean compilation status belongs to the corresponding experiment logs.

## Controller sufficient-exponent contract

`CurrentControllerUnits2011.power_dimension_47` and `power_dimension_2011` need only the equations `B^23 = 1` and `B^402 = 1`, respectively. The exponent congruences come from `auxiliary ≡ 1` modulo those exponents. Neither proof needs minimality of the exponent. Since `B = 2^94517`, the existing `two_pow_47` and `two_pow_2011` imply the required equations by commuting natural power exponents. This remains valid at dimension exponent zero: `auxiliary^0 = 1`.

The two `CurrentPowerCoordinates2011.generator_cast_47` and `generator_cast_2011` clients also only conclude `B^(auxiliary-1)=1`; their current use of `orderOf_dvd_iff_pow_eq_one` does not make exact fixed-prime orders necessary. They too can use annihilating powers, or the direct concrete exponent certificate. In contrast, `CurrentAuxiliaryOrder2011.generator_order_succ` supplies an exact auxiliary prime-power order to `CurrentPowerCoordinates2011.full_order`, and that exact order supports the later coordinate bijection. It must remain. The public fixed-prime exact-order declarations are also explicitly checked by `CurrentControllerData2011Checks.lean`, so preserve those declarations and audit tests unless deliberately reorganizing that API. The justified benefit is a weaker sufficient contract at four production clients, not global deletion of order theory. Do not claim source-line savings from deleting public exact-order declarations.

## Constructive degree-four enumeration

The original `ExecutableJones.starSum` enumerates all vectors in `(Fin (nu+2) -> Fin 5)`, retains those whose coordinates sum to four, and inserts literal zero expressions for all others. `Jones1982.star` is already `Finset.univ.piAntidiag 4` in the underlying `Paper1982/Coding.lean` source. An executable recursive weak-composition list can be related to that definition by membership and nodup proofs.

Do not use `Finset.toList` or `Multiset.toList` in the executable syntax path: both are explicitly noncomputable in the pinned Mathlib source. A recursion on coordinate count and remaining budget is constructive. Its order need not match the old bounded-vector order to preserve evaluated sums in the commutative ring, but the emitted raw `Expr` tree will change. Preserve semantic evaluation and polynomial identity, and separately inspect any tree-size, gate-count, digest, or literal-syntax regression expectations.

Counting caution: for `n` coordinates and budget `d`, the number of valid degree-`d` terms is `C(n+d-1,d)` when `n>0`. A recursion that tries every head `0..d` down to an `n=0` base still visits `C(n+d,d)` leaves, including zero leaves. Force the last coordinate to the remaining budget for an exact valid-term leaf count. For `n=nu+2,d=4`, these counts are `C(nu+5,4)` valid terms versus `C(nu+6,4)` leaves in the naive budget recursion. Distinguish callback evaluations, zero leaves, expression addition nodes, and runtime; none is automatically an elapsed-time measurement.

## Affine reflection

The revised `AffineReflection.lean` mechanism is sound on the stated integer domain. Let `A = 1 + b*V^2`. If `m <= 0`, `b > 0`, and `G > 0`, integrality yields `b >= 1` and `G >= 1`, hence

`y = 1 + 4*(b*m - A*G) <= -3 - 4*V^2 < -2*V`.

The final strict inequality follows from completing a square and holds for every sign of `V`. Thus the lower bound `-2*V < y` forces `m > 0`; no positivity assumption on `V` is needed for the common core.

For soundness, the involution `(m,G,y) -> (-m,-G,2-y)` preserves the affine equation. Replacing `V` by `abs V` also preserves it. The original hypothesis `abs y < 2*abs V` gives the lower bound `-2*abs V < 2-y`. A negative `G` would therefore imply `-m > 0`, contradicting the existing `m > 0` assumption. The shift is `2-y`, not `-y`; preserving the affine constant one matters.

For completeness, witnesses `G=b*g` and `y-1=4*b*e` give the explicit witness `m=e+(1+b*V^2)*g`. The common positivity lemma then applies using precisely the existing one-sided lower bound on `y`. The existing public `0<V` assumption can be retained even though the shorter proof does not use it. No Pell recurrence or stronger absolute-value premise is introduced.

## Shared finalizer evaluation

The displayed patch makes five exact evaluation lemmas in `JonesSyntax` public and reuses them in `ExecutableJones`. All executable definitions and their data remain unchanged. The duplication removed is semantic evaluation of identical `RingVars` finalizer fields, not a proposal to change the Jones expressions themselves. The additional public names need no new global simp attributes; use the explicit qualified lemmas in the client proof.

## Rejected semantic shortcut

Do not remove the `IsFormCodeSem` premise from `ObjectCodeBound.boundCodeRel_unique` by merely projecting a `BoundClosed` certificate graph. The former is an inductively generated intersection of constructor-closed sets, whereas the latter only imposes local post-fixed observation equations. Quantifier rows retain the same bound and therefore do not provide a decreasing rank. The `ZFAxioms` used by this API deliberately excludes Foundation/Regularity. An additional well-foundedness or internal rank argument would be needed; external Nat induction on arbitrary internal codes is not legitimate.

## Further ideas intentionally not promoted

Dedicated natural DAG interpretation and erasure, Boolean idempotent simplification by multiplicative cancellation, scan iteration, generic rule schedules, and formula satisfaction composition are already prior proposals. Exact witness-compaction section/idempotence lemmas were not found in the baseline catalog, but no surviving current client simplification was established, so no fifth novelty claim is made. A raw execution nonnegativity theorem independent of topology is plausible because invalid register references default to zero, but the typed natural-evaluator and generic invariant baselines substantially overlap its practical benefit; it is likewise not counted as a new deliverable.
