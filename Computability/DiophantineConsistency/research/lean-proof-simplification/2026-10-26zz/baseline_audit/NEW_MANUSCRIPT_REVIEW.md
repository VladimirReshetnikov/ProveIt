# New incoming manuscript exclusion review

Incoming inventory pin: `7ba7d102822df1eff376cbca913727d9d588ab4e`.

The two genuinely new manuscripts are `diophantine-lean-proof-deltas-2026-10-26.zip` (Deltas below) and `lean-residual-guards-2026-10-26.zip` (Guards below). Their complete reports, substantive technical/review/novelty notes, all delivered Lean kernels, patches and candidate source files, and the Deltas CSV novelty matrix were read. `NEW_MANUSCRIPT_COVERAGE.json` records exact bytes/hashes and separates reading from inventory-only evidence. No supplied script or Lean file was executed. Prior compiler statements below are historical claims, not new validation.

Every advertised outcome, optional interface, further client and notes-only direction below is excluded from round 7. This is a counterfactual union, not an assertion that mutually alternative patches coexist or compile together. A new client of these mechanisms does not earn novelty merely because its filename is recent. All previously inherited exclusions remain in force.

## M01 — Exact binary-rotation parameter equality and period normal form

**Sources:** Deltas `report.tex:106–172`, `lean/RotationPeriod.lean`, `patches/rotation-rephase.patch`; Guards `report/report.tex:261–354`, `evidence/rotation-RESEARCH.md`, `lean/RotationCongruence.lean`, `lean/RotationPeriod.lean`, `patches/rephase-assumptions.patch` and complete rephase candidate/check sources.

The literal operation reads the displacement only through `(W % v, (W / v : ZMod n))`. Equality of both observations gives equality of the complete output digit functions for arbitrary natural-valued digits. Full-window reduction `binaryRotation v (W % (v*n)) c = binaryRotation v W c`, modular-congruence equality, `Function.Periodic` with period `v*n`, arbitrary partial phases, whole-field specializations and actual width-47/cell-length-2011 clients are all assumed supplied. The current `physical_shift_eq` bridge and every advertised actual rephase adapter are included.

The union includes both body-only replacement retaining the unused old Boolean premise and the API-changing variant deleting `hc` from `rotation_eq` and `hd` from `normalization_rephase`, with production/check caller updates and optional compatibility wrappers. The same particular source, carries and digits transfer; scalar multiplier and quotient witnesses may change. A new generic congruence/period API or another displacement-normalization client is old even if the reports left installation optional until a second caller appears.

**Limits:** no digit bound, `v>0` or `NeZero n` is required for the generic equality under total definitions. At `v=0` or `n=0`, the displayed period is zero and no positive/least period is asserted. `binaryRotation v 0 c = c` remains false for unbounded digits; the old Boolean plain-rotation lemma cannot simply lose its guard. Normalization transport is conditional on existing `Facts`, not normalization existence for arbitrary digits. Full marked/scalar/mask packing retains its separately used Boolean bounds. Equality of ordinary multipliers is not granted.

## M02 — Same-window nonwrap capacity with two units of strict slack

**Sources:** Deltas `report.tex:173–230`, `lean/Capacity.lean`, `patches/no-wrap-capacity.patch` and novelty notes.

The exponent-free capacity theorem `F<B`, `delta<B`, `B+B<=Q` implies `F+delta<Q-1`; the radix specialization takes `rho>=2`, `m>=1`, both summands below `rho^(m-1)`, and obtains `F+delta<rho^m-1`. Both strict bounds contribute one unit of slack. The old `delta<rho^(m-2), m>=2` production theorem is a direct specialization via exponent monotonicity. Inline and optional public-helper versions, radix-two endpoint and future clients with only the weaker same-window increment bound are excluded.

**Limits:** retain natural truncated-subtraction guards and both strict inequalities. This is a numeric sufficient condition, not new mask preservation, mutation safety, or word-validity infrastructure. No theorem for arbitrary many summands is fabricated, but relabeling the advertised strict-slack capacity direction at another client is not novel.

## M03 — Internal quotient uniqueness by cancellation or interval separation

**Sources:** Deltas `report.tex:231–279`, `lean/InternalQuotientGap.lean`, `patches/logic-proof-refinements.patch`; Guards `report/report.tex:355–414`, `evidence/semantic-FINDINGS.md`, `lean/DivisionInterval.lean`, `patches/ObjectDivision-interval.patch`, complete ObjectDivision candidate, and independent review.

Both alternatives are old: (a) write `q'=q+s+1`, cancel common `q*d` to derive `r=s*d+d+r'`, then contradict `r<d`; (b) use `q*d+r<q*d+d<=q'*d<=q'*d+r'`. They delete the remainder-gap witness and the manufactured self-inequality. The first uses canonical additive order/cancellation without multiplication monotonicity. The second has a one-gap production form and an explicitly advertised zero-gap form using the assumed ordered-semiring/discrete-successor API (`q+1<=q'` and nonnegative multiplication). Symmetric quotient equality, remainder cancellation, public uniqueness adapters, and the existing quotient/remainder/positive-divisor/numeral conventions remain available.

**Limits:** all arguments are over arbitrary model-internal naturals, not a standard-Nat representation. The canonical natural order and discrete successor law are substantive; arbitrary signed remainders or nondiscrete nonnegative rational carriers invalidate the conclusion. A separate positive-divisor premise is unnecessary because `r<d` and canonical nonnegativity already imply it. In a one-sided comparison the second remainder upper bound is unused; the symmetric uniqueness call uses its counterpart. This asymmetry is already noted and is not a fresh premise-removal idea.

## M04 — Zero-test soundness from product and reconstruction rows

**Sources:** Deltas `report.tex:280–328`, `lean/TwoRowZeroTest.lean`, `patches/logic-proof-refinements.patch`, novelty notes and matrix.

Given `slack+1 != 0`, `bit*n=0`, and `n+bit*(slack+1)=slack+1` in a nonzero-multiplicatively-cancellative commutative semiring, split on `n=0`: cancel `slack+1` to get `bit=1`, or use zero-product cancellation to get `bit=0`. Both the minimal two-row theorem and the actual three-row certificate client ignoring the Boolean row are excluded. The actual internal successor-nonzero and ordered-semiring adapters, explicit import if necessary, and all public wrappers are assumed applied.

**Limits:** the literal Boolean polynomial row, row count, degree claims and expression semantics remain unchanged in this proposal. Nonzero successor is essential; rings allow `slack=-1`. The report explicitly reserves a broader review direction: determine which gadget rows actually determine the output on the intended carrier and organize soundness around that dependency set. Rebranding this principle at a new gadget is not fresh. That direction does not fabricate a universal theorem authorizing deletion of literal rows across arbitrary domains; actual row deletion would require independent semantic and cost analysis.

## M05 — Exact fixed-affine controller endpoints

**Sources:** Deltas `report.tex:329–361`, `lean/AffinePositions.lean`, `patches/affine-positions.patch`, novelty notes and matrix.

Expose the literal position `2+120198*j.val` locally with `change`, use linear arithmetic to prove `position_injective` after `ZMod.val_injective`, and prove `position_ne_three` without a representative-zero split. Both endpoints form one existing local cleanup; the exact actual ZMod domains and `k=0` case are included. No new embedding framework is claimed.

**Explicit further direction:** if the controller coefficient becomes variable, use symbolic positivity for affine injectivity and reduction modulo the step for the excluded position. This is an advertised reserved generalization, not a novel family in round 7. Preserve its positivity/nonzero-step and exact-domain guards rather than inventing an unrestricted statement.

## M06 — Recover source port positivity and scale bounds from rows 0/1

**Sources:** Guards `report/report.tex:155–260`, `evidence/semantic-FINDINGS.md`, `evidence/semantic-beta_call_sites.txt`, `lean/SourceGuardRecovery.lean`, `lean/SourceGuardClient.lean`, independent review, and integration plan.

For integer `J,beta,L,N`, retain `J>=0`, `L>0`, `N>=0`, `L=(1+J*beta)^2-1`, and `N=(1+J*beta)*(1+L)`. Then `q=1+J*beta>=2`, `J>0`, `beta>0`, `L>=3`, and `N>=8`. In the literal `SplitCertificate59.sourceRows` client, `x:Fin31->Nat` supplies nonnegativity; only `x24>0` is needed to infer `x0>0`, `ports0>0`, `x16>=8`. The actual row-decoding bridge is granted, not left as missing implementation.

All five advertised bootstrap migrations are old: `source_Y_ge_two`, `source_rank_half_lt`, `source_main_and_half_bounds`, `source_base_separation`, and `source_bootstrap`. So are internal/external callers, checks, source-facing compatibility wrappers, and adding recovered facts to the already proposed scale interface. `source_Y_ge_two_no_beta` needs only positive coordinates 24 and 9 plus source rows. The report expressly names further `source_transport_positive`, `source_native_rank_ge_twentyfour`, and `source_window_bound` clients (line 233); their guard-recovery adapters are excluded too. Its optional smaller API exposing only rows 0 and 1 rather than the universal all-row premise (line 219) is also old.

**Limits:** preserve the genuine `L>0`, nonnegative natural-coordinate interpretation and integral discreteness. Dropping these allows negative-q/negative-beta or zero cases; over rationals the constants 2/3/8 need not hold. This does not supply `15<=beta`, other port signs/bounds, K or mask bounds, rank/window bounds, complete positive-source existence, or outstanding Pell witnesses. It does not remove beta assumptions from abstract source-free Pell lemmas. It is conditional recovery, not construction of a source.

## Notes-only and overlapping directions retained in the exclusion union

- The Deltas caution against another `CurrentWordRephase2011` Facts smart constructor and generic population/sum aggregation reiterates older coherent-carry/finite-sum exclusions, not extra novelty.
- Guards' historical ledgers explicitly preserve notes-only optional `SuccAddOrder`, prime-radix APIs, fixed-kernel modulo-two projection, finite-update composition, endpoint-inclusive low-digit/marker independence, and rejected coordinate/control-update directions. These are old references and must remain in the inherited union; their mention is not a new proof or a fresh validation.
- Broad rotations, cancellation/order uniqueness, strict-slack capacity, row-dependency soundness, affine arithmetic endpoints, and source guard recovery must be screened semantically. A shorter tactic, new file, actual adapter, compile receipt, or different named client does not bypass the exclusions.

## Historical evidence versus current audit

Deltas' own proof source pin is `9d9d1123b39927d30363f1dcd53c23f0575c30ee`; Guards' is `f00ba53b331833c6cb64707bd90e48489e5610f5`, with its historical exclusion cutoff `60fcb2a69b7f1fdd4c3592ea5f164223cad50abe`. Their reported standalone compiler results and patch checks are not promoted into round-7 compilation evidence. Both reports explicitly leave full changed production modules/downstream integration unbuilt, and Guards leaves source-beta signature migration proposed. Those implementation limitations do not reduce the assumed-applied exclusion scope.

**Result:** six overlapping semantic families, with the listed optional APIs, reserved directions and real-client adapters, enter the round-7 prior baseline. No additional unrelated mathematical mechanism was found in the complete new prose/code read. No Lean, installation, network acquisition, incoming executable or upstream mutation was performed by this reader.
