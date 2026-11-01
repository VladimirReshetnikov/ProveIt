# 85-operation existential normalization investigation

An additional balance shift changes `F` as well as `C`: with `b=Jβ`,
`q=1+b`, `A=X+Kq` and `k=η+ζ`, it replaces `F` by `F+bt`, `C` by
`C−qbt`, and the first-root auxiliary `r` by
`r−qt(A+1)(bk+1)`, leaving the remaining coordinates unchanged. The exact
integer literal is invariant. More importantly,
`AdaptiveGap85BalanceModel.positive_zero_shift` proves in every IΣ₁ model
that, when the two displayed decrements are strictly below their coordinates,
the shifted tuple is again a positive zero and satisfies
`F′+C′+b²t=F+C`. The separate `gap_strictly_decreases` theorem gives strict
decrease for positive `b,t`. Matching guarded author/peer replays are in
`reviews/adaptive-gap85-balance-{shift,model,progress}-replay/`, with the
historical transitive project and external package boundaries recorded there.
These results do not show that an arbitrary zero satisfies the decrement
bounds, that the shift can be iterated sufficiently, or that any representative
satisfies `F+C<q`; the reverse 85-to-86 implication remains open.

The balance step yields a sharper conditional description of a minimal
positive zero. `AdaptiveGap85BalanceMinimal.minimal_zero_has_blocker` proves
in every IΣ₁ model that a positive zero assumed to minimize `F+C` must have
either `C≤qb` or `r≤q(A+1)(bk+1)`. `AdaptiveGap85BalanceLeast` applies the
IΣ₁ least-number principle to obtain such a zero from any positive zero,
**provided** the positive-zero score predicate is Σ₁-definable. That
definability is an explicit premise of the conditional theorem; its later
discharge and replay qualifications are described below. Matching
guarded replays are preserved in `reviews/adaptive-gap85-balance-minimal-replay/`
and `reviews/adaptive-gap85-balance-least-replay/`; the historical project
and package ancestry and lack of a direct-import trace remain as recorded.
Neither conditional result proves existence of a normalized representative.

The corresponding least-`F` result is established separately in
`AdaptiveGap85FirstScore`: positive-zero `F` scores are Σ₁-definable, so any
existing positive zero yields a positive zero with minimum `F`. If the first
port is positive, `minimal_first_has_blocker` shows that this witness has
either `F≤A(cU)` or `γ≤(q²−1)(A+1)c`, blocking the strict third shift.
The independently audited author/peer proof packet is
`reviews/adaptive-gap85-first-score-replay/`. This minimizing witness need
not be the one minimizing `F+C` above. Neither result establishes the
reverse implication or existence of a zero; historical transitive and
dynamic package ancestry remains inherited.

`AdaptiveGap85ScoreCoding.zeroScore_definable` is now replayed for the actual
85 literal in arbitrary IΣ₁ models. For each fixed external natural port
tuple, it codes a 13-tuple with Cantor pairing, proves every fixed natural
expression on that tuple is Σ₁-definable, and identifies the coded predicate
with the exact positive-zero score. `exists_minimal_blocked_unconditional`
discharges the earlier definability premise, while still assuming a positive
first port and an existing positive zero. It does not prove normalization,
the 85 equivalence, or an iPRA derivation of that equivalence.

The matched v3 replays and independent audit are preserved in
`reviews/adaptive-gap85-score-coding-v3-{input,replay}/`. Both source and
generated Checks bytes, private-overlay entries and realpaths, direct Lean
dependency resolution at three stages, provider companion candidates, and
Cantor direct inputs were guarded. The selected Cantor object was separately
reproduced byte-for-byte; its historical provider failed later on a different
module. The earlier unguarded and guarded-v2 packets are retained as qualified
preliminary evidence in `reviews/adaptive-gap85-score-coding-preliminary/`
and `reviews/adaptive-gap85-score-coding-guarded-replay/`. Neither the v3
replays nor the Cantor repair independently rebuild the historical transitive
project/package source-to-object or dynamic ancestry.

The 85-operation candidate is a 13-positive-coordinate reparameterization of the checked 86-operation candidate. Its finite circuit audit and one-sided machine implication are documented in [the candidate packet](../adaptive-gap85/README.md). The 85 no-zero statement implies machine nonhalting; the reverse implication is not established. Neither the candidate nor this note establishes an 85-operation equivalence with consistency.

The existing reverse transfer `AdaptiveGap85Exists.new_natural_zero_to_old_of_bound` maps an 85 zero to an 86 zero when that witness satisfies `F + C < q`, with `q = 1 + Jβ`. The earlier full-equivalence adapter assumes this for every 85 zero. This is stronger than necessary: it suffices to construct, for each 85 zero, some 85 zero whose positive coordinates satisfy the bound. The exploratory Lean file [ExistentialNormalization.lean](ExistentialNormalization.lean) states that existential representative hypothesis explicitly and derives the reverse zero transfer and no-zero equivalence from the existing lift. It compiled against `/tmp/adaptive-gap85-machine-m09n4q_7/lib` and inherited Foundation/Mathlib/package boundaries; it is a provisional scratch result, not an authenticated source-current replay. It does not prove that representatives exist.

The existing literal-preserving shift changes the positive-coordinate gap `C` by `d = (Jβ)·c·(Yq²)` while preserving both `F` and `q`. For positive coordinates, `d ≥ q−1`. Thus repeated applications of that particular shift preserve the residue of `C` modulo `d`; a representative with `F + C < q` requires a sufficiently small residue and positive values for the other shifted coordinates. If `F ≥ q`, this shift cannot establish the gap at all because it leaves `F` and `q` unchanged. The checked conditional `AdaptiveGap85ShiftModel.shifted_zero_breaks_gap` also produces a full zero violating the pointwise gap whenever its explicit threshold hypotheses are met. It does not assert the existence of such a zero, and it does not refute existential normalization. Existing artificial-port examples with `F=q` satisfy selected factor equations but are not full zeros and do not show fixed-port failure.

A necessary constraint from all four actual factors is already formally available: `AdaptiveGap85FirstDivisibility.expressionAt_Y_quotient85` proves `q³ ∣ Y` for every positive full zero in an arbitrary IΣ₁ model. This constraint invalidates the following numerical near-hit. With artificial `q=13`, `X=8`, `Y=5`, `η=815`, `ζ=789`, `T=6`, one obtains `Δ=2208`, `c=8835`, square first/main radicands and a positive integral `γ=45` in the restricted template; nevertheless `13³` does not divide 5. It is neither a full zero nor a counterexample for the actual fixed ports. The exact arithmetic is reproduced by [search_template.py](search_template.py).

The same script scans a deliberately narrow template: `c=4Δ+3`, a Pell-generated first-factor index, an auxiliary expression `R=cT−4Δ`, positive main-root orientation, `2≤q≤6`, `1≤X≤400`, `Y≤400` with `q³ ∣ Y`, and `1≤T≤99`. It checked 144 qualifying numerical combinations and found no hits. This is not a search of arbitrary witnesses, a model-theoretic argument, or evidence of global nonexistence.

For that same special template, the exploratory integer lemma [`TemplateConstraint.lean`](TemplateConstraint.lean) derives the necessary congruence `Y ∣ 45(T−1)` from its displayed main-root equation and `Y ∣ U`. It also shows `T=1` if `T≥1` and `45(T−1)<Y`. The author and independent same-parent Lean replays passed with matching source, object and full-log hashes; their guarded direct Mathlib inputs and inherited package boundary are recorded in [the replay receipt](../../reviews/adaptive-gap85-template-constraint-replay/README.md). Its main-root and Pell-template equations are explicit assumptions, and it has not been connected to an actual 85 zero or generalized to arbitrary IΣ₁ models. It narrows a counterexample search only within this particular template.

A stronger [special-template exclusion](TemplateExclusion.lean) has now passed author and independent integer Lean replays with matching source/object/log hashes; see [the exact replay receipt](../../reviews/adaptive-gap85-template-exclusion-replay/README.md). Under the displayed template `η = 4((Y(X+1))²+4Y(X+1)+3)+3−Y(8XY²+4)`, its positive main-root equation, `X≥1`, `Y≥8`, `η>0`, and `q ∣ Y`, it proves a contradiction. The key steps derive `H ∣ Yq²(8−X)` and `H ∣ 27(8−X)` for `H=4Y(X+1)+3`, then use positivity. These equations are not known for every 85 zero; the model-uniform positive- and negative-orientation results are recorded below. Thus this excludes that restricted artificial template, not the 85 candidate. Direct Mathlib objects were guarded; package-transitive ancestry remains inherited.

The [negative-root companion](NegativeTemplate.lean) has also passed guarded author and independent integer Lean replays with matching source/object/log hashes; [the replay receipt](../../reviews/adaptive-gap85-negative-template-exclusion-replay/README.md) records the exact assumptions and finite cases. For the same displayed η template and the negative main-root equation, it derives `H ∣ 27(8X+1)`, then `Y<54`; with `q≥2`, `Y≥8`, `q³ ∣ Y`, `X≥1` and `η>0`, it excludes the remaining integer cases. The only positive-X modular candidate is `q=2, Y=48, X=7`, for which η is negative; adaptive_binding independently checked this finite calculation without an X search bound in `negative_template_case_audit.py`. Taken together, the positive- and negative-root lemmas exclude only this special template under their displayed assumptions. These integer lemmas alone do not show every 85 zero has this template; the corresponding model-uniform results are recorded below.

A possible next step is to derive a small-residue or direct machine-decoding theorem from all four factor-unit equations together with `q³ ∣ Y`, then construct a positive 85 representative satisfying the reverse gap or avoid that gap altogether. Such a theorem must be uniform in arbitrary IΣ₁ models, preserve all positive coordinates, and then feed the existing source-theory and native intuitionistic proof transfers. Alternatively, a full artificial-port or actual-fixed-port zero with no suitable representative would show that a proposed normalization strategy fails; no such counterexample is currently claimed.

The Pell index trichotomy is now checked in arbitrary models of IΣ₁ in `AdaptiveGap85PellTrichotomy.lean`: for positive Q and k satisfying `x*x = 1 + Q*(Q+1)*k*k`, either `k = 2`, `k = 8*Q+4`, or `32*Q*Q+32*Q+6 ≤ k`. The focused author and independent replay match; see `reviews/adaptive-gap85-pell-trichotomy-replay/`. The direct imported object is guarded, while its historical transitive project ancestry and package ancestry are inherited.

Separately, `TemplateIndexBounds.lean` proves over the integers that the explicit special-template equations, positivity hypotheses, and an index trichotomy force the second index; matching replays are in `reviews/adaptive-gap85-template-index-bounds-replay/`. The model-uniform special-template inequalities are proved separately below; no theorem shows every 85-zero has this special-template representative. These results therefore do not establish the missing reverse implication or the 85-operation equivalence.

`AdaptiveGap85PellTemplateConditional.lean` also proves the second-index conclusion in arbitrary IΣ₁ models from the stated first-norm and template equations, provided the two displayed template inequalities hold. Its focused independent replays match; see `reviews/adaptive-gap85-pell-template-conditional-replay/`. The inequalities remain explicit assumptions in that theorem. All these statements retain the special-template hypothesis and do not establish the existence of such a representative for every 85-zero.

The subsequent `AdaptiveGap85TemplateInequalities.lean` proves both inequalities in arbitrary IΣ₁ models and derives the second index for the stated special template and first-norm equation from `X ≥ 1` and `Y ≥ 2`, with the stated positivity conditions. Its focused independent replay matches (`reviews/adaptive-gap85-template-inequalities-replay/`); historical transitive project and package ancestry remains inherited. The earlier integer-only limitation on these two inequalities is therefore superseded for this special template. The existence of a template representative for an arbitrary 85-zero is still open.

`AdaptiveGap85PositiveModular.lean` proves the positive-template cubic congruence in arbitrary IΣ₁ models: under `Y ≥ 1`, `q ∣ Y`, and the explicitly stated positive-root polynomial equation, `27*X` and `216` have the same remainder modulo `4*Y*(X+1)+3`. The focused author and peer replays match (`reviews/adaptive-gap85-positive-modular-replay/`). The imported project object's transitive ancestry and external package ancestry remain historical. This congruence alone is not a template exclusion and does not show that an arbitrary 85-zero has a template representative.

The positive orientation of the stated special template is now excluded in every IΣ₁ model by `AdaptiveGap85PositiveTemplate.exclude_positive_template`. The theorem retains its explicit first-norm, positivity, divisibility, template and positive-root assumptions; it derives the second index, obtains the cubic congruence and its size consequence, and reaches a contradiction. Five-module focused author and independent replays match (`reviews/adaptive-gap85-positive-template-model-replay/`); inherited project and external package transitive source ancestry remains historical. It does not prove that an arbitrary 85-zero admits this template.

For the negative orientation, `AdaptiveGap85NegativeModular.lean` proves in every IΣ₁ model, from `Y ≥ 1`, `q ∣ Y` and its explicitly stated balanced negative-root equation with a natural witness `L`, that `27*(8*X+1)` is zero modulo `4*Y*(X+1)+3` and that `Y < 54`. The focused independent replays match (`reviews/adaptive-gap85-negative-modular-replay/`), with inherited project and package transitive source ancestry historical. The natural witness must still be obtained from the actual equation; the remaining `Y < 54` special-template cases are excluded by the later theorem below.

`AdaptiveGap85NegativeSmallCases.lean` further reduces the balanced-negative case in every IΣ₁ model: assuming `q ≥ 2`, `Y ≥ 8`, `q*q*q ∣ Y`, and the displayed balanced negative-root equation, either `q=2`, `Y=8*t`, `1≤t≤6`, or `q=3`, `Y=27`. Independent focused replay matches (`reviews/adaptive-gap85-negative-small-cases-replay/`), with historical inherited transitive ancestry. That reduction alone does not eliminate those cases or derive the balanced equation from an arbitrary 85-zero.

`AdaptiveGap85NegativeMultiplier.lean` independently constructs an internal multiplier `m` with `1≤m≤6` and `27*(8*X+1)=(4*Y*(X+1)+3)*m` from the balanced negative-root equation, `Y≥8` and `q∣Y`. Matching focused replays are recorded in `reviews/adaptive-gap85-negative-multiplier-replay/`; inherited transitive source ancestry remains historical. That bound alone leaves the bounded cases and balanced-equation extraction open.

`AdaptiveGap85NegativeTemplate.exclude_negative_template` now excludes the negative balanced-root orientation of this exact special template in every IΣ₁ model. It assumes the displayed first norm, special-template and balanced-root equations, a natural witness `L`, `X ≥ 1`, `Y ≥ 8`, `q ≥ 2`, `q*q*q ∣ Y`, and the stated positivity/parameter conditions. The internal finite cases have the sole linear survivor `X=7`, `Y=48`, `m=1`, which contradicts the template equation. Seven-module coherent independent replays match (`reviews/adaptive-gap85-negative-template-model-replay/`); inherited project and package transitive source ancestry is historical. Extraction of the balanced-root witness and any special-template representative from arbitrary 85-zeros remains open.

`AdaptiveGap85TwoOrientationTemplate.exclude_two_orientation_template` combines the model-uniform exclusions of the two stated special-template root orientations. Its disjunction explicitly supplies either the positive witness pair or the balanced negative natural witness, along with the listed first-norm, positivity, cubic-divisibility and template assumptions. Focused author and peer replays match (`reviews/adaptive-gap85-two-orientation-replay/`), with inherited transitive source ancestry historical. It does not show that arbitrary 85-zeros satisfy those assumptions or have those witnesses, so the 85 reverse implication remains open.

`AdaptiveGap85SignedOrientationTemplate.exclude_signed_orientation_template` strengthens the two-orientation result to an arbitrary signed auxiliary term, represented by natural components `A,B`. On the negative side it derives the earlier natural balanced-root witness from the stated signed equation, rather than assuming that witness separately. Five-module focused author and peer replays match (`reviews/adaptive-gap85-signed-orientation-replay/`), with historical inherited transitive ancestry. The exact special-template equation, first norm, positivity, cubic divisibility and signed-root orientation disjunction are still assumptions; extracting them from an arbitrary 85-zero remains open.

The signed-template result now has an actual-zero client: `AdaptiveGap85NoThirdMain.actual_zero_not_third_main` proves in every IΣ₁ model that a positive zero of the literal 85 expression, with positive first port, cannot have third main Pell ordinate. It derives the required special-template and signed-orientation facts from the actual zero under that hypothesized index, rather than assuming them independently. Coherent author and independent replays match across 18 modules (`reviews/adaptive-gap85-actual-third-replay/`); the inherited project and package transitive source ancestry remains historical. This excludes one index only and does not prove arbitrary-zero normalization or the reverse implication.

The checked actual-zero consequence is stronger: `AdaptiveGap85IndexLowerBound` proves that a positive literal 85-zero with a positive first port has first Pell index at least 2, main Pell index at least 4, and `8*((v 6*v 7)*v 7)+4 ≤ v 9+v 10`, in every IΣ₁ model. Its author and independent replays match (`reviews/adaptive-gap85-index-lower-replay/`); inherited transitive project and package source ancestry remains historical. These are necessary bounds and do not establish that such zeros do not exist or prove the reverse implication.

A concrete partial arithmetic configuration shows why the two Pell norms, positivity and `q³ ∣ Y` alone cannot exclude main index 4: `AdaptiveGap85FourthNormExample.lean` checks `X=253`, `Y=8`, `q=2`, `eta=197347912`, `zeta=8192957886`, the two norm equations, and their first-index-3/main-index-4 polynomials. Independent focused replays match (`reviews/adaptive-gap85-fourth-norm-example-replay/`). This is not asserted to satisfy the signed root equations, to be a full 85-zero, or to use the actual fixed ports; it is not a counterexample to the desired equivalence.

`AdaptiveGap85FourthRootCongruence.fourth_root_congruences` proves fourth-index signed-root necessary conditions in every IΣ₁ model. Assuming `Y≥1`, `q ∣ Y` and one of the explicitly displayed fourth-root orientations, either `27*X ≡ 432` or `27*(16*X+1) ≡ 0` modulo `4*Y*(X+1)+3`. Three-module focused author and peer replays match (`reviews/adaptive-gap85-fourth-root-replay/`); inherited transitive project and package source ancestry remains historical. This theorem alone assumes the root orientation; its actual-zero binding and the fixed-port index-4 exclusion are recorded below.

`AdaptiveGap85ActualFourthRoot.actual_fourth_main_congruences` binds those fourth-index congruences to an actual positive literal 85-zero with positive first port and the explicit fourth-main-index hypothesis. The root orientation and needed divisibility are derived from that zero, rather than assumed. Four-module focused independent replays match (`reviews/adaptive-gap85-actual-fourth-root-replay/`), with inherited project and package transitive source ancestry historical. The congruences alone do not exclude index 4 or establish the reverse implication; the fixed-port exclusion below uses additional facts.

`AdaptiveGap85NoFourthLargeQ.actual_zero_not_fourth_main_of_large_q` now excludes main index 4 for an actual positive literal 85-zero with positive first port and `q≥5`; `AdaptiveGap85CurrentNoFourth.current_zero_not_fourth_main` discharges that bound for the literal fixed ports from `beta≥4`. Both hold in every IΣ₁ model. Independent ten-module source-directed replays PASS (`reviews/adaptive-gap85-no-fourth-replay/`); source/object hashes match, and the single warning-bearing log matches after normalizing its differing run-root path. The warning states the exponent 2011 was not evaluated. Historical inherited transitive ancestry remains explicit. Higher indices and the reverse implication remain open.

The checked bounds have been sharpened further. `AdaptiveGap85FirstIndexThree` proves that any positive 85-zero with a positive first port has first Pell index `n≥3`, main index `m≥4`, and `eta+zeta ≥ 32Q²+32Q+6` for `Q=X*Y²` (`reviews/adaptive-gap85-first-index-three-replay/`). For the literal current ports, `AdaptiveGap85CurrentIndexFive` proves main index `m≥5` (`reviews/adaptive-gap85-current-index-five-replay/`). Both statements are model-uniform and have matching focused independent replays; inherited transitive project/package ancestry remains historical. They constrain possible zeros but do not establish their nonexistence or the reverse implication.

`AdaptiveGap85CurrentIndices.current_zero_index_bounds` combines the two latest restrictions on the same Pell witnesses: any positive literal 85-zero at the actual fixed ports has `n≥3`, `m≥5` and `n<m`, in every IΣ₁ model. Its focused author and peer replays match (`reviews/adaptive-gap85-current-indices-replay/`), with inherited transitive project/package ancestry historical. It remains a necessary condition and does not prove the reverse implication.

The root congruence now holds at an arbitrary internal main Pell index. `AdaptiveGap85ActualAllIndicesRoot.actual_zero_root_congruences` derives from any actual positive literal 85-zero with positive first port an internal `m` satisfying either `27X ≡ 27·2^m` or `27(1+2^m X) ≡ 0` modulo `4Y(X+1)+3`. `AdaptiveGap85ActualLargeYPow.actual_zero_large_Y_forces_power` additionally proves `7·2^m≤Y → X=2^m` for that index. Six-module focused independent replays match (`reviews/adaptive-gap85-actual-all-indices-replay/`), with historical inherited transitive ancestry. The large-Y antecedent and impossibility of `X=2^m` are not proved, and these necessary conditions do not establish the 85 reverse implication.

`AdaptiveGap85CurrentAllIndicesRoot.current_zero_indices_root_congruences` combines the fixed-port bounds `n≥3`, `m≥5`, `n<m` and the arbitrary-index signed congruence for the same actual Pell witnesses. Four-module coherent independent replays match (`reviews/adaptive-gap85-current-all-indices-replay/`), with historical inherited transitive ancestry. This remains a necessary condition, not a proof of zero nonexistence or the reverse implication.


### Partial large-Y power-of-two norm example

A Lean-checked natural-number example has X=32=2⁵ and Y=579≥7·2⁵, positive auxiliary values, both Pell norm equations, and the first-index-three and main-index-five polynomial identities. Therefore these conditions alone cannot exclude the power-of-two alternative. The example fails q³∣Y for every q≥2; it is not a full 85-equation zero and does not establish anything about arbitrary IΣ₁ models. The focused author and independent replays, source and object hashes, full logs, and inherited package boundary are recorded in `reviews/adaptive-gap85-large-Y-power-example-replay/`.


### Partial large-Y example with cubic divisibility

A second Lean-checked standard-natural example has X=65536=2¹⁶, Y=36032920392046168, q=2, positive eta and zeta, Y≥7·2¹⁶, q³∣Y, both Pell norm equations and the first-index-nine/main-index-sixteen recurrences. It demonstrates that even these combined partial conditions do not rule out X=2ᵐ. It does not meet the actual fixed-port requirement q≥5, nor assert the signed-root equations or a full 85-equation zero; it does not establish the reverse implication. Author and independent replays match; see `reviews/adaptive-gap85-cube-power-example-replay/` for source, objects, full logs and the inherited package boundary.


### Partial large-q large-Y power example

A further Lean-checked standard-natural example has X=4294967296=2³², Y=140737488482304, q=8, positive eta and zeta, Y≥7·2³², q³∣Y, q≥5, both Pell norm equations and the first-index-20/main-index-32 recurrences. Even these combined partial conditions do not rule out X=2ᵐ. The example does not establish that q=8 is realizable at the actual fixed port, nor does it assert the signed-root equations or a full 85-equation zero. It does not establish the reverse implication. Author and independent replays match; see `reviews/adaptive-gap85-large-q-power-example-replay/` for source, objects, full logs and the inherited package boundary.


### Conditional divisible-coordinate gap obstruction

`AdaptiveGap85DivisibleGap.divisible_blocks` checks in every IΣ₁ model that positive F,C with b∣F cannot satisfy F+C<1+b; by symmetry the same applies if b∣C. Its forward lemma proves b∣F is preserved by adding b·t. Both known shifts change F and C by multiples of b=q−1, suggesting this residue is an obstruction to normalizing within their shift orbit. No actual zero is known to have a divisible coordinate, and the full shift-orbit claim is not formalized in this packet. Focused independent replays match (`reviews/adaptive-gap85-divisible-gap-replay/`), with historical inherited transitive ancestry.


### Conditional finite shift-orbit obstruction

`AdaptiveGap85ShiftResidue.orbit_blocks` now checks the residue argument in every IΣ₁ model: for an abstract step adding or subtracting multiples of positive b to F and C independently, a finite external sequence preserves b∣F or b∣C, and every positive endpoint fails F+C<1+b. It uses Lean's external finite reflexive-transitive closure, not an internally coded model-length iteration. Binding the actual literal shifts to this relation and establishing an actual zero with the residue remain open. Matching focused replays and historical inherited ancestry are recorded in `reviews/adaptive-gap85-shift-residue-replay/`.


### A third, residue-changing shift

`AdaptiveGap85ThirdShift.literal_eval_shift` proves that the corrected third coordinate shift preserves the exact 85 expression over every commutative ring. The gamma decrement is `(q²−1)(A+1)c·s`; no extra factor H occurs. This is a ring-level equality and does not yet establish a positive arbitrary-IΣ₁-model shift or a normalizing representative. Independently replayed source, logs and historical provider qualifications are in `reviews/adaptive-gap85-third-shift-replay/`.

The independently replayed `AdaptiveGap85ThirdResidueExample` checks positive integer coordinates before and after this shift, with artificial ports `(4,0,0,0)`, for which F changes from 0 to 1 modulo b=4. Thus the third shift can escape the residue invariant of the first two shifts on positive inputs. The example is not asserted to be an 85-equation zero or to use the actual fixed ports; it does not establish the 85 reverse implication. See `reviews/adaptive-gap85-third-residue-example-replay/`.


### Joint residue for the three shifts

`AdaptiveGap85JointResidue.literal_orbit_congruence` proves in every IΣ₁ model that any external finite sequence of the three coordinate shifts preserves the joint residue F−A·C modulo b, expressed without subtraction as `(F′+A·C)%b=(F+A·C′)%b`. The balance C-subtraction and third bA/F-subtraction bounds are explicit. The relation is broader than the zero-preserving moves, and does not claim positive intermediate coordinates or a model-internal unbounded iteration. Corrected-scope author and independent replays match (`reviews/adaptive-gap85-joint-residue-replay/`); earlier successful runs with a copied, incorrect scope field are preserved in `reviews/adaptive-gap85-joint-residue-scope-correction/`. Inherited project/package transitive source ancestry remains historical.

The independently replayed `AdaptiveGap85JointObstruction` derives a conditional limitation: if b divides both A and the initial F, no positive endpoint of that finite coordinate orbit meets F+C<1+b (`reviews/adaptive-gap85-joint-obstruction-replay/`). It remains unknown whether any actual 85-equation zero satisfies those divisibility hypotheses. Neither result proves or disproves the 85 reverse implication.


### Conditional minus-one joint-residue obstruction

`AdaptiveGap85JointMinusOne.orbit_blocks_minus_one` gives another independently replayed conditional obstruction in every IΣ₁ model. If b>1 divides A+1 and the initial `(F+C)%b=1`, no positive endpoint of the external finite three-shift coordinate orbit has F+C<1+b. Its coordinate relation is broader than zero-preserving moves; actual-zero occurrence of these assumptions and the 85 reverse implication remain open. See `reviews/adaptive-gap85-joint-minus-one-replay/` for the matching focused replays and historical inherited ancestry.

### Signed-rank obstruction and partial-factor family

`AdaptiveGap85RankRemainderObstruction.no_normalized_same_rank_residue` proves in every IΣ₁ model that if `q > 0` divides `C`, no pair with `C' > 0` and `F' + C' < q` can preserve the exact signed-rank residue modulo `q` when `q`, `J`, and the fixed ports remain unchanged. The restriction on preserving this residue is explicit; the result does not show that an actual 85-zero has `q ∣ C`. Matching focused replays are in `reviews/adaptive-gap85-rank-remainder-replay/`, with historical inherited project and package transitive source ancestry.

`AdaptiveGap85PartialRankRemainder.partial_family_blocks_rank_normalization` constructs, over the standard integers for arbitrary `b ≥ 1`, `k ≥ 0`, and arbitrary remaining ports, a positive tuple with `q=b+1` and `C=q` at which the actual first and auxiliary factors are one. The same signed-rank normalization is impossible there, and the full 85 expression is explicitly **nonzero**. Thus the first and auxiliary equations alone do not eliminate this obstruction; the tuple is not a full-zero example and neither result establishes or refutes the 85 reverse implication. The fixed-port specialization is a separate client. Matching focused replays are in `reviews/adaptive-gap85-partial-rank-replay/`, with historical inherited project and package transitive source ancestry.
