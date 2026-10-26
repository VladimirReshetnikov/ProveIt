# Novelty exclusions: packets n through z

Audited source pin: `96520cd1a5179f470b4da127bd47bc26a8d808ff`.
All relative packet paths below are under
`Computability/DiophantineConsistency/research/lean-proof-simplification/`.
This memo is an exclusion screen, not a claim that every original prototype was verified.
Read the report proposal sections, READMEs and relevant audit/technical notes. Historical copied
production trees are not counted as additional proposal manuscripts. The 114 inspected report,
README and audit text files remain available in the pinned local source mirror; redundant temporary copies were deleted.

## Packet-by-packet mechanisms

| Packet | Already proposed mechanism and concrete targets | Primary location |
|---|---|---|
| n | Reuse `decodeTable_total` and `tableCode_of_decode` for arbitrary raw parent codes, then typed `check_lists`; no independent re-encoding induction. | report/sections/03_parents.tex |
| n | One exact successful tree-decoder invariant yielding quotation recovery and depth/fuel bound; derive separate specs and monotonicity. | report/sections/04_decoder.tex |
| n | `Finset.sum_le_one_iff` for zero/singleton support; zero-base propagation as existing `propagate_from` specialization. | report/sections/05_finite_and_cycle.tex |
| n | Direct `binaryWord_prefix` specializations at offsets 19 and 20 with lambda address normalization. | report/sections/06_south_prefix.tex |
| n | Move binary-word congruence to definition layer; use for translated copy words and aggregation of horizontal bits. | report/sections/07_word_congruence.tex |
| n | Color-indexed `NorthView` retaining exact initializer/reset/seam alternatives; derive public boundary classifiers. | report/sections/08_north_view.tex |
| n | Replace CRT congruence tactic search by direct congruence composition; shared binary graph-composition depth bound including Fin-2 elimination. | report/sections/09_supplemental.tex |
| o | Direct South prefix clients; `theta a.val b` as aligned difference witness; specialize zero-base propagation. | report/report.tex pageheadings 4–5 |
| o | Two exact high-North/high-South equality-indexed fibers; eight boundary corollaries become specializations. | report/report.tex pageheadings 6–7 |
| o | Characterize an alternate index assignment by selection in the *same original word*; use `Selected.unique`, then transport marked-word correctness by function equality. | report/report.tex pageheading 8 |
| p | Positive factor/error-allowance parameter shared by `NativeHalfBinomial.upper_estimate_scaled` and `Ratio90.upper_estimate'`. | report.tex §A |
| p | Arbitrary-premise proof-fragment assembly, reverse-history suffix-length reference synthesis; old `fragment0`–`fragment3` wrappers. | report.tex §B |
| p | Successor-indexed fork certificate iff first; impossible output zero isolated once; no repeated predecessor cancellation. | report.tex §C |
| p | Projected support-difference separation using an additive quotient homomorphism; `NativeTemporalSupport54.clause_pair_one_zero`. | report.tex §D |
| p | Canonical square-pairing certificate witnesses (selector, slack, max), not just the output code; deterministic witness normal form. | report.tex §E |
| q | Remove internal inductions with unused IHs: `ObjectAdditionCancellation.addRel_zero_iff` and `ObjectNaturalZero.mulRel_zero_iff`; expose zero/successor decomposition earlier. | report/new-proof-simplifications.tex §2 |
| q | Negative norm excluded by squaring to a positive unit and using the fundamental unit's first-coordinate congruence; avoid separate descent. | same §3 |
| q | Three residue obstructions become ring substitutions into existing `ShortEquation.strong_ne_neg_one`; retain one mod-4 certificate. | same §4 |
| q | Heterogeneous minimum-sum saturation yields all block equalities, including coupled nonzero minima, with existing finite-sum equality library. | same §5 |
| q | Optional monotone local-certificate calculus for empty/union/insert on arbitrary internal model set carriers, with necessary naturalness premises. | same §6 |
| r | Simultaneous positive Pell-pair recurrence proves base monotonicity; compare actual values for `main_index_gt_first`, removing exponential detour. | report.tex §3 |
| r | Natural perturbation inequality and reusable power-sandwich theorem; separate arbitrary error budget; specialize both Pell upper bounds. | report.tex §4 |
| r | Exact integer half-binomial quotient: lower binomial block is the remainder; integer rounding replaces analytic extraction duplication. | report.tex §5 |
| r | One ordered tag/rule schedule syntax interpreted as semantic Boolean validity and PR program, with exact frozen-program erasure obligations. | report.tex §6 |
| s | Exact object-formula specifications normalized compositionally using local `simp only` over `Sat`, atoms, binders and environment projections; recursive expression spec becomes semantic fold. | report.tex §3 |
| s | Positive-scale Pell comparison shares upper/lower ratio proof; native denominator normalization stays explicit. | report.tex §4 |
| s | Optional integer recovery from two independent error budgets. | report.tex §5 |
| s | Optional shared union/insertion closure of observed internal certificate sets. | report.tex §6 |
| t | Identify annotated list codec with Mathlib's standard list coding; reuse encoded-list length; derive typed parent checker from raw decoder. | report/sections/02_encoding.tex |
| t | Local coefficient fiber as foundational convolution theorem; injectivity identifies a local source product; reuse selective zero theorem for separated rows. | report/sections/03_coefficients.tex |
| t | Pell fundamental criterion via magnitude of second coordinate; small ordinate (`y≤3`) proof and sharp failure at 4. | report/sections/04_pell.tex |
| t | First-exit minimality theorem returns an exit plus valid prefix, separated from tile geometry. | report/sections/05_first_exit.tex |
| u | Parameterized positive real error allowance for two Pell estimates. | report.tex §2 |
| u | Strong common native-rank lower envelope `(2q−1)(q²−1) ≤ R`, reused for coarse 40-bound and `3q` bound. | report.tex §3 |
| u | Centered integer induction for `interval_propagate`; alternative `Int.inductionOn'` axiom cost considered. | report.tex §4 |
| u | Least failure plus all earlier valid cases. | report.tex §5 |
| u | Wang matching constructed from shared horizontal edge fields, one nonzero bridge edge; retain unrestricted config/state wrappers. | report.tex §6 |
| u | Absolute-value trace bounds through existing absolute-value disjunction lemma. | report.tex §7 |
| v | Terminal-state code injectivity via the equivalence placing halt last; action-halt reflected through same map. | report/sections/04_encoding_action.tex |
| v | Machine step color proof splits only at old write site; destination test remains symbolic. | report/sections/05_machine.tex |
| v | `le_abs'.mp` directly supplies exterior trace disjunction. | same |
| v | Translated integer interval induction. | report/sections/06_interval.tex |
| v | Both horizontal edges from one pulse/bond signal. | report/sections/07_pulse.tex |
| w | Helical period as vector `(w,−1)` in `ℤ×ℤ`; integer-multiple closure replaces bilateral induction for row-zero and seam-time transport. | report.tex §3 |
| w | Two-radicand combiner identity proved algebraically before integer evaluation; avoid complex-square-root proof route. | report.tex §4 |
| w | Canonical twisted-band coordinate equivalence, signed address, quotient normalization, origin criterion; centralize repeated quotient/remainder arithmetic. | report.tex §5 |
| w | Construct matching rows/grid from shared edge fields with west(x)=E(x−1), east(x)=E(x); literal initializer and unrestricted step-pattern bridges. | report.tex §6 |
| x | `AnnotatedClosure.formCode_ge` from outer constructor minima; remove structural induction and quadratic bound infrastructure. | report/lean-proof-refinements.tex Proposal A |
| x | Derive strict multiplication via nonzero additive difference/no zero divisors before successor discreteness; Boolean-root theorem by cancellation; reverse two-file dependency. | same Proposal B |
| x | Helix/seam as period-one functions and integer-orbit rigidity. | same Proposal C |
| x | Preserve exact canonical band quotient matching/binding witness before existential erasure, reuse in marker module. | same Proposal D |
| y | Prune non-extremal rows in `index_span`: `k<21` already below final bound; only row 21 support inspected. | report/report.tex P1 |
| y | Integer multiples of two-dimensional helix period. | same P2 |
| y | Geometric width theorem `L+R≤N` from seam-free strip and translated seam; derive `N>2` without early-halting computation. | same P3 |
| y | Recover square-pairing branch from output threshold `pair(a,b)<m²+m ↔ a<b`; after maxima equal, two branches suffice. | same P4 |
| y | List-head bound via constructor equation `head_cons` and monotone addition. | same P5 |
| y | Existing `mul_geom_sum` supplies exact geometric identity, derive geometric upper bound without second induction. | same P6 |
| y | Optional internal order from strict total order; nonstrict-order definitional compatibility cost explicit. | same P7 |
| y | Supplemental Sidon polarization/factorization patch; acknowledged as same mechanism, not eighth headline proposal. | same supplement |
| z | Helical orbits via algebra of vector periods; seam-time transport likewise. | report.tex P1 |
| z | Fixed index-six Pell anchor (index five `xn_ge_a_pow` plus successor growth/monotonicity) instead of variable-exponent bootstrap. | same P2 |
| z | Signal masses from sufficient affine color statistics/moments; count semantic family quantities instead of recounting 942 entries per sum. | same P3 |
| z | Preserve whole receiver tile; canonical `stepTile` operating-row recognition via local determinism, south-row theorem by projection; avoid circular reliance on old conclusion. | same P4 |

## Broad and optional exclusions that cannot be called new

These are explicitly retained by the middle packets' prior-work ledgers, including
notes-only/deferred items. They are relevant when comparing a candidate even if its exact name differs.

* All generic list lookup, Option injectivity, recursor congruence, assignment naturality,
  concatenated witness existence, scanner fold/semiconjugacy and PR iteration abstractions.
* Shared residual sums of squares, shared semiring DAG soundness/completeness,
  degree/rename interfaces, topological invariant, common circuit tails and generator templates.
* Exact source low-register decoding (`q`, `L`, `N`, `X`), native-rank Nat/Int bridge,
  finite coefficient majorants, stencil fibers, convolution pushforward, support envelopes.
* Signed modular congruence as an equivalence up to sign; natAbs bridge and strict
  half-window uniqueness. Do not repackage `index_residues` sign branches as a new idea.
* Natural integer norm proof without rational detour; canonical exact rational roots;
  product-unit decomposition; finite support and invariant predecessor/reflection.
* General finite words/ZMod packing, monoid-algebra universal property, point-mass convolution
  rotation, exact scalar digit/carry decomposition, explicit cyclic carry classifications.
* Functional graph uniqueness, quotient projections, support-restricted evaluation/frame rules,
  and broad syntax-recursive pair induction are already exploratory directions.
* Generic finite controller certificates/rankings/SCCs are old. A concrete new invariant may differ.
* Internal recursive-graph preservation/fusion, definable induction transport, constructor views,
  single internal unique-existence induction, and all-model sealed completeness bridge are old.
* Shared proof tooling, profilers, import cuts, axiom audits, focused simp sets and generator
  synchronization are methodology, not new simplification mechanisms.

## Assessment for this iteration

The arithmetic territory is heavily covered. In particular, another common Pell estimate,
new coarse native-rank bound, growth/monotonicity argument, or generic norm minimization
interface should be rejected unless it removes an explicitly different obligation.

Two narrowly scoped arithmetic candidates survived the nearest-prior comparison:

1. `SignedPellResidue.signed_residue_cases`: apply `Nat.sub_eq_of_eq_add'` directly to the existing natural square identity `hn`, then `simpa only [pow_two, mul_assoc]` into `Pell.eq_pell`. This removes the intermediate product-form equation and a second `omega` proof. The existing `Jones1980.eq_pell_of_sq` was considered but rejected because it would add a heavy import; no new helper or import is needed. This changes the input boundary to Pell classification, before the signed-congruence/natAbs output transport covered by earlier work. The complete modified module compiled successfully, with no `sorryAx`; the exact module changes from 102 to 99 physical lines. Evidence is recorded separately in `arithmetic_proposals`.
2. `ThirteenFreshSeed.auxiliary_exists`: use already imported Mathlib `Pell.pell_eqz` and `Pell.dz_val` for the two integer norm equations, instead of casting `χ_sq` from natural numbers, proving subtraction guards, and normalizing the cast. This is theorem reuse at a constructive integer-norm boundary, not the earlier generic natural-norm/rational-detour proposal. The complete current modified module compiled successfully against cached baseline dependencies. No helper or import was added. The exact module went from 217 to 210 lines.

Searches of all 43 proposal packets and incoming prose found no `pell_eqz`/`dz_val` or direct `Nat.sub_eq_of_eq_add'` Pell-entry proposal. This absence is supplementary evidence only; the novelty claim rests on the exact changed obligations described above. The earlier signed-congruence and natural-norm proposals should still be explicitly acknowledged as adjacent prior work.
