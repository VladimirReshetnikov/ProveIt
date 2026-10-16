# Batch 150 / source 04 mathematical and executable review

Pin: `de047657e193ec605e930eaf149a44a38031820b`; compiler inputs pinned upstream
`297ab8df7e5de329605c3875b4934643b371a5e3`, imported helper cutoff
`5e5603303de0815c59a792763704bb00589fed99`. Full delivered report (all eight
sections), references, README, checker, tests, replay driver and relevant
machine-control source read on the stated untouched extraction; all executions
used this separate scratch copy. No checksum manifest was inspected or run,
no source patch was needed, and no proof-assistant build was attempted.

## Mathematical verdict and novelty

No concrete flaw found in the ordinary mathematical calibration or the exact
Q-tableau contract. The theory is equality-free EPSC with arbitrary matrices
and finite parameter lists, not one second-order all-relations axiom. The
profile-fragment decoder is locally bounded before Separation; nonemptiness
of the fragment permits the second decoder edge under the EPSC gate. The
transitive cover contains every subset of the supplied source. Exact classes,
raw Separation/Union, the disjoint two-bound gate and the return to PSC follow
without first-argument profile congruence. The Russell-root exact-image gate
explicitly excludes x∈A in its root branch, avoiding the outside-container-copy
pitfall. Hereditary saturation, purity cut, interpreted uniqueness up to D,
successor closure, and internal W then L arguments retain the necessary
functional-Replacement and internal/external-model distinctions. This mostly
consolidates prior sources 08/13/14 arguments; it does not supply a new serialized
proof-code or Lean calibration.

The actionable new frontend uses exactly R(i,j) and Q(A,B)=∀x¬(A∧B). Q binds
index zero in both children. Its lift/rebase operations preserve internal
bound indices and redirect only the base environment. The direct EPSC maps
are (2,0,parameters), (1,0,parameters), and (0,1,parameters) in the respective
three-binder contexts; the parameter offsets and all universal closures are
correct. The scope recurrence is exact, and every natural has a terminating
unambiguous formula decode. Both primitive constructors suffice for ordinary
equality-free FOL over nonempty domains; the displayed macro translations
handle vacuous binders explicitly.

Positive Q branches over one existing parameter; negative Q introduces the
next fresh symbol and both children. Both branches must close, entries remain
available, and saved branch counters make label reuse on disjoint branches
safe. The ordinary completeness argument schedules old positive entries at
later witnesses and produces a nonempty canonical model from an open fair
path. Every checker iteration consumes an operand. Public accepts() reaches
only internally generated positive EPSC roots, never the generic signed-root
helper. Exact EOF and atomic ordered-pair checks prevent forged conclusions,
missing siblings, parameter leakage, or a fresh witness identified with an
old symbol. I found no capture or false-acceptance hole in this code contract.
The abstract search/calibration theorem is ordinary ZFC mathematics, not a
proved binary-machine endpoint.

Schonfinkel's primary English translation p. 358 confirms the historical joint
connective/binder attribution:
https://content.wolfram.com/sites/43/2020/12/Schonfinkel-OnTheBuildingBlocksOfMathematicalLogic.pdf
The Andreka–Nemeti primary paper explicitly requires the ternary vocabulary
and recursive translation into three commuting modalities; it supports the
report's distinction from the retired binary C/G engine:
https://arxiv.org/pdf/1111.0995

## Actual executions

`uv run --no-project python reproduce.py`: PASS in 4.027 s. It runs both main and
additional checker suites, all 3 exact examples, the fixed 269 recipe and the
independent 4,533-pair RM verifier. `uv run --no-project python code/qnand.py
--prefix 1000`: PASS in 0.214 s, no accepted candidate, no consistency conclusion.
The main suite gives 10,000 numeric roundtrips; 20,480 rebasing and 40,960 shift
semantics cases; 320 independent evaluator comparisons; 256 matrices / 4,608 EPSC
finite-graph comparisons; 1,000 identity certificates; 1,000 wire roundtrips;
13 invalid regressions; cross-variable UI: 5 actions / 8 operands / 2 leaves and
variable identification: 13 actions / 20 operands / 4 leaves. Extra audit:
16 gapped-parameter matrices/256 comparisons, all 16,383 bitwords through length 13
(7,815 valid, 8,568 invalid), 255 shortlex candidates. These are finite diagnostics.

Both optional advertised grammar sweeps replayed: initial 960 recipes in 7.887 s
and targeted 6,000 in 34.593 s. Every delivered comparison key, including both
histograms, matches. There are 6,720 distinct recipes after overlap. All five
fixed output artifacts are byte-exact: DAG, named table, total table, grammar,
and RM certificate. The fixed table is 207 decision + 62 framework = 269 states,
537 named rows / 538 total rows; total table hash is
`5473038a3a07ab73677229208a91fc6e4bc4062603710f9ed48410bc784c522c`.
Certificate roots are pinned original 219 → 207, 4,533 pairs, including both
EDecnz branches (2,601 increment / 1,931 decrement / one halt). It is an exact-word
register correspondence, not a newly calibrated theory or binary compiler.

One engineering method limit was independently resolved. Delivered
`machine_control/library_grammar.py:120` charges only `cost=len(nn)` and
`:127` compiles the first node-count winner. Dispatcher depth actually varies.
The separate `audit_costs.py` replay charges every one of 6,720 distinct recipes
as decision nodes + 55 + depth, checks preservation of every control leaf, and
actually compiles/re-extracts each depth representative and every predicted
candidate≤269 (21 tables). Depth histogram: 6: 1, 7: 5,029, 8: 1,509, 9: 166, 10: 15.
Minimum 269 survives, with 16 total-cost minimizers. Thus there is no false
lower-state result, but future optimization must use full cost. Exact trial
records are in `exact_cost_replay.json`; this added audit took 41.061 s.

## Current-repository reconciliation

The report's snapshot predates several current results. Its statement that
the Lean 253 layer covers only 1,024 steps is now stale:
`Boot253.lean:958` proves `ZipRep (machine253.run 312975) bootTarget253`, with
state 33 / head −17 and the full finite tape frame including 158 spare blocks.
It still does not prove first arrival, RM 330 correspondence or runtime.
`logical_engine_completeness.md:268` now states source 19's 268-state retained
full-logic conjunction control; `:275–277` records 53,760 layout choices and
278/282-state full-equality PSC controls. The new report's269/279 best-control
comparison should remain dated to its cutoff. `TarskiComplete.lean:520–524`
now gives conditional named-variable full-equality completeness with explicit
hC/hC0 assumptions; it is not a proof of this new Q frontend.

RawPSCModel already has actual equality-free-Form instance adapters, raw power,
cover, Separation and Union (`:147–190`), purity cut/saturation/upward closure
(`:257–274`). `pure_hull_of_model:292–298` still requires the supplied relation's
definability, invariant and pure local bound. The full raw EPSC quotient,
its uniform proof transport, this Python checker and compiler/internal ZFC
endpoint remain unformalized. No current valid machine claim is refuted.

Recommended placement: complementary addition to the existing closure-kernel
host, no source superseded and no alteration of the seeded base article.
The new Q frontend is worth a measured prototype; its full matrix generator,
rebasing, arithmetic, environments, saved branches, freshness, outer search
and blank initializer must all be counted. A two-constructor syntax count
is not a binary-state estimate. Keep the old 269 control separate from Q.

Full machine-readable counts, commands, times, comparison outcomes and scope
are preserved in `verification.json` and `review.json` beside this dossier.
