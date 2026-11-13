# Signed ordinary-factor negative-unit prototype

`Ordinary12Residual.ordinary_factor_ne_negative_one` is a Lean theorem over
an arbitrary `IΣ₁` arithmetic model. Four arbitrary signed quantities are
encoded by eight natural coordinates. For the factor
`1 + AN² − d·(2b)²·Q`, its signed-pair evaluation cannot be the negative
unit. This is the abstract modulo-four exclusion needed for the ordinary
merger when `bn=2b`; it does not yet identify `AN`, `b`, `d`, and `Q` with
the actual twelve-variable literal or split its complete product.

`Ordinary12CarrierExclusions.lean` lifts the frozen parent's `first_bad` and
`main_bad` residue calculations to signed-pair factors without rank or
fixed-port hypotheses. `Ordinary12FactorSplit.lean` proves the abstract
three-factor positive-unit split when all three negative units are excluded.
`Ordinary12ComposedSplit.lean` combines these with the ordinary norm exclusion:
if the product of the three abstract factors is `+1`, each is `+1`. The
carrier exclusions are no longer hypotheses of that composed theorem. Their
identification with the literal graph remains a separate obligation.

The first two initial Lean attempts actually exited 1, respectively because
syntax evaluation and natural casts were not simplified; their failed sources
are retained. The corrected source actually compiled with exit 0 in session
`7263`, and its axiom report listed only `propext`, `Classical.choice`, and
`Quot.sound`. Those are Lean metatheory dependencies, not object axioms. The
initial exact session identifiers, source/object hashes and bounded overlay
record are in `initial-terminal-observations.json`.

An additional fresh replay actually exited 0 in session `65044`: it rebuilt
a file-by-file link overlay from the separately audited historical author's
20-module declared project dependency closure, checked 20 present object
hashes and 180 absent companion paths before and after, reran both expected
compile failures, compiled the corrected file in a third isolated output,
and checked Lean's direct dependency paths. The replay receipt preserves all
three commands, full output, exits, source hashes and available object hashes.
The failed attempts emitted `sorryAx` because elaboration failed; the final
successful report did not. This is a bounded single-author exploratory replay,
not the matched guarded project workflow; package-transitive, dynamic and
between-check ancestry are not fully authenticated.

To reproduce when the recorded ephemeral historical providers still exist,
choose **new** output and receipt paths, for example:

```sh
python3 Computability/DiophantineConsistency/research/ordinary12-ipra-bridge/model-prototype/replay.py \
  --output /tmp/ordinary12-model-residue-new \
  --receipt /tmp/ordinary12-model-residue-new-receipt.json
```

The compact44 `β=2^590069−1` and 2011 `β=2^94517−1` are different. The
actual graph binding, early rank and
rational-integrality recovery, compact44 checker calibration, and existence
of an iPRA proof remain open. No large project rebuild was run for this
prototype.

The clean carrier, abstract split and composition actually compiled with exit
0 in sessions `75631`, `28036` and `89671`. An earlier carrier compile also
exited 0 with an unused-simp warning, and its source and observation are
retained. A separate fresh composed replay actually exited 0 in session
`86605`, rebuilding the bounded base overlay and all three clean modules with
direct-import checks. Its receipt includes every compiler output and rechecks
the inherited seed hashes. It has the same single-author and external ancestry
limits as the earlier replay. To reproduce with fresh paths, run

```sh
python3 Computability/DiophantineConsistency/research/ordinary12-ipra-bridge/model-prototype/replay_composed.py \
  --output /tmp/ordinary12-composed-new \
  --receipt /tmp/ordinary12-composed-new-receipt.json
```
