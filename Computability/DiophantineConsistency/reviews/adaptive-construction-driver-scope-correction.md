# Correction to inherited construction-driver scope labels

A family of adaptive-construction replay drivers was copied from the initial correction-quotient driver. Their `state.json` files retain the literal string `model-uniform main-correction quotient from explicit Pell seed identities; no positivity or actual assembly claim`, even when the listed modules prove a different result. This is a metadata error. In particular the words “no positivity” do not describe the positive-witness clients. The field is an explanatory label; the independently replayed module names, source/object/log hashes, guard checks and recorded exit statuses are unaffected. Historical state files and their evidence manifests are preserved unchanged.

The actual scope of each packet is given by its named theorem and corresponding review:

- `adaptive-construction-correction2011-author.md`: additive main-correction quotient.
- `adaptive-construction-correction-positive2011-author.md`: positive main correction under explicit seed-index hypotheses.
- `adaptive-construction-correction-seed2011-author.md`: positive correction from the actual outer-seed relation.
- `adaptive-construction-seed-size2011-author.md`: first-seed ordinate size.
- `adaptive-construction-first-positive2011-author.md`: conditional positive first carrier.
- `adaptive-construction-first-seed2011-author.md`: first carrier from the outer seed.
- `adaptive-construction-first-actual2011-author.md`: first carrier from the actual vector, seed and explicit radix/rank facts.
- `adaptive-construction-transport-positive2011-author.md`: multiplier and transport-quotient positivity under explicit hypotheses.
- `adaptive-construction-transport-actual2011-author.md`: transport-quotient positivity from the actual old equations and explicit radix/rank facts.
- `adaptive-construction-main-exact2011-author.md`: exact main shift and scaled norm.
- `adaptive-construction-main-seed2011-author.md`: positive main coordinate and scaled norm from the outer seed.
- `adaptive-construction-main-factor2011-author.md`: literal main-factor unit from explicit additive carrier and norm data.
- `adaptive-construction-main-witness2011-author.md`: literal main-factor unit for the explicit witness.
- `adaptive-construction-first-factor2011-author.md`: literal first-factor unit from explicit additive carrier and norm data.
- `adaptive-construction-aux-exact2011-author.md`: exact auxiliary orientation from explicit seed data.
- `adaptive-construction-aux-factor2011-author.md`: literal auxiliary-factor unit from its two norms.
- `adaptive-construction-aux-witness2011-author.md`: literal auxiliary-factor unit for the explicit witness.
- `adaptive-construction-factor-lemmas2011-author.md`: reverse square-factor and strong-factor lemmas.
- `adaptive-construction-factor-zero2011-author.md`: literal zero from four signed factor units, including positive shifting.
- `adaptive-construction-witness2011-author.md`: explicit adaptive vector and its strong-factor unit.
- `adaptive-construction-witness-positive2011-author.md`: positivity of that vector from explicit coordinate assumptions.

This correction applies equally to peer runs using those copied drivers. The separate Assembly bridge driver has its own accurate scope, and the standalone Assembly projection driver has its own accurate scope. No item in this list establishes the current-source Assembly or an HA proof-existence result by itself. Future construction drivers should set their own scope string rather than inherit the quotient label.

The [frozen state inventory](adaptive-construction-driver-scope-correction-evidence/states.json) maps 55 distinct affected state snapshots to their actual primary module and corrected scope, including 41 recorded passes and 14 recorded failures, with 88 observed original or evidence paths. Every original state is copied byte-for-byte under its SHA256 in the evidence directory; the original files are unchanged. Its [57-file manifest](adaptive-construction-driver-scope-correction-evidence/FILES.json) has SHA256 `84ce4bb860f74c23e87d26d0a7c0d3559502749ff4edf5cc37747ae6783c1c4d`. The packaged driver records the inventory procedure; this is a snapshot of states visible when it was run, not a claim about later runs. The initial quotient states, whose label correctly describes their primary theorem, are excluded.

Root independently rehashed all 57 manifest entries, checked their recorded
byte counts, and verified the inventory contains 55 states with the stated
41 PASS and 14 FAILED statuses. The historical state files remain unchanged.
