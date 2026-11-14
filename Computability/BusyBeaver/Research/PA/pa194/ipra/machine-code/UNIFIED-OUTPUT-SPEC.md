# Unified site-25 output interpretation

`PA194UnifiedOutputSpec.selectedOutput` identifies the interpretation of the
right-hand term in `PA194UnifiedSourceStepSentence` in **every model of candidate
PRA**. If original logical register 8 is zero, the packed output is control 24,
left tape 1, path 27, a model-valued zero run and the *unchanged complete source
file*. Otherwise it is control 24, left tape 1, path 26, a model-valued zero
run and the source file with exactly logical register 8 updated to its
primitive-recursive predecessor. All other register values, the spare and the
numeric suffix remain arbitrary model elements. The explicit run lengths and
full encoded arithmetic appear in the theorem source.

`zeroOutputWord` is a model-uniform normalization of the numeric zero output
to the path-27 word; `zeroOutput` and `positiveOutput` establish the respective
conditional interpretations. The latter uses the model zero/successor
exhaustion and successor-of-predecessor relation to identify the actual
argument. `selectedOutput` chooses the correct case. Each theorem's Lean
axioms are `propext`, `Classical.choice`, `Quot.sound`; none uses `sorryAx`.
The displayed if-then-else is a **Lean metatheory** expression. This file does
not itself prove an iPRA branch implication, a full model-length literal/source
simulation, or either direction of PA consistency versus nonhalting.

## Staged source replay

`check-unified-output-spec.sh` recompiles the exact output specification in a
fresh output root, checks its source hash and all four printed axiom audits,
and refuses inherited Git-internal overrides. It uses a previously built
coherent PA194 machine root, the general project and Foundation objects, and
Lake/Mathlib. The checker pins the unified-build manifest and three imported
objects, but does not itself rebuild the machine closure or verify all its
transitive dependencies; hashes alone do not establish provenance. Create and
audit that root with the separate coherent build workflow before relying on
this suffix replay. The coherent build itself retains its prior startup/header
baseline and general logic foundations as explicit prebuilt prerequisites.
All shown roots are session-local.

From the repository root:

```sh
base=Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code
bash "$base/check-unified-output-spec.sh" \
  "$PWD" \
  "$base/PA194UnifiedOutputSpec.lean" \
  /dev/shm/pa194-unified-coherent/build \
  /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib
```
