# PA194 unified native source-step sentence

`PA194UnifiedSourceStepSentence.nativeIPRA` proves, in the repository's native
`IPRAStandardTheory.standardTheory`, a universally closed equality of
primitive-recursive terms for one model-uniform finite literal-machine step.
The left side applies `PA194Stepper.stepper` to **one canonical packed input**:
control 24, left tape 1, and the path-25 header, zero run, delimiter and the
complete `sourceFileCode` of the original eleven logical input arguments. The
12 quantified variables contain the padding k followed by those arguments;
argument 8, the tested source register, is variable 9.

`selectCode` tests that original register and chooses the applicable branch
clock and output. At zero it selects the checked zero-branch result; at a
successor it selects the positive-branch result with `m = pred(register 8)`.
The latter retains the exact updated file term for replacing register 8 with
m, including the spare and arbitrary numeric suffix. The zero branch's input
header is initially given by eight doublings, while the positive branch uses
the path-25 word; the checked `PA194Path25Input.site25Input` identifies the
two for arbitrary candidate-PRA model elements.

`PA194SelectedInputFile.selectedFile` proves that the branch-selected input
file equals the original unmodified file in every candidate-PRA model, using
zero/successor exhaustion and the predecessor identity. The stronger
`PA194SelectedInputFrame.selectedInput_eq` combines this file agreement with
the path-25 header identity and proves equality of the **entire selected packed
input** and the canonical original input. The unified sentence then composes
that result with the already checked `PA194BothBranchesSentence` equality,
uses completeness to obtain a candidate classical PRA proof, and transfers the
universally closed equality to native iPRA. All named axiom audits are
`propext`, `Classical.choice`, and `Quot.sound` without `sorryAx`; these are
Lean metatheoretic axioms, not added object-theory axioms.

This sentence is one unconditional, model-uniform finite-step component; it
does not by itself identify the full physical runtime with every source
controller instruction or establish either direction of the PA consistency /
literal-machine nonhalting equivalence. The correspondence with standard
literal zipper frames is a separate result; arbitrary model numeric suffixes
are retained here and are not represented as arbitrary nonstandard finite
Lean lists.

## Staged replay and limitation

`check-unified-source-step.sh` pins and recompiles 21 source modules into one
fresh output, including both branch sentences, the selected-file and packed
input identities, the unified sentence, their immediate path/step modules,
and equality transfer. It checks the listed axiom audits and refuses any
`sorryAx` in the build logs.

The explicitly supplied ordered roots below include several **mixed prebuilt
PA194 machine overlays** and general project/foundation overlays. The deeper
transitive closure, Lake and Mathlib are not rebuilt or authenticated by this
checker. Source pins alone cannot prove compatibility of imported objects.
This is a staged suffix replay, not a clean coherent full-closure rebuild; all
shown roots are session-local and must be replaced with matching dependencies.

From the repository root:

```sh
roots=/dev/shm/pa194-dense-startup-agent:/dev/shm/pa194-standard-bridge:/dev/shm/pa194-startup-preserved:/dev/shm/pa194-model-neighborhood:/dev/shm/pa194bridge-probe/build:/dev/shm/binary-tape-code.1tywTlrA:/dev/shm/pa194-header-coherent/hardlink-baseline:/tmp/current14-standard-fresh-build-20261104/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib
base=Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code
bash "$base/check-unified-source-step.sh" \
  "$PWD" \
  "$base/PA194BothBranchesSentence.lean" \
  "$base/PA194SelectedInputFile.lean" \
  "$base/PA194SelectedInputFrame.lean" \
  "$base/PA194UnifiedSourceStepSentence.lean" \
  "$roots"
```

The checker rejects inherited Git internal overrides and does not set them.

A later [coherent machine-specific rebuild](UNIFIED-COHERENT.md) passed from
a previously source-built startup/header baseline, without machine-specific
fallback overlays. The baseline and general foundations remain staged inputs.
