# Native iPRA sentence for the PA194 positive branch

`PA194PositiveBranchSentence.lean` states an explicit universally closed
primitive-recursive term equality for `PA194Stepper.stepper`. Its twelve
object-language variables supply a padding value k and the eleven logical
source arguments. Argument 8 is syntactically replaced by `m+1`, where `m`
is the value at the variable previously occupying that slot. All other source
arguments, including the spare and numeric suffix, are arbitrary.

Both sides use packed control 24 and left tape code 1. The input's right tape
is the fixed source path 25 followed by the model zero-run/delimiter/full
source file; the output's right tape is path 26 followed by its corresponding
zero run, delimiter, and **exact** file
`sourceFileCode (Function.update args 8 m)`. The primitive-recursive term
`clock` is the positive-branch clock from
`PA194Path25To26.positiveBranchPath25To26`; it differs from the zero branch.
The source's term definitions are the authoritative full specification.

`modelSentence` proves the equality in every candidate-PRA model by applying
the model-uniform path theorem to the values of the syntactically substituted
arguments and proving the corresponding updated-file identity. `classicalPRA`
uses completeness to derive the universal closure in candidate classical PRA.
`nativeIPRA` transfers the universally closed equality to
`IPRAStandardTheory.standardTheory`. This establishes a model-uniform finite
machine step, not either direction of a consistency/nonhalting equivalence.
Lean's three printed axiom reports contain `propext`, `Classical.choice`, and
`Quot.sound`, with no `sorryAx`; these are metatheoretic Lean assumptions,
not additional axioms of the object theory.

## Replay and limitations

`check-positive-branch-sentence.sh` pins and rebuilds thirteen source modules
in one fresh output. They include `PRAEqualityToIPRA`, the source file and path
identifications, the positive two-pass/site-26/path-25-to-26 results,
`PA194StartupSentence` (whose term helpers are reused), and the native sentence.
It checks the three named sentence axiom reports and rejects `sorryAx`.

The explicitly supplied ordered roots below include multiple prebuilt PA194
machine overlays and general project/foundation objects. All other transitive
imports, including the deeper machine dependency closure and Lake/Mathlib,
remain precompiled. The checker neither rebuilds nor authenticates those
transitive objects; source hashes alone do not establish object compatibility.
Thus this is a staged suffix replay, not an independently verified coherent
full-closure build. All roots shown are temporary session-local artifacts.

From the repository root:

```sh
roots=/dev/shm/pa194-dense-startup-agent:/dev/shm/pa194-standard-bridge:/dev/shm/pa194-startup-preserved:/dev/shm/pa194-model-neighborhood:/dev/shm/pa194bridge-probe/build:/dev/shm/binary-tape-code.1tywTlrA:/dev/shm/pa194-header-coherent/hardlink-baseline:/tmp/current14-standard-fresh-build-20261104/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib
base=Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code
bash "$base/check-positive-branch-sentence.sh" \
  "$PWD" \
  "$base/PA194PositiveBranchSentence.lean" \
  "$roots"
```

The checker rejects inherited Git internal overrides and does not set them.
