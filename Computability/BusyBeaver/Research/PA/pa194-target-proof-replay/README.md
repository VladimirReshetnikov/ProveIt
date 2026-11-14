# Replay of accepted target lines

`PA194TargetReplay.lean` proves that an accepted target line continues to
produce the same result at a later stage when every previously accepted
referenced entry is preserved. The all-model `extended_replay` theorem covers
the complete independent dispatcher, including MP, generalization, all leaf
forms and the rho8/gate guards. The hypotheses are an ordering of the two
stages and `AgreeAccepted`, which requires preservation of nonzero history
entries at offsets below the old stage. The theorem works in every
candidate-PRA model with IΣ₁ arithmetic, including nonstandard values.

The theorem deliberately makes no preservation claim for rejected lines:
a line whose reference was formerly out of bounds can become accepted after a
prefix is added. This replay property is a step toward composing proof
programs; it does not itself prove MP closure, construct the concatenated
vector, supply a finite code for the transformation, or establish source or
machine calibration.

Run from the repository root with the matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/pa194-target-proof-replay/check.sh
```

The final module was rebuilt against the freshly rebuilt generalization module
and previously checked deeper prerequisites. A full nested replay of this
wrapper has not yet been completed. Its printed axiom dependencies contain no
`sorryAx`.

An independent suffix replay recompiled the accepted-line replay module using
the separately checked target proof-leaf object and retained generalization and
prerequisite overlays. The reported theorem axioms did not include `sorryAx`.
