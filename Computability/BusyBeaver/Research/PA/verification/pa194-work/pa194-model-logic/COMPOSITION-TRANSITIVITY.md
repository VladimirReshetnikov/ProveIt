# Source order-isomorphism transitivity, conditional on Separation

This source-natural-deduction port of `Computability/BusyBeaver/Research/PA/verification/other-machines/jamesyc-upstream/pa196/M6PA/Calibration/RelationalIsoComposition*.lean` constructs finite composition prefixes by ordinal induction, verifies the resulting graph is an order bijection, and concludes `compositionIsoTransitivity`: from source equality, empty set, adjunction, intersection, the exact graph-parameter-closed Separation instance, `domain a`, and isomorphisms a→b and b→c, it derives `orderIso a c`.

The Separation premise remains explicit. This package alone does not discharge it in the source theory, prove translated PAeq transitivity, establish proof compilation, or yield an iPRA implication.

Reproduce from the repository root with a fresh empty output:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-logic/check-composition-transitivity.sh "$PWD" /dev/shm/pa194-composition-transitivity-repo-NEW
```

The checker rebuilds 29 new source modules and a seven-report audit in a single output. It uses the separately replayed inverse-graph construction, source ordinal-induction proof, graph operations, Foundation, and other prebuilt objects from the explicitly enumerated paths; it does not rebuild the full dependency closure.
