# Source order-isomorphism symmetry, conditional on Separation

This is a source-natural-deduction port of the finite inverse-graph construction in `Computability/BusyBeaver/Research/PA/other-machines/jamesyc-upstream/pa196/M6PA/Calibration/RelationalIsoInverse*.lean`. It constructs an inverse prefix by ordinal induction, proves that the prefix reverses an order bijection, and concludes `inverseIsoSymmetry`: given source equality, empty set, adjunction, intersection, the exact graph-parameter-closed Separation instance, `domain a`, and `orderIso a b`, it derives `orderIso b a`. The separation premise is explicit. This package alone does not discharge the premise in the source theory, prove the translated PAeq symmetry axiom, establish proof compilation, or yield an iPRA implication.

Reproduce from the repository root with a fresh empty output:

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-logic/check-inverse-symmetry.sh "$PWD" /dev/shm/pa194-inverse-symmetry-repo-NEW
```

The checker rebuilds all 26 new source modules and an audit module in a single output, and checks seven named axiom reports for `sorryAx`. It uses retained prebuilt objects from the explicitly enumerated `LEAN_PATH` overlays, including the source ordinal-induction proof and graph operations. The separately source-replayed mulZero baseline provides the common point-graph source objects. Full dependency-closure replay is not claimed.
