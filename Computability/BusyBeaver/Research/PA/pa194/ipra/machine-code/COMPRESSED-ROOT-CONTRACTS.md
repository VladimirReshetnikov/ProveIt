# Exact literal contracts between source roots

The runtime normalizer combines adjacent affine runs and removes trailing
blanks on the left. `PA194CompressedNormalization.matchesCorrect` proves that
its accepted endpoint comparison preserves the packed configuration in any
PRA model. Its run concatenation and blank-run equations use open induction
on the model-valued lengths.

`PA194CompressedRootContracts.contractCorrect` uses the actual folded
transition table, the source-program paths and the original compressed
root-frame layout. Given a successful finite contract and the model-local
register oracle, it produces a positive model-valued clock from the exact
literal input frame to the specified literal output frame. The literal gap
is the common model parameter plus the standard offset dictated by the path
length and the prior effect. `noInteriorHalt` rules out an earlier halt in
every covered model with IΣ₁, since a halt persists and the final root
control is 24.

The root-to-root result takes the register oracle, the relationship between
its box values and the two register-file arguments, and the Boolean success
of the finite certificate as premises. Those are the inputs to supply for
a completed source instruction and for internal iteration.

Run from the repository root with a fresh output.

```sh
python3 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-compressed-root-contracts.py \
  "$PWD" Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code /dev/shm/pa194-compressed-root-contracts-repo \
  Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/compressed-root-contracts-stages.txt
```

The three modules rebuild in one output against the listed dependency
stages, including the repository-built compressed executor and run-scan
modules. The checker snapshots its manifest and each selected direct
input. The prebuilt physical, M6 and Foundation transitive source closure
remains unauthenticated.
