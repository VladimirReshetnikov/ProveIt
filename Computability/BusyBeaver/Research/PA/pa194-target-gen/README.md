# Candidate-PRA target generalization step

`checkGen : Code 2` takes an accepted premise value and a quantifier label.
The accepted encoding of theorem number `a` is `a+1`, and zero means rejection.
`check_correct` proves in every candidate-PRA model with an IΣ₁ arithmetic
reduct that the result equals `y+1` exactly when the premise equals `a+1` for
some `a` and `y = allValue label a`. Zero premise values reject. Inputs and
witnesses may be nonstandard.

The independent standard Nat theorem `eval_allBinary` identifies the fixed
constructor with `PA196.Commands.Code.U`, the universal-quantifier encoding
used by the actual PA194 numerical calculus. The all-model rule step is proved
separately and does not follow merely from this standard binding.

This checks one step given an already accepted premise. It does not look up or
validate proof histories, implement a complete target checker, supply a source
proof compiler, establish PA calibration, or prove a machine reduction.

The final module passed a fresh Lean 4.32 suffix build against the retained MP,
h1, source, target, project and Foundation overlays. The printed theorem axiom
dependencies are `[propext, Classical.choice, Quot.sound]`, without `sorryAx`.
A full nested replay using the script below is pending.

From the repository root, using matching audited project and Foundation objects:

```sh
IPRA_LEAN_OVERLAY=/path/to/project/lib \
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
  Computability/BusyBeaver/Research/PA/pa194-target-gen/check.sh
```

The script rebuilds its prerequisite chain under `/dev/shm` by default; set
`TMPDIR` for another suitable temporary directory.
