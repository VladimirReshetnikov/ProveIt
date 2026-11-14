# Candidate-PRA target modus-ponens step

`checkMP : Code 3` checks a modus-ponens step from three numeric inputs: an
accepted minor value, an accepted major value, and the requested conclusion.
A theorem number `a` is represented by the accepted value `a+1`; zero denotes
rejection. `check_correct` proves in every candidate-PRA model with an IΣ₁
arithmetic reduct that the step returns `b+1` exactly when there is an `a`
with minor `a+1` and major `impValue a b + 1`. Thus zero inputs reject. All
inputs, including `a`, may be nonstandard.

`impValue` uses the machine's triangular Cantor pairing. The separate standard
Nat theorem `eval_impBinary` proves that the corresponding fixed candidate-PRA
constructor evaluates to the actual PA194 numerical implication
`PA196.Commands.Code.I`. This standard identification does not replace the
all-model checker-step proof.

The step receives previously accepted values as inputs. No proof-history
lookup or verification, generalization, complete target checker, source proof
compiler, PA calibration, or machine reduction is proved here.

The final module passed a fresh Lean 4.32 suffix build against retained h1 graph,
checker, standard binding, earlier source and target suffixes, and audited
project and Foundation overlays. Its printed main theorem axiom dependencies
are `[propext, Classical.choice, Quot.sound]`, without `sorryAx`. The full
nested replay using the script below is pending.

From the repository root, with matching audited project and Foundation objects:

```sh
IPRA_LEAN_OVERLAY=/path/to/project/lib \
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
  Computability/BusyBeaver/Research/PA/pa194-target-mp/check.sh
```

The script rebuilds its prerequisite chain under `/dev/shm` by default; set
`TMPDIR` for another suitable temporary directory.

An independent suffix replay recompiled the target MP step against separately
checked h1 and source-search prerequisites, reusing the other overlays. The
reported theorem axioms did not include `sorryAx`.
