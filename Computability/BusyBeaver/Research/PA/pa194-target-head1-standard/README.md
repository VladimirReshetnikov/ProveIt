# Standard binding of the fixed target h1 code

`eval_machineHead1` proves that the exact fixed candidate-PRA h1 generator from
`pa194-target-head1` evaluates on standard natural inputs to the actual
`PA196.Commands.Code.head1` formula used by the PA194 numerical calculus.
`head1_code_derivation` then constructs the corresponding actual
`PA194DerivationCompiler.Derivation.h1`.

The proof reconciles the candidate-PRA interpretation's natural addition,
multiplication, numerals, and triangular pairing with the concrete Nat
operations. It uses the separately proved all-model constructor equations and
the standard pairing witness equality; it does not infer nonstandard behavior
from standard evaluation.

The result is specific to the h1 axiom. It does not supply a uniform
parameter-free definition of the complete target proof checker, justify other
target rules, give a source proof compiler, or prove PA/machine calibration.

The final module passed a fresh Lean 4.32 suffix build against the retained
head-1, source-inversion, target-compiler, project and Foundation overlays.
The printed theorem axiom dependencies are `[propext, Classical.choice,
Quot.sound]`, without `sorryAx`. Its full nested replay is pending; the
source-shift prerequisite has separately passed its full replay.

From the repository root, with matching audited project and Foundation objects:

```sh
IPRA_LEAN_OVERLAY=/path/to/project/lib \
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
  Computability/BusyBeaver/Research/PA/pa194-target-head1-standard/check.sh
```

The script rebuilds the prerequisite chain under `/dev/shm` by default; set
`TMPDIR` for another suitable temporary directory.

An independent suffix replay recompiled this module against the separately
checked target-generator and derivation dependencies, reusing the other
prerequisite overlays. Both reported theorems had no `sorryAx` dependencies.
