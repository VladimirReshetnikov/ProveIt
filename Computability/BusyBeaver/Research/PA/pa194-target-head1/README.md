# Target-machine Cantor code and one h1 certificate

`PA194TargetCantor.lean` constructs a fixed candidate-PRA witness for the
machine's triangular Cantor pairing, using its actual bounded polynomial graph
and a candidate-PRA witness theorem. `modelCantorSelected` establishes its
value for every input in every candidate-PRA model, including nonstandard
inputs. This triangular pairing is the numerical machine/calculus pairing; it
is distinct from Foundation's own pairing used to package proof certificates.
The witness is chosen once and then used in all models.

The module composes that witness into fixed codes for the machine's implication,
universal quantifier, negation, existential quantifier and first AX head.
`machineHead1_model` proves the exact head-1 expression in every covered model.
In candidate-PRA models whose arithmetic reduct satisfies IΣ₁,
`Head1Certificate` is a Σ₁-definable relation for a single tagged h1 leaf, and
`head1Leaf_model` constructs such a certificate and theorem number. The
`head1Certificate_definable` theorem is a model-level definability statement;
it is not a proved parameter-free uniform formula for the whole checker.

Separately, `cantor_eq_machine` and `eval_fixedCantor` identify the triangular
pairing and the witness code with the machine's exact pairing on standard
naturals. `head1_exact_standard` constructs an actual
`PA194DerivationCompiler.Derivation.h1` for the independently defined standard
head-1 expression. The final equality between the **complete** fixed h1
code's standard evaluation and that expression is not yet established; the
candidate-model and standard Nat arithmetic instances must be reconciled.
Consequently the all-model leaf certificate must not yet be treated as a
verified port of the upstream target checker. Other target rules, full proof
certificates and their soundness, the source-rule compiler, PA calibration,
and the machine reductions are also open.

The final module passed a fresh Lean 4.32 suffix build against the retained
source-inversion, target-compiler, project and Foundation overlays. The printed
theorem axiom dependencies are `[propext, Classical.choice, Quot.sound]`,
without `sorryAx`. The full nested replay below is pending. The source-shift
prerequisite has passed its own full replay; the other retained prerequisite
objects must be rebuilt by the script for a complete replay.

From the repository root, with matching audited project and Foundation objects:

```sh
IPRA_LEAN_OVERLAY=/path/to/project/lib \
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
  Computability/BusyBeaver/Research/PA/pa194-target-head1/check.sh
```

The script uses `/dev/shm` for temporary objects by default. Set `TMPDIR` to
another suitable temporary directory if required.
