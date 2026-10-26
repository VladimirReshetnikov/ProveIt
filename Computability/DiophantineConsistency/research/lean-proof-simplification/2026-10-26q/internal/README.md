# Delete two unused internal inductions

## Result and status

The source targets are `ObjectAdditionCancellation.addRel_zero_iff` and
`ObjectNaturalZero.mulRel_zero_iff`, at ProveIt commit
`9bd29079d5e1c6cc1c0bcaee6cb57d59b835cba9`.

Both old successor branches discard their induction hypotheses. A single
zero/successor decomposition of the second operand is sufficient. The patches
remove the private `zeroSumStage` / `zeroProductStage` formulas and their
satisfaction specifications. They retain `cancellationStage` and its genuine
induction, all public theorem statements, the reverse implications, and the
arbitrary-model/internal-omega domains.

**Checked:** `InternalZeroCore.lean` compiles with Lean 4.32.0. Its two generic
semantic theorems have empty axiom lists. Both patch variants pass
`git apply --check` against exact copies of their pinned source files. Public
target headers are byte-identical. The existing zero/successor block is moved
byte-identically in the production variant.

**Not checked:** the repository-dependent modified modules, the extraction
module in its actual dependency environment, and downstream clients have not
been compiled. A standalone semantic-interface check is not a full-module
receipt. No build-time or proof-object-size improvement is claimed.

## Why the case split suffices

For addition, if the second operand is zero, functionality of addition gives
that the first operand is zero. If it is a successor of `n`, obtain the
addition result at `n`. The successor law and functionality would identify
an internal successor with the empty set, contradicted by its self-member.
No conclusion about addition at `n` is used.

For multiplication, a zero second operand settles the disjunction. For a
successor of `n`, obtain the product at `n`. The successor equation and
functionality make the sum of that product and the first operand equal to
zero. The addition zero criterion makes the first operand zero. Again, no
zero-product statement at `n` is needed.

The decomposition theorem itself is a valid theorem about every internal
natural, including nonstandard elements. It does not identify internal omega
with Lean's `Nat`.

## Choose one patch

### Preferred integration candidate: production.patch

The already-proved `nat_zero_or_succ` is located in the relatively heavy
`BoundedZFCConsistency.InternalSat` module. Importing that whole module into
arithmetic solely for one case distinction would add avoidable dependencies.

This variant moves its unchanged formula/specification/theorem block to a new
`BoundedZFCConsistency.NaturalCases` module. The new module imports
`OmegaRecursion` and `CodePredicate`; the latter supplies `fNatF_spec`.
Both are already dependencies of `ObjectArithmetic`. `InternalSat` imports
the new module, preserving all three qualified declaration names. The addition
module imports it directly; multiplication sees it through the existing chain.

The production variant touches four files (including the new file), and its
**raw pinned-snapshot** total is **30 fewer physical lines and 1,238 fewer
UTF-8 bytes**. This includes the new module, import changes, and moved text.
It is not an estimate of the incremental savings after every old proposal
has hypothetically been applied.

### Smallest textual experiment: minimal.patch

This variant changes only the two target files and adds an `InternalSat`
import to the addition module. It removes **41 physical lines and 1,626 UTF-8
bytes** against the raw pinned snapshot. The larger dependency is why it is
not the preferred integration candidate.

These are alternatives, not cumulative patches. Apply exactly one.

## Files

- `InternalZeroCore.lean`: self-contained checked semantic mechanism.
- `core-validation.log` and `validation.json`: exact replay evidence.
- `production.patch` / `minimal.patch`: alternative integration candidates.
- `production/` / `minimal/`: complete corresponding modified sources.
- `baseline/`: exact pinned originals used for textual applicability checks.
- `metrics.json`: file hashes, public-header checks, source-size metrics.
- `make_candidates.py`: recreates both variants from the pinned Git objects
  without modifying the repository.

## Replay

Check the standalone semantic proof with the pinned compiler:

```sh
lean InternalZeroCore.lean
```

Regenerate against a checkout containing the pinned commit:

```sh
python3 make_candidates.py --repo /path/to/ProveIt --out /path/to/output
```

For a production integration trial, use an isolated checkout and then run:

```sh
git apply --check /path/to/production.patch
git apply /path/to/production.patch
lake build BoundedZFCConsistency.NaturalCases BoundedZFCConsistency.InternalSat DiophantineConsistency.ObjectAdditionCancellation DiophantineConsistency.ObjectNaturalZero
lake env lean Computability/DiophantineConsistency/Lean/checks/ObjectAdditionCancellation.lean
lake env lean Computability/DiophantineConsistency/Lean/checks/ObjectNaturalZero.lean
```

The commands in the last block are future integration steps, not successful
runs reported by this package. Rebuild affected dependent modules and inspect
endpoint axiom reports before adoption.

## Nonduplication

The earlier proposals share definable-induction transport and recursive-graph
preservation/fusion. This change removes two inductions whose hypotheses are
unused, together with their dedicated formulas. Searches across all six placed
packets and five incoming archives found no proposal for either target,
`zeroSumStage`, `zeroProductStage`, or this unused-induction elimination.
The only `ObjectAdditionCancellation` matches were source inventory paths.
