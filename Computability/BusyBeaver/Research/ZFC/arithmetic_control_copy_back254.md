# Internal copy, restore, and argument push

[ArithmeticControlCopyBack254](../../Lean/BusyBeaver/ZFC/ArithmeticControlCopyBack254.lean) proves a reusable copy/restore contract over arbitrary internal IΣ₁ register files. `CopyBackShape` contains literal `CopyShape` and `MoveShape` interfaces and their register/control equalities. It has no assumed execution theorem.

`copy_back_run` requires only `S1 = 0`. It adds the original argument-register value to TW, restores that argument register, and preserves every other coordinate, including arbitrary S2. Its exact internal execution time is `7 * oldArgument + 2`. The argument is distinct from TW and S1 by the underlying copy shape.

`argument_push_run` composes a clean `PushShape` with this copy/restore suffix. It requires both scratch coordinates zero and the argument register distinct from WS. The resulting whole file changes only:

- `TW := oldArgument`;
- `WS := cantor(oldTW, oldWS)`.

The argument and all other fields remain unchanged, and the theorem supplies a positive internal execution time. This generic unit does not bind a particular AX control interval. Concrete occurrences and the complete interpreter/Enum and binary consistency comparisons remain separate obligations.

The [audit](arithmetic_control_copy_back254_audit.lean) has five named axiom probes and nine typed callers, including arbitrary model/file inputs, arbitrary other-coordinate preservation, scratch preservation, and specialization to the AC register without assuming a concrete control occurrence. The successful source/audit run took 3.048 and 2.077 seconds with zero warnings. The two register-distinctness probes use `propext` and `Quot.sound`; the remaining three use only `propext`, `Classical.choice`, and `Quot.sound`.

The [verification record](results/arithmetic-control-copy-back254-verification.json) and [existing-evidence review](results/arithmetic-control-copy-back254-review.json) preserve exact inputs, raw outputs, and the fresh source object and first provider recorded before audit. The reviewer independently checked the root-authored source, the later repair, and the actual evidence; that reviewer authored the audit and original guard, which is disclosed in the record.

The first source attempt left two coordinate-preservation goals unresolved and emitted three unused-simp warnings. The successor changes only those two proof bodies to explicit read/write rewrites; all theorem statements, the exact clock, audit callers, and proof limits remain unchanged. [The history](results/arithmetic-control-copy-back254-history.json) preserves the initial failure, original source/guard, both preparations, repair and reviews, successful raw logs, and root receipts. An earlier metadata newline inspection was a false alarm: its assertions failed before mutation, and its correction remains in that history.

The guard selects 98 project providers from the exact checked ParamPush parent, five directly imported Foundation/Mathlib boundaries, the separately retained inherited `HFS.Seq` pair, and Init/Omega. ParamPush recorded its source object before audit but lacked a separate fresh-first-provider field; the guard resolves its recorded search path now without inventing historical capture. CopyBack records both before audit.

The maintained [guard](check_arithmetic_control_copy_back254.py) changes only the source, audit, and [provider-proposal](results/arithmetic-control-copy-back254-provider-proposal.json) default paths. The exact historical dependency/cache providers are prerequisites. No compiled caches are distributed and no clean-checkout dependency build is claimed. Preparation invokes no Lean or version query:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_control_copy_back254.py \
  --repo "$PWD" \
  --dependency-root /path/to/the/recorded/dependency-root \
  --param-push-evidence Computability/BusyBeaver/Research/ZFC/results/arithmetic-control-param-push254-verification.json \
  --output /tmp/fresh-copy-back-preparation \
  --prepare-only
```

After reviewing preparation, omit `--prepare-only` in a fresh output directory to run source and audit under default proof limits, one thread, a 4,096 MiB memory limit, and a shared 120-second budget.

The underlying register program is Mira-Cult's, imported from Jeff's verification; the original TMBuilder framework is Wade's. [Prog254.lean](../../Lean/BusyBeaver/ZFC/Prog254.lean) records the source and attribution.
