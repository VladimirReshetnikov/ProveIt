# Internal AX parameter1 push

[ArithmeticControlAXParamPush254](../../Lean/BusyBeaver/ZFC/ArithmeticControlAXParamPush254.lean) binds the actual register-interpreter controls 222–248 to the checked `ParamPushShape`. Its 26 instruction edges and 34 successor branches are literal facts about the finite control catalogue. The reusable parent supplies the unbounded internal execution proof.

For any internal IΣ₁ register file with `S1 = S2 = 0`, `ax_param_push_run` reaches control 248 after positive internal time with the complete file effect:

- `TW := oldP1`;
- `WS := cantor(oldTW, oldWS)`;
- all other seven coordinates unchanged.

The parameter register is restored. The separate `copy_tail_run` contract starts at control 241, permits arbitrary old TW and S2, and requires only `S1 = 0`. Its exact internal clock is `7 * oldP1 + 2`; it adds old P1 to TW while restoring P1 and retaining every other coordinate. Files, parameters, and clocks range over the ambient model rather than only standard natural numbers.

This checkpoint covers the parameter push. The following implication constructor at 248–275 and the complete AX, interpreter/Enum, and binary PA consistency comparisons are separate obligations.

The [audit](arithmetic_control_ax_param_push254_audit.lean) has six named axiom probes and eight typed callers covering the three finite entry/exit facts, preservation of arbitrary coordinates and scratch zeros, the additive tail, and the whole push. The successful source and audit took 50.794 and 1.936 seconds, with zero warnings. The three finite-source probes use only `propext`; the other three use only `propext`, `Classical.choice`, and `Quot.sound`.

The [verification record](results/arithmetic-control-ax-param-push254-verification.json) records the fresh source object and its first provider before the audit, all 224 input hashes, and raw compiler output. The [existing-evidence review](results/arithmetic-control-ax-param-push254-review.json) independently checks that evidence and the small source repair.

The first source attempt failed in the coordinate-preservation proof because a rewrite stated for `writeValue` did not match the local `put` expression. The successor adds a typed `read_put_other` wrapper and uses it in the two rewrites. The theorem statements, all finite bindings, audit, and proof limits remain unchanged. [The history](results/arithmetic-control-ax-param-push254-history.json) preserves both source/guard versions, the failed source output, the repair, both unbuilt preparations, successful raw logs, reviews, and root receipts. No audit was reached in the failed attempt.

The guard selects exactly 98 project providers from the checked ParamPush parent, five directly imported Foundation/Mathlib boundaries, the separately retained inherited `HFS.Seq` pair, and Init/Omega. The parent recorded its source object before audit but lacked a separate fresh-first-provider field. Its recorded library path is resolved now; that check does not invent a historical capture. This occurrence records both fields before its own audit.

The maintained [guard](check_arithmetic_control_ax_param_push254.py) changes only the source, audit, and [provider-proposal](results/arithmetic-control-ax-param-push254-provider-proposal.json) default paths. The exact historical dependency/cache providers remain prerequisites. Compiled objects are excluded from the publication, and no clean-checkout dependency build is claimed. Preparation invokes no Lean or version query:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_control_ax_param_push254.py \
  --repo "$PWD" \
  --dependency-root /path/to/the/recorded/dependency-root \
  --param-push-evidence Computability/BusyBeaver/Research/ZFC/results/arithmetic-control-param-push254-verification.json \
  --output /tmp/fresh-ax-param-push-preparation \
  --prepare-only
```

After reviewing preparation, omit `--prepare-only` in a fresh output directory to run source and audit with default proof limits, one thread, a 4,096 MiB memory limit, and a shared 120-second budget.

The register program is Mira-Cult's, imported from Jeff's verification; the original TMBuilder framework is Wade's. [Prog254.lean](../../Lean/BusyBeaver/ZFC/Prog254.lean) records the source and attribution.
