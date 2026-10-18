# Actual AX parameter-push prefix

`ArithmeticControlAXPrefix254.ax_prefix_run` executes the actual interpreter's first AX parameter push in every IΣ1 model. It requires both scratch registers to be zero and returns with `TW := old P1`, `WS := cantor(old TW, old WS)`, preserving all other fields. `dispatch_ax_prefix_run` also executes the three-instruction opcode classifier, changing `AC = c + 3` to `c`.

The finite catalogue indices are 41–66, ending at 67. Arithmetic control codes are index plus one, so the represented endpoint is code 42 to code 68. These are interpreter control indices, not binary-machine states. The copy/restore tail has exact clock `7 * old P1 + 2`; the complete prefix has a positive existential clock supplied by the existing generic Move/Copy/Pair and ParamPush proofs.

The [successful record](results/arithmetic-control-ax-prefix254-verification.json) contains seven named axiom probes and eight typed callers, with no warnings. Source and audit took 14.946 and 1.882 seconds. Three source-identity probes use `propext`; the four runtime probes use only `propext`, `Classical.choice` and `Quot.sound`. All 221 inputs and the fresh source object were checked before and after the audit, and independently rehashed during the [existing-evidence review](results/arithmetic-control-ax-prefix254-review.json).

The strict guard selects 98 actual project providers from the exact successful ParamPush record. It retains six explicit cached Foundation/Mathlib boundaries; five are direct project imports, while HFS.Seq is an inherited boundary. Init and Omega are separately pinned toolchain boundaries. No dependency is rebuilt. Both fresh proof commands share 120 seconds, with one thread, 4,096 MiB and default limits for the new source and audit.

The first actual attempt failed in two scratch-preservation rewrites because `put` had not been unfolded. The repair adds `put` to those two rewrite lists; theorem statements, control bindings, audit and limits are unchanged. [History](results/arithmetic-control-ax-prefix254-history.json) preserves the failed attempt, successful retry, exact executed guards, proof snapshots, logs, and repair/source-review records. Publication performs no proof replay and changes only the guard's default source/audit paths.

With the recorded dependency objects still available:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_control_ax_prefix254.py \
  --repo "$PWD" \
  --dependency-root /home/codex/src/Proofs \
  --param-push-evidence Computability/BusyBeaver/Research/ZFC/results/arithmetic-control-param-push254-verification.json \
  --output /tmp/zfc-arithmetic-ax-prefix254-prepared \
  --prepare-only
```

Preparation checks current hashes and provider selection without a compiler or version query. Remove `--prepare-only` for the bounded source/audit check. The dependency-root path can name another checkout with the exact recorded pins and objects.

This closes the first AX prefix of the shared interpreter. The complete AX bundle, interpreter-to-scheduler comparison, seeded scheduler connection, actual 246-state arithmetic binary simulation, and internal ZFC proof comparison remain separate. In particular, the imported arithmetic binary relation still concerns Perm252; this module does not relabel it as a 246-state result. The original source program retains Mira-Cult, Jeff Ketchersid and Andrew James Wade's attribution.
