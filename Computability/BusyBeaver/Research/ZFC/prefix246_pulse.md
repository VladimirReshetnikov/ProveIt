# Local pulse contracts for prefix246

`Prefix246Pulse.lean` proves the two three-step pulse contracts directly on the exact 246-state table. From old75 over `00`, execution follows old75→255→255→131, writes `11`, and exits one cell left of the original head. From `01`, it follows old75→255→131→112, restores `01`, and exits at the same relative position. Both contracts retain arbitrary finite left and right context. The Core client preserves the complete represented infinite tape.

The self-return from old255 reads the one written by old75 two transitions earlier. This proof uses the local tape shape directly; it does not copy the 250-state machine's global left-neighbor invariant onto the folded state.

Root's first source/audit run passed: 3 named axiom probes and 4 typed callers, only `propext` and `Quot.sound`, with zero warnings. Source took 0.597 seconds and audit 0.650 seconds. The exact source object was recorded before the audit and retained unchanged afterward. All 19 recorded inputs were rechecked. The guard uses one thread, 4,096 MiB, a shared 120-second budget and default Lean proof limits. It rebuilds no dependencies and queries no compiler version.

The four project providers are the checked TablePrefix246 plus exact Core, FiniteZipper and ZipperRuns objects. Init and Lean.Elab.Tactic.Omega are explicit supplied toolchain boundaries. The exact successful source and audit are published unchanged; only the guard's source/audit default paths change. Full first-attempt records and logs are retained, with an archive assembled from the exact run snapshots and recorded guard hash after the successful run.

From the repository root, using a new external output directory:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/check_prefix246_pulse.py \
  --repo "$PWD" \
  --table-evidence Computability/BusyBeaver/Research/ZFC/results/table-prefix246-verification.json \
  --output /tmp/zfc-prefix246-pulse-check --prepare-only
```

Preparation checks bindings without invoking Lean or querying its version. Removing `--prepare-only` requests the bounded source/audit proof run. The original successful record retains the actual scratch Table246 evidence path used in that run; the identical maintained record can be supplied by the command above.

These are local contracts. Complete register macros, decoder coverage, the new blank bootstrap, the consistency endpoint and PA internalization remain separate. Attribution is retained from the checked Prefix250Pulse local proofs, Mira-Cult, Jeff Ketchersid and Wade's framework, and source63's contextual-fold contribution.
