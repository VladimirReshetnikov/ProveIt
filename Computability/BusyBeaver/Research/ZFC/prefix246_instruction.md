# Complete instruction steps for prefix246

`InstructionPrefix246.lean` turns an accepted instruction check into a strictly positive segment of actual 246-state execution and a new complete dispatch frame. Its premises retain the clean register tail, whole source tape and a nonempty finite spare suffix.

Increment appends one value-one spare. Decrement and control instructions retain the original spare suffix; positive decrement adds one gap cell. Path-length bounds and logical-tail preservation justify every target frame. The halt theorem follows the actual checked halting transition, including its final write and movement in the symbolic proof.

Root's first source/audit run passed: seven named axiom probes and seven typed callers, standard Lean axioms only, zero warnings. Source took 0.741 seconds and audit 0.447 seconds. The guard uses one thread, 4,096 MiB, a shared 120-second budget and default proof limits. It builds no dependencies and makes no version query. Final evidence review rechecked all 62 recorded inputs, the complete 22-project import closure, Init/Omega boundaries, actual first providers and the fresh object recorded before audit.

The sole successful attempt and raw snapshots are retained; the history archive was assembled after success from those exact bytes. Publication changes only the guard's source/audit default paths.

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/check_prefix246_instruction.py \
  --repo "$PWD" \
  --frame-evidence Computability/BusyBeaver/Research/ZFC/results/prefix246-frame-verification.json \
  --output /tmp/zfc-prefix246-instruction-check --prepare-only
```

Use a new external output directory. Preparation runs no compiler or version query; removing `--prepare-only` requests the bounded source/audit run. The original record retains the actual scratch Frame evidence path; the identical maintained record is accepted above.

Acceptance of each site remains an explicit premise. Complete decoder coverage, actual blank startup, runtime equivalence, binary consistency and PA internalization are separate obligations. Attribution follows the checked 250-state instruction proof and the Mira-Cult, Jeff Ketchersid and Wade framework.
