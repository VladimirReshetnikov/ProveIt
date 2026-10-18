# Whole-tape dispatch frames for prefix246

`Prefix246Simulation.lean` connects the generic physical-register dispatch frame with the checked 246-state symbolic executor. Its source adapter consumes path bits from the existing path and zero gap while preserving every tape cell. Its target adapter retains arbitrary overflow and extra distance, with the full register file and spare suffix.

The physical permutation is unchanged. Increment appends a value-one spare, and decrement preserves the complete suffix. A separate nonempty-spare premise supplies the ten blocks required for valid symbolic execution. Removing exterior zero padding is justified through the whole-tape representation; it does not truncate register data.

Root's first source/audit run passed: 14 named axiom probes and 14 typed callers, standard Lean axioms only. Source took 0.964 seconds and audit 0.526 seconds. One inherited unused-simp source warning remains; the audit has zero warnings. The guard keeps one thread, 4,096 MiB, a shared 120-second budget and default proof limits, with no dependency builds or version query.

Final evidence review rechecked all 59 recorded inputs, the complete 21-project import closure, Init/Omega boundaries, actual first providers and the fresh object saved before audit. The sole successful attempt and raw snapshots are retained; the history archive was assembled after success from those exact bytes. Publication changes only the guard's source/audit default paths.

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/check_prefix246_frame.py \
  --repo "$PWD" \
  --site-evidence Computability/BusyBeaver/Research/ZFC/results/prefix246-site-verification.json \
  --output /tmp/zfc-prefix246-frame-check --prepare-only
```

Use a new external output directory. Preparation invokes no compiler or version query; removing `--prepare-only` requests the bounded source/audit run. The successful record retains its actual scratch Site evidence path; the maintained identical record is accepted above.

These are conditional frame and register-update adapters. They do not close all-site acceptance, the complete runtime equivalence, actual blank startup, binary consistency or PA internalization. Attribution follows the checked 250-state contracts and the Mira-Cult, Jeff Ketchersid and Wade framework described in the source.
