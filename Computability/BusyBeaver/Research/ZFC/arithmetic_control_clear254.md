# An actual internal clear loop

`ArithmeticControlClear254.lean` proves a clear-register loop for the represented interpreter of the literal `Prog254` leaf catalogue. For every IΣ1 model and arbitrary internal nine-register file, a tested value `v` is replaced by zero after exactly `2*v+1` logical interpreter steps. The other fields remain those of the same file.

The generic contract takes an actual-catalogue `ClearShape`: a decrement/test leaf, its positive continuation back to the test, and its zero exit. The closed instance uses indices 6431/6432/6433, logical register 5 (param2), and physical register 7. Its endpoint is the next literal `brk1` leaf, before executing that leaf. The three source equations and all resolver paths are proved against the actual catalogue; the discovery JSON supplies no trusted premise.

The induction fixes the original whole file and tracks a bounded internal iteration index with a Σ1 predicate. It does not use an ordinary finite `RMDag.Run` derivation to model a nonstandard loop count, nor assume an existential clock uniformly over files. The clock above counts represented logical instructions, not binary-machine steps. The internal L2/Enum interpreter connection remains a separate obligation.

The first complete check is run4: 9 ordered axiom probes, 11 generic/specialized callers, standard axioms only, and zero warnings. Source compilation took 42.472 s and the audit 2.390 s. All 88 project prerequisites, 6 external boundaries, 199 recorded inputs and the fresh object were checked before/after; dependencies were reused without rebuilding or downloading them.

All earlier attempts remain in the history. Run1 failed the grouped structure declaration and closed catalogue recursion depth. Before that first build, unused global resource settings were removed. Run2 failed only physical-index alias normalization; run3 checked the source but failed a zero-file audit caller's numeral normalization. Run4 is the first overall PASS. Only the three measured closed catalogue equations have local `maxRecDepth 8192`; the generic IΣ1 proof retains default limits and no heartbeat increase.

A separate maintained-default preparation validates paths and providers without compiling a proof. The portable guard is byte-identical to the final executed driver. For an existing pinned Foundation/Mathlib build and the checked ControlRun evidence:

```bash
python3 Computability/BusyBeaver/Research/ZFC/check_arithmetic_control_clear254.py \
  --repo /path/to/Proofs --dependency-root /path/to/built/Proofs \
  --run-evidence /path/to/Proofs/Computability/BusyBeaver/Research/ZFC/results/arithmetic-control-run254-verification.json \
  --output /outside/Proofs/clear-check
```

Add `--prepare-only` for metadata validation. This local contract does not establish the complete internal L2 scheduler simulation, a new consistency equivalence, or a smaller machine.
