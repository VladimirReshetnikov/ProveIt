# Actual initial fetch in the represented interpreter

`ArithmeticControlFetch254.lean` proves the initial fetch block of the literal `Prog254` interpreter for every IΣ1 model. All register values and loop counts may be internal. It uses actual catalogue controls 0–10, with `initialControl` at index 0 and the next read entry at index 10, path 10000 (`resolveControl [true]`). The physical indices of NP, PL and scratch1 are 6,1,8.

If PL is positive, exactly 2 logical instructions decrement PL and reach the read entry; the other fields remain unchanged. If PL=0 and scratch1=0, exactly `7*NP+4` logical instructions load old NP into PL, increment NP, restore scratch1 to zero and reach that same read entry. Every other field is preserved. The hypotheses on the zero branch are explicit; the positive branch permits arbitrary NP and scratch values.

The two actual loops are separately checked. The D0/I8/I6/C3 loop copies the source counter into PL and scratch1 in `4*NP+1` instructions. The D6/I0/C2 loop consumes scratch1 into NP in `3*scratch1+1` instructions. Their proofs fix the original whole file and use bounded internal iteration indices with Σ1 induction. They do not infer a runtime for arbitrary internal inputs from an ordinary finite `RMDag.Run` derivation or use a Π2 uniform-runtime induction premise.

Every finite source and resolver equality is proved against the actual catalogue; an untrusted Python discovery/clock diagnostic is separately archived. Its 11 examples are not an all-input certificate. The checked endpoints match the two existing ordinary `L2Control.fetch_zero`/`fetch_pos` contracts, but this module does not prove the complete internal L2/Enum equivalence. Its clock counts represented logical instructions, not binary-machine steps.

Run2 is the first complete source/audit PASS: 12 ordered axiom probes, 15 generic and specialized callers, standard axioms only, zero warnings. Source compilation took 6.959 s and the audit 2.285 s. The guard checks 89 exact project prerequisites, 6 external boundaries, 201 inputs and the fresh object. It rebuilds or downloads no dependency. Run1 remains a source FAIL with four normalization goals and 13 diagnostic unused-simp warnings; its audit did not run. The repair stages projection rewrites before unfolding file definitions and names the three intended run-additivity boundaries. No hypothesis, endpoint, clock or resource limit changed.

The portable checker is byte-identical to the final executed driver. Its separate maintained-default preparation is recorded as UNBUILT:

```bash
python3 Computability/BusyBeaver/Research/ZFC/check_arithmetic_control_fetch254.py \
  --repo /path/to/Proofs --dependency-root /path/to/built/Proofs \
  --clear-evidence /path/to/Proofs/Computability/BusyBeaver/Research/ZFC/results/arithmetic-control-clear254-verification.json \
  --output /outside/Proofs/fetch-check
```

Add `--prepare-only` for metadata validation against an existing pinned Foundation/Mathlib build. The next runtime obligation is the actual unpair/read macro and its equality to the represented command decoder. No new consistency endpoint, whole PA equivalence or state reduction is claimed here.
