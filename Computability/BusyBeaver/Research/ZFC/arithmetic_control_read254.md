# Actual first read in the represented interpreter

`ArithmeticControlRead254.lean` proves the first read/unpair macro of literal `Prog254`, using actual catalogue controls 10–24, for every IΣ1 model. The input register file and every loop counter may be internal. With scratch1 and scratch2 initially zero, `read_ac` reaches control 24 after a positive internal logical time. It replaces PL by `second(oldPL)`, adds `first(oldPL)` to AC, restores both scratch registers to zero, and preserves every other field of the complete nine-register file.

Every finite source and continuation equality is proved against the actual catalogue. The three separately checked transfer loops are the nested scratch2→scratch1 loop, scratch2→PL restoration, and scratch1→AC output. Each takes exactly three times its old source register plus one logical instructions, including the zero exit. The walk body takes four instructions when scratch1 is positive and `3*(oldScratch2+1)+4` when scratch1 is zero.

The Cantor inverse-successor laws require only IOpen. At a diagonal boundary, the next projections are `(second(n)+1,0)`; elsewhere they are `(first(n)-1,second(n)+1)`, with an explicit nonzero premise for the truncated predecessor. Thus the literal scratch walk agrees with the existing represented Cantor projections on arbitrary internal inputs.

The outer proof fixes the original file. For every internal `t≤oldPL`, its Σ1 induction invariant asserts an existential logical clock reaching the explicit file with PL=`oldPL-t`, scratch1=`first(t)` and scratch2=`second(t)`. This keeps the induction at Σ1; it does not use a universal-files/existential-time induction principle. Final restoration and output discharge the whole-file endpoint. When oldPL=0, the three final zero tests already give a positive duration.

Run2 is the first complete source/audit PASS: 16 ordered axiom probes, 19 generic and specialized callers, standard axioms only, and zero warnings. Source compilation took 9.956 s and the audit 2.507 s. The guard verifies 90 exact project prerequisites, 6 external boundaries, 203 inputs and the fresh object. It builds or downloads no dependency and replays neither the native site certificates nor the 82,552-step bootstrap. Run1 remains a source FAIL with eight elaboration errors and zero warnings; its audit did not run. The repair explicitly unfolds three private transfer instances and unfolds five local lets before projection rewrites. No statement, clock, model assumption or resource limit changed.

The portable checker is byte-identical to the successful executed driver:

```bash
python3 Computability/BusyBeaver/Research/ZFC/check_arithmetic_control_read254.py \
  --repo /path/to/Proofs --dependency-root /path/to/built/Proofs \
  --fetch-evidence /path/to/Proofs/Computability/BusyBeaver/Research/ZFC/results/arithmetic-control-fetch254-verification.json \
  --output /outside/Proofs/read-check
```

Add `--prepare-only` for metadata validation against existing pinned Foundation/Mathlib objects. The separate maintained-default record is UNBUILT and is not another kernel replay.

This is the actual first read needed by the interpreter-to-scheduler route. Its clock counts numbered register instructions; binary-time transport is a separate existing result. The second read, dispatch and remaining constructor contracts still need their all-internal connections. No complete internal L2/Enum equivalence, whole PA consistency equivalence, or state reduction is claimed by this module.
