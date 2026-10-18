# Conditional runtime equivalence for prefix250

`RuntimeInstancePrefix250.lean` connects the checked instruction adapter to the generic positive-segment simulation. Its relation requires a clean logical PC, the complete binary dispatch frame, and a nonempty finite physical spare suffix. Increment appends a value-one spare; all other instructions retain the suffix. Header-distance changes from positive decrement and PC overflow are already handled by the frame and instruction layers.

For any program with exact site coverage, the module proves register-machine halting equivalent to halting of the exact prefix250 binary machine from any related configurations. It also transports every finite register run to a positive binary run. Coverage supplies a decoded leaf and its exact consumed PC; a stopped logical execution is identified with a halt leaf using that coverage. Both halting directions use the previously checked finite positive-simulation theorem, including absorbing halted states and a lower bound on elapsed binary steps.

The first source/audit attempt passed with 11 named axiom probes and 12 typed callers. Source took 0.623 seconds and audit 0.480 seconds, with zero warnings and only standard Lean axioms. The guard uses one thread, 4,096 MiB, a shared 120-second wall budget and default Lean proof limits. It rebuilds no dependencies. Its exact closure contains 26 project providers, with Init and Lean.Elab.Tactic.Omega as explicit toolchain boundaries. The successful Instruction parent is pinned, and the three additional generic providers are RuntimePerm252, SiteCoverage and RMBisim.

The complete first attempt, raw snapshots, source-object-before-audit binding, all 72 current input hashes, and the author evidence review are preserved. A separate independent source/audit/interface review is embedded verbatim in the review record. Publication retains the exact successful source and audit; it changes only the guard's two default paths. The original successful record identifies the maintained Instruction evidence path supplied to the proof run.

From the repository root, using a new external output directory:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/check_prefix250_runtime.py \
  --repo "$PWD" \
  --instruction-evidence Computability/BusyBeaver/Research/ZFC/results/prefix250-instruction-verification.json \
  --output /tmp/zfc-prefix250-runtime-check --prepare-only
```

Preparation checks all bindings without invoking Lean or querying its version. Removing `--prepare-only` requests the bounded source/audit run. Results and full history are under `results/prefix250-runtime-*.json`.

Exact site coverage and the initial dispatch frame remain explicit premises. This module supplies no closed all-sites theorem, complete blank bootstrap, exact250 consistency endpoint or PA-internalized equivalence. It retains the Mira-Cult, Jeff Ketchersid and Wade attribution from the maintained permutation252 framework.
