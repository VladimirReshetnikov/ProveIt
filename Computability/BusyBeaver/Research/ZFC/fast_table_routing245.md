# Fast lookup for the exact 245-state machine

[FastTableRouting245.lean](../../Lean/BusyBeaver/ZFC/FastTableRouting245.lean)
represents all 490 actions of the [routed machine](candidate-routing245/README.md)
in a balanced lookup tree. Its 245 leaves have depth seven or eight. Lean
proves equality with the [literal table](table_routing245.md) for every working
state and both read symbols, then equality of the two complete machine values.
This permits faster reduction in subsequent execution proofs.

Both theorem audits and four typed callers passed on the first run, with
zero warnings. The callers include equality of execution from every
configuration for every natural time. Source checking took 5.291 seconds;
the audit took 0.240 seconds. The transition equality uses no axioms, and
machine equality uses only standard `Quot.sound` through function extensionality.
The finite equality uses `decide +kernel` with default proof limits.

The [actual PASS record](results/fast-table-routing245-verification.json)
has SHA-256
`b9aa533b7e04c59a382147b3c165c20e2366be008981e43695050e4ac705b09d`.
The checked source is
`bcacf9874bf3439c538c8544a724caac2f817e52b58eaaf07f0806666d4dde64`;
the fresh object is
`988045b83e5e6295f2435741b1bddf7d311c7028979dd7d273b0ef9141933e13`.
The [history](results/fast-table-routing245-history.json) retains the executed
programs, source, audit, logs, first draft and independent reviews.

The selected project dependencies are exactly the checked `Core` and
`TableRouting245` source/object pairs. The compiler and implicit `Init` are
pinned. Source and audit run serially with `-j1 -M4096`, sharing a 120-second
limit. The guard binds the fresh object before the audit and checks all
inputs, providers and that object afterwards. No dependency build, download,
compiler-version query or raised proof limit is used.

The [publication record](results/fast-table-routing245-publication.json)
binds maintained paths to the actual execution. The maintained guard's
`--prepare-only` mode invokes no proof command; a full check requires the
exact historical providers and toolchain. Published source and audit retain
the successful bytes.

From this directory, using fresh external output directories:

```sh
python3 -B generate_fast_routing245.py --check
python3 -B check_fast_table_routing245.py --output /tmp/routing245-fast-prepared --prepare-only
python3 -B check_fast_table_routing245.py --output /tmp/routing245-fast-checked
```

This proves equality of two implementations of the same transition table.
The 407,915-step blank startup, register simulation, source-program
bisimulation, complete decoder coverage and 245-state consistency endpoint
remain separate Lean obligations. The original calculus and all machine
attributions are preserved in the candidate and literal-table documentation.
