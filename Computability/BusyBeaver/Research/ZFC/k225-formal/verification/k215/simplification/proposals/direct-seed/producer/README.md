# Maintained shared-basis producer

`repository/` mirrors the necessary ProveIt paths so that the updated maintained
producer can run without a full checkout. It contains the two proposed Lean files,
the unchanged `DomRho8.lean`, the updated producer, and its four pinned inert input
files. `expected/` contains the exact generated outputs and diagnostic metrics.

From the packet root:

```sh
make check-producer
```

For a separate regeneration directory:

```sh
python3 producer/repository/Computability/BusyBeaver/Research/ZFC/k225-formal/generate_dominated_implication_lean.py \
  --out /absolute/new/generated-lean
```

The producer pins every input by SHA-256, audits the restricted-row guards and
modus-ponens structure, checks all six public targets, and pins the emitted shared
core exactly. It reads the preserved ancestry data without executing an upstream
renderer. The raw proof has 58 private MP steps and one public MP step; the
rendered version has 56 private and three public MP steps. Both total 59. There
are 23 restricted-row uses and no seed use.

This fixed-input syntactic audit is not a proof kernel. Kernel evidence comes from
the joint fresh Lean replay in `../lean/`, which uses these exact core and adapter
bytes. The unrestricted adapter uses trivial domination to reuse the shared
derivation; the numerical adapter is byte-identical to the baseline.

`source_metrics.json` measures the actual changed production files, including the
maintained producer. The preserved inputs were already present in the pinned
repository and are not added or overwritten by the patch.
