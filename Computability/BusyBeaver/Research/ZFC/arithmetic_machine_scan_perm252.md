# An unbounded scan of the actual 252-state table

[`ArithmeticMachineScanPerm252`](../../Lean/BusyBeaver/ZFC/ArithmeticMachineScanPerm252.lean)
proves the following endpoint for every internal `n`, `L` and `X` in every
IΣ1 model:

```
frame L R := cantor 72 (cantor L R)
runFrom n (frame L (onesPrefix n X)) = frame (onesPrefix n L) X
```

Canonical state 71 has numeric state code 72. Its actual read-one row writes
one, moves right and returns to itself, with positive action code 292.
The proof connects this value to the existing literal table through the
checked static-key lookup theorem. Both complete numeric tape halves are
preserved. The suffix may itself start with one, so the theorem gives the
endpoint after `n` steps without asserting first exit from the scan state.

An explicit fixed Σ1 frame graph supplies a total Δ1 frame function. Together
with total Δ1 `runFrom` and the [prefix algebra](arithmetic_tape_prefix254.md),
it makes the scan invariant, universally quantified over both tape halves,
Π1. IΣ1 Π1 induction then applies at the changed left half `2*L+1`.
No restriction to externally standard lengths is used.

The [fresh check](results/arithmetic-machine-scan-perm252-verification.json)
passes eight axiom reports and eleven callers, with standard Lean axioms and
no warnings. It reuses 26 project modules and five identified external
providers. The [independent review](results/arithmetic-machine-scan-perm252-review.json)
checks the final source, audit, selected providers and fresh object. Two
earlier elaboration failures are retained: the explicit frame graph replaced
failed bounded definability automation, then required numeral normalization.

```sh
python -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_machine_scan_perm252.py \
  --repo /path/to/Proofs --dependency-root /path/to/built/dependency-checkout \
  --run-from-evidence /outside/successful-run-from/verification.json \
  --prefix-evidence /outside/successful-tape-prefix/verification.json \
  --output /outside/new-empty-machine-scan-check
```

`--cache` relocates the full project cache; `--run-from-cache` and
`--prefix-cache` relocate only those two new prerequisite objects. Portable
preparation is distinct from the original successful proof check.

This is one unbounded actual-row scan. The complete internal register,
dispatcher and scheduler comparisons remain open. Nonstandard numeric tapes
are interpreted internally; the theorem does not identify them with external
finite Core runs. Attribution for the machine remains in
[`TablePerm252`](../../Lean/BusyBeaver/ZFC/TablePerm252.lean).
