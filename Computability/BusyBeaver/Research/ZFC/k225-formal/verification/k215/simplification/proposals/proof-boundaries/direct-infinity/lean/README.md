# Checked direct-Infinity proposal

This folder contains the generic Lean proof, two adapters using the current
repository definitions, a reproduction driver, and source-bound evidence.
The full mathematical argument and integration plan are in `DIRECT_INFINITY.md`.

## Reproduce

Use Lean 4.32.0 and a checkout of ProveIt at
`6d9800d1ca67c52db0eb6e1c65df7b5cab9cdb95` with these trees available:
`Computability/BusyBeaver/Lean`, `Logic/FirstOrder/Lean`, and `SetTheory/ZF/Lean`.
On Linux or WSL, from this folder run:

```sh
python3 check_adapter.py /path/to/ProveIt /path/to/lean-4.32.0/bin/lean
```

The driver recompiles every selected project module, with no timestamp skips
and no project object reuse. It records source, log, and object SHA-256 values.
It uses a per-module process lock shared with the other proposal checks.

The delivered final run checks **40 modules afresh**. The authoritative final
records are `evidence/build-info.json`, `evidence/manifest.json`, and the matching
per-module logs. The three files containing `failed` and the
`manifest-before-final-retry.json` file preserve rejected earlier attempts;
they are not accepted proof evidence. The final fresh run supersedes the
intermediate retry records.

The new three Lean modules total **304 physical lines and 12,408 bytes**.
`ordinary_quotient_infinity` uses only `propext`, `Classical.choice`, and
`Quot.sound`. Its conclusion is exactly the existential empty-set/ordinary-
successor clause required by the current `ZFAxioms.inf` field, on the actual
`KQ1Model.quotientMember` relation. No K215 endpoint rebuild or production
adoption is claimed.
