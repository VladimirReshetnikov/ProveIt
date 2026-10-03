# Parallel five-particle involution research packet

Completed bounded construction, separate from Reports 15 and 19. No article, universal new-rule emission, upload, or public change.

## Finding

A new binary number-conserving full-shift CA uses two parallel involutions and has sufficient radius `180D+258+9J`. It agrees with the prior ordered compiler on every admissible five-particle state, including source-step timing and both reflections. It differs intentionally on malformed inputs. Prospective candidate-key preservation is essential; mere endpoint isolation is insufficient.

- `PROOF.md`: construction, source-uniform preservation, explicit constants, limits
- `audit-lemma.md`: independent full-shift lemma audit
- `audit-preservation.md`: independent arbitrary-source geometric and guard audit
- `parallel_particles.py`: finite-support reference interpreter and local-output function
- `frozen_reversible_binary.py`: unchanged pinned prior compiler supplying template data
- `COMPILER_PROOF.md`, `SOURCE_SCHEMA.md`: unchanged inherited old-rule background, not the new rule
- `test_parallel.py`: source paths, full cycles, malformed cases, locality, and old-rule distinction
- `test_periodic_lemma.py`: independent exhaustive periodic model and mutation counterexamples
- `test_public_api.py`: exact integer/Boolean inputs, immutable snapshots, and alias rejection
- `*-receipt*.json`, `*.log`: normal/optimized evidence
- `manifest.json`, `SHA256SUMS`: packet inventory and hashes

Run offline from this directory:

    python test_parallel.py
    python -O test_parallel.py
    python test_periodic_lemma.py
    python -O test_periodic_lemma.py
    python test_public_api.py
    python -O test_public_api.py

The source interpreter's `E`, `P`, and inherited `factors` ledger fields count endpoint template types. They are not an ordered runtime factor sequence for the new CA; it has exactly two full-shift involution blocks. The universal ledger radius is a symbolic substitution only. This reference implementation builds small-source template arrays and is not intended to build the universal array.

All assertions relevant to checker correctness use explicit exceptions and survive Python optimization. Timings in receipts vary on replay. This is a mathematical proof with independent audits and finite executable corroboration, not proof-assistant verification.

For an invariant source tree, use `python -B` (and `-O` for optimized runs) and append `--output-dir /an/external/directory` to each checker command. All input paths are resolved relative to the scripts, so replay may run from a different working directory. The main suite takes about 90–100 seconds per mode here; the periodic and API suites take under two seconds each. Python standard library only; no network, browser, upstream third-party execution, or external sibling tree is required.

Only `ParallelCompiler` is the supported source-facing constructor. Finite supports must be sets/frozensets of exact Python integers; flags must be exact Booleans. The internal generic harness does not enforce custom guards' locality/purity/symmetry theorem assumptions. The public compiler obtains only the pinned immutable finite class guards.

Semantic computation/target statements transfer on admissible inputs. Report 19's evaluator and Report 20's ordered-factor/event-budget full-malformed-state certificates do not automatically evaluate or certify this new rule. Two parallel CA blocks do not imply two inexpensive arithmetic factors or transfer the old circuit counts.
