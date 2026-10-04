# Five-signal validity: explicit ordinary-integer certificate

The primary result is in **PROOF.md**. It gives a direct positive-integer Diophantine certificate for the actual five-live-signal infinite-complete-macro validity predicate, using two fully expanded Pell-based POWER modules rather than generic MRDP.

Primary ledgers:

| Input interface | Positive witnesses | Equations | Gates | M | Addition/subtraction | Exact degree |
|---|---:|---:|---:|---:|---:|---:|
| Three positive gaps | 81 | 44 | 344 | 136 | 208 | 12 |
| One positive Cantor code | 85 | 46 | 367 | 144 | 223 | 12 |

The one-input decoding is fully paid. Optional quartic residue-selector versions save one witness and cost six more gates; they are secondary alternatives, not improvements under a single resource ordering.

## Files

- `PROOF.md`: complete iff proof, domains, all equations, degree proof, resource ledger, dependencies and limitations
- `emit_certificate.py`: newly authored fixed-size source emitter
- `evidence/*-linear.dag.json`: authoritative primary polynomial sources
- `evidence/*-quartic.dag.json`: explicit alternative polynomial sources
- `evidence/*.receipt.json`: exact emitter witness/residual/gate ledgers
- `check_semantics.py`: newly authored exact arithmetic and negative tests
- `evidence/semantic-checks.json`: semantic test receipt
- `review/ALGEBRA_REVIEW.md`: independent reduction and bounded-extraction review
- `independent_audit/EXPANDED_SOURCE_REVIEW.md`: independent full expanded-source audit
- `independent_audit/check_dags.py`: separately authored exact sparse-polynomial checker, including all thirty POWER residuals
- `independent_audit/audit-receipt.json`: independent normalized residual/output identities, source pins, counts, degrees, and 32 corruption rejections
- `sources/`: inert dependency copies and provenance; no source there was executed
- `PACKET_MANIFEST.json`: relative-file hashes for the packet

## Verification scope

The owned semantic checker passed 15,804 outer-system instances, 65,732 bounded-extraction candidates, 10,000 code round trips, and 3,951 gap round trips. It fully instantiated eight complete exponent-zero Pell certificates across all four source variants. Of 660 positive single-leaf perturbations, 644 were rejected and 16 correctly remained zeros because they changed Bezout coefficients multiplying zero. Nonzero-exponent tests independently compute ordinary powers and check the outer constraints; they do not numerically instantiate their potentially enormous Pell auxiliaries.

The independent source checker proves exact algebraic identity of every residual and of the full normalized sum of squares against a separate mathematical specification. All inputs, witnesses, and gates are live. Its exact degree computation is 12 for all variants. It also verifies that the current POWER prelude and fifteen equations match the prior source after declared renaming.

These are conventional mathematical and source audits, not a new Lean formalization. The supplied geometric theorem and the pinned constructive Pell theorem are the explicit inherited dependencies. No physical simulator, upstream executable, saved program, or older checker was run. No finite-fold, singlefold, or real-witness assertion is made.

## Optional fresh rechecks

From this directory, ordinary or isolated Python can run the newly owned scripts:

    python -I emit_certificate.py
    python -I check_semantics.py
    python -I independent_audit/check_dags.py

The first regenerates the four fixed DAGs. The second reads the DAGs as inert JSON and tests exact integer arithmetic. The third independently reads and normalizes the source; it never imports or runs either emitter or prior programs. Existing dependency files can be inspected without executing any code.
