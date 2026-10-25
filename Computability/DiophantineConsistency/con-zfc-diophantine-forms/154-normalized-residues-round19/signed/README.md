# Round 19 signed common-sphere equations

All variables are unrestricted integers. Each JSON equation is the sum of
squares of every listed residual. Full collected coefficients are supplied.

| Endpoint | Variables | Rows | Degree | Terms | Height |
|---|---:|---:|---:|---:|---:|
| balanced244 (principal) | 244 | 176 | 4 | 5212 | 3968 |
| dimension243 | 243 | 175 | 4 | 19517 | 7680 |
| balanced247 (intermediate) | 247 | 179 | 4 | 5328 | 3968 |
| sparse250 | 250 | 182 | 4 | 4770 | 6709 |
| dimension246 | 246 | 178 | 4 | 21537 | 6144 |
| lowheight247 | 247 | 179 | 4 | 10422 | 3840 |
| exposed247 (height-one lifting source) | 247 | 179 | 4 | 4889 | 170496 |

The balanced244 construction improves the newly inspected common-remainder
252-variable predecessor (252/182/5340/128446) on all four varying metrics.
It also improves the prior round18 direct record (258/186/5364/128446).
These are achieved constructions, not minimum claims.

`PROOF.md` proves the new common-sphere/odd-radix composition and all algebraic
transformations. Together with the complete retained ordinary signed C222
calibration, it proves in ZFC that each polynomial has no integer zero if
and only if Con(ZFC). This is not a consistency proof or a new end-to-end
proof-assistant endpoint.

Run with Python 3 standard library only:

    python build.py --check
    python verify.py
    python -O verify.py

The producer is deterministic. The independent verifier imports no producer
code, checks the actual old sign guard, the exact new semantic rows, all
reversible transformations, unit polynomial restorations, coordinate compaction,
every coefficient and all metrics, and rejects deliberate corruptions.

`inherited_common/` is the complete portable direct component of the incoming
Common Remainders/Radix47 package. To replay its separate original arithmetic
certificate, run from that directory:

    python -B code/verify.py --rebuild
    python -B -O code/verify.py

The mathematical proofs and literal checked records, not finite root tests,
are the basis for the unbounded equivalence. Fixed operation certificates
suffice; no optimization heuristic or network connection is needed.
