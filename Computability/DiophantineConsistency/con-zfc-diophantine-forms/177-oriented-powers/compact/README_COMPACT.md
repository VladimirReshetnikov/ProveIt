# Square transport and a polynomial root center

This is a supplemental compact construction for the ProveIt research packet.
All ten variables are **strictly positive integers**. The unrestricted-integer
principal equation is supplied by the main packet.

## Literal equations

| File in compact_equations/ | Degree | Binary operations |
|---|---:|---:|
| inverse_trace232_bV.json | 232 | 85 |
| inverse_trace232_b2.json | 232 | 85 |
| centered224.json | 224 | 90 |

The first combines the existing inverse-Lucas correction with the unsquared
trace. The second proves the square-transport variant left open by the trace
source. The centered equation lowers the degree by using that stronger
transport estimate and a constructive positive lift.

`PROOF_COMPACT.md` contains the full new ordinary proof and the exact inherited
logical boundary. `compact_section.tex` is the report section. The two pinned
source proofs are retained for the mathematical interfaces used here; their
full transitive native/K215 calibration is cited rather than recompiled.
`NOTICE_COMPACT.md` identifies attribution and scope.

The complete fixed numerical tuple is in coefficients/. Its independent
finite reconstruction program and the original printed recipe are included.
Both raw and deterministic compressed hashes match the pinned parent exactly.
No coefficient is unspecified. DAG nodes introduce no additional unknowns.

## Verification

Use Python 3.10 or later and its standard library:

    python3 -B build_compact.py --check
    python3 -B verify_compact.py
    python3 -O -B verify_compact.py

The checker verifies every actual gate, all inputs and ports, free polynomial
identities, exact complete leading forms, operation counts and all coefficient
bytes. It rejects both alternative binary operators at every gate.
Its receipt is COMPACT_VERIFICATION.json, which it overwrites on a new run.

To reconstruct all coefficient payloads from the finite recipe:

    python3 -B reconstruct_coefficients.py

This performs no machine execution, proof search or consistency decision.
Finite artifact checks do not replace the unbounded proof or inherited
logical calibration. No new kernel-checked theorem, global minimum or
historical-priority claim is made.

Source snapshot: ProveIt commit
`0c48d332df6b0e50d4e5b6251c531898f5682c72`.
