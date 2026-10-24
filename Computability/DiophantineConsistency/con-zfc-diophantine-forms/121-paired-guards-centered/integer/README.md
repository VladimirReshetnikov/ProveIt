# Eleven-integer frontier refinement

Five nondominated literal equations: 688/124, 728/120, 820/119, 964/118, and 1632/112, where each pair is exact total degree / live binary arithmetic operations. All use eleven unrestricted integers and six authenticated fixed numeral payloads. The 820 and 964 endpoints use a new two-group coprime norm. The other three evaluate exactly the previous mathematical polynomials with two fewer operations.

No ten-variable endpoint or degree below688 is claimed. No global optimality, consistency proof, new formal endpoint, or internal object-ZFC certificate is claimed. PROOF.md includes both existence directions, complete definitions, all multiplier changes and fixed-witness order. source/ retains inherited unbounded proof dependencies and notices.

Offline reproduction, Python3 standard library only:

    python build_prior_optimized.py
    python build.py
    python check.py
    python -O check.py

CHECK.json and CHECK_OPTIMIZED.json independently verify every live register, all conjugate identities, exact degree cancellations, complete coefficient recipes and payload hashes, topology, liveness and operation counts. Dominated comparison circuits are clearly identified in PROOF.md.
