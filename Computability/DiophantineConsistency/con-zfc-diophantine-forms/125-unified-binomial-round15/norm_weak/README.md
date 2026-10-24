# Separate weak-Y split-carrier tradeoff

This package does not change either frozen graph in ../norm/.

- weak_integral_centered_paired.json: 11 unrestricted integers, exact degree416,125 live binary operations.
- weak_integral_direct_paired.json: 11 unrestricted integers, exact degree456,124 live binary operations.

Complete mathematical proof: ../scalar/CRT_CARRIER_PROOF.md, with its parent PROOF.md and full retained source dependencies. Exact algebraic degree/cost proof: DEGREE_PROOF.md. Independent literal/semantic review: ../scalar_audit/CRT_AUDIT_RESULTS.json and CRT_CARRIER_AUDIT.md. The precise all-integer bootstrap recovers the lost cubic-Y scale from the split carrier before using its size bounds or assuming c!=0.

Rebuild deterministically with python build_norm.py; verify with python check_norm.py and python -O check_norm.py. The generator uses only owned local code and Python's standard library; the verifier additionally uses installed SymPy. No upstream executable is imported.

The six ports in coefficients/BINDING.json are all fixed to their full authentic payloads, not free parameters. Every binary addition, subtraction and multiplication is counted, including scalar multiplication and squaring; reuse and leaves are free.
