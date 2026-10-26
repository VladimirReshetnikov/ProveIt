# One reciprocal budget for the Pell cap and digit remainders

The explicit polynomial `equations/integer82_degree16964_linear.json` has 82
unrestricted integer inputs, exact degree 16,964, 23 residual squares and
1,723 binary arithmetic operations. It refines the pinned direct 85-variable
parent by replacing two private ternary nonnegativity certificates with one.
The 81-variable companion has degree 2,097,732 and 1,711 operations. The
106-variable degree-32 companion uses 1,830 operations. These three combine
the new reciprocal guard with the separate linear sign-orientation numerator
proved in `proofs/LINEAR_ORIENTATION.md`. All three selected profiles are
listed in `equations/RESULTS.json`.

`proofs/FUSION.md` contains the complete ordinary proof of the new step,
including soundness before the Pell sign bootstrap and a quantitative
canonical-witness completeness bound. The final consistency equivalence
uses the named inherited C222/ZF/ZFC calibration. No global minimum or
new end-to-end Lean/Rocq theorem is claimed.

Run from this directory:

```sh
python3 -B verify_all.py
python3 -B -O verify_all.py
```

Rebuild and byte-compare the exact outputs with `python3 -B rebuild_all.py`. All programs
use Python's standard library. The independent checker imports neither
the producer nor upstream search code. It verifies exact source bindings,
semantic ports, every preserved expression, the new guard polynomial,
square-sum output, exact degrees, height bounds and real occurrence of
every input, and rejects 15 deliberate corruption controls. The complete
immediate parent is retained as `sources/parent_archive.zip`; the full
checker extracts it temporarily, checks every copied source binding and
runs its original verifier before checking the new transformations.

The immediate source archive is the repository file
`docs/incoming/ConZFC_Direct_Integer_Elimination_2026-10-25.zip` at commit
`b42c796d1f5de9912a576bc2fd77b778ae7402bf`. Its literal projected parents
and 219-coordinate source are retained under `sources/`; its ordinary
proof is retained as `sources/PARENT_PROOF.md`. Its full original archive is
included. Earlier calibration declarations remain identified inherited
theorems, with the same historical formalization boundary as that archive.

Named gates in the JSON are polynomial abbreviations, not additional
unknowns. Circuit operation counts differ from bit complexity. Exact
expanded coefficient heights and monomial counts of these high-degree
polynomials are not claimed.

Inspect the input order with `python3 -B evaluate.py --variables`; use
`--tuple tuple.json` to evaluate at supplied integers. Adding
`--modulus 1000000007` performs modular evaluation. `--zero` is an explicit
all-zero tuple fixture. A modular zero is not an integer zero. No program
searches for a refutation or decides consistency.
