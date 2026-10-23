# Ten integers via a two-root congruence finalizer

`generated/integer10.json` is the primary literal polynomial. The exact live
operation count and total degree are in `generated/METRICS.json`; independent
checks and nonzero highest-degree residues are in `CHECKS.json`.

Run from any working directory:

    python build_integer.py
    python verify_integer.py

The builder uses Python's standard library. The checker additionally uses
SymPy for one exact polynomial identity. No network or upstream program is
required. The alternative in `alternative_low_cost/` has its own complete
literal coefficients, data and checks; run the same two commands there.

All four inherited source ports are kept together. Fixed coefficient
magnitudes are unsigned little-endian files, gzip-compressed with zero mtime;
signs and SHA256 hashes are in `fixed/MANIFEST.json`. Their interpretation is
literal, not existential. The fixed source radix and threshold are also
materialized. Named registers introduce no additional quantified unknowns.

`PROOF.md` gives the mathematical equivalence, while `section.tex` is the
report section. The source-gap theorem and inherited source/compiler and
arithmetic bridge proofs are retained under `upstream/`. The new finalizer
does not decide consistency or constitute an end-to-end Lean/Rocq certificate.

Compared with the incoming degree-separated ten-integer expression, this
composition uses a quartic two-root norm rather than an eight-factor norm.
Parity makes the two radicands unequal on every signed assignment. A
conditional low-mask-bit deletion removes the outer leading block while
preserving the required residue modulo3. Exact shared power chains reduce
gates without altering coefficients. The fixed threshold is precomputed;
adding five constant-only gates restores the older evaluator convention.

This is not a claim of global minimality. All inherited notices and licenses
remain applicable, and dependencies are explicit rather than hidden behind
finite regression tests.

Historical relative paths inside preserved input binding files are provenance,
not active release paths. The retained complete interface proof is
`upstream/COEFFICIENT_PROOF.md`; the active four binary files are in `data/`.
