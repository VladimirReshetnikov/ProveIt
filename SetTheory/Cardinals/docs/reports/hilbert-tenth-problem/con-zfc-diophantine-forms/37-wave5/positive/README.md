# Positive wave-5 synthesis

Primary results, all with twelve strictly positive supplied unknowns:

* `shift_half_product.json`: degree **1061**, **120** operations.
* `tight_half_product.json`: degree **1065**, **119** operations.
* `mid_half_product.json`: degree **1069**, **117** operations.
* `short_plain_product.json`: source30's **identical fixed polynomial**, degree
  **1081**, reevaluated in **109** operations rather than 111.
* The last family's system has **104** operations; its proved transport-shifted
  system has **103**. These are different coordinate presentations, not identical
  polynomial lists at the same inputs.

Each family also has a comparison system, a system with z_old=z+1, and a sum of
squares. Read `PROOF.md` for the complete table, all definitions, root recovery,
strict positivity in coordinate substitutions, and uniform exact-degree proofs.
`section.tex` is the short report section without a preamble.

The source30 whole Wang943 tuple is selected by `COEFFICIENT_BINDING.json`.
Paths point to the parent delivery's shared `../coefficients/` files. The generator
verifies all four raw SHA-256 hashes before emitting any new packet. The literal
original binding is preserved under `upstream/`; no source ports are spliced.

Rebuild with Python 3:

    python build_positive.py
    python check_positive.py

The emitter uses the standard library. The checker uses NumPy for complete
finite-field univariate polynomial specializations, plus a separately implemented
rank-eight algebra for exact conjugate products. No upstream Python is executed
or imported. `BUILD_RECEIPT.json` records gate counts, and `CHECK_RESULTS.json`
records the diagnostics. Every packet distinguishes its exact degree from the
larger syntactic upper bound that ignores cancellation.

The selected source pin is
`8c6eec9d19ef80538c8e61ff6e0180040583446a` in VladimirReshetnikov/ProveIt.
`SOURCE_PROVENANCE.json` lists inspected source files, Git blob IDs, URLs, and
local hashes. The root-level theorem remains the inherited ordinary mathematical
equivalence with Con(ZFC), not a newly kernel-checked theorem or an assertion
deciding consistency. No eleven-variable result or sub-67 equation is claimed.
