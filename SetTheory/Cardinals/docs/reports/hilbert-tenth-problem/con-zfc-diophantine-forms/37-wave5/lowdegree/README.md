# Integer low-degree and circuit synthesis

New results on the shared complete source19/source30 compact Wang943 tuple:

- 50 unrestricted integers, 29 quadratics, 111 comparison operations; quartic
  SOS in 197 operations. This removes one integer packing register from the
  previous 51-integer quartic, with a signed-domain-valid restoration.
- 24 unrestricted integers, degree1936 in 161 operations; three-equation system
  degree1920 in 156 operations; SOS degree3840 in 164 operations. A smaller
  ratio weight, scalar trace/product norm, shared HQ and direct comparison
  improve the previous degree1936 evaluations at 167/168 operations.

`PROOF.md` gives formulas, both directions, all sign and zero-boundary cases,
exact degrees and the dependency boundary. `build.py` generates literal JSON
circuits. `check.py` independently checks their identities, degrees, liveness,
and eight-factor norm evaluation. `CHECKS.json` is the latest receipt.
`integer50_quartic_expanded.json` also gives every expanded residual and the
full 414-term quartic. `SOURCE_PROVENANCE.json` freezes exact upstream text
copies at ProveIt commit 8c6eec9d19ef80538c8e61ff6e0180040583446a.

Run:

    python build.py
    python check.py

Dependencies: Python3, SymPy, NumPy. New generators/checkers are authored for
this synthesis; received source programs remain inert. Historical source
bindings remain untouched, but every new artifact binds atomically to
`../coefficients/COMPACT_COEFFICIENT_BINDING.json` with MF already shifted.

The result is an ordinary mathematical Con(ZFC) equivalence, not a proof of
consistency, an end-to-end proof-assistant certificate, or a minimality claim.
