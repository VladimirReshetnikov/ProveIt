# Split116 with the whole compact54 tuple

This is a separate candidate artifact; delivered packages are unchanged.
Its positive and natural coordinate orders are `b,g,h,s,w,C,i,j,n`.
The positive polynomial has 473 binary operations and exact degree 1,910,404;
the natural polynomial has 480 operations and the same degree.

All four coefficient ports come from package 54. MF_source is already shifted.
The weighted coefficient bound is 2^864015, the radix floor is
2^864027, and the threshold scale is 2^6912205.
Every live nonliteral fixed leaf is materialized as a signed magnitude in fixed/.

Reproduce from the repository with `python -B tools/generate_split116_compact.py --tuple compact54 --check` (from the research root).
PROVENANCE.json binds the whole tuple, retained source/proofs and adapted code.
REPLAY.json and EXTRA_CHECKS.json report finite checks.

No new unbounded compiler calibration, Lean consistency endpoint, internal ZFC
derivation, or global simplicity minimum is claimed for this candidate.
