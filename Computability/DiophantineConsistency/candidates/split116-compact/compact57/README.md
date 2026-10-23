# Split116 with the whole compact57 tuple

This is a separate candidate artifact; delivered packages are unchanged.
Its positive and natural coordinate orders are `b,g,h,s,w,C,i,j,n`.
The positive polynomial has 473 binary operations and exact degree 1,910,404;
the natural polynomial has 480 operations and the same degree.

All four coefficient ports come from package 57. MF_source is already shifted.
The weighted coefficient bound is 2^1182955, the radix floor is
2^1182967, and the threshold scale is 2^9463725.
Every live nonliteral fixed leaf is materialized as a signed magnitude in fixed/.

Reproduce from the repository with `python -B tools/generate_split116_compact.py --tuple compact57 --check` (from the research root).
PROVENANCE.json binds the whole tuple, retained source/proofs and adapted code.
REPLAY.json and EXTRA_CHECKS.json report finite checks.

No new unbounded compiler calibration, Lean consistency endpoint, internal ZFC
derivation, or global simplicity minimum is claimed for this candidate.
