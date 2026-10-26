# Trace plus inverse Lucas correction

New AI-assisted composition for ProveIt at commit
fb1bed5eb7196cf35abfaa746c18c6ee7eae6cfb.

The principal graph has ten strictly positive variables, 85 live binary
arithmetic gates, and exact degree 232. The b-squared variant has the same
headline metrics and reduces the carrier numerator degree from 57 to 21.

- COMPOSITION_PROOF.md gives the new unbounded argument and exact scope.
- equations/ contains both literal polynomial DAGs.
- inherited/ contains the two immediate parent DAGs and proof texts, a
  complete finite coefficient recipe, and retained source notices.
- coefficients/ contains the actual four fixed integers as gzip-compressed
  canonical unsigned little-endian bytes and their full manifest.
- build_coefficients.py reconstructs all four coefficients from the exact
  436-character seed, action decoder, 943-tile table, and radix67 recipe.
- verify.py verifies the literal parent-to-child edit, topology and full
  liveness, all raw coefficient bytes, the full homogeneous leading form,
  and a free-polynomial completeness-map identity.
- SOURCE_PINS.json records the immediate pinned repository sources.
- NONTRANSFER_NOTE.md explains why the related P66 trace substitution is
  not automatically valid; it is not a counterexample to P66.

Run, with Python 3.10 or later and no external dependencies or network:

    python3 -B build_coefficients.py
    python3 -B verify.py

To rebuild the actual coefficient payloads:

    python3 -B build_coefficients.py --write

Finite graph and coefficient checks are complete and offline. The ordinary
unbounded proof explicitly composes the immediate parent results with their
named inherited Pell/native/refutation calibration. Those deeper repository
dependencies are citations, not a newly supplied or executed end-to-end
Lean/Rocq object. No consistency conclusion or global minimum is claimed.

The reported 170 mutation rejections mean that either wrong binary operation
at each of the 85 literal rows is rejected by the exact independently
reconstructed parent-edit graph comparison. They are not independent
unbounded semantic proofs for 170 altered constructions.

New work follows ProveIt's MIT No Attribution license. The inherited notice
records previous contributors and source boundaries. Source Git blob IDs
and raw artifact SHA256 hashes serve different purposes and are not
interchanged.

