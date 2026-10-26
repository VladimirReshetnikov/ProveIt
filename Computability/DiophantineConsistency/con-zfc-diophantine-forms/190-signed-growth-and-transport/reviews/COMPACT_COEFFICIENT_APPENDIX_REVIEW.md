# Fixed-coefficient appendix review

Reviewed the new `report/compact_coefficients.tex` against the archived indexed
constant specification and current `compact/source/rebuild_coefficients.py`.
Only the finite coefficient recipe was extracted; no historical equation or
historical proof-status note was imported. The sole constant renaming is K to K0.

A targeted independent reconstruction from the printed finite formulas checked
the 430 action decoder and complete, nonoverlapping 943-tile enumeration. The
436-character numeral was extracted directly from the new LaTeX and compared
character-for-character with the reconstruction script. All 11 correction
triples were also extracted and checked directly. The four independently
reconstructed integers equal the current script's values and authenticated
payloads. No simulation, refutation search, or polynomial-zero search occurred.

The numeral SHA-256 is `2a7a2f9315975135265f9dbe60f2290117c18225b448e5692c7b2da65f18882b`.

| Port | Bits | SHA-256 of unsigned little-endian bytes |
|---|---:|---|
| beta | 590069 | `0664a868cbfef9869ea05c40a1c445563f685ff857092594c1c1223bc4b21f9d` |
| K0 | 592884 | `0a86821a704294199c2e1a50379d242c96840a3366e9d965689ba3d74605203f` |
| MC | 590069 | `6007cabd5f5228618e8fb613f386d8fc3692a24520d6e4cd72af0262aae1ade4` |
| MF | 590070 | `48333b0d30a4edeb8579f44286cb59806c5622cb42b367f5b5f9ee827711c737` |

This is a mechanical finite-data check, not a new calibration theorem.
