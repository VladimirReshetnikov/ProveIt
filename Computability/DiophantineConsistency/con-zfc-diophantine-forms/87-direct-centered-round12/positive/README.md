# Positive-variable contribution, round12

- New: p11_degree211.json, eleven positive variables, degree211,113 operations.
- Reconstructed existing manuscript: p12_degree70.json, twelve positive variables, degree70,100 operations. Not claimed as new theorem.
- PROOF11.md gives the full new proof; section.tex is ready for inclusion in the combined report.
- PROOF12.md explains the materialization and its precise ordinary-source boundary.
- interfaces/ retains source proofs and graph inputs; native/ contains the whole actual compact44 tuple and provenance.
- Run `python build.py` to reproduce the graphs, then `python check.py` (also works with `python -O`). No upstream Python is executed.
- All coefficients and circuit registers are fixed integers or polynomial abbreviations. Only the listed witnesses are quantified.
- Mathematical equivalence proofs retain inherited native compiler/calibration interfaces; these are not new Lean/Rocq certificates and not global minimality claims.
