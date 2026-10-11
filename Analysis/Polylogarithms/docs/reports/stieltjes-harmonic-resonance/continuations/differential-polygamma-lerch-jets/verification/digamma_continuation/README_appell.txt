Gamma--Appell continuation: exact algebra and diagnostics

Keep these scripts and their JSON records together in one directory.
Requirements: Python 3, SymPy, mpmath. The research source is appell_section.tex.

Commands, in order:
  python compute_appell.py
  python mzv_weight6.py
  python verify_appell.py
  python numeric_appell.py

compute_appell.py constructs exact finite pole data, residue defects, strict
upper/lower word concatenations, and ordinary higher-pole word tables. It writes
appell_4.json through appell_7.json.

mzv_weight6.py generates 49 classical shuffle/stuffle/duality equations in 16
admissible weight-six words, selects 16 independent rows, and writes their
rational inverse and the complete solution to mzv6_relations.json. It also
reproduces J7 = 3731*zeta(3)^2/4 + 918631*zeta(6)/240.

verify_appell.py independently multiplies the stored rational certificate,
checks all 49 equations, verifies the printed sixth/seventh directional
simplifications using only differentiated free-order stuffle identities,
and tests the exact finite-index versus tail-index conversion. It rejects
two altered directional coefficients. The 14 named controls are recorded
in exact_appell.json. These are finite algebra checks; the article proves
the analytic continuation, convergence, and finite-part normalization.

numeric_appell.py compares a direct Taylor-subtracted finite-part integral
with an independent Gamma beta-kernel integral plus the ordinary defect
logarithm series. It uses 80 working decimal digits, a cutoff of 96, and
42 inverse-power tail terms. Recorded discrepancies are about 8.80e-56
and 5.72e-54 at degrees six and seven. The data in numeric_appell.json are
floating-point diagnostics, not interval certificates.

The *.base64 file and sources/ directory in the agent scratch workspace are
retrieval intermediates. They are not part of the research deliverable.
