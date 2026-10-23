# Positive gap-coordinate source refinements

Main theorem: GAP_SOURCE_PROOF.md; optional guard theorem: EIGHT_GUARD_PROOF.md.
Editable report section: section.tex.

Run `python build_gap_source.py` (or `python -O build_gap_source.py`) to
reconstruct the polynomial sources and test the old incoming positional
certificate. Source inputs are inert JSON; no imported upstream code runs.

Valid with the original certificate:
- gap87_source.json: old P = new P + eta + zeta; 87 records.
- gapN86_source.json: additionally old N = new N + 1; 86 records.
- gapL86_source.json: alternatively old L = new L - 1; 86 records.

Requires a fresh positional certificate:
- gapNq85_source.json: old P = new P + eta + zeta and old N = new N + q;
  85 records. Its positive-domain equivalence is proved, but its old-certificate
  kernel files are diagnostic only: they have one target collision.
  Use the separate new encoding certificate for any final equation.

GAP_SOURCE_CHECKS.json explicitly distinguishes these outcomes. A successful
checker run means all EXPECTED outcomes matched, not that the deliberately
failing old layout for the 85-record source became valid.

Exploratory programs/logs are discovery provenance, not theorem dependencies.
They do not claim global optimality. In particular, candidate target changes
from repair_single_target.py are not production certificates.

The parent source and tuple/calibration lineage are inherited from the pinned
incoming source package. Preserve its notices with the enclosing artifact.
