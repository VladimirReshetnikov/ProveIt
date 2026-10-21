Five-zero source recoding (research partial result)
==================================================

This directory contains five exact 206-DAG-node sources equivalent, at
primitive ordinal control-flow level, to the 203-node dominated-rho8 K218
source. Their maximum zero run is five, versus six in the baseline.
These files are source programs, not 206-state Turing machines. No <=217-state
binary machine has been verified by this source experiment.

Portable verification (Python 3.10+, standard library only):
  python3 -B verify_sources.py

Deterministic reconstruction of the four interval-DP sources:
  python3 -B zero5_dp.py --source data/seed205.json --out replayed_dp --beam 4

The output directory must not already exist. Its source-206-0.json through
source-206-3.json match data/zero5_dp0.json through data/zero5_dp3.json exactly.
The source-language module is copied unchanged from the ProveIt repository:
  Computability/BusyBeaver/Research/ZFC/k218-quantifier-stability/pricing/
  source_language.py
Its attribution comments remain intact.

The verifier checks the recorded hashes; full binary prefix-tree syntax;
source metrics; equality of the primitive word; equality of every guarded
successor under two different CFG constructions; and the unchanged first
37 initializer instruction addresses. The mathematical consequence is exact
step-for-step source semantics for all natural register vectors.

The receipt files record the searches as they were performed. Scratch paths
inside historical receipts are provenance only and need not exist to run
verification. Their finite search counts do not assert a lower bound.
The physical-rotation search/finite-test receipts are supplementary negative
coverage: their best table remained at 218 states with 26 six-zero source
addresses. That table is not part of this source-only deliverable.

source-results.tex is a section fragment for inclusion in the main report.
