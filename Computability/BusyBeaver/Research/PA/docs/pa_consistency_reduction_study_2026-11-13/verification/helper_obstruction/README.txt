Exact bound for one frozen PA194 selector-sharing template
========================================================

Run:
  python3 -B verify_helper_obstruction.py

Python's standard library suffices; no Git checkout, external solver,
proof assistant, or internet connection is required. Assertions must be
enabled. The checker re-enumerates its finite optimization model from the
supplied raw transition table, then checks an exact rational dual certificate.

Verified result:
  raw controls:       201
  AX readers:          67
  useful helper types: 1039
  possible fold pairs: 120
  linear constraints:  265
  lower bound on helpers minus folds: -7
  lower bound on resulting control count: 194

The template is deliberately restricted to this frozen source grammar,
disjoint incoming-bit reader pairs, and direct selector helpers whose
destinations are existing raw controls. All action equalities and provider
matches are evaluated as literal RAW rows BEFORE any aliases. It does not
include equalities or provider matches created by other identifications,
mutually supporting aliases, helpers targeting new helpers, different
source associations, modified fixed controls, longer detours, or changes
to the logical calculus. Simultaneous fold compatibility is relaxed.

This is not a lower bound on arbitrary Turing machines. It does not produce
a new consistency machine, prove nonhalting, or finish the requested
construction below 194 states.

helper_obstruction.tex contains the mathematical statement and proof.
helper_lp_certificate.json contains the finite model and rational dual.
primary201.native.tm is the frozen input; its provenance is described in
that TeX fragment and its hash is checked by the verifier.
helper_obstruction_verified.json records the successful checker output.
helper_obstruction_manifest.json hashes the central files.
The two LICENSE files retain notices for the upstream raw transition table.
