Independent literal-tape verification of PA194TDY
================================================

From the archive root, run:

  python3 -B verification/literal/check_tdy.py

Python's standard library is sufficient. Assertions must be enabled; do not
use Python -O or PYTHONOPTIMIZE. The vendor directory preserves the original
checker sources, metadata, source reference, and licenses without changes.
The original vendor README describes its original package; use check_tdy.py
as the entry point for this package.

This checker supplements the oracle-based Python and JavaScript regression
checks. It uses an independent symbolic tape representation and assumes no
register arithmetic-box oracle. Four generic unary-list sweep lemmas are
rederived from the actual PA194TDY transition rows. The complete source
control-flow graph is independently resolved in two ways and compared both
with source/instructions.json and the frozen 195S reference instruction map.

Each primitive source outcome is then replayed using literal transitions,
self-loop induction, the four newly checked list traversals, and exact
finite-list word identities. Its physical duration is an explicit affine
expression with nonnegative coefficients and strictly positive constant.
The parameter scope is nine independent natural register values, both
decrement cases, header distance 48+n for every natural n, and an arbitrary
finite nonempty list of arbitrary natural spare values.

A separate bytearray simulator checks the entire 57,594-step blank startup
and every cell of the complete expected seed frame, including the zero
exterior. Dense/native conjugacy and both literal-table hashes are checked.

The recorded directory contains the four list-lemma traces, all per-source
affine duration and head-motion certificates, the complete startup frame,
and the summary receipt. PROVENANCE.json identifies the imported snapshot
and gives SHA-256 values for all unmodified vendor files.

These are executable finite and symbolic certificates supporting the
ordinary mathematical PA simulation proof. They are not a new end-to-end
Lean/Rocq theorem or a PA proof-code compiler. The numerical-calculus PA
calibration and corpus-novelty census are separate obligations documented
elsewhere in this package.
