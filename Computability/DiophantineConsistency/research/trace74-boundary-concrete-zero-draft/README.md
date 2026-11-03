# Proposed same-witness boundary zero

This source applies the independently checked seed specialization to the eight model facts with the exact same W/S, retaining the resulting witness. It proves in the author check that this witness is positive, has `w 0 = w 1 = w 2 = 1`, makes the formal 74-operation graph zero, and satisfies `q = w 1 + w 2` for the arbitrary port tuple `(1,1,28,0)`.

The author Lean check passed; the [independent post-run review](../../reviews/trace74-boundary-concrete-zero-result-independent/README.md) passed. The tuple violates the fixed BFS port bounds, and a connection to external displayed files remains separate. Parent provider and package/source-ancestry boundaries remain.

The [independent source review](../../reviews/trace74-boundary-concrete-zero-draft-independent/README.md) checked the shared W/S, all eight hypotheses and same-witness guard equality; it did not run Lean.
