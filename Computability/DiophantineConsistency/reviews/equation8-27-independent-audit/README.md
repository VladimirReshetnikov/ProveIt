# Independent provisional 27-variable equation audit

The audit covers the candidate PDF with SHA-256 `181e6b6dea3c1bd9433e3a5f93fa4b10894616463b94d23f0fe717d290bb04e2`. It independently binds the 27 distinct inputs and four fixed ports and checks all 129 printed gates against the candidate DAG, including topological order, unique names, liveness, and the output. The sparse-polynomial display validator compares 40 definitions and all 18 squared residuals, including the fixed decimal constants, and is exercised with additional sign, extra-square, unknown-name and gate-operator mutation controls.

The explanatory gate aliases were checked individually. An initial discrepancy called the printed gate `m` by its internal name `f2`; it was corrected before this audit and the corrected PDF hash is recorded above. Two isolated clean builds reproduce the PDF byte-for-byte, with no overfull/underfull boxes or font warnings. Both resulting pages were visually inspected and their images are retained here.

This audit is strictly a check of the provisional display and finite graph, not a Lean proof of model witness transport, iPRA equivalence, current-source dependency closure, or global minimality. The PDF explicitly identifies its model and native proofs as open. The displayed polynomial degree is supported by separate integer-polynomial checks, not a Lean degree theorem.
