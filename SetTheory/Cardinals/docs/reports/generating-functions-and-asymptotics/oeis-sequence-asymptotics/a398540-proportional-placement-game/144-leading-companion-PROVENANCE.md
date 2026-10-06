# Computational provenance

This companion was implemented for Report144 on 3 October 2026. Its mathematical definition and required analytic inputs are stated in the accompanying report and in this directory’s README. It is a finite exact verification package, not a substitute for the report’s mathematical proofs.

The principal implementation uses an integer binomial-tail representation of the beta-bin weights and computes every term in every row. The second route uses an independently implemented alternating polynomial antiderivative and symmetry reduction. Separate recurrence vectors are constructed and compared term by term. Both representations are explicitly displayed in the README, so reproduction does not depend on any earlier implementation.

The fixture was generated from the two-route implementation and validated afresh in normal and optimized isolated runs. All 130 adversarial tests passed in both modes, and normal and optimized verification summaries were byte-identical. The full rational-vector digest is f6910ee2606f2272b4293f20e2d923961d6245e64743e112bc23c8cdc777c2f7. The public package manifest records all deliverable file hashes. A hash identifies bytes; the mandatory exact recomputation supplies the mathematical finite check.

The trusted base is the Python interpreter and its standard library. The tests do not claim protection against replacement of that trusted base. No external PDFs, private notes, floating-point diagnostic results, or runtime-duration fields are included.
