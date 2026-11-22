# Validation and proof status

The full mathematical proof is in the report. Its constants and arithmetic
scope were independently reviewed, including the raw certificate extension,
the translated-center domain margin, determinant conditioning, and the finite
Neumann coefficient-error estimates.

The completed checks are:

1. Lean 4.32.0 compiled the standalone finite core directly and with Lake.
   The compiler output and axiom reports are in ../lean/build.log.
2. The exact-rational validation passed all 1,317,978 assertions in the
   recorded finite suite. The result is in python_validation.json.
3. The report was compiled from its included LaTeX sources and visually
   inspected after rendering. The final layout report is in pdf_validation.json.

The complete implicit theorem is not yet a checked Lean theorem or an
object-iPRA proof term. The exact-rational tests are implementation evidence,
not a proof of universal analytic hypotheses.
