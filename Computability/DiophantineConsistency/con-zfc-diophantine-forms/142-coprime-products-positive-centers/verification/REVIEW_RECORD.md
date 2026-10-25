# Research and release review record

Prepared 25 October 2026 within an AI-assisted research workflow. This is
not outside human peer review or an end-to-end proof-assistant certificate.

## Unbounded arithmetic review

The product constructions were developed separately from their independent
review. `product_review.md` records the full second derivation of soundness,
completeness, integrality, positive witnesses, exact degree, and source
restoration. `product_review_checks.json` binds that review to the three
final graph files. The degree calculation was corrected from a preliminary
433-versus-435 arithmetic discrepancy before release; the final degree is
433 everywhere that states the preferred endpoint.

The ten-variable composition was reviewed against its source interface.
Specific issues checked were the sign of the unshifted auxiliary input,
the exclusion of the main index three, the necessity of authenticating a
bounded index before claiming full carrier divisibility, the whole-product
projection, and recovery of `q|s` in the partial-saturation companion.
No coprimality of the full denominator with the remaining scalar factors
is assumed where only the `q^4` divisor is available.

The direct natural construction was reviewed in both directions. The
positive-center proof restores the old nonnegative congruence quotients
before invoking their semantic interpretation. Aggregate remainder bounds
have an additional completeness budget, and the deleted factorial-digit
bound is proved from exact powers and a ceiling equality before using the
factorial/binomial interpretation. The contraction certificates establish
nonnegative restoration of every eliminated coordinate.

The final prose review checked domains, numerical endpoint tables and
source boundaries. It corrected two wording issues: P14 saves one net
coordinate, and the bundled logical interface files are selected sources,
not a complete proof-assistant dependency closure. Python reproduction is
self-contained.

## Finite release checks

`FINAL_CHECK.json` and `FINAL_CHECK_OPTIMIZED.json` record actual invocations
of the top-level verifier in normal Python and `python3 -O`. Both completed
all seven component commands successfully, including full direct rebuilds.
Their initial distribution-manifest field records that those runs occurred
before final packaging. The finished distribution's `SHA256SUMS` is checked
separately and is also checked automatically on every subsequent verifier
run from the delivered archive.

The finite checks cover exact circuit topology and liveness, operation
counts, degree certificates, independent formula evaluations, all four
reconstructed fixed constants, all 275 raw quadratic rows, all restoration
certificates, every collected quartic coefficient, all twelve rebuilt JSON
files, and exact parsing of all printed direct residuals. Mutation controls
test the actual validators. Small Pell examples test implementation details;
they do not replace the general proofs or supply a consistency witness.

The report is compiled with pdfLaTeX and rendered with Poppler for visual
review. Distribution checksums are produced after the final report and
release metadata are frozen.

## Logical boundary

The new reductions give ordinary proofs formalizable in ZFC. Their final
calibration uses the exact retained indexed native/K215 interface or the
direct C222/ZF/ZFC interface, respectively. The associated proof sources,
selected logical interfaces, producer closure and pinned references are
identified in the component provenance records. Neither finite testing
nor this review asserts that ZFC is consistent or that the polynomials
actually lack solutions.
