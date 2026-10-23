# Attribution and proof dependencies

This package was prepared with AI assistance for Vladimir Reshetnikov's
ProveIt project on 23 October 2026. Its mathematical proofs and code remain
open to human review. Independent reviews in this package were conducted
by separate AI work streams and are not external human endorsements.

## New material in this package

The new component is the explicit, direct, multi-residual quadratic source
encoding: Sidon digit positions, separated reversed coefficient blocks,
simultaneous no-carry tests, the arbitrary-packed-witness bounds, and its
specialization to the fixed Con(ZFC) parent system. The package also
provides the resulting arithmetic circuit, exact symbolic and degree
audits, source-interface checks, documentation, and reproduction support.

The general Sidon/Golomb-ruler ideas and classical carry identities are not
claimed as new. The concrete finite-field construction and the provenance
of the chosen positions are described and checked in the included proof
notes and Sidon verifier. No global optimality is claimed for those positions.

## Inherited material

- **Zhi-Wei Sun**, *Further results on Hilbert's Tenth Problem*, Science
  China Mathematics 64 (2021), 281-306, arXiv:1704.03504v7: the digit-mask
  and binomial no-carry lemmas, the source-interface pattern, and the
  relation-combining background.
- **Zhi-Wei Sun**, *Ten unknowns for Hilbert's tenth problem over the
  integers*, arXiv:2609.01594v2 (2026): the general ten-integer reduction,
  Lucas certificate, binomial bridge, and interpolation theorem. The
  unknown-count theorem is Sun's result.
- **Matiyasevich, Robinson, Jones and other authors credited in the
  inherited sources**: the underlying Diophantine, Pell, and
  relation-combining methods.
- **ProveIt package 31**, `31-sun10`, at revision
  `22e75dd6b87b1b199bb08c778d7cf075ae5aae08`: the fixed parent residuals,
  complete 121-by-8801 coefficient tuple, K215/compiler ancestry,
  ten-integer finalizer including its quintic merger and separating
  weights, and arithmetic-circuit infrastructure adapted in `circuit.py`
  and `build.py`. The source-coding portion of that builder is replaced
  by the construction proved in this package.
- **The K215 machine's authors and upstream contributors**, as identified
  in the preserved machine and compiler notices: retain the complete
  upstream notices. This
  package does not reassign their authorship.

The new report, code, and supporting material are supplied for incorporation
into ProveIt under its MIT-0 terms. Copied or adapted third-party material
retains its original terms and notices. In particular retain
`vendor/package31/coefficients/licenses/LICENSE`, `LICENSE.Wade`,
`NOTICE-K215.md`, and the other included upstream notices. This paragraph
does not relicense any external paper or third-party source.

## Mathematical status

The theorem is a provability equivalence in ZFC for the inherited calibrated
proof predicate. It is neither a proof of Con(ZFC) nor a proof of its
negation. The new source lemma has an ordinary mathematical proof and
independent finite implementation checks. No new end-to-end Lean/Rocq
formalization is claimed, and Sun's 2026 preprint remains an explicit
mathematical dependency.
