# Reproduction and package checks

Checked 2 October 2026. These are deterministic computational and rendering checks, not a proof of asymptotic remainder bounds.

## Environment

- Python 3.12.14
- SymPy 1.14.0 and mpmath 1.3.0, pinned in requirements.txt
- pdfTeX 3.141592653-2.6-1.40.26 (TeX Live 2025/dev/Debian)
- Poppler pdftoppm 26.05.0

The existing build script fixes SOURCE_DATE_EPOCH and compiles twice. Its isolated rebuild produced a byte-identical nine-page PDF. A different TeX distribution may render an equivalent document without producing identical bytes; the byte-equality test intentionally detects such a difference.

## Mathematical replay

A clean replay in temporary storage regenerated the following and compared them with the supplied records:

- Both symbolic saddle algorithms through order three
- The independent hand-expanded first two marking-saddle corrections
- The fresh independent direct-poset audit through n=8, both direct symbolic saddle expansions through order three, local singular coefficients, conditional correction identity, source/data hashes, and covariance samples
- All 30,326 record/cycle forward-and-inverse round trips through n=8, including rotated cycles and reversed cycle-set order, and all one-cycle count checks
- Every exact refined row through n=400
- Independently enumerated literal binary-word joint counts in the pair count and isolated-element count through n=8
- Every stored singular-expansion, complex-parameter, moment, local-count, and conditional-isolated-mean sample, excluding the nondeterministic elapsed-time field
- The final PDF rebuilt in isolated temporary storage

A separate additional manual degree-six exponential expansion verifies b3 against the stored symbolic formula without importing the coefficient generator. The release verifier repeats this check and compares the full JSON result.

## Release integrity

The verifier requires SHA256SUMS, rejects an absent or incomplete manifest, checks all recorded file hashes, and compares the independent audit outputs exactly. The missing-manifest negative test was checked. All calculations are repeated in temporary directories; the release files are not overwritten. The archive contains the report, editable source, expanded proof, scoped reviews, exact data, algorithms, recorded checks, and reproduction scripts. Build caches, page PNGs, planning material, and unrelated earlier releases are excluded.

Finite computations establish only the tested exact ranges and numerical comparisons. They do not prove the general saddle theorems, establish certified finite-n constants, extend the density range to either endpoint, or imply convergence of a fixed-order Poincare series. The report explicitly records slow convergence at density 0.2.
