# Smaller explicit Diophantine forms for Con(ZFC)

Pinned review: VladimirReshetnikov/ProveIt, commit ae3007ca4467011e0e051c84acb4a1dd13971b0e, wave-3 packages 16--23.

Read report/synthesis_report.pdf (editable TeX and Markdown alongside it). This package is a mathematical synthesis and reproducible finite audit, not a proof of consistency, global optimality, or a newly kernel-checked end-to-end theorem.

## Recommended forms

- 12 strictly positive unknowns, one equation, exact degree 1081, 111 binary ring operations: positive/positive12_product.json. The 3-equation system uses 107 operations and maximum degree 1072.
- 24 unrestricted integers, one equation, degree 2240, 165 operations: integers/integer24_sharp_pair_norm165_degree2240.json.
- 25 unrestricted integers, degree 920, 131 operations: integers/integer25_small_weight131_degree920.json.
- 26 unrestricted integers, degree 214, 123 operations: integers/integer26_ordinary_two_root123_degree214.json.
- 31 strictly positive unknowns, 22 quadratic equations, 65 comparison-circuit operations: arithmetic/quartic31_system.json. The single quartic uses 130 operations: arithmetic/quartic31_circuit.json.
- 9 nonnegative unknowns, one equation, exact degree 120724*5^32+366, 1840 operations: nine/nu31/nine_compact_magnitude_tight.json.
- Same original package18 nine-variable polynomial, faster evaluator only: review/nine_optimized/nine_generic32_majorant.json, 1704 operations at unchanged degree 161844*5^33+484.

All arithmetic costs count binary +,-,* with sharing; scalar multiplication and squaring are charged, fixed-constant construction is not. Domain, equation count, degree, operation count and coefficient size are different objectives. No one construction is globally called simplest.

## Constants

COEFFICIENT_BINDING.json selects one complete compact Wang943 four-port tuple for every recommended circuit. The four actual integers appear exactly once, in compiler/coefficients_compact/*.bin (unsigned little-endian, no header). ZIP compresses them. MF means shifted MF_source, never native MF. Historical default backend annotations are provenance only and are overridden together by this binding.

The Jones bound z=2^45933757 is materialized in nine/z_index.bin. Its 402 weighted coefficient constants and y_index are explicit bounded finite recipes in nine/nu31/COMPACT_CONSTANTS.json, not materialized integers. They are fixed coefficients, never free unknowns. The parent witness parameter is nu=31, unrelated to the compact radix exponent 5^10.

## Verify without mutating this release

Use Python 3.10+ with NumPy already available:

    python3 verify_release.py

The verifier first checks every immutable file digest, exact source Git blob/SHA256 identities and all materialized coefficient values. It then copies this tree to a temporary directory and runs only newly authored checkers/emitters there. It checks frozen arithmetic skeletons after emitter replay and rechecks the delivered tree unchanged. Do not use python -O: optimized mode is explicitly rejected because assertions are audit checks. No network, received-program execution, installations or public writes are needed.

The received package18 Python source is renamed with a .inert suffix and is never imported. Received Lean files are read-only provenance, not a claimed rebuild. Historical emitted data are inert JSON. The executable audit modules in the active check suite are new local work.

PORTABILITY_TRANSFORMS.json records the small packaging-only adapters: shared central coefficient paths and local inert emitter parents. It does not alter any polynomial. RELEASE_MANIFEST.json is immutable and is not generated or rewritten by verification.

## Proof boundary

The full new proofs are included in the report appendices and the lane directories. Their inherited dependencies remain the exact K215 refutation-machine calibration, blank/native/Pell compiler, coherent compact Wang943 transfer, relevant signed rank/population lemmas, and Jones's applicable nine-witness theorem. Exact finite audits and modular diagnostics do not replace those ordinary unbounded mathematical proofs.

The retained source and comparison notes include intermediate results as history. Current metrics are those above, review/FINAL_NINE_REVIEW.md and review/NU31_INDEPENDENT_AUDIT.json. In particular the final nine degree has +366, not a discarded draft +334, and the same-polynomial control has 1704 operations, not the earlier intermediate 2915.

## Rebuild the PDF

On a machine with Pandoc, XeLaTeX and DejaVu fonts:

    python3 report/build_report.py

Run this in a working copy, not the immutable release. No TeX cache or operating-system font files are bundled. The standalone report/synthesis_report.tex can also be compiled with XeLaTeX directly.
