# Report 224

All fixed order asymptotics for restricted two covers and line graphs

Reconstructed edition 2, 5 October 2026. This is a new reconstruction with fresh checks, not a byte-identical recovery of an earlier draft.

## Mathematical scope

- V = A060053; U = A014500
- H is the positive weighted Poisson sum
- L is the corrected labelled line-graph sequence, beginning 1,1,2,8,60,729,11600
- The legacy multiplier matches the retrieved A132219 terms but is not the corrected L
- Exact-saddle, finite-shift, and explicit Lambert remainders have different scales
- All fixed-order statements are asymptotic theorems; software caps do not limit the theorems
- Inverse model roots do not certify arbitrary integer thresholds without true-sequence bounds

The leading equivalents and exact graph identities are credited to Cameron, Prellberg and Stark. The report makes no worldwide novelty claim. No conjectured remainder is attributed to OEIS: the retained A060053/A014500 histories checked during source review contained no such conjecture.

## Requirements

Python 3.11+ suffices for exact counts and tests. The PDF builder also needs pdfTeX/TeX Live and the standard packages geometry, fontenc, lmodern, amsmath, amssymb, amsthm, mathtools, booktabs, longtable, array, microtype, hyperref and bookmark. The code was checked with Python 3.12. The optional symbolic tools use SymPy 1.14.0; numerical diagnostics use mpmath 1.3.0. Optional libraries do not certify floating-point intervals.

The builder makes a private pdfLaTeX format; it does not install packages or change user-global TeX configuration. On a standard TeX Live system the normal paths work. For the supplied stripped Debian TeX tree it uses the existing /usr/share/texlive/texmf-dist tree without relying on an ls-R index. Byte equality is expected with an identical toolchain, not across arbitrary font, TeX, or dependency versions.

## Exact counts and finite inverse scans

From this directory:

    python -B code/exact_counts.py --max-index 20
    python -B code/exact_counts.py --max-index 100 --model L --threshold 1000000
    python -B code/test_exact.py --cap 640
    python -B -O code/test_exact.py --cap 640
    python -B code/endpoint_check.py --max-index 6

The exact software cap is n=640. The threshold command reports the first crossing within the computed range, without assuming small-index monotonicity. Failure to find one does not imply that no larger index qualifies. Thresholds accept 1 through 4000 decimal digits. Local chunked integer conversion works even with PYTHONINTMAXSTRDIGITS=640; no global integer-string security limit is modified.

The default exact test reruns endpoint enumeration through n=5, compares the n<=80 independent exact fixture, checks all 101 downloaded U and V terms and all 18 downloaded legacy terms, and checks the U/V binomial transform through the requested cap. The separate n=6 endpoint run can take noticeably longer. The n=6 fixture was freshly generated and independently checked before packaging. Assertions are not used for public test conditions; -O leaves checks active.

## Optional symbolic and numeric checks

    python -B code/verify_coefficients.py
    python -B code/generate_coefficients.py --order 3 --out /tmp/coefficients_fresh.json
    python -B code/check_saddle.py --ns 20 50 100 200 500 1000 --dps 80 --order 3 --output-dir /tmp/saddle_fresh

The coefficient output file and numerical output directory must not already exist. The supported symbolic order is 0 through 3. Frozen coefficient JSON omits runtime measurements and is deterministic. The generator uses only finite Stirling/collision truncations. Its order cap is a tested implementation cap; the report proves every fixed order separately.

The numeric program supports n=2 through 10000, order=0 through 3 and precision=40 through 200 digits. The positive-tail bound is a mathematically justified formula evaluated in floating point, not an interval certificate. The frozen saddle diagnostics use the six indices in the command above. The report's numeric values are illustrations, not proofs of an effective onset.

## Deterministic PDF and ZIP builds

Choose a new output directory outside the source package, with no symlink ancestor:

    python -B build.py --out /tmp/report224_normal --cap 640 --symbolic-check
    python -B -O build.py --out /tmp/report224_optimized --cap 640 --symbolic-check

Add PYTHONINTMAXSTRDIGITS=640 to either command to exercise the minimum supported Python digit limit. The builder may be invoked by absolute path from another working directory. Omitting --symbolic-check removes the optional SymPy dependency and its check from build_checks.json.

Each build verifies MANIFEST.sha256, runs the tests, compiles the TeX three times, rejects overfull boxes/missing glyphs/undefined references, preserves all source bytes, and writes Report224.pdf plus Report224.zip. The ZIP contains the sources, code, data, source ledger, PDF and deterministic build receipt; sorted members have fixed timestamps and uncompressed storage. Logs and a private TeX working directory remain outside the ZIP for inspection. The ZIP has no external-source PDFs, source HTML dumps, caches, or private working records.

To compare two builds, compare complete ZIP bytes and member lists/bytes, not only a summary hash. Matching build outputs do not replace mathematical review or visual inspection of every PDF page.

To rebuild an extracted ZIP, run build.py directly in the extracted Report224 directory. The manifest checks every input source and rejects unexpected files. It excludes only the two reserved generated root members Report224.pdf and build_checks.json; the builder regenerates them and inserts each once in the new ZIP.

## Files

- src/: full editable TeX report
- code/: exact model, endpoint enumeration, regression tests and optional symbolic/numeric tools
- data/exact80.json: independent exact arithmetic fixture, all five models n=0..80
- data/endpoints6.json: independent endpoint enumeration n=0..6
- data/coefficients_order2.json and coefficients_order3.json: exact symbolic outputs
- data/saddle_diagnostics.json: non-certified 80-digit floating-point observations
- sources/: retrieved OEIS numerical b-files and source ledger
- MANIFEST.sha256: source-tree integrity manifest
- build.py: source-preserving deterministic builder

No external publication, OEIS update, or repository change is performed by these scripts.
