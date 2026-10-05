# Report 106

The second logarithmic term for regular Tesler matrices (OEIS A008608).
Prepared for Vladimir, 2 October 2026.

## Main conclusion and limits

With C = pi sqrt(8/27), the report proves

log a_n = C n^(3/2) - (3/4) n log n + O(n log log n).

It also gives the sharper two-sided bounds and the next integer-threshold
inverse correction. The leading logarithmic equivalent was proved by
Balashov, Bulavenko and Molybog (2026) and is explicitly credited. No O(n)
remainder, multiplicative equivalent, amplitude, full expansion, or exhaustive
novelty certification is claimed.

## Contents

- report106.tex: complete editable proof, with bibliography
- report106.pdf: compiled reader-facing report
- build.sh: deterministic three-pass LaTeX build
- checks/: exact finite verification and adversarial tests
- sanity/: floating-point profile consistency checks, separately labeled
- sources.json: primary source locations, versions, inspected theorem locations
  and fingerprints of the external reference PDFs consulted (not redistributed)
- environment.txt: versions used for the recorded build and sanity computation
- verification_summary.json: concise verification record
- manifest.json and verify_package.py: SHA-256 integrity check of packaged files

## Verify and reproduce

Unpack into a fresh directory. First check the delivered bytes:

    python3 verify_package.py

Then run the exact checks, including 31 deliberate corruptions in both normal
and optimized Python:

    python3 checks/run_corruptions.py

The exact suite uses only the Python standard library (Python 3.9 or newer).
All guards remain active with `python -O`. See checks/README.md for the precise
finite scope. The generated JSON/text logs include the execution host's clock;
those timestamps will naturally change on rerun. The deterministic baseline
verification results themselves can be compared byte for byte.

Build the PDF with an installed TeX Live distribution:

    bash build.sh

Required LaTeX packages: fontenc, inputenc, lmodern, microtype, geometry, amsmath,
amssymb, amsthm, mathtools, booktabs, enumitem, fancyhdr, hyperref and their
standard dependencies. The script uses a local format and explicit font maps
in the recorded environment, fixes SOURCE_DATE_EPOCH and suppresses PDF dates
and trailer identifiers. It fails if the final log contains an overfull box or
unresolved reference. Byte-identical reproduction was checked in the recorded
TeX environment; different TeX/font releases may change bytes or pagination.

Optional floating sanity (NumPy required):

    python3 sanity/profile_sanity.py --output sanity/profile_results.json

That run evaluates the exponential profile at n=2048 and n=4096. It is not
interval arithmetic and does not prove any analytic inequality. Last-bit
floating results can vary across platforms. No external author's code is run.

The build creates build/, qa/ and ordinary LaTeX intermediates. The distribution
manifest intentionally lists only shipped files. Check the manifest before
rerunning tools that refresh shipped logs/results.

## Evidence boundaries

The analytic proof establishes the asymptotic theorem, conditional only on the
stated, cited existing counting theorem and classical eta transformation.
Finite exact computation checks algebra, indexing and small counts; numerical
sanity checks have still weaker evidentiary scope. Neither proves a limit or
substitutes for a uniform analytic estimate.
