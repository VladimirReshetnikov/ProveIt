# Report 237: All Fixed Order Asymptotics for Total Kostka Sums

This self-contained package contains the article, TeX sources, and finite
reproducible calculations. `Report237.pdf` is the readable article;
`SOURCES.md` records the source boundary and attributions.

## Results

For the total Kostka sum A104779, the article proves every fixed support
truncation with the natural remainder, and hence expansions to every fixed
half-integer order. It gives explicit coefficients, certified constant
intervals, a controlled Lambert-W/Newton inverse with a two-ceiling threshold
enclosure, corresponding factorial-scale results for A321652 and A068313, and
a sharp total-variation limit for the complete nonunit margin profile.
An exact Gaussian half-axis split also retains an alternating recessive sector,
with a separate fixed-order expansion for each sector. This does not provide
an exponentially accurate error bound for a fixed truncation of their sum.

The imported exact enumeration identities are credited to Schwob. The article
separates those identities from its asymptotic arguments. Finite computations
do not establish global novelty, a numerical asymptotic onset, or unconditional
rounding at a specified finite input. A068313 has official offset 1; its value
at zero in the programs is an explicitly labelled empty-object extension.

## Requirements and quick checks

Python 3.12, SymPy 1.14.0 and mpmath 1.3.0 were used for the reference build.
The two package versions are pinned in `requirements.txt`. PDF reproduction
also requires pdfTeX/LaTeX with the standard packages used by `article.tex`.
Byte-identical PDF reproduction is toolchain-dependent and is checked rather
than assumed.

From this directory:

    python -B code/exact_counts.py
    python -B code/certify_constants.py
    python -B code/symbolic_coefficients.py
    python -B code/guard_tests.py
    python -B build.py --verify-only

These regenerate the contents of the four receipts stored under `code/`. Programs write
results to stdout; they do not replace the frozen receipts. The first two
checkers and guard checker also accept `--output` for a new file outside the
source package. Repeat the checks with `python -B -O` to test optimization-safe
validation. No correctness condition depends on Python assertions.

## Rebuild and actual-ZIP reproduction

Choose new output directory names whose parents exist. Existing directories,
source-tree destinations, and symlink paths are rejected.

    python -B build.py --report-number 237 --output-dir /tmp/report237-build
    python -B code/reproduce_zip.py --archive /tmp/report237-build/Report237.zip --output-dir /tmp/report237-replay

The build checks the complete source manifest, regenerates all exact/guard
receipts, compiles in a disposable directory, requires the frozen PDF to match
byte for byte, and emits a deterministic `Report237.zip`. It never rewrites
sources or reference receipts. This is a frozen Report237 package: the optional
report number accepts integers from 1 through 9999 but must equal 237. It is
not a renumbering or report-allocation tool.

Replay validates the actual archive against this trusted source package before
executing extracted code. Separate normal and optimized builds must reproduce
all archive member bytes and metadata, the complete ZIP, PDF, exact receipts,
and build checks. Both source trees and the input archive must remain unchanged.
The manifest is an integrity record, not a digital signature.

## Exact certificates versus diagnostics

- `code/count_receipt.json`: exact three-sequence prefixes through n=20, plus
  independent symmetric-margin enumeration and two fixed-margin identities
- `code/constant_receipt.json`: five exact-rational, outward-rounded intervals
  of width 10^-40, with independent finite-product formula checks
- `code/symbolic_receipt.json`: exact saddle, logarithmic, multiplicative,
  fixed-shift, inverse, and companion coefficient identities
- `code/guard_receipt.json`: bounded-input and filesystem/manifest/ZIP guards

`python -B code/diagnostics.py` and
`python -B code/sector_diagnostics.py` are separate floating-point arithmetic. Their
numbers are not interval certificates or exact verification receipts. See
`COMPUTATION.md` for algorithms, finite supported domains, and limitations.

The public package contains no third-party full-text PDFs and needs no network
connection for its computations or build once dependencies are installed.
