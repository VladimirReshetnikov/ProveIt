QUANTITATIVE IMPROVEMENTS TO THE EXACT-COUNTING CONTRACTION ALGORITHM
Research note prepared for Vladimir Reshetnikov, 26 October 2026

START HERE
----------
Read report.pdf. Its complete editable LaTeX source is report.tex.

The report proposes three proved modifications relative to the cited preprint:
1. An exact count of tapered Hermite conditions, reducing h from about 3M/u
   to M/u, and a precision allowance with leading term 6MD/u rather than 24MD/u.
2. A revised contraction schedule with explicit base-two coefficient
   648.4410666487529 in the s/sqrt(log_2(s)) exponent. The same explicit
   analysis of the source schedule gives 18535.75383166837.
3. Streamed finite-difference packet coefficient extraction with at most
   2^L grid evaluations, instead of the source's exp(O(L log s)) routine,
   retaining polynomial space and handling even factorial denominators.

SCOPE
-----
The global logarithmic orders for exact counting are NOT improved:
  arbitrary fixed-width CNF: 2^{O_k(n loglog n / sqrt(log n))};
  fixed clause density:     2^{O_{k,D}(n / sqrt(log n))}.
The numerical coefficient comparison concerns proved upper-bound analyses.
It is not a measured speedup, a running-time lower bound for the original
algorithm, or a claim that actual times have that ratio.

The source packing, deformation, integrality, and recursive identities are
dependencies. This package is not an independent proof of the full ETH claim.
The executable implements the coefficient kernel and parameter checks;
it is not an end-to-end SAT or tensor-contraction solver, and no Lean or
other proof-assistant verification is claimed.

FILES
-----
report.pdf / report.tex
  Complete mathematical report, proofs, limitations, and research questions.
INTEGRATION.txt
  Source labels and exact changes, including creation-precision handling.
source_manifest.json
  Immutable source commit, URLs, source Git blob hashes, and local SHA-256s.
code/packet_extraction.py
  Exact streaming coefficient kernel over scalar or monic extension rings.
code/test_packet_extraction.py
  Independent direct-multiplication comparisons and edge cases.
code/contraction_parameters.py
  Exact taper, valuation, schedule algebra, and displayed constants.
code/test_contraction_parameters.py
  Finite exact-arithmetic verification.
code/fetch_source.py
  Optional download of the four pinned source files, with Git blob checks.
verification/
  Recorded checks, detailed coefficient proof, and independent schedule audit.
SHA256SUMS.txt
  Checksums of package contents, excluding this checksum file itself.

REPRODUCE
---------
Python 3.10+ and its standard library suffice for all code. From this directory:

  python3 code/test_packet_extraction.py
  python3 code/test_contraction_parameters.py
  python3 code/contraction_parameters.py

The second test command writes a fresh parameter_validation.json next to
its script. The archived record is in verification/parameter_validation.json.
Floating point is used only to display constants, not for exact taper,
valuation, or coefficient arithmetic. The parameter prototype uses one
optional guard bit beyond the report's proved sufficient precision.

To rebuild the PDF with a conventional TeX Live installation:

  pdflatex -interaction=nonstopmode -halt-on-error report.tex
  pdflatex -interaction=nonstopmode -halt-on-error report.tex

To retrieve the pinned sources (requires internet access):

  python3 code/fetch_source.py --destination upstream_source

VALIDATION RESULTS
------------------
Coefficient kernel: all 8 test methods passed; 19,542 exact comparisons.
Parameters: all 5 test methods passed, including 168 taper cases,
15,492 node-valuation checks, 432 independent rational products, and
46,476 recovery-precision checks.
These finite checks supplement the proofs. They do not prove the full solver.

SOURCE
------
OpenAI, The Exponential Time Hypothesis is False, revised 25 October 2026.
Repository: https://github.com/openai/math
Commit: 7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a
Directory: preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026

The upstream preprint and source files are not redistributed in this archive.
Use the pinned links or the verified optional fetch script to obtain them.
