iPRA: COVERAGE OBSTRUCTIONS AND REPRODUCIBLE CHECKER AUDIT

Read report.pdf (or compile report.tex) for the mathematical results and
limits. This package does not claim a newly smallest axiomatization or a
new qualifying proof checker below the existing complexity envelope.

Run with CPython 3.12.14 for exact source-normalization comparisons:

  python3 reproduce.py

This uses only the Python standard library and no network. It measures
complete inherited checker sources, checks their pinned hashes and metrics,
and runs the seven-packet false-goal attack plus three positive fixtures
under ordinary and optimized Python. Fresh results are written to
evidence/reproduction.json. The UNSOUND experiment is expected to accept
the false goal; the control and local repair are expected to reject it.

Folders
  controls/     Six exact inherited incumbent sources and provenance.
  experiments/  One explicitly UNSOUND prototype and an uncertified local
                repair; neither is delivered as a qualifying checker.
  fixtures/     Attack, detailed call trace, and attributed positive inputs.
  evidence/     Static census receipts, original metrics, reproduction.
  tools/        Read-only source-census utility; it never executes the
                Python sources it inspects.
  sections/     LaTeX source of the full countermodel proof.

Optional full-source census against a local checkout:

  python3 tools/census.py /path/to/ProveIt --commit 95d3dd192e97a19bd4f8783c764331ec41126264 --output census.json

The compact coordinate records of 239 tokens / 256 AST nodes / 461 bytes are
attained by different files and retain a promised input alphabet and public
grammar. The strict native records of 319 / 358 / 599 use a different validation
contract. These are observed sizes, not proved global lower bounds.
Gzip-9 sizes are reported separately for raw and normalized source.

The numerical experiments are finite evidence. They do not replace the
written mathematical arguments or certify the repaired prototype.
Inherited material retains the upstream MIT No Attribution license.

Build the PDF with python3 build_pdf.py (requires installed TeX).
The helper uses a private format if an installed TeX cache is missing.
It does not download packages or modify system TeX configuration.
