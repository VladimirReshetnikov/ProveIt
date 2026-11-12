iPRA WITHOUT AN INTRODUCTION WITNESS PARAMETER
12 November 2026

MAIN RESULT
The introduction rule can always use the newest ambient numerical parameter,
or zero in an empty scope. No witness term is supplied by a certificate.
The report proves exact equivalence on all native Eq/Q/D sequents for both
the eight-rule native kernel and its seven-rule diagonal variant. The pinned
whole-domain bi-interpretation with full first-order iPRA transfers unchanged.

The new mathematical equivalence is a written proof, not a new Lean result.
This package is a matched checker simplification, not a global size record
or a claim of absolute mathematical minimality.

START HERE
  ipra_no_witness.pdf       Compiled research report with complete rule inventory
  ipra_no_witness.tex       Complete standalone LaTeX source for the report
  CLAIMS.json              Exact scope of the claims and verification status
  PROVENANCE.json          Pinned repository and reference-file provenance
  code/checker_seven.py     Main complete standalone seven-rule checker
  code/checker_eight.py     Simpler eight-rule variant
  code/control_seven.py     Matched unrestricted-witness control
  code/control_eight.py     Matched unrestricted-witness control
  code/FORMAT.txt           Complete JSON syntax and instruction format
  code/verify.py            Measurements, fixtures, and independent translations
  code/verified/           Positive/negative certificates and receipts
  evidence/validation.json Verification summary
  proof_notes/             Detailed compiler and predecessor notes
  reference/               Selected unchanged pinned upstream source files

RUN
  python3 code/verify.py
  python3 code/checker_seven.py < code/verified/seven_naming_two.json

A successful checker exits with status zero and prints exactly ACCEPT.
Exceptions reject. The checker itself imports only json; fixture generators,
translators, controls, and reference files are not trusted dependencies.

MEASURED UNDER CPYTHON 3.12.14 (tokens / AST nodes / normalized bytes)
  control_eight.py       979 / 1086 / 2834
  checker_eight.py       971 / 1078 / 2817
  control_seven.py       932 / 1029 / 2770
  checker_seven.py       924 / 1021 / 2753
The whole normalized source module is measured. No module docstrings or
hidden helper dependencies have been omitted from the delivered checker.

VALIDATION
18 positive fixtures and 33 rejection fixtures, each in normal and optimized
Python: 102 command-line checks. Each positive fixture also passes a matched
control and an exact pinned repository checker after separate translation.
The H(2) certificate validates the case/naming scaffold. It is not a complete
machine verification of the predecessor proof or the equivalence theorem.

BUILD THE PAPER
With a normal TeX Live installation:
  latexmk -pdf -interaction=nonstopmode -halt-on-error ipra_no_witness.tex
or run pdflatex twice. The source has no external input-file dependency.

DEPENDENCY
VladimirReshetnikov/ProveIt, commit
9f9545f5ffd9e0392d4a36639503aca12383450a
Logic/PrimitiveRecursiveArithmetic/ConciseIPRA
The proof transfers the existing native/iPRA bi-interpretation; it does not
claim to recompile the upstream Lean project.

LIMITS
The repository's compact 516-byte checker is smaller and uses another
contract. The three-family clause calculi have fewer primitive families.
This new theorem removes the introduction witness argument without changing
the raw native language or its derivable sequents. Combining it with the
three-family systems needs a separate noncircular equality bootstrap.
