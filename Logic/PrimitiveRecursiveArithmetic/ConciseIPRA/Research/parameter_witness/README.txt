iPRA with parameter witnesses
============================

Research package, 12 November 2026.

Baseline: VladimirReshetnikov/ProveIt, commit
9f9545f5ffd9e0392d4a36639503aca12383450a,
Logic/PrimitiveRecursiveArithmetic/ConciseIPRA.

This package develops a restriction of the existential witness of the
native introduction rule to zero or an in-scope numerical variable.
The final report and executable checks accompany this file.

MAIN RESULT

The final five-family raw clause calculus uses one bit in its introduction
rule: zero or the newest existing numerical parameter. The empty-scope
fallback is zero in case mode. Arbitrary witness terms are eliminated.
The report proves equality of all contextual derivability relations with
the pinned native calculus, preserving its full intuitionistic
bi-interpretation with iPRA and its identity domain composites.

The scalar predecessor construction is inherited. Its new purely
equational dependency organization removes the circularity in using
predecessor to name arbitrary terms before full logical completeness.

FILES

ipra_parameter_witness.pdf and .tex: report, complete new proof appendices.
paper/: editable LaTeX appendix sources.
checker/checker.py: complete standalone checker.
checker/reference/raw_two_case.py: exact matched pinned control.
checker/FORMAT.txt: full certificate format and Boolean mode decoder.
checker/fixtures/: actual positive and negative certificates.
checker/METRICS.json, checker/VALIDATION.json: measured executable evidence.
code/check_scalar_arithmetic.py: direct finite iteration model checks.
reference/: attributed baseline sources, license, and inspected Lean endpoints.
PROVENANCE.json: pinned source paths and verified hashes.
MANIFEST.json: SHA-256 and size for each other included file.
CLAIMS.json: exact achievements and limitations.
evidence/: combined reproduction receipts.

REPRODUCTION

  python3 reproduce.py
  python3 checker/checker.py < checker/fixtures/generated/packet_numeral_2.json
  python3 build.py

The checker and validation use Python's standard library only. Report
rebuilding requires pdfLaTeX and the LaTeX packages listed in its preamble.
Use CPython 3.12.14 for exact normalized-source size comparisons.

MATCHED METRICS

                         Tokens  AST nodes  Normalized UTF-8 bytes
Pinned two-case control     837        977                   2956
One-bit introduction        833        971                   2947

Only the module docstring is removed; ast.unparse normalizes the complete
module and one LF is appended. The new reduction is 4 tokens, 6 AST nodes,
and 9 bytes. Existing two-case Eval is not counted as a new contribution.

LIMITS

This is not a global checker-size record or an absolute-minimality proof.
The repository contains much shorter compact codecs with different
representations and contracts. This is a strict matched improvement in
a straightforward complete checker and a substantive restriction of the
primitive witness interface.

There is no implemented universal proof compiler. The written theorem
constructs the translation; the example converter handles only a selected
corpus. Certificates can grow. Practical recursion and memory limits apply.
Finite tests do not prove universal soundness or bi-interpretability.

This is a written mathematical proof with executable certificate checks.
The new restriction has not been checked in Lean or another proof assistant.
