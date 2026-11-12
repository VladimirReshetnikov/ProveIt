A DETERMINED WITNESS FOR iPRA
============================
Prepared for Vladimir Reshetnikov, 12 November 2026.

Start with report.pdf. Its main source is report.tex; the other top-level
TeX files and reference/scalar_predecessor.tex are included automatically.

RESULT
------
In the raw native scalar calculus, DI by cases need not receive a witness.
Always choose the newest numerical parameter, or zero in an empty scope.
Keep the separate QI progress rule for literal equations. This has exactly
the same consequences on all open native sequents as the pinned NPrf kernel.
The ordinary iPRA bi-interpretation and both identity numerical composites
therefore transfer unchanged. There is no naming-pattern exception.

The reduction also applies to the strict guarded clause presentation.
Its complete checker is smaller in all three matched source coordinates:

                              tokens   AST nodes   normalized bytes
Unrestricted control           1078       1252           3442
Previous naming dispatch       1159       1339           3688
Newest parameter               1070       1243           3425

This answers the pinned README's Further question 2 in written mathematics:
zero-or-variable witnesses suffice; deterministic newest-or-zero suffices.
It does not establish an absolute minimum among all codecs or all theories.

BASELINE
--------
Repository: https://github.com/VladimirReshetnikov/ProveIt
Directory: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA
Pinned commit: 8fa5ade009b5cceba7b68f07b6a834fe77cf10c1
The exact source paths and hashes are recorded in PROVENANCE.json.

ARTIFACTS
---------
report.pdf / report.tex             Main article and compiled PDF
logical_proof.tex                   Exact native equivalence proof
guarded_reduction.tex               Guarded companion and matched comparison
arithmetic_audit.tex                Removes the predecessor proof's apparent
                                   dependence on Boolean/disjunctive case splits
code/checker_native.py              Independent raw eight-rule checker
code/checker_guarded.py             Measured guarded six-family checker
code/FORMAT.txt                    Exact JSON syntax and all primitive rules
code/verify_*.py                    Proof-certificate and arithmetic checks
code/measure.py                    Reproducible complete-source metrics
examples/                          Actual accepted JSON proof certificates
evidence/                          Machine-readable results
reference/                         Attributed predecessor proof, arithmetic
                                   bridge, logical macros, and exact controls
CLAIMS.json                        Explicit claim and verification boundary
MANIFEST.sha256                    File integrity ledger

REPRODUCTION
------------
Python checks use only the standard library (Python 3.10+; measured on 3.12.14):

  python3 reproduce.py

The scripts locate files relative to their own paths, so the working
directory does not matter. To check an individual certificate:

  python3 code/checker_native.py < examples/native/symbolic_successor_packet.json
  python3 code/checker_guarded.py < examples/guarded/naming_family_two_nonzero_witness.json

Consult the actual examples/guarded directory for its complete file list.
The proof packet formats of the two checkers are intentionally distinct.

Compile the report using a normal pdfLaTeX installation:

  python3 build_pdf.py

VERIFICATION BOUNDARY
---------------------
The central equivalence is a written mathematical proof, with an explicit
scope-sensitive compilation argument. It is not a newly compiled Lean or
Rocq theorem. The existing pinned Lean iPRA bridge was inspected, not rebuilt.

Native checking includes an actual finite raw proof of the generic naming
family X(S t) with t an open parameter, and a separate checked branch giving
S b = S t. The entire predecessor theorem and the universal completeness
translation are proved in the article, not certified by those finite tests.

Arithmetic validation includes literal scalar evaluation at small inputs
and replay of selected symbolic equation-case certificates. Those checks
are not represented as a full proof-assistant verification.

The existing source controls and inherited written arithmetic are credited
to ProveIt contributors; their MIT No Attribution license is retained under
reference/LICENSE-ProveIt.txt. The new result is identified separately from
the inherited predecessor, logical macros, and iPRA bridge.
