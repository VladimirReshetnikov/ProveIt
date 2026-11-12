iPRA: SMALLER CHECKERS AND LIMITS OF ALGEBRAIC SIMPLIFICATION
Prepared for Vladimir Reshetnikov, November 10, 2026
===========================================================

OUTCOME
-------
This package contains two verified smaller checker implementations, complete
axiomatizations and bi-interpretation proofs, and an extension of earlier obstruction arguments.
It does NOT establish a single checker below all three current coordinate
minima, an absolutely simplest axiomatization, or the requested significant
positive breakthrough. That remaining limitation is stated in the report.

Current corpus minima: 277 normalized tokens / 311 AST nodes / 672 normalized
bytes, achieved by different complete programs.

                          Tokens   AST   Normalized bytes   Raw bytes   Gzip-9
code/checker_loop.py          276   305                749         746      398
code/checker_bytes.py         280   319                652         652      394

Gzip is an FYI metric, not the optimization target. Exact compressed files
are included as code/checker_loop.py.gz and code/checker_bytes.py.gz.
Normalized gzip sizes are 399 and 394 bytes. Source normalization follows
the unchanged inherited full-module protocol on CPython 3.12.14.

MATHEMATICAL EXTENSION
---------------
The countable structure of eventually constant natural-number sequences,
with all PR operations pointwise, satisfies PR defining equations,
constructor separation, every literal-equation induction instance, and
every universal Horn arithmetic law true in standard N. Each finite
parameter expansion nevertheless has a nontrivial order-two automorphism.
This applies the already-established automorphism obstruction to a new
countable power construction and prevents ordinary definable bi-interpretability with any iPRA model,
even with different domains, finite-dimensional coding, quotients, and
finitely many parameters. The proof also extends to arbitrary finitary
expansions of standard (N,0,S) and induction for finite conjunctions of atoms.
The earlier unary-amalgam argument and product-coverage example are
credited explicitly, with exact nested sources in reference/audit/prior_math.
The extension identifies a precise obstruction to purely algebraic simplification;
it does not prove a lower bound on all proof-checker sizes.

An alternative H binder reads as exists x forall y (B(x,y) -> B(x,Sy)).
Its introduction is unrestricted progress; induction is confined to
equation-only iteration in elimination. Boolean Cases remains explicit.
A parity/half construction realizes universal quantification using one
progress step. This presentation is fully specified and bi-interpretable
with iPRA, but is not assigned the small D-checkers' measurements.

START HERE
----------
report.pdf                     Full mathematical report and all proof appendices.
report.tex                     Standalone LaTeX source, all local inputs expanded.
report_main.tex                 Modular authoring source.
code/checker_loop.py            Entire iterative trusted checker.
code/checker_bytes.py           Entire 652-byte trusted checker.
code/readable_checker.py        Standalone explanatory implementation.
code/INHERITED_FORMAT.txt       Exact original flat packet format and decoder.
theory/                        Report sections, new results, attributed obstructions.
reference/                     Attributed inherited complete arithmetic bridge.
reference/audit/                Pinned census and six exact comparison programs.
tests/                         Inherited proofs and new targeted regressions.
evidence/                      Measurements, provenance, and verification receipts.
reproduce.py                   Read-only offline verification of the package.
build.py                       Rebuild the standalone source and PDF.
MANIFEST.json                  SHA-256 and size of every distributed payload.

REPRODUCE
---------
With Python 3.12 and the standard library:

    python3 reproduce.py

To submit one canonical proof:

    python3 code/checker_loop.py < tests/fixtures/contextual_induction_seed_congruence.json

If your Python minor version differs, ast.unparse or AST metrics may differ.
Proof checking itself does not depend on the measurement utility.

The reproduction driver verifies manifests and measurements, then checks
31 inherited examples with all three implementations under ordinary and
optimized Python. It also runs a context-isolation control and a 1600-step
continuation stress case. At a recursion limit of 1000, the iterative
checkers accept the deep valid proof and the recursive checkers reject it
with RecursionError. A deliberately flawed mutable-context control is
created only inside a temporary directory to expose an actual soundness bug.

To rebuild the PDF with a standard TeX Live/MiKTeX installation:

    python3 build.py

The source requires the packages named in report_main.tex. Compilation uses
no network, shell escape, or external bibliography processor. Rebuilding
the PDF can change metadata and its manifest hash; verify the distributed
manifest before rebuilding or work on a copy.

SOURCE AND LIMITS
-----------------
Repository snapshot: 0300a290bedee5019c974291850b798378438b2e
https://github.com/VladimirReshetnikov/ProveIt/tree/0300a290bedee5019c974291850b798378438b2e/docs/drafts

The audit covers 16 current ZIPs, 22 distinct archive contents, 297 distinct
Python sources, 516 distinct-archive source occurrences, and 2249 nested
occurrences including repeated inclusions. Exact source identities are
recorded, but the large original ZIPs are not duplicated in this package.
The original repository was read without modification.

The mathematical results have written proofs and independent assistant
review. They are not Lean/Rocq formalizations or external human peer review.
Finite executable tests do not prove the universal metatheorems. The Python
runtime and standard JSON parser are shared trusted infrastructure.
The loop's inherited iterable opener has documented noncanonical aliases;
canonical array/integer proofs are the completeness interface. The byte
profile retains an explicit list test. All inference checks remain active
under Python -O.
