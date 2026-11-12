COMPLETING THE SUCCESSOR-SEEDED SCALAR BASIS FOR iPRA
==================================================
Prepared for Vladimir Reshetnikov, 2026-11-10.

Read report.pdf or rebuild it from report.tex and its included .tex files.
standalone.tex is the same report with all TeX and checker inputs expanded.
The complete TeX source, proofs, checkers, fixtures, measured source controls,
audit evidence, and frozen draft ZIPs are included.

Main mathematical result
------------------------
Terms: x | 0 | J(n,a;u.h), with S(a) := J(0,a;u.0).
Computations: J(0,a;u.h)=S(a); J(Sn,a;u.h)=h[J(n,a;u.h)/u].
The update binds one changing state variable. The report constructs a finite
predecessor P with internal proofs P(0)=0 and P(Sn)=n. It then recovers ordinary
initialization by P(J(n,a;u.S(h[Pu/v]))).

With the explicitly stated native logical rules, this gives whole-domain
bi-interpretability and equiconsistency with full first-order iPRA. Both
numerical composite isomorphisms are identity relations. The finite case
proof before predecessor, full logical return translations, equality
reflection, and general PR compiler are included.

The exact numerical basis and conditional initializer compiler already occur
as an unresolved candidate in the supplied shared-continuation draft. The new
contribution is completing its missing predecessor proof by shifted affine
alignment, a capped predecessor, and a three-value correction. No invention
of the candidate grammar, absolute minimality, or global priority is claimed.

Exact complete-checker measurements (CPython 3.12.14)
--------------------------------------------------
                                  tokens   AST   normalized bytes
Prior corpus coordinate envelope    281    315          685
code/checker_direct.py               283    320          687
code/checker.py                      284    322          681
code/checker_ast.py                  282    313          707
code/checker_ast_total.py            287    314          711

Different programs attain the new AST and byte improvements. No supplied
program beats every old coordinate. The old envelope is an observed minimum
among inspected implementations, not a mathematical lower bound. The source
representation savings are separated from the arithmetic contribution.

The AST profile allows documented harmless raw iterable aliases. On malformed
nonempty strings it relies on Python's finite recursion limit to reject; an
ideal interpreter without such a limit would diverge. The byte and direct
profiles keep explicit list dispatch. Canonical certificates use lists and
integers for every profile.
The additional total-input AST profile rejects strings and nonempty objects
immediately, allows only {} as a zero/truth alias, and still improves AST
size by one node. It uses list copying and a normal assignment expression.

Reproduce
---------
  python3 reproduce.py
  python3 reproduce.py --corpus
  python3 build.py

Python diagnostics use only the standard library. Measurements are pinned to
CPython 3.12.14 because ast.unparse can differ across releases. Build the PDF
with a normal TeX Live/MiKTeX distribution providing pdflatex, amsmath,
amsthm, mathtools, geometry, lmodern, microtype, listings, booktabs,
enumitem, fancyhdr, hyperref, and the other packages listed in report.tex.
latexmk is optional. All commands run without network access.

Validation boundary
-------------------
The main suite passes 216/216 ordinary and -O complete-process runs, plus
24/24 targeted mutation controls. The focused AST suite passes 90/90 runs,
with some overlapping cases. The total-input AST suite passes 94/94 runs.
Numerical diagnostics pass 306 checks.
These tests do not formally certify the arithmetic or metatheory. The full
predecessor derivation has not been emitted as a native kernel certificate,
and there is no Lean/Rocq formalization. The report provides the written
whole-domain proofs, with independent internal assistant review.

Provenance
----------
Repository: https://github.com/VladimirReshetnikov/ProveIt
Commit: 2fdcf5bf988bead821c416649f713f98b7ed8776
Directory: docs/drafts (nine direct ZIP archives, including their history).
See sources/, reference/PROVEIT_LICENSE.txt, evidence/, and bibliography.
The source corpus audit finds 415 Python occurrences and 164 unique hashes.
The textual audit is an aid to review, not a proof of global novelty.

Files
-----
report.tex, report.pdf       Main mathematical treatment.
standalone.tex              Fully expanded single-file TeX source.
theory/                     New bootstrap, native bridge, implementation proof.
reference/                  Attributed inherited arithmetic proofs and controls.
code/                       Complete kernels, measures, numerical diagnostics.
tests/                      Named producer, certificate fixtures, run receipts.
evidence/                   Corpus, novelty, semantic reviews, validation records.
sources/                    Exact nine archived proposals at the pinned commit.
CLAIMS.json                 Machine-readable statement of claims and limitations.
MANIFEST.sha256              Integrity hashes for the delivered package files.
