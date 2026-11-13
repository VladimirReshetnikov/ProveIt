BOUNDED CONVERSION FOR INTUITIONISTIC PRIMITIVE RECURSIVE ARITHMETIC
==================================================================
Prepared for Vladimir Reshetnikov, 12 November 2026.

RESULT AND LIMIT
---------------
This package proves a new sufficient computation discipline for a complete
presentation of iPRA. The calculus BH_3 keeps raw terms and has seven primitive
rule families. Its only computation rule changes the left endpoint of an
equation by one reversible iterator contraction, at the root or after at
most three consecutive iterator-counter edges.

A finite naming packet recovers general equality transport from substitution
for a literal variable. Both iterator equations and the omitted introduction
case are derived. The result is exact equivalence with the native kernel on
EVERY raw open sequent. Composing with the repository's established bridge
gives equiconsistency and bi-interpretability with full first-order iPRA,
whole numerical domains, actual equality, and identity numerical comparison
maps.

THE REQUESTED GLOBAL CHECKER-SIZE TARGET IS NOT MET.
The new checker measures 1056 significant tokens / 1127 AST nodes / 3089
normalized code bytes. The matched weak-head control measures
1062 / 1123 / 3119. Thus 6 tokens and 30 bytes are saved, while 4 AST nodes
are added. These programs remain larger than the existing compact/native
frontiers. Neither depth three nor seven primitive families is proved minimal.

The new theorem is a written proof, supplemented by symbolic certificates
and a separate proof/code audit. It is not a Lean/Rocq formalization or an
external human peer review. The inherited Lean bridge sources were inspected,
not rebuilt here.

OPEN FIRST
----------
ipra_bounded_head.pdf  Complete article, proofs, limitations, and checker listing.
ipra_bounded_head.tex  Standalone source for that article.
FORMAT.txt            Exact certificate syntax and all rule/scoping checks.
CLAIMS.json           Machine-readable claim and verification boundaries.

CONTENTS
--------
paper/       Modular article source.
code/        Standalone checker, untrusted certificate producer, reproducibility.
tests/       23 positive/negative certificates plus translated control examples.
controls/    Exact incoming weak-head source and matched explicit-leaf control.
reference/   Pinned Lean declarations and small incumbent checker sources.
evidence/    Measurements, execution results, provenance, and written audits.
MANIFEST.json SHA-256 hashes and lengths of the delivered files.

REPRODUCE
---------
From this directory, with Python 3.10+ (measurements use CPython 3.12.14):

    python3 reproduce.py

This verifies the manifest before regenerating the finite fixtures and
measurements. The entire checker is measured, including parsing, validation,
scope checks, inference rules, and the acceptance driver. Explanatory module
docstrings are excluded in the repository's code-only convention; their
included sizes are also disclosed in evidence/verification.json.

Check one symbolic proof:

    python3 code/bounded_checker.py < tests/transport_symbolic.json

Rebuild the standalone TeX and PDF with a normal PDFLaTeX installation:

    python3 build_report.py

The checker has no external Python dependency. PDF generation needs the
standard TeX packages listed in paper/front.tex. The included Lean files are
reference excerpts retaining upstream imports, not a standalone Lean project.

VERIFICATION
------------
23 generated fixtures.
68 isolated CLI checks, including ordinary and optimized Python, all passing.
11 positive fixtures translated to the weak-head control and checked in both
modes (22 of the 68 checks).
18 separate depth/scope/capture boundary checks, all passing.
The main 8,833-byte symbolic transport certificate uses HC depths 0/1/2/3
60/8/6/2 times respectively.
These finite checks do not prove the universal theorem; its written proof
appears in the article.

COMPUTATIONAL CONSEQUENCE
-------------------------
BH_3 proof checking is primitive recursive on finite syntax. In contrast,
even a uniform zero-versus-nonzero test for all closed raw iterator terms is
not primitive recursive, by diagonalization. Consequently weak-head
normalization is not primitive recursive either. The repository already
proved the corresponding full-normalization obstruction and discussed fuel;
the article attributes that prior result explicitly.

BASELINE
--------
Repository: https://github.com/VladimirReshetnikov/ProveIt
Directory: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA
Pinned commit: eb0e0e00147e9f8d29737ff58587852008ecf4c3

All eleven integrated article chapters and all seven incoming archives were
included in the source audit. Archive Git blob identities were verified.
The coordinatewise compact envelope 244 / 265 / 477 combines DIFFERENT
programs and input protocols. The native public-goal envelope is
321 / 369 / 596; the whole-certificate-alphabet envelope is 330 / 380 / 621.
They are achieved upper bounds on an unknown optimum, not mathematical
lower bounds. The report never presents an envelope as one program's size.

No repository write or publication was performed.

LICENSE
-------
The inherited code and documents are under the upstream MIT No Attribution
license, retained in reference/LICENSE-ProveIt.txt and controls/.
New package code and prose are offered under the same license.
Intellectual attribution and provenance are retained throughout.

