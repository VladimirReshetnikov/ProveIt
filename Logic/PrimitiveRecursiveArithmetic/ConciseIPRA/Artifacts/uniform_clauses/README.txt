IPRA WITH UNIFORM CLAUSE USE
===========================
Prepared for Vladimir Reshetnikov, 11 November 2026.

START HERE
----------
ipra_uniform_clauses.pdf is the research report.
ipra_uniform_clauses.tex is its standalone editable LaTeX source.

RESULT
------
Four proof instruction families (clause use, two-case computational equality,
paired elimination, paired introduction) and ONE EXPLICIT FIXED REFLEXIVITY
AXIOM CLAUSE. Ordinary local assumptions use unconditional clauses; conditional
closures use singleton-premise clauses. The public language remains Eq/D over
raw scalar iterator terms, with ordinary capture-avoiding substitution.

The report proves exact consequence equivalence with the existing raw-clausal
presentation. Composing with the existing native/iPRA bridge preserves the
whole numerical domain, actual equality, and identity graphs x=y for both
numerical composites. Reflexivity has not been eliminated as a logical
principle, and the number four counts instruction families, not an invariant
number of primitive logical ideas.

MEASURED IMPROVEMENT AND LIMIT
-----------------------------
Complete normalized checkers, CPython 3.12.14:

                                      Bytes  Tokens  AST  Gzip9
Published raw-clausal checker          3046     853   993   990
Selected uniform-clause checker        2912     807   931   994

The reduction is 134 bytes (4.40%), 46 tokens (5.39%), 62 AST nodes (6.24%).
Gzip grows by four bytes. The matched same-validator controls isolate the
clause change (80 bytes), the redundant Eval-case deletion (47 bytes), and
validator factoring (7 bytes). The last change does not change the calculus.

This is a modest presentation improvement. It is NOT a proof of global
minimality and does NOT beat the repository's compact 516-byte codec or its
other compact minima. The report distinguishes their validation contracts.
The arithmetic bridge and the deletion of Eval's identity case are inherited;
the new contribution is the uniform clause interface and concrete measured
composition. No new Lean/Rocq verification is claimed.

REPRODUCE
---------
No third-party Python packages are required.

    python3 verify_manifest.py
    python3 reproduce.py
    python3 code/checker.py < examples/reflexivity.json

The delivered validation passed 37 positive theorem certificates, 37 exact-goal
translation round trips, 34 adversarial certificates, seven malformed input
documents, 56 inherited regression cases, and 484 full subprocess checks.
Normal and optimized Python and the readable and normalized kernels are
covered. Tests are finite implementation evidence; the mathematical claims
rest on the report's proofs and the attributed arithmetic bridge.

To rebuild the PDF with a TeX installation:

    python3 build.py

The build script compiles a copy of the single TeX source in a temporary
directory, with shell escape disabled. A rebuild may change PDF metadata and
therefore its SHA-256. The manifest describes the original delivered files.

FILES
-----
code/checker.py              Readable standalone trusted checker.
code/checker_normalized.py   Same complete checker after normalization.
validation/                 Standalone comparison kernels, checked proof
                            translators, adversarial fixtures, and verify.py.
examples/                   Small valid certificates.
evidence/                   Measured results, reproduction receipt, review.
reference/                  Attributed pinned proofs and selected Lean sources.
PROVENANCE.json              Repository commit and source paths/hashes.
CLAIMS.json                  Machine-readable proved claims and limits.
MANIFEST.json                SHA-256 hashes of delivered payload files.

The proof transformers are untrusted producers. They validate their input and
output but are NOT imported by the standalone trusted checker. Reference
proofs are likewise not runtime dependencies.

UPSTREAM
--------
https://github.com/VladimirReshetnikov/ProveIt
Commit: 5d85023b0688e03b75f0ec3a04bb43ef0bb51705
Scope: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA
Upstream files and modifications are distributed under the included MIT No
Attribution license. No change to the remote repository was made.
