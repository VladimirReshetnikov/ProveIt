iPRA: ZERO AS AN EXPLICIT DEFINITIONAL ALIAS
Prepared for Vladimir Reshetnikov, 12 November 2026
=================================================

RESULT
------
One complete typed Eq/D checker has 331 significant tokens, 373 AST nodes,
and 625 normalized UTF-8 bytes on CPython 3.12.14. The pinned repository's
prior typed Eq/D envelope is 334 / 386 / 628, attained by three different
programs. The new single program is below all three coordinates.

This is a conservative definitional presentation of the inherited native
theory, with the public zero encoded by raw atom 1 and the explicit auxiliary
equation c=0 included in the initial context. All logical and arithmetic rules
are retained. Both numerical domains are whole, equality is actual equality,
and the bi-interpretation with full first-order iPRA has identity numerical
composites and both formula round trips.

THE UNRESTRICTED MINIMIZATION REQUEST REMAINS OPEN. This package does not beat
the 478-byte compact checker, whose public grammar is promised rather than
validated. No arithmetic axiom deletion, absolute simplest axiomatization,
or universal source-size lower bound is claimed.

READ
----
ipra_zero_alias.pdf       Main report, with the complete rule inventory,
                         alias equivalence, interpretation round trips,
                         checker, exact scope and further research questions.
ipra_zero_alias.tex       Main LaTeX source.
foundations.pdf          Inherited foundational chapter: logic, predecessor,
                         equality reflection, pairing, primitive recursion,
                         and the complete iPRA bi-interpretation.
foundations.tex          Wrapper for the attributed foundational chapter.

IMPLEMENTATION
--------------
implementation/alias_inverted.py    Main complete 331 / 373 / 625 checker.
implementation/checker_readable.py  Readable standalone implementation.
implementation/compile_alias.py     Untrusted mathematical proof compiler.
implementation/verify_alias.py      Metrics, AST audit, provenance and tests.
implementation/fixtures/generated/  Seven genuine positive certificates.
implementation/verification.json    Full verification receipt.
implementation/PROVENANCE.json      Pinned code and fixture provenance.
implementation/README_CODE.txt      Detailed checker and certificate contract.

The reference article sources are included in reference/upstream_article/.
They reproduce the pinned upstream article, with all chapters and preamble.
The separately compiled foundations chapter changes only one cross-reference
to a chapter outside that excerpt. Its wrapper adjusts layout.
evidence/ contains two independent written audits and exact article hashes.
CLAIMS.json records the claims and explicit limits.
MANIFEST.sha256 records every delivered file other than the manifest itself.

RUN
---
From the extracted directory:

  python3 implementation/alias_inverted.py < implementation/fixtures/generated/public_zero_reflexivity.json
  python3 implementation/checker_readable.py < implementation/fixtures/generated/nested_D_transport.json
  python3 reproduce.py
  python3 reproduce.py --pdf

The two examples print ACCEPT. Reproduction verifies the delivered hashes
before regenerating certificates and running tests. With --pdf it also builds
both PDFs. A local pdfLaTeX installation is needed to build the PDFs; the
builder can generate a missing pdflatex format from an installed LaTeX tree.
All reproduction is offline. Exact source-size measurements require CPython
3.12.14. Rebuilding PDFs changes their metadata and therefore their manifest
hashes; preserve the original delivery if you want to verify it again.

VALIDATION AND COMPLETENESS
--------------------------
The checker validates the whole input's exact integer/list alphabet and the
public goal's sorted padded arities and closed scope. Acceptance is normal
exit with exactly ACCEPT followed by one newline. Unused certificate prefixes
are allowed, but still type-checked.

Soundness is asserted for all accepted raw goals. Completeness is asserted
for the distinguished canonical encoding of every abstract native theorem.
The inherited validator also admits redundant references to administrative
padding slots; completeness for every such redundant spelling is not claimed.
No canonical-input promise is needed to make an accepted goal sound.

Do not replace every serialized 0 with 1. The compiler proves formula
transport from the retained equation c=0, including through nested binders;
zeroes in computation and instruction fields keep their inherited roles.

VERIFICATION
------------
51 candidate cases x 2 implementations x 2 Python modes = 204 runs.
121 inherited cases x 2 Python modes = 242 runs.
2 additional no-alias negative controls correctly reject.
All expected outcomes passed. Exact AST transformation audit passed.
All 146 included code/fixture reference Git blobs matched the pinned commit.
The additional 17 article/license/reference files and all thirteen incoming
ZIP archives were also checked by their Git blob identities. The corrected
334 / 386 / 628 frontier includes the incoming equation-alias and atomic-seed
checkers, whose exact sources and measurements are included in
reference/incoming_audit/ and evidence/incoming_audit.json. Finite tests are evidence, not universal soundness proofs.
No new Lean/Rocq proof or upstream Lean rebuild is asserted.

PROVENANCE AND LICENSE
----------------------
VladimirReshetnikov/ProveIt
Commit f2e1d0f2d29042fa2d76244639c13425c46d16b4
Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

The complete source programs, certificate protocol, existing mathematical
bridge and foundational appendix are attributed in the report and provenance
files. The new code and report may be used under the same MIT No Attribution
license as the included upstream material; see LICENSE.txt.

