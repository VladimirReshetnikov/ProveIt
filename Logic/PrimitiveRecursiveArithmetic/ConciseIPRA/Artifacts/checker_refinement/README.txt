A CERTIFIED CHECKER REFINEMENT FOR iPRA
November 12, 2026

RESULT AND LIMIT
The compact standalone checker is 488 normalized UTF-8 bytes, versus the
exact current 495-byte control. The native companion validates the entire
input alphabet and initial native Eq/D public goal in 646 bytes, versus
its matched 666-byte control.

This improves byte size only. It does not remove a mathematical axiom,
change the native scalar theory, improve the token/AST minima, or prove an
absolute smallest axiomatization. The user's stronger aim of a new, simpler
mathematical basis remains unresolved by this report. The full native
theory, both ordinary interpretations, and both identity-graph numerical
composites are stated and supported by the included inherited foundations.

Complete-module vectors (significant tokens / AST nodes / normalized bytes):
  controls/checker_bytes495.py    267 / 299 / 495
  code/checker_bytes.py           271 / 304 / 488
  controls/checker_native666.py   342 / 391 / 666
  code/checker_native.py          343 / 392 / 646

The current overall compact coordinate envelope is (249,271,495), attained
by three different programs in the incoming three_field archive. Retaining
its token/AST records and adding the new byte program gives (249,271,488).
No single program in this package has that combined vector.

INPUT CONTRACTS
Use code/checker_native.py for arbitrary submitted JSON. It retains the
whole-input integer/list gate (including unused data) and public-goal
validation. The 488-byte compact program assumes the existing canonical
closed guarded Eq/D public syntax contract; it has no separate public
grammar validator and accepts some administrative truth aliases.

The new modules and matched controls accept the same finite certificates
under sufficient resources. They return different internal success values,
so memory use can differ. Normal exit with exactly ACCEPT followed by a
newline is acceptance; exceptions reject. No assertions implement gates.

READ AND REPRODUCE
  ipra_checker_refinement.pdf is the report with inherited proof appendices.
  ipra_checker_refinement.tex and reference/*.tex are its complete sources.

From this directory:
  python3 verify_manifest.py
  python3 verify.py
  python3 reproduce.py --pdf

The manifest checks the delivered bytes. Run it before rebuilding: a new
PDF build refreshes derived evidence and PDF metadata, so those hashes can
legitimately differ from the delivered versions afterward.

Exact measurements use CPython 3.12.14. The verifier has only standard-library
dependencies. It checks four complete modules and runs all 121 required
fixtures against candidate/control, normally and with -O: 484 isolated CLI
executions. All expected outcomes matched in the included verification run.

PDF rebuilding requires an installed TeX distribution. build_pdf.py first
tries normal pdfLaTeX, then can create a private format from installed TeX
sources without network access or system-wide changes. The report declares
its font maps explicitly. A normal configured TeX installation can also use
  latexmk -pdf ipra_checker_refinement.tex

BASELINE AND ATTRIBUTION
  Repository: VladimirReshetnikov/ProveIt
  Commit: 42fba2a76aea6eb41a8c4acfe7761620f58956ee
  Directory: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA
  Current baseline archive: docs/incoming/ipra_three_field_2026-11-12.zip
  Git blob: 152c09e61c95029a143198d019e94e570898f980
  Archive bytes: 1,103,030

All three current incoming archives were examined and checked against their
repository Git blob identities. The archive contains the exact selected
controls and upstream mathematical reference sections with their license.
The successful-return/comprehension technique and Boolean-order guards were
already in inferred_major; the new result is their measured composition
with the newer context-first source. This provenance is explicit in the
report, IMPLEMENTATION_PROOF.txt, and PROVENANCE.json.

CONTENTS
  code/                    new standalone acceptance modules
  controls/                exact matched source controls
  tests/                   all required regression cases and expected results
  reference/               attributed mathematical proof sources
  evidence/                measurements, independent reviews, PDF build/QA
  IMPLEMENTATION_PROOF.txt  universal finite-execution simulation arguments
  verify.py                executable comparison and measurement
  reproduce.py             verification and optional PDF rebuild
  build_pdf.py             offline PDF builder
  PROVENANCE.json           pinned sources and hashes
  MANIFEST.sha256           delivered-file integrity hashes

No new Lean/Rocq verification is claimed. Finite test success is not a proof
of mathematical soundness; the report separates the simulation proof from
the inherited arithmetic and logical bi-interpretation. Further research
questions are included.
