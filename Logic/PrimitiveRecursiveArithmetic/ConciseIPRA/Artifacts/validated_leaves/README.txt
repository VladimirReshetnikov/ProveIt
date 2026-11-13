A VALIDATED SHARED-LEAF PRESENTATION OF iPRA
and a common obstruction for adaptive iteration
Prepared for Vladimir Reshetnikov, 12 November 2026
================================================

STATUS
------
This package is a verified partial result. It does not establish a globally
simplest axiomatization or a construction below all current compact minima.

The complete whole-input checker is 606 normalized bytes, against its exact
608-byte control. The native-public-goal companion is 579 bytes, against
581. Both have unchanged token counts and one additional AST node. No
arithmetic axiom is deleted. The compact frontier 242 tokens / 262 AST nodes /
469 bytes (three different programs) is unchanged.

The mathematical supplement proves a common extension of the article's two
almost-unary barriers: finite adaptive queries in seed AND update, multiple
registers, and counter-dependent query locations. Numeric outputs may depend
only on answers from ONE supplied body. Controls may select among finitely
many fixed primitive-recursive output maps. This gives no addition, selector,
or pairing term in that class; it does not exclude general formula-defined
interpretations of iPRA.

OPEN FIRST
----------
ipra_validated_leaves.pdf    Full report, explicit rules, proofs and limits.
ipra_validated_leaves.tex    Standalone compilable TeX source.

CHECKERS
--------
code/checker_strict606.py    Recommended complete JSON interface. Validates
                           the entire input alphabet and native Eq/D goal.
code/checker_native579.py   Validates the native Eq/D goal. The universal
                           argument assumes integer/list certificate trees.
                           Its integer identity gate is CPython-specific.

Both read one JSON array, with four-field packets consumed from the end and
the public goal as the final element. Numerical zero is encoded by integer
1. It is distinct from administrative marker 0. All details are in the report.
Accept means exit status zero and exactly ACCEPT followed by a newline.
Exceptions and resource exhaustion are nonacceptance. Proof completeness
uses the usual ideal model with unbounded finite resources.

Run an example from this directory:
  python3 code/checker_strict606.py < fixtures/guarded_induction_with_used_hypothesis_local.json

REPRODUCE
---------
  python3 reproduce.py
  python3 build_pdf.py

The first command checks the supplied manifest, regenerates translated
certificates, reruns substantive accepted/rejected cases normally and with
Python -O, and remeasures complete sources. It uses only Python's standard
library. Run under CPython 3.12.14 for the exact metrics. The PDF build needs
pdfLaTeX and the ordinary packages declared in the standalone TeX source.
Reproduction writes generated receipts to a fresh temporary directory and
does not modify the delivered evidence.

CONTENTS AND ATTRIBUTION
-----------------------
fixtures/                  Thirteen substantive translated proofs.
tests/                     Portable translation and isolated-process checks.
evidence/                  Actual metrics, receipts, proof notes, independent
                           review and source provenance.
reference/controls/        Exact comparison modules, including compact records.
reference/source_fixtures/ Original certificates used by the translator.
reference/article/         Complete pinned upstream article TeX sources.
reference/incoming_reports/Selected upstream reports for reference; fragments
                           there are not independently compilable deliverables.
CLAIMS.json                Machine-readable claims and explicit nonclaims.
MANIFEST.sha256            SHA-256 ledger of every package file except itself.
LICENSE.txt                MIT No Attribution; inherited work is credited.

SOURCE SNAPSHOT
---------------
https://github.com/VladimirReshetnikov/ProveIt
Commit 6874c85a4cea45d881de73620284fcc75d740942
Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

All twelve incoming ZIP archives at this snapshot were extracted. Their exact
sizes and identities are recorded in evidence/provenance.json. Current
comparison controls were measured locally, rather than copied from the
older top-level README table.

The native calculus, arithmetic/logical bridge, sorted arity codec, and
shared-leaf principle are inherited. New work consists of their explicit
validated composition, its scope proof and certificate translation, and
the common adaptive-query obstruction. The numerical domains and equality
are unchanged, so the inherited interpretation comparison graphs remain x=y.
No new Lean or Rocq verification of the Python implementations is claimed.
