A 468-BYTE CHECKED PRESENTATION OF iPRA
Prepared for Vladimir Reshetnikov, 12 November 2026
================================================

OPEN FIRST

  report.pdf
  report.tex

RESULT AND LIMIT

The complete direct-source checker code/checker.py has:

  271 significant Python tokens / 305 AST nodes / 468 normalized bytes.

The current 469-byte compact incumbent has 272 / 306 / 469. The new
program combines that shared-leaf implementation with the existing even
binder-coordinate shift. It removes one token, one node, and one byte
against that exact incumbent. The mathematical axiom basis is unchanged.

The independent current compact envelope changes from 241 / 262 / 469 to
241 / 262 / 468. Each coordinate minimum belongs to a DIFFERENT program.
This is not a new axiom deletion, not an absolute simplestness theorem,
and not one checker below every current coordinate minimum. The stronger
mathematical breakthrough requested has not been established in this report.

The public theory remains bi-interpretable and equiconsistent with FULL
FIRST-ORDER intuitionistic primitive recursive arithmetic, with whole
numerical domains, actual equality, and identity numerical comparison graphs.
The arithmetic/logical bridge is inherited from the pinned repository.
The new successful-run correspondence is proved separately in report.tex.
There is no claim that Lean has verified the tiny Python program.

INPUT CONTRACT

The input is one JSON array consumed from right to left, ending in [A,0].
A is a canonical CLOSED guarded Eq/D public formula in the shifted codec.
Every consumed instruction has four fields [m,s,u,t]. All certificate
data are finite exact-integer/list trees. Unused prefixes are allowed.
Acceptance is normal exit with exactly ACCEPT and one LF. Exceptions reject.
The compact checker does not validate the entire promised public grammar
or alphabet on arbitrary JSON. Ideal completeness ignores finite resource
limits. The stronger validation categories are reported separately.

REPRODUCE

  python3 reproduce.py
  pdflatex -interaction=nonstopmode -halt-on-error report.tex
  pdflatex -interaction=nonstopmode -halt-on-error report.tex

Python checks use the standard library only and require no network.
Measurements use CPython 3.12.14 ast.unparse plus one LF. Source parsing,
JSON input, and the explicit success marker are included in the measurements.
The measured checker imports no project helper, payload, compiler or table.

The main suite runs 140 isolated ordinary/-O executions and eight successful
trace conversions. A separate four-execution negative demonstration compares
the correct checker with an explicitly UNSOUND no-parity mutant. Every
expected outcome matched. Finite tests support the written universal proofs.
Freshness/context attacks, false conclusions, and genuinely used induction
are included. The latter translation inserts 13 hypothesis packets into
268 old instruction packets, producing 281 calls.

FILES

  code/checker.py
    Complete measured 468-byte program.
  code/readable_checker.py
    Standalone readable expansion with the same scope and evaluation schedule.
  code/translate_offset_to_shared.py
    Untrusted successful-trace converter from the existing 472-byte protocol.
  controls/
    Exact byte controls and independent token/AST incumbent sources.
  fixtures/
    Positive proofs, negative attacks, and source certificates for translation.
  negative/
    Deliberately UNSOUND no-parity program, false goal, and explanation.
    Never use that program as a proof checker; it exists as a regression control.
  evidence/
    Measurements, source identities, and execution receipts.
  reference/
    Pinned inherited mathematical sources and selected Lean theorem sources.
    Chapter fragments and the selected Lean files are reference dependencies,
    not standalone TeX/Lean projects. The new report is self-contained as a
    statement and proof of the new refinement, with its inherited dependencies
    explicitly identified.
  review/
    Independent mathematical correspondence and inherited-bridge audits.
  CLAIMS.json, PROVENANCE.json, MANIFEST.sha256
    Precise claims, identities, and integrity checks.

PIN

  https://github.com/VladimirReshetnikov/ProveIt
  78edba03ee060644464f76e388578584b356520a
  Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

Nineteen incoming archives and seven nested archives were inspected.
The inspected later remote head made no change to the target subtree.
No remote repository mutation or publication was performed.

Reference sources retain the repository's MIT-0 license. New code and text
in this package are also provided under MIT-0; see LICENSE.txt.
