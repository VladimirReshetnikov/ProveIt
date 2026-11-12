ORBIT CLOSURE FOR iPRA
=====================
Prepared for Vladimir Reshetnikov, 12 November 2026.

OUTCOME
-------
This package does not meet the requested complete-checker size threshold.
It supplies a fully specified theory equivalent to full first-order iPRA,
a strict standalone checker, a general proof translator, a proved narrower
successor-uniqueness result, and an exhaustive audit of current Python sources.
It does not claim the simplest axiomatization or a new checker record.

START HERE
----------
report.pdf is the mathematical report, with explicit axioms and all logical
and nonlogical rules, both interpretations and their composites, proofs,
measurements, limitations, and further research questions.
report.tex is its self-contained editable LaTeX source. It includes the full
selected checker listing and needs no external figures or TeX inputs.

PROVED RESULTS
--------------
1. Orbit uniqueness:
      from f(Sz)=h(f(z)), infer forall y [f(y)=I(y,f(0);u.h)].
   It is exactly equivalent to pointwise scalar UR over arbitrary retained
   contexts. In a native presentation the conclusion is the corresponding
   Q closure. No target term is supplied by the inference. The selected
   checker also infers f and h from the proposed conclusion.

2. Successor-only uniqueness:
      from f(Sz)=S(f(z)), infer f(t)=I(t,f(0);u.Su).
   It already gives contextual induction for every zero equation q(n)=0.
   The retraction proof uses numerical cases where the existing proof uses
   arbitrary-update uniqueness. Full-iPRA equivalence of this restricted
   successor principle is not established.

3. The existing zero-induction fiber countermodel refutes successor
   uniqueness and therefore does not settle that principle's incompleteness.
   Successor uniqueness also gives the commutative-monoid laws for addition
   and n+k(n)=n+k(0) when k(Sn)=k(n); cancellation remains an explicit gap.

The complete Orbit theory inherits the established scalar-UR equivalence.
Its interpretations use whole numerical domains and actual equality; both
numerical composite isomorphisms have graph x=y. No claim is made that iPRA
proves its own consistency. New arguments are not Lean/Rocq verified.

MEASUREMENTS
------------
CPython 3.12.14; complete standalone modules; actual docstrings removed;
ast.unparse plus one LF; layout/comment tokens excluded; all AST nodes.

                                      Tokens    AST    Bytes
Inherited strict scalar UR              1124   1175    3393
Orbit, templates supplied                1132   1178    3400
Orbit, templates inferred                1145   1194    3455

The selected Orbit checker is larger than its matched control.
The existing compact coordinate envelope is 256 / 276 / 506, attained by
different existing programs. Compact protocols and strict public syntax
validation are different contracts; the report does not conflate them.

VALIDATION
----------
The Orbit suite has 156 ordinary/optimized Python checker executions:
92 expected acceptances, 64 expected rejections, zero mismatches, plus two
actual translator CLI checks. The inherited suite has 66 process checks.
These are finite implementation checks, not general formal verification.

All 90 Research package trees were inventoried. All 5,825 Python paths
deduplicate to 1,380 exact Git blobs, each hashed, parsed and measured.
106 sources cheaper in at least one coordinate are explicitly classified
as utilities rather than standalone acceptance checkers. Repository source
code is not executed by the audit. Frozen docs/incoming contains only its
placeholder. The audit does not claim a universal complexity lower bound.

REPRODUCE
---------
Run in a Python 3.12 environment:

  python3 verify_manifest.py
  python3 reproduce.py
  python3 orbit/code/orbit_inferred.py < orbit/validation/closed_identity_orbit.json
  python3 orbit/translate_ur.py inferred < orbit/reference/examples/scalar_ur_ur_nested_iterator_scope.json

The checkers print ACCEPT and exit zero on a valid certificate. They use
the standard library only. The translator is untrusted and checks its own
output with the standalone target checker.

To rebuild the report with TeX Live:

  python3 build_pdf.py

Regenerating the PDF or evidence can change hashes. Verify the delivered
manifest first. No network access is needed for any reproduction step.

FILE MAP
--------
report.tex/.pdf              Complete report and editable source.
orbit/code/                 Complete selected and comparison checkers.
orbit/translate_ur.py        General finite-proof translator.
orbit/validate.py            Certificate and measurement tests.
orbit/validation/            Fixtures and recorded results.
orbit/README.txt             Detailed certificate format and provenance.
audit/blobs/                 Exact frozen Python source corpus.
audit/all_source_metrics.csv All 1,380 source measurements.
audit/frontier.json          Corrected attainable coordinate envelope.
audit/subfrontier_exclusions.json  Eligibility decisions for cheap utilities.
audit/reproduce_audit.py     Offline source-hash and metric replay.
reference/scalar_uniqueness/ Inherited mathematical proof fragments.
reference/LICENSE.txt       Inherited MIT No Attribution notice.
PROVENANCE.json              Pinned source identities and claim boundaries.
CLAIMS.json                  Machine-readable statements and nonclaims.
evidence/                   Reproduction and PDF build/visual checks.
MANIFEST.json                SHA-256 hashes of delivered files.

SOURCE
------
https://github.com/VladimirReshetnikov/ProveIt
Commit: 62396b06020f794fa6dc01b4025a6a5db9d4d28a
Path: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA
No repository files were changed.
