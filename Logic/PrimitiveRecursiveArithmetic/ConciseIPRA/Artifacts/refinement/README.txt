CONCISE iPRA: A BYTE REFINEMENT AND A TWO-FIELD PROOF PROTOCOL
Research package prepared for Vladimir Reshetnikov, 12 November 2026

STATUS: PARTIAL RESULT; THE REQUESTED OVERALL SIMPLICITY TARGET IS NOT MET

This package gives an exactly justified implementation refinement of an
existing presentation of intuitionistic primitive recursive arithmetic,
together with a two-field certificate protocol and its written justification.
It does not establish a globally simplest axiomatization, a new arithmetic
or logical axiom deletion, or a checker below every current size coordinate.

The comparison is pinned to VladimirReshetnikov/ProveIt commit
25fa7ee05ea2e4347d1fdef8498c4c644c31f1ca, including the incoming archives in
Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/docs/incoming/.
No modification to the GitHub repository is part of this delivery.

1. WHAT WAS ACHIEVED

The complete compact checker decreases from 495 to 488 normalized UTF-8
bytes: seven bytes, approximately 1.41 percent. The new program has 271
significant Python tokens and 304 AST nodes, versus 267 tokens and 299 AST
nodes for its matched 495-byte control. Thus the byte improvement costs four
tokens and five AST nodes.

The observed coordinatewise envelope before this refinement is 249 tokens,
271 AST nodes, and 495 bytes, attained by different programs. The new vector
(271,304,488) does not dominate that envelope. These observed minima are
empirical comparison values, not a mathematical lower-bound theorem.

A strict guarded companion has 855 bytes, versus 862 for the exact same
validator attached to the 495-byte control, or 869 for the older published
strict companion. Its token and AST counts are 423 and 474, so this is also
a byte-only improvement. The existing 643-byte native public-goal checker
has a different interface and does not impose the same whole-input alphabet
rejection; the 855-byte companion is not claimed as a general strict-checker
record.

The two-field protocol is a separate substantive change in certificates.
Computation equations are recognized directly from the requested goal and
consume no proof packet. Every remaining instruction supplies a major
formula and one payload. The reference implementation has 295 tokens,
352 AST nodes and 742 normalized bytes. It simplifies the supplied data but
does not improve the checker-size frontier.

2. MATHEMATICAL AND VERIFICATION STATUS

The report explicitly specifies the ordinary intuitionistic arithmetic
theory and its logical interface, the native paired-binder presentation,
the two interpretation directions, and equiconsistency. The whole-domain
bi-interpretation with iPRA, using actual equality and identity composites,
is inherited from the cited ProveIt development and reproduced foundations.
The 488-byte checker preserves that theory by a bidirectional finite-success
execution argument relative to the matched control.

The change uses an eager singleton-list comprehension. A successful call
returns True or a nested singleton list; changing the corresponding major
check from None-or-m*3 to truthy-and-m*3 preserves the value and scheduling.
The continuation must execute before success is returned. Scope checks,
fresh-parameter allocation order, and major-premise proofs remain present.
The readable implementation exposes that order explicitly.

The two-field protocol has a written proof and an independent mathematical
review. No newly machine-checked Lean or Rocq proof, nor a new run of the
repository's Lean development, is claimed. "Verified" in the report title
refers to the stated program argument and executable checks, not a new
proof-assistant certification. Copied foundation sections retain their
original mathematical context and attribution; they are not new results
of this investigation.

Finite executable checks support implementation confidence. They do not
replace universal soundness, completeness or interpretation arguments.
Finite-success correspondence assumes sufficient finite implementation
resources. Nested return lists can use more memory or stack than the control
at a fixed interpreter limit.

3. CONTENTS

report.tex, report.pdf
  The complete LaTeX research report and compiled paper, including explicit
  theory specifications, comparisons, proofs, limitations and foundations.

code/
  checker_compact.py: the complete 488-byte profile.
  checker_strict.py: the 855-byte guarded companion.
  checker_readable.py: a separate readable expansion of the compact checker.
  two_field_reference.py: the 742-byte two-field protocol reference.
  README.txt: detailed executable contracts.

baseline/
  Exact normalized comparison programs: compact 495, strict 862 and 869,
  the three-field 249-token and 271-AST profiles, and native 643.
  LICENSE-ProveIt.txt records the upstream license.

foundation/
  Reproduced ProveIt sources for the arithmetic/logical basis, predecessor,
  equality reflection, primitive recursion, interpretation bridge, guarded
  language and raw-decoder dependencies.

proofs/
  The trace-equivalence proof, the two-field protocol and independent review,
  plus relevant inherited protocol and contract notes.

tests/
  Frozen JSON certificates, source and hash manifest, rejection cases, and
  the separate deterministic computation-leaf evaluator.

evidence/
  Full-module measurements, CLI results, source provenance, frontier
  remeasurement, computation-leaf receipts, and claims.json.

measure.py, reproduce.py, build.py
  Standalone measurement, test reproduction, and paper build entry points.
  Measured checker modules import none of these helpers.

4. REPRODUCE THE MEASUREMENTS AND CLI CHECKS

From the extracted archive directory run:

  python3 measure.py
  python3 reproduce.py

The checker tests require Python and its standard library only. Published
normalized counts use CPython 3.12.14. The measurement is ast.unparse of the
parsed complete module, followed by exactly one newline. It includes imports,
JSON input parsing and the ACCEPT output. Token exclusions are documented in
measure.py and the paper. Source and normalized SHA-256 hashes are recorded.

The recorded final suite contains 112 fixture entries and 898 isolated CLI
executions, with zero failures. Every program/fixture pairing is run normally
and under -O. The compact candidate, readable implementation, compact control,
strict candidate and two strict controls each receive 132 executions. The
two three-field profiles each receive 40; the two-field reference receives
26. These totals overlap the preliminary 264- and 396-execution comparisons
discussed in the report and should not be added to them as independent tests.

The suite covers computation, introduction, transport, induction with a used
hypothesis, D elimination and Q specialization, malformed JSON prefixes,
false equations, context leaks and future-coordinate capture. Both the compact
and strict candidates reject the inherited 17-packet future-scope attack.

Outputs are evidence/metrics.json and evidence/validation.json. Timeout,
fixture-hash mismatch, inconsistent acceptance output, or an unexpected
verdict is a test failure. The native 643-byte contextual baseline is measured;
the delivered CLI suite does not claim a fresh audit of its different contract.

5. REPRODUCE THE SEPARATE COMPUTATION-LEAF TEST

  python3 tests/check_computation_leaves.py

To replace its receipt with the reproduced JSON output:

  python3 tests/check_computation_leaves.py > evidence/computation_leaf_results.json

The recorded deterministic run examines 20,000 generated integer/list leaf
candidates. Of these, 4,065 pass the entry scan and direct computation
recognizer; all 4,065 evaluate to true equations under the separate sorted
numerical evaluator, with zero evaluator-budget failures and zero false
equalities. The test uses a fixed rigid-parameter assignment and a finite
evaluation budget; it is not an exhaustive semantic proof.

An additional targeted-review receipt records 8,008 dummy-slot/nested-state
cases: 3,608 accepted and evaluated true, 4,400 rejected, no budget failures,
and no counterexamples. That receipt is evidence/twofield_targeted_leaf_audit.json.
It is separate from both the 898 CLI executions and the 20,000-candidate run.
Reproduce it with:

  python3 tests/check_targeted_leaves.py

6. CHECK AN INDIVIDUAL CERTIFICATE

For a supplied strict positive example:

  python3 code/checker_strict.py < tests/fixtures/progress/computation_zero_local.json

For a supplied two-field positive example:

  python3 code/two_field_reference.py < tests/two_field/computation_zero.json

Acceptance requires exit status zero and exactly ACCEPT followed by a newline.
Exceptions reject. The two-field protocol is not interchangeable with the
four-field packet streams; use the fixture families assigned to each program.

The compact checker assumes its documented closed guarded Eq/D public-goal
and integer/list certificate contract. The strict companion validates the
whole JSON alphabet and the guarded public goal, including scope, but retains
the inherited administrative interpretation of auxiliary fields. It does not
require every unused integer/list prefix packet to be a canonical inference.

7. BUILD THE PAPER

  python3 build.py

The build script runs pdflatex twice on report.tex and produces report.pdf.
A normal LaTeX installation with the packages named in the report preamble is
required. All included source dependencies are local; neither the checker
tests nor the paper build performs runtime downloads.

The archive includes SHA256SUMS for all delivered files except the manifest
itself. To regenerate the manifest and the ZIP after intentional edits, run:

  python3 package.py

The PDF layout review is recorded in evidence/pdf_quality_review.json.

8. PROVENANCE AND LIMITS

Repository:
  https://github.com/VladimirReshetnikov/ProveIt
Pinned commit:
  25fa7ee05ea2e4347d1fdef8498c4c644c31f1ca
Project:
  Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

evidence/source_provenance.json identifies inherited and derived modules,
their source hashes, and upstream archive origins. tests/fixtures.json records
certificate hashes and canonical archive/member origins. The reproduced
foundations are attributed in the report; license texts accompany the package.

The research outcome remains partial: seven fewer compact source bytes and a
proved certificate-protocol change, with the iPRA bridge explicitly inherited.
No program delivered here is simultaneously below 249 tokens, 271 AST nodes
and 495 normalized bytes. No absolute minimality or requested overall
axiomatization breakthrough is claimed.
