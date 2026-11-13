AN EXACT iPRA CHECKER AND INTRODUCTION BY RECONSTRUCTION
13 November 2026

READ FIRST
  ipra_reconstructed_introduction.pdf
  ipra_reconstructed_introduction.tex

RESULT AND LIMIT
The requested global size breakthrough was not established.

1. exact/code/checker.py is one complete JSON checker with genuine numerical
   binding: 313 significant tokens / 357 AST nodes / 590 normalized bytes;
   gzip level 9, mtime zero: 370 bytes. It improves all three coordinates of
   the inspected exact-binding envelope 316 / 358 / 591.

2. sorted/code/checker.py is one smaller program for the predecessor's padded
   sorted grammar: 298 / 336 / 573; gzip9: 358. It improves that envelope's
   299 / 337 / 575 but does not validate genuine binding in public terms.

3. synthesis/synthesis_checker.py implements a seven-rule calculus whose
   introduction matrix is reconstructed from its successful premise proof.
   The report proves equality of all open consequences with the native
   calculus. The existing full first-order iPRA bi-interpretation therefore
   applies with both formula round trips and identity numerical graphs.
   Its readable reference checker is larger: 1896 / 2182 / 7639; gzip9:2249.

These are separate results. The seven-rule calculus is NOT implemented by
the 590-byte checker. The latter refines the inherited presentation.
Neither checker beats the compact promised-grammar envelope 238 /255 /455
under its seeded-header convention. No absolute minimality, new deletion
of an arithmetic principle, or new Lean/Rocq verification is claimed.

EXACT PUBLIC SYNTAX
With p genuine enclosing numerical binders:
  term(p) = 1 | true | 3+2j (0<=j<p)
            | [term(p)] | [term(p),term(p),term(p+1)].
  formula(p) = [term(p),term(p)] | [formula(p+2)].
The goal must be formula(0). Code 1 and JSON true both mean zero. A singleton
term means successor; a ternary term means iteration, binding only in its
third child. A binary formula is equality; a unary formula is the paired
binder D. The report states D's reading and all logical macros.

The input is one JSON array whose last element is the goal. Earlier records
are consumed from right to left. Unused prefix data does not create any
assumption. The whole counted program includes its reader and success output.
There is no external rule table, verifier or trusted compiler.

RUN
  python3 exact/code/checker.py < exact/examples/zero.json
  python3 exact/code/checker.py < exact/examples/induction.json
  python3 exact/code/checker.py < exact/examples/implication.json
  python3 exact/code/checker.py < exact/examples/reject_capture.json

The first three accept. The last rejects a future-eigenparameter capture.
Acceptance is normal exit with exactly ACCEPT followed by LF; exceptions
and all other results reject. Mathematical finite-proof completeness assumes
adequate interpreter resources, as in the upstream comparison.

S7 RECONSTRUCTION EXAMPLE
  python3 synthesis/synthesis_checker.py < synthesis/synthesis_fixtures/marked_witness_recovers_fixed_data.json

S7 supplies a witness, a fresh counter, a local seed formula, and a proof
under that seed. It computes the matrix from the proved successor conclusion
and checks the seed against the reconstructed instance. The seed is fixed
before its branch is checked. The marker lemma prevents accidental abstraction
of fixed data; the proof jointly recovers case introduction and full formula
transport by binder rank. No quantified-formula induction is added.

REPRODUCE
Use CPython 3.12.14 for exact published normalization counts.
  python3 reproduce.py
  python3 reproduce.py --tests
  python3 build_report.py

The first verifies MANIFEST.sha256 and measures the selected complete sources.
The second additionally executes all packaged test suites. Verify the original
manifest before rebuilding: a regenerated PDF or receipt can have a different
hash. The build script uses installed pdfLaTeX and downloads nothing.

AUDIT
The source pin is ProveIt commit e0d702b905c74b74a23d045f8289b151bb8ebcff.
All 3,268 Python files under Artifacts were matched to Git blob identities.
All seven current incoming ZIPs were matched exactly and included. The census
has 3,423 parseable source files, 1,974 distinct normalized programs, and no
parse failures. It includes tests and rejected experiments, not only valid
checkers. The report's envelopes use the documented complete programs.

The selected source controls are bundled. evidence/census.json contains the
full census, and evidence/incoming_archive_verification.json gives all seven
archive identities. tools/audit_repository.py reproduces a local repository
census without executing any measured source. It is optional; the complete
corpus is not duplicated in this archive.

VERIFICATION STATUS
The exact checker: 43 regression cases, 14 Boolean-alias positives, 4,350
independent exact-grammar comparisons, 504 active-scalar checks, 22 complete
normal/optimized process runs, no failures. A readable expansion agrees on
all 43 regressions. Positive examples include induction that actually uses
its hypothesis and a 331-call all-number symmetry proof.

The S7 checker: 21 positive/negative fixtures, 42 normal/optimized process
runs and 1,501 deterministic syntax-law checks, no unexpected outcomes.
Finite tests are supporting evidence, not a proof of universal soundness.
The full-equivalence argument is the written theorem in the report.

reference/NativeBiInterpretation.lean is the exact pinned bridge interface.
Its transitive imports are in the source repository. This archive does not
claim to compile a new Lean or Rocq development.

CONTENTS
  exact/          Recommended checker, readable expansion, proofs, examples,
                  source fixtures, untrusted translator, tests and controls.
  sorted/         Secondary padded-grammar checker and its evidence.
  synthesis/      S7 reference checker, syntax-law tests and 21 certificates.
  sections/       Complete mathematical proof of S7 equivalence.
  reference/      Baseline controls, inherited base source and Lean interface.
  evidence/       Census, source verification, measurements and reviews.
  tools/          Optional full-corpus measurement script.
  STATUS.json     Machine-readable result and limitation statements.
  MANIFEST.sha256 Integrity hashes of every other delivered file.

No remote repository files were modified.
