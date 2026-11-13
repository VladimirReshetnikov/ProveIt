A SMALLER EXACT PROOF-INPUT PRESENTATION OF iPRA
13 November 2026

START HERE
  ipra_exact_threshold.pdf
  ipra_exact_threshold.tex

RESULT AND LIMIT
The complete standalone code/checker.py measures 314 significant Python tokens,
357 AST nodes, and 590 normalized UTF-8 bytes with CPython 3.12.14. This one
program is below all three coordinates of the inspected exact-public-syntax
envelope 316 / 358 / 591. The source grammar, genuine numerical binding, and
public true-as-zero alias of the intrinsic-validation control are unchanged.

THE REQUESTED GLOBAL TARGET REMAINS UNMET. This is not below the compact
promised-grammar envelope 239 / 255 / 460, or its seeded-sequent variant
238 / 255 / 455. It does not delete an arithmetic axiom, establish absolute
minimality, or constitute a new mathematical axiomatization. It is a modest
complete-checker refinement of the inherited native scalar iPRA presentation.

THEORY
The report explicitly states all eight native axiom/rule families, the
ordinary intuitionistic first-order realization, logical macros, and both
interpretations. The inherited native/iPRA bridge has whole numerical domains,
actual equality, identity comparison graph x=y, and both formula round trips.
The checker presents the same full theory. No new Lean/Rocq or Python-runtime
formal verification is claimed.

INPUT AND SUCCESS
Input is one JSON array. Its final element is the closed public Eq/D goal;
earlier records are consumed from right to left. Native numerical zero is code 1
(the JSON value true is an explicitly allowed public alias); genuine bound
variables use codes 3, 5, 7,... . Public false and padding slots are rejected.
Each ordinary proof packet has four fields [s,u,t,m]. In actual introductions,
use mode u=0 for equation progress and u=2 for cases. The supplied witness is t.
The public goal syntax and all parameter/binder codes remain unchanged.

Acceptance means normal exit with exactly ACCEPT followed by LF. Exceptions,
missing packets, missing marker, and resource failures reject. Unused JSON
prefix records are permitted and provide no assumptions. Mathematical
completeness uses unbounded finite resources, as in the source comparison.

The new protocol does not accept exactly the same certificate byte strings as
the old one. Only actual introduction fields should be translated; a global
replacement of integers would corrupt terms and other rule arguments.
tests/translate.py traces the source checker to make the appropriate edits.
It is an untrusted certificate producer, not a proof-search oracle.

QUICK START
  python3 code/checker.py < examples/computation_zero_local.json
  python3 code/checker.py < examples/guarded_induction_with_used_hypothesis_local.json
  python3 reproduce.py
  python3 measure.py
  python3 tests/verify.py
  python3 tests/verify_threshold_modes.py
  python3 build_pdf.py

The first two commands print ACCEPT. reproduce.py remeasures the checker and
runs all shipped positive/negative examples through both the compact checker
and readable expansion. measure.py remeasures the included complete controls.
tests/verify.py reruns the larger grammar/type/mutation/process suite.
tests/verify_threshold_modes.py reproduces the extra 90 threshold/capture
trials and compares the results with their frozen receipt in evidence.
The Python tools use only the standard library and need no network or source
checkout. build_pdf.py uses installed TeX; it can create private format/font
maps when an installation lacks caches, without changing system configuration.

CONTENTS
  ipra_exact_threshold.tex/.pdf   Standalone report and compiled 13-page PDF.
  code/checker.py                 The complete counted module.
  code/readable.py                Explanatory standalone expansion.
  examples/                      Fourteen accepted proofs and two rejections.
  controls/                      Exact predecessor, old proof fixtures, and
                                 selected frontier controls with attribution.
  tests/                         Portable trace translator and validation.
  evidence/                      Source census, metrics, validation receipts,
                                 build/layout evidence, and source identities.
  proofs/                        Independent correctness reviews and carefully
                                 marked unresolved research directions.
  reference/                     Native arithmetic/logic bridge source,
                                 checker-protocol chapter, Lean theorem
                                 identification module, and upstream license.
  CLAIMS.json                    Machine-readable boundaries of the result.
  MANIFEST.sha256                Integrity manifest for the delivered files.

The copied article chapter sources are reference excerpts from a larger TeX
project; compile the standalone report at the archive root. The copied Lean
identification module is not a self-contained Lean project; its transitive
dependencies remain in the pinned repository. Original/adapted upstream
material is under the included MIT No Attribution license.

VALIDATION
Fourteen translated native derivations; 12,742 independent grammar comparisons;
13,120 opener/type checks; 490 positive variants; 10,866 false/invalid-export
mutations; 232 standalone normal/-O process runs; 90 additional threshold/future
parameter capture trials; 32 packaged compact/readable example runs. No
unexpected outcomes were found. These finite checks support, but do not replace,
the written soundness/completeness argument.

SOURCE PIN
  https://github.com/VladimirReshetnikov/ProveIt
  f25af53c682ea76c57b67c70c976bcaf836b0c91
  Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

All eight incoming ZIPs at that snapshot were included in the comparison.
No remote repository change was made. The exact-profile improvement is 2 tokens,
1 AST node, and 1 byte against the envelope, not a global simplicity theorem.
