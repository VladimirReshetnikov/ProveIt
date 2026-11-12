DETERMINISTIC WITNESS OPENING FOR iPRA
Prepared for Vladimir Reshetnikov -- November 11, 2026

START HERE

  ipra_deterministic_opening.pdf   Complete research report.
  ipra_deterministic_opening.tex   Standalone LaTeX source, with code embedded.
  code/checker_open.py            Selected checker for the new theory.

THE NEW MATHEMATICAL RESULT

Keep the existing full-normal-form scalar terms, Eq/D formulas, reusable
clauses, single introduction rule, and fixed universal-reflexivity clause.
Change witness opening. For fresh b, inspect the normalized zero and first
rows of its matrix B. If B(b,0) is literally 0=0 and B(b,1) is literally
b=t, select t; otherwise select b. Open the clause at this selected value,
retaining the fresh numerical scope b, and prove the unchanged outer goal.

The selected value may contain b. There is no supplied equality proof,
replacement term, or intermediate branch formula. There are three inference
families (Use, Introduce, Open) and one explicit fixed axiom clause.

The written proof establishes full normalized substitution in derivations,
including selector changes caused by substitution; ordinary paired
elimination; unrestricted equality transport; and exact equivalence for
arbitrary canonical clause sequents. The inherited whole-domain iPRA bridge
then supplies actual equality, identity numerical composite graphs x=y,
both formula round trips, and equiconsistency with full first-order iPRA.

WHAT THE MEASUREMENTS DO AND DO NOT SAY

Complete-module metrics: CPython 3.12.14, actual docstrings removed,
ast.unparse, one final LF; common Python/standard-library runtime excluded.

                                             Bytes  Tokens  AST
  Immediate mathematical predecessor          2273     732  813
  Selected automatic-opening checker           2253     730  809

  Separate inherited compact control             516     265  306
  Separate compact continuation refactor          508     267  302
  Separate inherited AST profile                  602     260  278
  Separate refactored AST profile                 580     263  276
  Separate native goal-validated control          788     358  413
  Separate native goal-validated refactor         780     360  409

The 508-byte checker is NOT an implementation of the new opening rule.
It implements the existing guarded compact calculus under the same
canonical integer/list and public-goal contract as its control. It omits a
separate public-goal grammar validator; the native 780-byte profile retains
its matched control's validator. The existing 256-token minimum is not
improved. No single program dominates all old coordinates. These are
attained implementation sizes, not proved universal lower bounds.

BASELINE

  Repository: VladimirReshetnikov/ProveIt
  Commit: 17898ea7e6a1300dfdcad71040d5daeed67916d4
  Directory: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

The comparison includes all 67 filed packages described in the README and
the six incoming archives at that commit. The immediate predecessor is
ipra_witness_discharge_2026-11-11.zip. Exact source/provenance records and
the inherited MIT-0 license are included. No remote repository was changed.

EXECUTE

  python3 reproduce.py
  python3 code/checker_open.py < examples_open/positive/reflexivity_0.json
  python3 -O code/checker_open.py < examples_open/positive/reflexivity_0.json

An individual checker accepts only when it prints ACCEPT and exits zero.
The main checker uses no assert-based trust decision. Exceptions reject.

REBUILD THE REPORT

  python3 build_report.py --pdf

Alternatively, run pdflatex on the standalone .tex source. The source uses
standard TeX Live packages and does not require shell escape or network
access. Exact source-size reproduction uses CPython 3.12.14.

CONTENTS

  sections/            Editable mathematical and explanatory sections.
  code/                Selected automatic-opening checker and an intermediate
                       deterministic-discharge variant, clearly separated.
  examples_open/       Primary positive/negative examples and matching old proofs.
  examples/            Intermediate variant's examples and checked translations.
  validation/          Untrusted proof producers, verification, independent replay.
  compact/             Independent 508-byte/276-node/780-byte refactor, controls,
                       authenticated fixtures, proof of accepted-trace equivalence.
  evidence/            Measurements, executed checks, audits, and PDF QA.
  reference/           Exact predecessor checker, selected pinned Lean snapshots,
                       inherited mathematical bridge sources, README, and license.
  CLAIMS.json          Supported claims and explicit limits.
  PROVENANCE.json      Pinned comparison and source identities.
  MANIFEST.sha256      Checksums for the delivered files other than itself.

VERIFICATION BOUNDARY

Universal mathematical claims have written proofs and independent reviews.
Executable tests validate implementations and attack essential guards.
There is no new Lean or Rocq verification, and the inherited Lean project
was not rebuilt. The primary tests contain matched old proofs of the tested
theorems, not a generic executable compiler for every opening proof. The
intermediate discharge variant has an executable translation to the old
checker. The compact refactor has a separate universal accepted-trace proof.

Full normalization is included in the trusted code. No uniform primitive
recursive normalization bound or internal universal evaluator is asserted.
Finite-runtime resource exhaustion may reject a mathematically valid long
proof. Further research questions appear in the report.

