CONCISE iPRA: A 47-NODE PREDECESSOR AND SMALLER VALIDATED CHECKERS
Prepared for Vladimir Reshetnikov, 12 November 2026

RESULT AND LIMIT

This archive contains a 47-node fully expanded scalar predecessor, proved
using equation induction alone, and five smaller complete checkers for the
inherited native iPRA presentation.

The full requested result -- an axiomatization below the entire existing
compact checker frontier -- has NOT been established. The current compact
coordinate envelope (244 tokens, 267 AST nodes, 478 normalized bytes) is
unchanged. No absolute minimality or primitive axiom/rule deletion is claimed.

The current absorbing predecessor has 50 nodes. The new term has 47: three
nodes or 6% fewer. Its factor map has 28 nodes, compared with the current
30-node map. This changes the factor's structure and lies outside the fixed
outer-selector architecture for which the current package proves a 30-node
lower bound. It does not contradict that scoped bound or prove a global one.
The single-paired-binder universal benchmark drops from 60*n+4 to 57*n+4.
All definitions are fully expanded; no sharing or new primitive is hidden.

The absorbing orbit, selector cancellation and parameterized toggle lemma
are credited as prior work. The additional steps are placing the ramp payload
inside that toggle, and reversing the saturation comparison. The final
comparison includes all thirteen incoming archives at the snapshot below,
including the three added during this research run.

Complete checker metrics, CPython 3.12.14, ast.unparse plus one newline:

  program                       tokens   AST nodes   normalized bytes
  checkers/code/native_tokens.py   321       371             618
  checkers/code/native_ast.py      323       369             622
  checkers/code/native_bytes.py    334       380             596
  checkers/code/strict_size.py     330       380             638
  checkers/code/strict_bytes.py    340       385             621

Different programs attain different coordinates. The native-goal envelope
improves (324,370,607) -> (321,369,596). The native-goal plus whole-input
alphabet envelope improves (334,386,628) -> (330,380,621).
These are two stronger validation contracts than the compact interface.
Native-only mathematical soundness retains the inherited integer/list
proof-alphabet promise; strict programs check that alphabet themselves.
The strict programs also compose an attributed rejection-sentinel refinement
from the current absorbing_orbit package.

MATHEMATICAL STATUS

report.pdf / report.tex specify every primitive axiom schema and inference
rule, prove the new predecessor equations, prove the checker transformations,
and explain the composition with the inherited full first-order intuitionistic
bi-interpretation. The numerical interpretation has whole domains, actual
equality and identity composite graphs. Equiconsistency is a corollary.

The new results have written proofs and reproducible executable checks.
They are not newly formalized in Lean or Rocq. The existing Lean development
and arithmetic bridge are attributed dependencies and were not rebuilt here.
Independent review means a second review within this research run, not
external peer review. Finite tests do not substitute for universal proofs.

FILES

  report.tex / report.pdf         Main paper, complete claims and limits.
  mathematics/predecessor47.tex   New equational construction and prior credits.
  mathematics/predecessor47.py    Literal AST builder, node counter, evaluator.
  mathematics/*_ast.json         Fully expanded term and exact node inventory.
  mathematics/*_expanded.txt     The expanded scalar term in readable notation.
  mathematics/*_results.json     Finite arithmetic test ranges and results.
  mathematics/reference50/       Exact current control and its scoped bound.
  mathematics/verify_reference50.py  Source hashes and AST alpha-equivalence.
  checkers/code/                 Five complete standalone acceptance programs.
  checkers/controls/             Their exact frozen predecessors.
  checkers/fixtures/             Genuine proofs and malformed/capture attacks.
  checkers/PROOF.txt             Phase, evaluation-order and sentinel proofs.
  reference/                    Attributed inherited proof sources/incumbents.
  evidence/                     Intake, hashes, measurements and review receipts.
  CLAIMS.json                    Machine-readable success/failure boundaries.
  PROVENANCE.json                Source identities and licensing.
  MANIFEST.sha256                SHA256 of every other delivered file.

REPRODUCTION

Run from the extracted archive root:

  python3 reproduce.py
  python3 build_pdf.py

reproduce.py checks the distribution manifest, measures nine frozen incumbent
modules, verifies the five exact source transformations, reruns the arithmetic
artifacts and verifies the exact current 50-node control in a temporary copy.
By default it also reruns all 880 checker process executions there. It does
not overwrite the delivered evidence. Use --quick to select one positive
and one negative fixture per checker instead of all fixtures (20 executions).
Use --skip-manifest only after an intentional local edit; this is a support
script option, never an option of a measured proof checker.

The Python tools require only the standard library. Exact source metrics use
Python 3.12.14. The PDF builder needs installed pdfLaTeX sources and the
packages listed in report.tex. It has a private-format fallback for an
incomplete filename cache; it downloads nothing and never enables shell
escape. Reference chapter fragments are reading dependencies, not standalone
build targets.

An individual strict proof check:

  python3 checkers/code/strict_bytes.py < checkers/fixtures/strict_proofs/computation_zero_local.json

Success is normal process termination with exactly ACCEPT and a newline.
Failure, different output, or nontermination is not acceptance.

PINNED COMPARISON

https://github.com/VladimirReshetnikov/ProveIt
Final inspected commit: 2c7617bb03bbbb15a4534c5468f7df8da22c7ab4
Initial inventory: b9aa36102e523213ae956b474ec651bfde3e5665
Directory: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

All thirteen incoming archives were authenticated against their Git blob
hashes and reviewed for relevant proposals. Exact earlier and later receipts
are retained separately; archive_audit.json combines all thirteen identities.
The selected incumbent programs are included for offline remeasurement.
The audit does not certify every historical proof or exhaustively classify
all possible proof checkers.

Inherited and new material use the attached MIT No Attribution license.
