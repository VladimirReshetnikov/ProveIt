iPRA: scope elimination and a frontier audit
==========================================
Prepared for Vladimir Reshetnikov, 12 November 2026.

OUTCOME
The requested below-frontier axiomatization was not established.
This package is an honest research result: a pinned audit, an exact
implementation transformation, a written simulation proof, and a concrete
counterexample to a tempting cheaper shortcut. It changes no arithmetic
axiom or inference rule.

At the pinned repository snapshot, the surveyed compact envelope is
248 significant tokens / 270 AST nodes / 487 normalized bytes, attained
by three different complete programs. The exact transformation here has
267 tokens / 303 nodes / 500 bytes, against its matched control's
267 / 298 / 492. It therefore does not meet the requested threshold.

READ FIRST
report.pdf is the main report; report.tex and scope_invariant.tex are its
LaTeX sources. The report states the native and guarded rules explicitly,
identifies the inherited full bi-interpretation, proves the exact scope
invariant, explains the failed shortcut, and lists further research questions.

FILES
implementation/context_floor.py   Complete exact transformed checker.
implementation/baseline492.py     Exact normalized matched upstream control.
implementation/readable.py        Standalone readable implementation.
implementation/verify.py          Regression and transformation checks.
implementation/verification.json  Full test receipt.
implementation/fixtures/          42 distinct inherited input fixtures.
implementation/experiments/       Deliberately UNSOUND diagnostic and attack.
reference/                       Pinned controls, inherited proof sources,
                                 upstream README and original license.
evidence/                        Measurements, archive hashes, audit receipts.
measure.py                       Recompute delivered whole-module sizes.
audit_sources.py                 Remeasure 352 pinned inspected sources,
                                 without executing any of them.
verify_manifest.py               Check the delivered-byte manifest.
CLAIMS.json                      Explicit claims and nonclaims.

REPRODUCE (from this directory, no network needed)
  python3 verify_manifest.py
  python3 measure.py
  python3 audit_sources.py
  python3 implementation/verify.py
  latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex

Source metrics were computed using CPython 3.12.14. The PDF requires the
LaTeX packages listed at the start of report.tex. Rebuilding the PDF changes
metadata; verify the delivery manifest before rebuilding.

CHECKER CONTRACT
The compact public interface assumes canonical closed guarded Eq/D goals
and intended exact integer/list certificate trees. It is not a full JSON
alphabet or public-grammar validator. Some off-contract fixtures are used
only to compare operational behavior. Acceptance is exit status zero with
exactly ACCEPT followed by LF. An unused prefix of packets is permitted.
The theory claims concern the guarded public language, not all raw aliases.

PROVENANCE
Repository: https://github.com/VladimirReshetnikov/ProveIt
Commit: 36d37fc1071fe289371f6bcd7dcfa0eac593a5a6
Path: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA
The native/guarded theory, codec, controls and fixtures are inherited.
Original license: reference/LICENSE-ProveIt.txt.

LIMITS
Finite tests are not a soundness proof. The written new result proves
checker-to-checker equivalence; the arithmetic bi-interpretation and
upstream checker-to-calculus correspondence are inherited. No new Lean or
Rocq verification, no global simplicity minimum, and no below-frontier
construction is claimed. The observed envelope is not a mathematical
lower bound.
