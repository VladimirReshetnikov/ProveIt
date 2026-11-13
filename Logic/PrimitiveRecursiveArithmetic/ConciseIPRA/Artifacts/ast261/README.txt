A SMALLER CHECKING PRESENTATION OF iPRA: 261 AST NODES
Prepared for Vladimir Reshetnikov, 13 November 2026
===================================================

OPEN FIRST
  report.pdf
  report.tex + unary_relation_rigidity.tex

RESULT AND LIMIT
The complete direct-source compact checker has 247 significant tokens,
261 AST nodes and 557 normalized UTF-8 bytes under CPython 3.12.14.
The exact strongest identified AST control has 246 / 262 / 556.

The change reduces the observed AST minimum by ONE node. It adds one
token and one byte relative to that control, and does not improve the
separate 242-token or 469-byte records. The coordinate envelope changes
from 242 / 262 / 469 to 242 / 261 / 469, attained by DIFFERENT programs.
No new arithmetic axiom deletion, simultaneous improvement in all three
coordinates, global minimum or substantial mathematical simplification
is claimed. The stronger requested goal remains unestablished.

The program composes shared_leaf's strongest AST profile with the
default-initialization technique already used in uniform_terminals.
Moving k=0 into the definition-time expression d=(k:=0) gives the same
module state before any check. Every function body and later call is
unchanged. The report proves equality of subsequent checking behavior;
the inherited iPRA bi-interpretation and equiconsistency transfer.

MATHEMATICAL CONTENT
The report states the full native and guarded rule inventories and the
logical macros, describes both whole-domain interpretations and their
identity comparison graphs, and distinguishes inherited results from
the new implementation theorem. A second proved lemma restricts
countermodels to unary congruence: parameterized separation and
two-point interpolation force a compatible reflexive relation to be
identity or universal. Its constructive content and the missing
separation hypothesis in the weakened calculus are explicit.

RUN
  python3 code/checker.py < fixtures/global_guarded_induction_with_used_hypothesis.jsonl
  python3 measure.py
  python3 verify.py
  python3 verify_manifest.py
  latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex

The 14 original fixture streams yield 21 test inputs after seven false
goal substitutions. Two programs and ordinary/-O execution give 84
isolated runs, with zero unexpected outcomes. The structural test
checks that only initialization placement changes. Finite examples
support the written universal preservation proof, not replace it.

Check the delivery manifest before regenerating evidence or the PDF:
runtime metadata and PDF timestamps may change on reproduction. The
checker and verification scripts use only the Python standard library.

INPUT CONTRACT
JSON lines: a canonical closed guarded Eq/D public goal first, then one
three-field packet per consumed line. Certificate trees use exact integers
and lists. This compact profile assumes the alphabet and public grammar;
it is not an arbitrary-JSON/full-input validator. Unused trailing input
is allowed. Success is normal exit with exactly ACCEPT followed by LF.
Theoretical completeness uses unbounded execution; physical Python
processes have resource limits.

FILES
  code/checker.py                  New complete 261-node module.
  controls/checker_ast262.py       Exact current AST control.
  fixtures/                       14 inherited positive/negative streams.
  verify.py, measure.py            Offline reproduction scripts.
  evidence/                       Tests, metrics, audits, review and provenance.
  reference/article/              Full inherited unified article source.
  reference/lean/                 Selected interpretation theorem sources.
  CLAIMS.json, PROVENANCE.json     Machine-readable claims and sources.
  LICENSE.txt, MANIFEST.sha256     License and delivery checksums.

BASELINE
  https://github.com/VladimirReshetnikov/ProveIt
  Commit: 31e1e9220868788a85ca5fea351d7ab4097cfa4a
  Path: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

All 12 current incoming archives were considered. The expanded audit
parsed 4,716 .py/.py.gz source occurrences, 1,705 distinct normalized
modules, with zero parse failures; the new checker hash was absent.
This is a corpus comparison within a direct-source accounting class,
not a theorem excluding all other presentations.

The inherited theory, control, fixtures and reference article are credited
to the ProveIt research corpus. The original MIT-0 license is retained.
The reference article is not a new result of this package. The selected
Lean files were inspected, not recompiled, and are not a self-contained
Lean project. No repository mutation, commit or publication was made.
