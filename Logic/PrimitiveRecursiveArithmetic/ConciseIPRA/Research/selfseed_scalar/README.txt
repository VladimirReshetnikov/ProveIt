SCALAR SELF-SEEDED ARITHMETIC AND THE iPRA CHECKER FRONTIER
Research prepared for Vladimir Reshetnikov with ChatGPT, 10 November 2026

RESULT AND LIMIT
----------------
The new arithmetic uses F(0;v.h)=S(h(0)) and
F(Sn;v.h)=h(F(n;v.h)). Its update binds only the previous state: it
has neither an independent initializer nor an old-counter argument.
The report gives a written whole-domain bi-interpretation proof with
full first-order intuitionistic PRA. It explicitly charges ordinary
intuitionistic first-order equality logic, successor injectivity,
0!=S0, a Boolean test of actual equality, and literal-equation induction.
Zero-or-successor coverage is derived, using a finite-case predecessor.

This is a new structural trade-off relative to the inspected drafts,
not a proof of a simplest axiomatization. No complete measured checker
for the new F arithmetic is supplied. The requested significant reduction
in complete-checker complexity remains unresolved.

Separately, modest compositions of existing checker techniques lower
the observed byte minimum from 558 to 554 and the observed AST minimum
from 296 to 291, in different programs. These implement the inherited
initialized-iterator arithmetic. Their measurements DO NOT measure the
new scalar self-seeded arithmetic.

START HERE
----------
ipra_selfseed_scalar.pdf   42-page report, full new proof, and attributed
                          appendices supplying the inherited kernel theory.
ipra_selfseed_scalar.tex   Standalone LaTeX: all fragments and listings inlined.
report.tex                Editable master source.
theory/selfseed.tex       Exact independently reviewed new arithmetic source.
CLAIMS.json               Machine-readable claims and qualifications.
PROVENANCE.json           Snapshot, attribution, and copied-source hashes.
MANIFEST.json             SHA-256 and length of every delivered payload file.

The separate review is by another assistant instance in the same session.
There is no Lean/Rocq formalization or external human peer-review certificate.
Finite numerical tests supplement the written proof; they cannot establish
soundness for all proofs or bi-interpretability in nonstandard models.

COMPLETE CHECKER PROFILES
------------------------
All measurements include the whole Python module and its JSON input and
verdict driver. The common Python/JSON runtime is excluded, matching the
inspected benchmark convention. Source is normalized by ast.unparse after
removing genuine docstrings. Gzip level 9 is informational only.

File                                      bytes tokens AST gzip9
reference/baseline_checker.py                566    264 308   351
reference/baseline_checker_bytes.py          558    264 310   345
reference/baseline_checker_joint.py          598    262 296   350
code/local_argument.py                      562    267 309   344
code/local_argument_bytes.py                554    267 311   339
code/local_loop_joint.py                    642    263 291   353
code/local_loop_joint_separate.py           641    262 293   354

The inherited coordinate minima were 558/262/296. The new family reaches
554/262/291, with different programs. No selected program improves all
three coordinates. These are achieved upper bounds on an unknown optimum,
not mathematical lower bounds on every possible presentation.

The two local_argument profiles have structurally recursive parsing on
finite JSON. The generic traversal in the loop profiles can recurse on
malformed nonempty strings until the real CPython stack limit rejects.
An ideal interpreter without that limit could diverge. The smaller AST
count therefore is not a claim of an equally small total abstract parser.

REPRODUCE OFFLINE
----------------
Use CPython 3.12.14 with zlib 1.3.2 for the recorded exact lengths.
No third-party Python package is needed for the finite checks.

    python3 verify_manifest.py
    python3 reproduce.py

reproduce.py remeasures all seven selected/baseline modules, verifies and
remeasures the 443 frozen corpus sources, regenerates proof cases using an
independent named producer, checks 332 full-process verdict expectations
(120 accepts, 212 rejects), and checks 5,509 source-arithmetic expectations.
The selected kernels are tested with ordinary and optimized Python.
A deliberately unsound control reproduces its false proof as expected.

The independent arithmetic transcription checks can also be repeated:

    python3 evidence/independent_review/check_source_macros.py

This gives another 1,248 finite expectations. Neither test script is part
of a trusted proof checker. No source compiler is being claimed executable.

Example of running a complete checker on a supplied positive certificate:

    python3 code/local_argument.py < tests/examples/I0_arbitrary_seed.json

Acceptance means exit status zero AND exactly the output line ACCEPT.
A traceback, nonzero exit, timeout, or an incidental word is rejection.
The kernels deliberately use no trusted assert statements.

BUILD THE REPORT
----------------
With PDFLaTeX and the packages listed in report.tex installed:

    python3 build.py

This regenerates the standalone TeX source and compiles the PDF in three
passes with shell escape disabled. The standalone TeX can instead be
copied to an empty directory and compiled directly with pdflatex.
PDF metadata timestamps may differ on a rebuild. Runtime versions may
change normalized or compressed lengths. Work on a copy when experimenting:
the delivered manifest applies to the original payload bytes.

SOURCE AND EVIDENCE
-------------------
The frozen comparison is VladimirReshetnikov/ProveIt at commit
76a2651601d17b34d46753f189ea026a21ce8d29, docs/drafts.
All 17 direct ZIPs were checked against GitHub Git-blob SHA-1 and byte
length. Recursive inspection found 32 distinct archive payloads and
443 distinct Python source files (2,239 occurrences). All 38 sources at
or below any candidate coordinate minimum were reviewed: three complete
checkers and 35 supporting utilities. See evidence/novelty_audit.txt,
evidence/source_manifest.json, evidence/corpus_verified.json, and
evidence/boundary_classification.json. reference/source_corpus contains
the exact 443 source byte strings, named by SHA-256; all_sources.json
maps their original archive locations.

The mathematical ancestor is the bounded-initializer B_epsilon basis,
whose update sees the old counter. The new theory removes that binder
but adds explicit successor injectivity, which B_epsilon derives.
Independent-seed removal, equality tests, bounded compilation, and
majorants already appear in the supplied work and are attributed.
The selected kernel compositions inherit lexical scopes, arity coding,
certified-zero normalization, and tuple-loop ideas from existing drafts.

reference/*.tex supplies the complete inherited initialized-iterator
theory used by the measured kernels. Those appendices retain historical
claims such as "new" referring to their original reports. Only the
inherited checker listing path was changed. The repository's MIT No
Attribution license is in reference/LICENSE-ProveIt.txt.

tests/failed_opaque contains explicitly failed experiments, not selected
checkers. One has an integer/float capture exploit proving 0=S0; its
stricter variant loses canonical universal-reflexivity certificates.
The exact attacks and their outcomes are retained for auditability.

Evidence files are research receipts, including historical absolute paths
and names of unselected experiments. Those paths are provenance, not
execution dependencies. All packaged reproduction commands use relative
paths derived from their own locations and need no network connection.

FURTHER QUESTIONS
-----------------
1. Can the new F theory derive successor injectivity without circularity?
2. Can all of its logic, equality, schemas, and parsing be implemented in
   a complete checker smaller than the inherited frontier?
3. Can finite-case source compilation receive practical size bounds?
4. Can the joint predecessor/coverage induction and the two-sentinel
   compiler be formalized in a proof assistant?

The report's conclusions distinguish the proved arithmetic construction,
the modest implementation results, finite evidence, and unresolved goals.
