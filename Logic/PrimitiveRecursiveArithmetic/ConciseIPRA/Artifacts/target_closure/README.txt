TARGET-DIRECTED CLOSURE AND SMALLER TYPED CHECKING FOR iPRA
Prepared for Vladimir Reshetnikov - November 11, 2026

START WITH report.pdf. The source report.tex is standalone.

WHAT WAS ACHIEVED

1. A new seven-rule target-directed progressive calculus T. Its closure
   elimination supplies one numerical target, without the old orbit term.
   Written proofs give exact consequence equivalence with the incoming
   uniform_progress calculus on all Eq/Q/D formulas and arbitrary contexts.
   Composing with the attributed existing bridge gives whole-domain,
   actual-equality bi-interpretability and equiconsistency with iPRA,
   including both formula composites and numerical identity graphs x=y.

2. A smaller complete checker for the EXISTING conditional Choice-DI theory.
   Exact integer/list certificate typing moves to a lexical JSON gate.
   The kernel and canonical public grammar are unchanged. The complete
   module is 895 normalized bytes, 399 tokens, 453 AST nodes, gzip-9 512,
   compared with 1039 / 442 / 502 / 547 for the frozen typed control.
   The more explicit error-reporting version is 963 bytes.

THE LIMITATION IS MATERIAL

The 895-byte program is NOT an implementation of the new T calculus.
The new T checker has 4532 normalized bytes, versus 4553 for its exact
orbit comparator; the existing witness-sensitive checker is smaller at
4456 bytes. The distinct compact canonical-goal frontier (256 tokens /
278 AST nodes / 521 bytes, achieved by three different programs) is not
improved. This work does not establish an absolutely simplest theory or
a mathematical reduction below every current proposal.

FILES

  report.pdf, report.tex       Main report and standalone LaTeX source.
  foundations.pdf, .tex        Attributed inherited proofs, compiled together.
  report_main.tex, sections/   Editable modular main source.
  foundations_main.tex        Editable modular foundations source.
  code/lexical_compact.py      Recommended 895-byte full typed Choice-DI checker.
  code/lexical_explicit.py     Same lexical theorem with descriptive rejection.
  code/target_checker.py       Complete direct checker for the new calculus T.
  reference/                  Frozen comparison modules and upstream sources.
  tests/                      Certificates, independent producers and regressions.
  evidence/                   Metrics, gzip streams, audit and verification receipts.
  CLAIMS.json                 Machine-readable result and qualification ledger.
  PROVENANCE.json              Implementation-source provenance.
  evidence/provenance.json    Repository snapshot and four incoming blob identities.
  MANIFEST.sha256             Checksums of every other delivered file.

REPRODUCE

From the extracted directory, with Python 3.12 or a compatible later version:

  python3 reproduce.py

This uses only the Python standard library. It remeasures all complete
checkers, writes deterministic gzip streams, verifies AST identity of the
unchanged compact proof kernel, and reruns the delivered tests. The recorded
run used CPython 3.12.14 and zlib 1.3.2 and had 652 subprocess executions,
zero mismatches, 3068 lexical-gate checks per profile, 30 closed target cases,
5 open-sequent controls, and 600 independent substitution/lift checks.

Examples of accepting certificates:

  python3 code/lexical_compact.py < tests/lexical/atomic_case_empty_list.json
  python3 code/lexical_compact.py < tests/lexical/atomic_progress_integer_zero.json
  python3 code/target_checker.py < tests/target/anchored_closure_at_successor.json

Acceptance requires normal exit and exactly ACCEPT followed by a newline.
Every exception is rejection. Resource exhaustion is not acceptance.
The universal equivalence claims use ideal finite certificate semantics;
stack, parser, memory, and integer-size limits can differ operationally.

To regenerate the standalone TeX sources and compile both documents:

  python3 build.py

A normal pdflatex installation with the packages named in the sources is
required. Each standalone .tex can also be compiled directly twice with
pdflatex. The delivered PDFs were compiled from the delivered sources.

VERIFICATION STATUS

The new mathematical and parser-preservation theorems are complete written
proofs with independent same-run review. Tests are implementation evidence,
not substitutes for those proofs. No new Lean/Rocq verification is claimed.
The existing Lean bridge endpoints were read, not rebuilt in this environment.

The compact family uses Choice-DI: the field u=[] selects cases, while u=0
selects progress at equations. Both remain available at every witness.
The target-calculus family instead has root-directed introduction and the
progressive atomic reading specified in the report. Do not mix certificates
or semantics across these families.

SOURCE SNAPSHOT

  https://github.com/VladimirReshetnikov/ProveIt
  76697262071ada91f29c14d9cf3801a64dacb994
  Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

Five inherited scalar foundation sources were checked byte-for-byte against
their current Git blob identities. The source restriction proof and two Lean
endpoint files were retrieved at the pinned commit. Copied upstream material
retains the repository's MIT No Attribution license and explicit attribution.
