RETAINED-VALUE VALIDATION FOR AN EXACT PRESENTATION OF iPRA
13 November 2026

START WITH ipra_retained_validation.pdf (editable source: .tex).

RESULT AND LIMIT
The recommended complete checker, code/checker.py, measures
309 significant Python tokens / 355 AST nodes / 582 normalized UTF-8 bytes.
One program is below every coordinate of the inspected exact-binding
envelope 316 / 358 / 591. The new three-profile envelope is 303 / 338 / 582,
attained by DIFFERENT programs.

THE REQUESTED GLOBAL FRONTIER CROSSING WAS NOT OBTAINED. These programs do
not beat the compact promised-syntax envelope 239 / 255 / 458, or the
seeded-context conventions reaching 238 tokens and 455 bytes. They refine
the existing native scalar calculus. No new arithmetic axiom deletion,
absolute simplest theory, or new Lean/Rocq verification is claimed.

WHAT CHANGES
The existing parity operation validates every retained numerical leaf.
An additional integer coercion is unnecessary. A floating-point source can
serve as an exposed template hole, but never as a retained variable or a
used substitution image. All public goals, checked majors and context
entries remain fully checked. A second change evaluates the source instance
of an elimination only when that elimination matches.

The mathematical theory is the existing Choice-DI/native scalar theory.
Its ordinary realization is bi-interpretable and equiconsistent with full
first-order intuitionistic primitive recursive arithmetic. Both numerical
domains are whole, equality is actual, and both numerical comparison graphs
are x=y. The paper states the primitive rules, logical macros, ordinary
axioms, translations, and the exact boundary of imported results.

INPUT AND ACCEPTANCE
Each checker reads a whole JSON document: a list with its closed public
Eq/D goal last. Earlier proof packets are popped from right to left.
code/checker.py takes four-field packets [s,u,t,m]. The two other profiles
take three-field packets and require their own fixtures; do not mix them.
The public grammar has actual binding slots, no dummy slots. Numerical
zero has code 1; slot j has code 3+2j. Public true is a permitted zero-code
alias. Public false and all public floats are rejected. Arbitrary unused
prefix records are allowed. Python's JSON numeric extensions are discussed
in the paper; they cannot survive a goal scan.

Acceptance means exit status zero and exactly ACCEPT followed by a newline.
Exceptions and resource failures reject. Normal and optimized (-O) Python
are supported. Mathematical completeness uses unbounded finite resources;
fixed interpreter/hardware limits can reject large correct proofs.

RUN
  python3 code/checker.py < examples/zero_computation.json
  python3 code/checker.py < examples/induction.json

Both print ACCEPT. The second certificate uses its induction hypothesis.
examples/false_equation.json and examples/float_goal.json reject.

REPRODUCE
  python3 reproduce.py
  python3 reproduce.py --tests
  python3 build_report.py

Use CPython 3.12.14 for exact source metrics. The first command verifies the
manifest and measures the complete programs. The second runs the focused
verification suites. The build script requires installed TeX, uses no
network, and can build a private format when system format caches are absent.
Regeneration can change logs/receipts/PDF bytes; verify the original manifest
before rebuilding. Finite tests support the written universal arguments;
they do not constitute formal verification.

FILES
  code/          Recommended checker, two profiles, readable expansion.
  examples/      Accepting and rejecting four-field certificates.
  tests/         Grammar, scope, malformed-data and process regressions.
  evidence/      Measurements, receipts, independent written reviews.
  reference/     Matched controls, exact upstream sources and attribution.
  STATUS.json    Machine-readable claim boundaries.
  PROVENANCE.json  Source snapshot and inspected incoming archive hashes.
  MANIFEST.sha256  SHA-256 integrity manifest, excluding itself.

SOURCE SNAPSHOT
  VladimirReshetnikov/ProveIt
  e0d702b905c74b74a23d045f8289b151bb8ebcff
  Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

Closing delta review: f25af53c682ea76c57b67c70c976bcaf836b0c91.
The new structural-parameters archive does not change the compact or
exact-binding envelopes compared above. Evidence and its archive hash are
recorded separately; the supplied upstream reference files retain their
original pinned snapshot.

The inherited Lean identification module is included as a source reference,
not as a standalone Lean project. Its transitive dependencies remain in the
pinned repository. No remote repository content was changed.
