A SMALLER CHECKER ENVELOPE FOR iPRA
==================================
Research package, 12 November 2026.

PINNED BASELINE

VladimirReshetnikov/ProveIt
62396b06020f794fa6dc01b4025a6a5db9d4d28a
Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

RESULT AND LIMITS

The empirical coordinatewise envelope falls from 256 significant Python
tokens / 278 AST nodes / 516 normalized bytes to 253 / 275 / 515.
THE THREE MINIMA ARE ACHIEVED BY THREE DIFFERENT PROGRAMS.

                           Tokens  AST nodes  Normalized bytes
Pinned token control          256        283               594
New token profile             253        280               599
Pinned AST control            260        278               602
New AST profile               257        275               607
Pinned byte control           265        306               516
New byte profile              264        304               515
Readable strict companion     580        666              2473

The new token and AST programs infer an elimination's required major when
its target instance matches the current goal. They still check that major.
The byte program replaces the matrix-root mode selector by 3 % len(a),
preserving the meaningful cases and using the documented truth aliases.

These are refinements of the inherited scalar-iterator presentation.
They do not delete a mathematical axiom or establish global minimality.
No single supplied program is below all three old coordinate minima.
The token and AST profiles each grow by five bytes against their own
matched controls. The compact profiles assume a canonical guarded public
goal; the strict companion includes that validator and exact JSON types.

The separate finite-menu obstruction is mathematical: restricting DI
witnesses to zero/parameters and QE targets to arbitrary compositions of
any fixed finite collection of PR operations loses native consequences.
The proof constructs a scalar majorant, an external nonstandard cut, and
a closed guarded lost theorem. It is a rule-sound two-carrier reading,
not a first-order model on a domain closed under every term operation.
It does not rule out all possible changed-domain bi-interpretations.

DELIVERABLES

ipra_smaller_envelope.pdf       Compiled research paper.
ipra_smaller_envelope.tex       Main editable LaTeX source.
sections/finite_menu.tex        Complete obstruction proof.
checkers/tokens.py             Complete 253-token program.
checkers/ast.py                Complete 275-node program.
checkers/bytes.py              Complete 515-byte program.
checkers/readable_strict.py    Larger readable public-input checker.
reference/checkers/            Three exact frozen comparison programs.
reference/foundations/         Attributed arithmetic and decoding sources.
reference/BASELINE_README.md   Exact inspected repository summary.
fixtures/                     Actual original, erased, repaired, attack,
                              and arity-test certificates.
validation/                   Reproducible focused check scripts.
evidence/                     Measurement and validation receipts.
PROVENANCE.json               Pinned source paths, hashes, and URLs.
CLAIMS.json                   Machine-readable claims and limitations.
MANIFEST.sha256               Archive file integrity ledger.

REPRODUCTION

    python3 reproduce.py
    python3 build.py

Use CPython 3.12.14 for exact ast.unparse-based measurements. The checking
and validation code use only the standard library. PDF rebuilding needs
pdfLaTeX and the packages named in the document preamble. build.py can
initialize a local pdflatex format if the installation lacks one, without
changing the system's format configuration.

Example invocation (the file is a local-scope, zero-neutral certificate):

    python3 checkers/bytes.py < fixtures/zero/computation_zero_local.json

Acceptance means successful exit and exact stdout ACCEPT followed by LF.
Exceptions reject. Python -O is supported; trusted checks are not asserts.
Unused prefixes remain permitted by the compact contract. The strict
companion validates all input leaves, including unused prefixes.

EVIDENCE

The final reproduction ran 631 checker processes, with no unexpected
outcomes. This includes 31 erased-major certificates, involving 7607 erased
fields, and actual repaired certificates accepted by the old controls.
It also covers missing-premise attacks, future-variable capture, context
leaks, ordinary versus optimized Python, formula arities, and the intended
empty-truth-alias rejection in the new byte profile.

These are finite tests. Universal claims rely on the written proofs and
the explicitly inherited arithmetic bridge. There is no new Lean/Rocq
verification and no claimed numerical or finite simulation proof of the
nonstandard-cut theorem. Runtime recursion/memory bounds can reject very
large certificates; the theoretical algorithms use unbounded finite
resources, as do the matched reference presentations.

ATTRIBUTION

The upstream material retains its original permissive license, included
under reference/LICENSE-upstream.txt and validation/LICENSE-upstream.txt.
The foundational arithmetic, guard translation, and compact decoder are
inherited work. Earlier constructed-major and prevalidation interfaces
are acknowledged in the paper. The finite-menu proof and the measured
refinements are presented with their precise scope, not as a claim of
priority over all mathematical literature.
