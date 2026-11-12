EQUALITY IN THE INITIALIZER: A SIMPLER PRESENTATION OF iPRA
Prepared for Vladimir Reshetnikov, November 11, 2026.

MAIN RESULT

The six-rule calculus replaces arbitrary-template equality transport
with replacement of an iterator's initializer. Zero iteration is
definitional, so the same rule includes root replacement. One iteration
applies any fixed numerical template, so all congruence is derived.

The equality instruction takes only two proof arguments. Its conclusion
is inferred from their conclusions; no template, counter, update body,
or occurrence path is transmitted as extra equality-instruction data.

The report proves exact sequent equivalence after canonical normalization,
including body extensionality and substitution coherence. It transfers
both full first-order iPRA interpretation composites. Domains remain
whole, equality remains actual equality, and the numerical composite
isomorphisms have graph x=y.

This is a new restriction of the equality interface, not a proof of
absolute minimality. The six-rule count was already attained by an
incoming report. The present transparent checkers are not new global
compressed-codec records.

START HERE

report.pdf                  Complete paper, including inherited foundations.
report.tex                  Standalone TeX: no external inputs or figures.
main.tex and sections/      Editable manuscript components.
code/seed_only.py            Complete selected strict proof checker.
code/general_context.py     Matched one-template control.
code/seed_checked.py         Explicit-shape implementation of the new rule.
code/translate.py            Untrusted proof translations in both directions.
code/FORMAT.txt              Exact certificate grammar and instructions.
code/certificates/           Positive and negative standalone JSON fixtures.
code/results.json           Detailed validation receipt and metrics.
shared_traversal/            Separate refactoring of the inherited checkers.
evidence/summary.json        Compact results and measurement summary.
evidence/source_provenance.json
                            Pinned identities of inherited foundations.
reference/                  Attributed arithmetic proofs and upstream license.
CLAIMS.json                 Exact claims and exclusions.
SHA256SUMS                  Checksums of the delivered files.

MATCHED MEASUREMENTS

                       Tokens   AST nodes  Normalized bytes   Gzip-9
One-template control     1202       1360              4029      1173
Initializer rule         1192       1347              3979      1175
Reduction                  10         13                50        -2

The byte reduction is 1.2410%. Normalization removes true docstrings,
runs ast.unparse, and appends one LF under CPython 3.12.14. Gzip level 9
uses timestamp zero and is informational. Both entire modules include
syntax/scope validation, substitution, all rules, and JSON input/output.

A separate shared-traversal refactoring reduces the incoming canonical-R
checker from 4611 to 4079 normalized bytes. It leaves that calculus and
its certificate language unchanged. This is not the source of the
matched 4029-to-3979 equality comparison.

The audited incoming compressed profiles already include 516 bytes for
a guarded compact codec and 870 bytes for a fully validated Eq/Q/D codec.
Their encodings differ; this package does not beat those global figures.

RUN AND REPRODUCE

From this directory:

  python3 code/seed_only.py < code/certificates/seed_only/direct_root_reflexivity.json
  python3 -O code/seed_only.py < code/certificates/seed_only/direct_root_reflexivity.json
  python3 reproduce.py
  python3 build.py

The first two commands print exactly ACCEPT and exit zero.
The third verifies the manifest when present, rebuilds matched sources,
and reruns both validation packages. It needs only Python's standard
library. The fourth assembles standalone report.tex and compiles PDF
with pdflatex and standard TeX Live packages.

The already assembled report.tex can also be compiled directly:

  pdflatex -interaction=nonstopmode -halt-on-error report.tex
  pdflatex -interaction=nonstopmode -halt-on-error report.tex
  pdflatex -interaction=nonstopmode -halt-on-error report.tex

Rebuilding PDF may change its checksum in a different TeX environment.
Verify the frozen archive first. Use --skip-manifest for reproduction
after an intentional edit. Other Python versions can change ast.unparse
measurements and gzip output.

EVIDENCE AND LIMITS

The final new-calculus suite passed 600 command-line checks, 30 closed
translation round trips, one open-context round trip, 180 independent
numerical substitution comparisons, and explicit nested-counter/capture
controls. The separate shared-traversal package passed 516 process checks,
480 numerical comparisons, and 2400 exact old/new traversal comparisons.

Independent assistant reviews checked the new mathematical arguments
and the strict checker's invariant. These are not external peer reviews
or proof-assistant certificates. The universal metatheorems are written
proofs; no new Lean/Rocq formalization is claimed. Existing upstream Lean
results were inspected, not rebuilt.

SOURCE

https://github.com/VladimirReshetnikov/ProveIt
Pinned commit: 6bf83d8765614b0af51b35747e07fb057d6b2f42
Path: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

The existing native logical bridge, scalar arithmetic, witness-directed
introduction, canonicalization idea, and fixed-position congruence
predecessors are explicitly attributed in the paper. The new contribution
is their specific initialized-scalar fusion, its premise-inferred equality
instruction, the four-node congruence expansion, and the matched checker.
