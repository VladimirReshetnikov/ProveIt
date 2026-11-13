IPRA: CHECKER COMPOSITIONS AND A PADDING-SLOT OBSTRUCTION
=======================================================

13 November 2026. Start with report.pdf; its complete source is report.tex.

The requested new axiomatization strictly below the existing complexity
envelope was NOT obtained. No globally simplest theory or checker is
claimed. This archive contains the reproducible partial results below.

The main mathematical finding is a new completeness obstruction for the
broader sorted public grammar. It admits [[5],[1]], ordinarily S(0)=S(0),
but the native proof protocol accepts NO finite certificate for that
spelling. Interpreting only the second successor padding slot as an
arbitrary constant c preserves successful-run soundness; that goal becomes
S(c)=S(0). This does not contradict canonical completeness or the inherited
bi-interpretation with iPRA. See report.pdf, Section 6, and the two
independent proof notes in proofs/.

This directory contains four new implementation compositions of the current
ConciseIPRA calculus. They remove no arithmetic axiom or logical inference
rule. Their inherited ordinary realization is the existing iPRA presentation.

The recommended exact-syntax entry point is code/checker_exact.py. It includes
the complete byte587 inference core and a readable exact encoder-image
validator in one standalone file. Its only import is the standard JSON
library. All of its source is charged: 581 tokens / 641 AST nodes / 1424
normalized bytes, gzip-9 631 bytes. It makes no size-record claim.

Result, CPython 3.12.14
---------------------
                                tokens    AST    normalized bytes   gzip-9
code/checker_tokens304.py          304     359          652           391
code/checker_joint311.py           311     350          685           402
code/checker_ast345.py             328     345          665           401
code/checker_bytes587.py           325     367          587           386

The pinned repository, including its four incoming ZIP archives, has
coordinate envelope 306 / 348 / 589 for profiles that validate sorted
syntax and the full parsed alphabet. These programs
give 304 / 345 / 587, attained by DIFFERENT programs. No program here is
below all three prior coordinates. The smaller promised-grammar compact
envelope 239 / 255 / 461 remains unchanged. These observed corpus minima
are upper bounds on an unknown optimum, not mathematical lower bounds.

All four programs parse one whole JSON document and enforce the complete
integer/list alphabet, including unused prefixes. Their entry traversal
checks the existing P^ed_1 sorted public Eq/D grammar, using numeral zero
code 1. That validator permits dummy-slot aliases. The theorem is soundness
for every accepted JSON input, and completeness for CANONICAL encodings of
the ordinary native theorems. It is not a claim that every admitted alias
of an ordinary theorem has an accepted certificate. Canonical encodings
refer only to genuine numerical binders, not to dummy padding slots.

checker_exact.py enforces that canonical restriction itself. It carries a
Boolean availability mask for every padding/genuine binder position:
D adds two genuine slots, successor two padding slots, each iterator counter
and seed one padding slot, and the iterator body one genuine slot. It rejects
both [[3],[1]] and [[5],[1]] as noncanonical, as well as dummy references in
iterator counters and seeds. It admits actual bound-variable references.
The inference core is AST-identical to checker_bytes587.py, and its reader
still validates the entire parsed integer/list alphabet.

What changes
------------
The first three profiles compose the already studied eager opening
    (d mod 2) * open(image)
with an empty-list administrative premise and the newest validated
three-field/structural-pattern profiles. The image is evaluated even when
d is even, which preserves missing-image scope rejection during validation.
The administrative resource [] has the ordinary formula reading 0=0.

The byte profile composes the normalized-computation-terminal transformation
with the existing eager 589-byte profile. A no-image scan of the candidate
computation equation supplies the canonical zero representation throughout,
so the explicit zero repair in its left counter is deleted.

The semantic components are inherited, but these complete source
compositions are absent from the audited pinned source census. This is a
source-composition result, not a claim of a new mathematical axiomatization
or literature-wide priority.

Interfaces
----------
Every program reads a JSON array as a stack; the last item is the public
goal. The token and joint programs consume three-field [source, mode/seed,
template] packets. The AST program consumes four-field [major, source,
mode/seed, template] supply packets. The byte program consumes four-field
[source, seed/mode, template, major] packets. Unused prefixes are allowed
but still checked for the exact integer/list alphabet.

Acceptance is normal exit with exactly ACCEPT followed by a newline.
Exceptions reject. Mathematical completeness uses arbitrarily large finite
resources, not a fixed machine's memory or recursion limit.

Reproduce
---------
Check archive integrity BEFORE regenerating evidence or the PDF:

    python3 check_manifest.py

Then reproduce the implementation and mathematical audit evidence:

    python3 verify.py
    python3 verify_exact.py
    python3 research/verify_second_dummy.py
    python3 research/audit_second_dummy.py
    python3 code/checker_exact.py < fixtures/exact_zero_computation.json

Compile the paper with a normal LaTeX installation:

    pdflatex -interaction=nonstopmode -halt-on-error report.tex
    pdflatex -interaction=nonstopmode -halt-on-error report.tex

Regeneration may legitimately change runtime metadata and PDF timestamps.
The original SHA-256 manifest should therefore be checked first.

The verifier checks the exact stated AST transformations against frozen
controls, measures the complete modules, and runs 420 isolated
candidate executions with ordinary Python and Python -O. There are 65
three-field cases (16 positive), 37 supply cases (16 positive), and 43
terminal cases (14 positive). Cases include used induction hypotheses,
compound implication, transport, computation, whole-input type rejection,
false equations, future-scope capture, context leaks, and missing packets.
All 420 executions passed. Finite tests do not prove universal correctness.

The exact standalone checker adds 13 targeted grammar checks and 102
ordinary/-O executions across 51 cases, with no failures. The cases include
all 14 canonical terminal positives, noncanonical successor/iterator dummy
aliases, and an explicit zero-iteration certificate whose body genuinely
uses its bound accumulator. These tests do not assert that all possible
proofs of a dummy-alias goal fail; the obstruction is a separate theorem.

Canonical recoding changes only the administrative marker. For three-field
certificates, [0,[],w] and [0,0,w] become [[],[],w] and [[],0,w]. Numerical
zero code 1, closure-specialization source 0, computation predecessor 0,
and mode fields remain unchanged. The four-field translator replaces an
exact zero major marker by []. The byte profile additionally rotates each
four-field record. Applying these translations to malformed fixtures is
only a perturbation test, not a raw-certificate equivalence claim.

Files and provenance
--------------------
code/       Complete measured modules and deterministic gzip-9 copies.
report.tex, report.pdf: complete research article and compiled PDF.
controls/   Exact current matched control files and gzip-9 copies.
fixtures/   Attributed upstream regression cases, compactly serialized.
proofs/     The precise inherited arguments used by the composition.
evidence/   Source provenance, measurements, and executable receipt.
research/   Independent padding audit and failed normalization shortcut.
reference/Lean/: selected unmodified interpretation source files, not a
complete independently buildable Lean project; no rebuild is claimed.
CLAIMS.json: machine-readable claim boundaries.
MANIFEST.sha256: integrity hashes for the distributed files.

Repository: VladimirReshetnikov/ProveIt
Commit: 7a7633980dbca7f599322a5e7f1e65fb1cddb7c8
Subtree: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

The controls and fixtures come from the pinned incoming packages
ipra_validated_three_field_2026-11-13.zip and
ipra_checked_reduction_2026-11-13.zip. Their original paths and SHA-256
identities are recorded in evidence/provenance.json. The upstream MIT No
Attribution license is included. No remote repository files were modified.

No new Lean/Rocq verification of Python semantics or rebuild of the full
inherited mathematical bridge is claimed.
