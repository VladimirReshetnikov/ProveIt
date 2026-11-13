LOCAL VALIDATION FOR SMALLER iPRA PROOF CHECKERS
13 November 2026
================================================

READ THIS FIRST
--------------
The recommended complete checker is code/checker_exact.py:

    312 significant tokens / 353 AST nodes / 588 normalized UTF-8 bytes

It improves every coordinate of the inspected exact-public envelope
316 / 358 / 591. The concrete intrinsic predecessor is 316 / 360 / 591;
the 358-node coordinate belongs to a different program with stricter
whole-document alphabet validation. Each new size triple belongs to one
complete program, including its reader, validation, and ACCEPT output.

A smaller sorted companion, code/checker_sorted.py, is 297 / 336 / 556.
It retains administrative padding slots and has completeness for canonical
encodings, not for every alias its parser admits. Prefer the exact checker.

THE STRONGER REQUESTED GLOBAL TARGET IS NOT MET. These programs do not beat
the compact promised-syntax coordinates 239 / 255 / 460, or 238 / 255 / 455
when seeded sequent input is admitted. These are observed finite-corpus
extrema, not proved universal complexity lower bounds. No absolute simplest
axiomatization or new arithmetic axiom deletion is claimed.

MATHEMATICAL CONTENT
--------------------
report.pdf and report.tex specify the complete existing native calculus:
scalar iterator terms, Eq/Q/D formulas, all eight primitive inference rules,
their side conditions, and explicit macros for ordinary intuitionistic logic.
The report gives the local validation and scope arguments for the new checker
and explains how the established native/iPRA bi-interpretation transfers.
Both numerical domains are whole, equality is actual, both formula round
trips are inherited, and both numerical comparison graphs are x=y.

tail_induction.tex is a separate mathematical alternative: forward iteration
together with equation induction allowing one changing parameter. It derives
the backward computation law and is admissible in iPRA using a single
literal-equation invariant. The report proves both interpretations and their
composites. No smaller checker is asserted for this alternative.

No new Lean or Rocq verification of Python semantics is claimed, and the
upstream Lean project was not rebuilt. The supplied identification module
is a reference to the inherited proof, not a standalone Lean project.

INPUT AND RUNNING
-----------------
The programs read one JSON array. Its last item is the public goal; earlier
three-field packets are consumed from right to left. Even a terminal proof
call consumes a packet. The exact public grammar follows the actual binders
of successor, iterator, and D. Numerical zero is code 1; true is a spelling
alias for that code. A public float, false, or unavailable variable is rejected.
Unused prefix data may contain arbitrary JSON objects. It is not an assumption.

Run with Python 3.12.14 for the exact published measurement convention:

    python3 code/checker_exact.py < examples/exact_zero.json
    python3 code/checker_exact.py < examples/exact_induction.json
    python3 code/checker_sorted.py < examples/sorted_zero.json

Each successful process prints exactly ACCEPT followed by a newline.
For example the complete minimal zero-computation certificate is:

    [[0,1,1],[[1,1,1],1]]

Its goal is I(0,0;u.0)=0. The false-goal example must reject:

    python3 code/checker_exact.py < examples/exact_false_zero_one.json

Exceptions and nonzero exits are rejection. No input is executed as code.
Python -O preserves every check. Mathematical completeness uses ideal finite
unbounded resources; a real process has finite memory and recursion limits.

REPRODUCE
---------
    python3 reproduce.py
    python3 reproduce.py --metrics-only
    python3 build_pdf.py

The test run recorded 1,486 normal/-O process checks with zero failures,
3,242 independent public-grammar comparisons with zero mismatches, and
exact recompilation of 14 canonical proof trees. It includes the readable
checker, malformed claims, false goals, genuinely unused opaque data,
numeric packet aliases, and future-witness capture attempts.

The full process receipt is evidence/reproduction.json. Running the suite
again overwrites that receipt; --metrics-only writes a separate file.
Finite tests support implementation review and do not replace the universal
proofs. The compiler and reproduction harness are not trusted by either
standalone checker.

build_pdf.py uses an installed TeX distribution. Where ordinary pdflatex
is already configured, two passes on report.tex suffice. The helper can
construct a private format/font map when caches are missing; it downloads
nothing and does not change system TeX configuration. The report requires
the included tail_induction.tex, code listing, and evidence/test_summary.tex.

CONTENTS
--------
report.tex, report.pdf         Complete paper and compiled version.
tail_induction.tex            Included mathematical alternative.
code/checker_exact.py         Recommended 588-byte complete program.
code/checker_sorted.py        556-byte sorted companion.
code/checker_readable.py      Standalone explanatory exact checker.
examples/                    Directly runnable positive/negative inputs.
fixtures/                    Frozen source and regression certificates.
compiler/, compile_examples.py
                             Untrusted, attributed canonical proof compiler.
controls/                    Exact predecessor and comparison sources.
reproduce.py                 Offline measurements and regression harness.
build_pdf.py                 Portable build helper for installed TeX.
evidence/                    Receipts, metrics, corpus census, and reviews.
reference/                   Pinned article sources and Lean identification.
CLAIMS.json                  Machine-readable claims and unresolved goals.
PROVENANCE.json               Source commit, archive members, hashes.
MANIFEST.sha256               Integrity hashes for the delivered file set.

SOURCE PIN AND COMPARISON
-------------------------
Repository: VladimirReshetnikov/ProveIt
Commit: e0d702b905c74b74a23d045f8289b151bb8ebcff
Project: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

The read-only census covers the integrated code and all seven then-current
incoming ZIPs: 3,803 Python/source-gzip occurrences, 2,126 distinct raw
contents, and zero parse failures. Exact normalized copies of the two new
programs were not found. That is a finite-corpus statement, not a historical
priority claim. General implementation mechanisms and the arithmetic basis
are explicitly inherited.

To repeat the source census with a separately obtained pinned checkout:

    python3 evidence/audit_frontier.py /path/to/ConciseIPRA

Its raw minima include non-checker scripts and rejected diagnostics and must
be classified by contract; simply taking the minimum of all .py files is not
a valid frontier computation. The retained qualified comparison is in the
paper and evidence/exact_comparison.json.

Upstream-derived source material retains the repository's supplied license
in reference/LICENSE. There was no modification or push to the repository.
