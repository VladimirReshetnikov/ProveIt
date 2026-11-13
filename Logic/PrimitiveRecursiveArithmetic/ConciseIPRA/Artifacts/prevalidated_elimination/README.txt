PREVALIDATED ELIMINATION FOR iPRA
Research prepared for Vladimir Reshetnikov, November 10, 2026.

RESULT AND LIMIT
----------------
This package obtains a smaller complete proof checker for the inherited
full first-order intuitionistic PRA presentation. It does not establish
the requested significant new simplest axiomatization.

The comparison is pinned to ProveIt commit
76a2651601d17b34d46753f189ea026a21ce8d29, all 17 current docs/drafts ZIPs.
The recursive census covers 3,557 Python occurrences and 443 distinct sources.

Whole programs (CPython 3.12.14, zlib 1.3.2):
                                     bytes  tokens  AST  gzip-9
Old coordinate envelope                 558     262  296      --
code/checker.py: explicit list test      547     263  307     347
code/checker_bytes.py: compact list test 539     263  309     342
code/checker_structure.py: qualified     576     261  292     345

The old and new envelopes combine different files. No single delivered
program beats all three old coordinate minima. The explicit-list and byte
profiles terminate structurally on finite parsed inputs under the ideal
resource-unbounded reading. The generic structural profile retains its
inherited malformed-string/finite-runtime qualification. Gzip is FYI.

OPEN FIRST
----------
ipra_prevalidated_elimination.pdf  Complete report and inherited proof bridge.
ipra_prevalidated_elimination.tex  Standalone LaTeX, all inputs expanded.
report.tex, theory/, reference/    Modular authoring sources and attribution.
AXIOMS.txt                        Compact complete primitive inventory.
code/readable_checker.py           Executable explanatory transcription.
CLAIMS.json                       Exact status, measurements, and limitations.

NEW CHECKER DISCIPLINE
---------------------
Fix an elimination template and both instances before proving its major.
The major is still checked before continuation. Its successful None return
is reused to construct the exported assumption. Non-real internal 1j cannot
equal any JSON value, so it safely replaces a disabled matcher; internal 0j
fails if a missing numerical substitution is used. Neither is an arithmetic
constant in the object theory. The byte saving from the exact old parent is
19 bytes, decomposed into 11 for scheduling/folding, 6 for the guarded matcher,
and 2 for the missing-image spelling.

The canonical native consequence relation is preserved, with whole-domain
bi-interpretability and equiconsistency with iPRA. Raw JSON acceptance is
NOT identical: examples demonstrate incomparability in both directions.
The proofs are written mathematics, not Lean or Rocq formalizations.

SEPARATE MATHEMATICAL RESULT
----------------------------
Positive-iteration terms over standard N are constants, projections, or
strictly increasing in every essential coordinate and at least that input
plus one. A finite dependency-cycle proof excludes every nontrivial
term-defined operation with a two-sided identity on a finite-tuple domain
with actual equality. An explicit integer-difference quotient shows why
quotient equality is a substantive exception. This does not establish an
interpretation of iPRA in the whole eager theory: its inherited finite model
collapses that quotient. Proofs and transcription checks are included.

REPRODUCE OFFLINE
----------------
  python3 reproduce.py
  python3 build.py
  python3 package.py

Python 3.12 is the exact measurement runtime. The checkers require Python
3.8+ and the standard JSON library. PDFLaTeX with the packages declared in
report.tex is required to rebuild the PDF. No network is needed.

To check a single packet:
  python3 code/checker.py < packet.json
Acceptance requires exit status zero AND exactly ACCEPT on standard output.
All checking assertions remain active under Python -O; the kernels contain
no trusted assert statements. Input data is never executed as Python code.

TESTS AND TRUST BOUNDARY
-----------------------
The selected small programs import only JSON. Producers, source normalizers,
experimental checkers, examples, and receipts are untrusted support artifacts.
Tests cover genuine induction, retained hypotheses, witnesses, closures,
transport, zero-computation repair, malformed scopes, failed majors,
forbidden compound induction, and the new sentinel guard. Unsafe mutations
are constructed only in temporary directories to demonstrate guard necessity.
Finite tests do not replace the universal written proofs.

The experimental synthesis programs are larger, separately labeled, and
are not claimed as established replacements for the selected kernels.
The files in reference/corpus_sources preserve historical source bytes for
static measurement. They are not invoked and may contain obsolete paths.

ATTRIBUTION
-----------
Arithmetic and logical foundations, the arity codec, certified-zero repair,
and original proof producers come from the supplied ProveIt drafts.
The five mathematical bridge appendices are copied unchanged with exact
source hashes and attribution; the repository's license is included.
