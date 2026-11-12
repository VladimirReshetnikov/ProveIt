UNIFORM BINDING FOR INTUITIONISTIC PRIMITIVE RECURSIVE ARITHMETIC
Research note prepared for Vladimir Reshetnikov, 11 November 2026

START HERE

report.pdf is the mathematical report.
report.tex is the standalone LaTeX source, including the complete checker.
code/checker.py is the complete trusted Python module.

RESULT

A smaller complete realization of the current counter-aware Eq/D clause
calculus. Numerical terms have one ternary recursor R(n,a;i,u.h).
Successor is R(0,a;i,u.0). Both R and D bind exactly two variables in
their last child. One sorted traversal handles grammar/scope validation,
canonical zero-body erasure, and capture-avoiding binder opening.
The clause context length determines the free-parameter scope.

The five primitive schemes are Refl, counter evaluation, Use, Open, Close.
The report states every scheme and proves the full first-order iPRA
comparison, both formula composites, and both numerical composites.
Numerical domains are whole; equality is actual equality; numerical
composite isomorphisms have graph x=y.

MEASURED COMPLETE MODULES (CPython 3.12.14)

Program                       Bytes   Tokens   AST   Gzip-9
Exact incoming scalar C5        2283     741     826     818
Matched shared-walker scalar    2284     699     773     878
SELECTED UNIFORM-BINDING R      2238     693     764     866

The new module is smaller in every primary source coordinate than both
controls. Against the exact incoming control, savings are 45 bytes (1.97%),
48 tokens (6.48%), and 62 AST nodes (7.51%). Gzip grows by 48 bytes.
Gzip is maximum level 9 with timestamp zero and is informational.

The selected readable file is 2694 bytes (gzip-9 1124); the exact incoming
readable file is 2717 bytes (gzip-9 1036). All helpers, parsing, validation,
scope checks, and command-line logic are counted.

WHAT THIS DOES AND DOES NOT CLAIM

The arithmetic recursor, counter-evaluation equality theorem, and five-rule
architecture are inherited. The new contribution is a smaller complete
combination, with one shared sorted traversal, a matched control, and
portable proof recodings and verification. No new arithmetic axiom deletion,
absolute minimum, or priority outside the pinned snapshot is claimed.

The repository has shorter compact encodings, including a reported
516-byte codec and an incoming 820-byte native validator. This package
does not claim a corpus-wide checker-size record. Its positive comparison
is against the directly comparable current goal-directed clause checker.

The mathematical proof is written and independently reviewed. Finite tests
support the implementation. No new Lean or Rocq verification is claimed.
The existing scalar Lean project was inspected, not rebuilt.

REPRODUCE

    python3 reproduce.py --check-manifest
    python3 code/checker.py < examples/positive/used_induction_three.json
    python3 code/checker.py < examples/negative/false_equation.json

The positive certificate prints ACCEPT and exits zero.
The negative certificate prints REJECT and exits nonzero.

    python3 reproduce.py --pdf

also rebuilds the standalone report with pdfLaTeX and shell escape disabled.
Only the Python standard library is needed for code verification.
Pattern matching requires Python 3.10+; exact reported metrics use 3.12.14.
PDF rebuilding may alter PDF metadata and therefore its checksum.

VERIFICATION

37 accepted closed theorem fixtures; 37 exact-goal bidirectional round trips
(74 compiler direction checks); 56 rejected adversarial certificates;
186 CLI runs in ordinary and optimized Python; 16464 independent grammar
comparisons; 900 opening identities; 304 counter-evaluation semantic
identities; 160 generated open transport derivations; 12 additional
erased-body boundary rejections. Zero mismatches and zero skipped cases.

Reflexive goals intentionally ignore their unused proof payload, matching
the incoming baseline's contract. Every goal is validated before this leaf
rule. Normalization checks the original body before any canonical erasure.
Physical resource limits apply to sufficiently large certificates.

FILES

report.tex / report.pdf       Standalone source and compiled research report.
paper/                       Editable source sections.
code/checker.py               The entire trusted checker.
code/translate.py             Checked, untrusted proof recoders.
code/verify_examples.py       End-to-end theorem and adversarial replay.
code/audit.py                 Independent grammar and numerical audit.
code/measure.py               Complete-module measurement script.
examples/                    Accepted and rejected public JSON certificates.
tests/counter_source/         Inherited forward proof fixtures.
reference/                   Exact controls, attributed foundations, license.
evidence/                    Measurements, normalized/gzip modules, test results.
FORMAT.txt                   Certificate grammar and rule contract.
CLAIMS.json                  Machine-readable claims and exclusions.
PROVENANCE.json               Pinned source identities and SHA-256 checksums.
MANIFEST.json                 Integrity hashes of all payload files.
build_report.py              Reassemble standalone source.
build_pdf.py                 Compile PDF in a temporary directory.
reproduce.py                 Single reproduction entry point.

PROVENANCE

Repository: https://github.com/VladimirReshetnikov/ProveIt
Pinned commit: 0ebd0c6b358f38bb0ad2883faf775421599c8aae
Subtree: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

All six incoming archives in that snapshot were inspected.
No remote repository mutation was performed.

Inherited sources retain the supplied MIT No Attribution license.
New code and report material may be reused under the same terms.

