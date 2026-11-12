A SMALLER CLAUSAL PRESENTATION OF iPRA
Prepared for Vladimir Reshetnikov, November 11, 2026

MAIN RESULT

Two complete related presentations are supplied.

1. code/raw_two_case.py: raw terms and ordinary capture-avoiding substitution.
   Five instruction tags: Refl, two-case Eval, clause Use, D elimination,
   and witness-directed D introduction. Eval's direct equality-composition
   branch is eliminated by a zero-iterator frame.

2. code/zero_base.py: zero-normal terms and normalizing substitution.
   Five instruction tags: Refl, one successor Eval, clause Use, D elimination,
   and introduction using progress exactly when its instantiated zero base
   is literally the formula 0=0. Otherwise it uses case introduction.
   This version has no separate equation-root or literal-witness mode test.

Both ordinary realizations are bi-interpretable and equiconsistent with full
first-order intuitionistic primitive recursive arithmetic. In both directions
the numerical domain is whole, equality is actual equality, and the numerical
interpretation composites are internally isomorphic by the identity graph x=y.

The written proof gives every primitive rule, recovers equality and intuitionistic
logic, recovers equation induction, and states both interpretation composites.
The inherited scalar arithmetic bridge is included in full as appendices.

The component reductions already exist in the pinned repository and its incoming
archives. This is their explicit integration, with smaller complete implementations
and checked proof transformations. It is not an arithmetic breakthrough or a claim
to an absolute minimum. The historical compact codecs remain smaller.

MEASURED COMPLETE CHECKERS

CPython 3.12.14; remove module docstring, ast.unparse, append one LF.
All parsing, grammar validation, scopes, opening, rules and CLI are counted.

Profile                                  Bytes   Tokens   AST nodes
Exact incoming raw clausal                3046      853       993
Matched raw control                       3003      842       984
Raw root-free proposal                    2956      837       977
Normal control retaining root Eval        2993      864      1006
Normal single Eval, witness guard         2948      853       992
Normal single Eval, fixed-zero guard      2948      852       987

The raw rule deletion alone saves 47 bytes, 5 tokens and 7 AST nodes against
the matched control. The exact upstream comparison includes a separately
identified 43-byte cleanup of a single-use constructor helper.

The fixed-zero companion is 8 bytes smaller than the raw proposal, but has
15 more tokens and 10 more AST nodes. Neither dominates the other in all
coordinates. The raw proposal is recommended if ordinary substitution or
the token/AST coordinates matter most; the fixed-zero companion is the
smallest-byte, simplest-arithmetic profile in this matched implementation family.

FILES

report.pdf              Complete report with inherited bridge and code listings.
report.tex              Standalone editable LaTeX source: no external inputs needed.
paper/manuscript.tex    Editable main assembly source.
build_report.py         Reassembles report.tex from source fragments and actual code.
reproduce.py            Replays all selected tests and measurements; --pdf also builds PDF.
code/raw_two_case.py    Primary raw standalone checker.
code/zero_base.py       Selected fixed-zero canonical standalone checker.
code/checker.py         Tested witness-guard canonical intermediate (comparison).
code/raw_translate.py  Raw root-branch elimination compiler, exact end sequents.
code/zero_base_translate.py
                        Canonical proofs translated to inherited independent checker.
code/validate*.py      Validation and certificate-generation programs.
code/FORMAT.txt         Exact certificate and scope conventions.
code/*certificates/     Checked positive certificates and relevant translated copies.
code/reference/         Independent inherited controls used for portable reproduction.
code/STATIC_AUDIT.txt   Invariant-based implementation audit and precise CLI caveats.
reference/bridge/       Five unchanged inherited arithmetic/logical proof fragments.
reference/BASELINE_README.md
                        Current proposal index at the pinned comparison revision.
evidence/              Measurements, validation summaries, provenance, PDF review.
CLAIMS.json             Precise machine-readable claims and limitations.
MANIFEST.json           SHA-256 checksums of distributed files other than this ledger.

RUN

From this extracted directory:

    python3 reproduce.py
    python3 code/raw_two_case.py < code/raw_certificates/used_induction_hypothesis.json
    python3 code/zero_base.py < code/zero_base_certificates/nonzero_witness_used_progress.json

Both selected checkers accept exactly a decoded JSON object with keys "goal" and
"proof". An accepted certificate prints ACCEPT and exits with status zero.
A rejected certificate prints REJECT and exits nonzero. The default JSON parser
uses last-key semantics for duplicate textual keys; decoded grammar and scope
validation are strict. The verifier does not depend on Python assert statements.

To rebuild the PDF:

    python3 reproduce.py --pdf

Or directly compile the delivered standalone source with two or three pdflatex
passes. Python validation requires only the standard library and no network.
PDF creation requires a normal TeX Live installation. Exact source-size metrics
are pinned to Python 3.12.14 and may change under a different ast.unparse version.

VALIDATION

Raw: 33 positives, 27 negatives, 120 ordinary/optimized CLI checks; 33 exact
sequent translations, reverse inclusions, and checks of the exact N+2k proof-node
formula. Canonical witness intermediate: 15 positives, 27 negatives, 84 CLI runs,
15 independent native translations and 6000 independent opening comparisons.
Selected fixed-zero companion: 17 positives, 28 negatives, 90 CLI runs and
17 accepted translations into the inherited seven-rule zero-normal checker.
All recorded runs have zero unexpected outcomes.

The tests exercise actual induction-hypothesis use, closure specialization,
compound formulas, repeated-variable congruence, normalization exposed by
opening, malformed counter rejection and eigenvariable escape rejection.

These finite implementation checks supplement written mathematical proofs.
No new Lean or Rocq formalization is claimed, and the upstream Lean project
was not rebuilt here. Python resource limits can reject sufficiently large
valid finite certificates. There is no advertised general raw-to-canonical
certificate compiler. Only the stated exact-syntax and canonical-native
translations are executable in this package.

PROVENANCE AND LICENSE

Repository: https://github.com/VladimirReshetnikov/ProveIt
Pinned revision: 831081033253cca2115196cf86bb99c77ed2aeae
Subtree: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA
Five incoming archives, as well as filed research and the Lean source index,
were reviewed. Exact paths and hashes are in evidence/provenance.json.
Inherited code and proof fragments carry the supplied MIT No Attribution
license, included in code/LICENSE-upstream.txt and reference/bridge/.
