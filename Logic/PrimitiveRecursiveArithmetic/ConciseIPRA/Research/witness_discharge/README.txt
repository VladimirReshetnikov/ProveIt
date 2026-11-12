iPRA WITH EQUALITY AT WITNESS DISCHARGE
======================================
Prepared for Vladimir Reshetnikov, November 11, 2026.

START HERE
----------
report.pdf is the complete mathematical report.
report.tex is its standalone editable LaTeX source, with all mathematical
appendices and the complete checker listing embedded.

RESULT
------
The delivered presentation has three inference families (Use, Intro, Name)
and one explicit fixed reflexivity axiom clause. The new Name inference
combines equality substitution with existential-witness discharge:

  prove D B;
  in the fresh witness b's clause context, prove b=t and F;
  export nf(F[t/b]) if this normalized formula has no free b.

The target t may contain b, and t=b recovers ordinary elimination. A finite
naming packet recovers arbitrary term transport, then full formula transport.
The report proves exact open-sequent equivalence with the existing separate-
rule calculus. Composing with the included arithmetic and logical bridge
gives bi-interpretability and equiconsistency with full first-order iPRA.
Both numerical domains are whole; equality is actual equality; both numerical
composite isomorphisms have graph x=y.

The native syntax contains normal scalar iterator terms and Eq/D formulas.
Computation normalization is part of the specification and measured checker.
No extra arithmetic, logical, equality, induction, or case rules are implicit.

WHAT IS NEW
-----------
The new mathematical contribution is the uniform equality-aware discharge
rule, removing the separate equality instruction. The scalar arithmetic,
D binder, full normalization, naming packet, zero-witness repair, and initial
reflexivity clause are inherited mechanisms and are credited explicitly.
The scoped search covered all filed research texts and the six incoming
archives at the pinned snapshot; it is not a universal priority claim.

COMPLETE CHECKER MEASUREMENTS
-----------------------------
CPython 3.12.14, module docstring removed, ast.unparse, one final LF.
Gzip uses maximum compression level 9 and timestamp zero (informational).

                                        Bytes Tokens AST  Gzip9
Selected witness discharge               2273   732   813   903
Matched separate rules                   2362   769   841   917
Witness discharge with explicit fuel     2486   777   868   967
Matched separate rules with fuel         2575   814   896   980
Incoming single-evaluation checker       2283   741   826   818

The matched comparison isolates the rule fusion: 89 bytes, 37 tokens,
28 AST nodes and 14 gzip bytes saved. The incoming single-evaluation
comparison also changes normalization and is not an isolated experiment.
The readable selected source is 3593 bytes / 1566 gzip bytes, including its
interface documentation and comments. All raw measurements are recorded.

This is a structural and matched-checker improvement, NOT a proof of absolute
minimality. It does not beat the repository's separate 516-byte compact codec.
There is no claim of new Lean/Rocq verification of the complete result.

NORMALIZATION AND THE OPTIONAL FUEL VERIFIER
--------------------------------------------
Every fixed scalar term denotes a primitive-recursive function. Uniform
normalization on all finite term codes is total recursive, not primitive
recursive. No internal uniform evaluator or totality axiom is added to iPRA.

code/checker_fuel.py uses the same three inference families and adds a
nonnegative integer fuel field. It decrements fuel at every recursive
normalization and proof-checking entry. The bounded certificate predicate
is primitive recursive. Sufficiently large finite fuel verifies every
unbounded certificate, so the two interfaces have exactly the same theorems.
The matched fuel control contains the identical budget mechanism.
These algorithmic completeness claims idealize unbounded finite storage.
Concrete Python stack or memory limits can reject a mathematically valid
certificate even when the supplied fuel would suffice in that idealization.

REPRODUCE
---------
Python verification needs only the standard library.

  python3 verify_manifest.py
  python3 reproduce.py
  python3 code/checker.py < validation/examples/successor_congruence.json
  python3 code/checker.py < validation/reject_examples/false_equation.json

The first theorem prints ACCEPT and exits zero; the false equation prints
REJECT and exits unsuccessfully. To use the bounded checker, add a fuel
integer to a valid certificate and run code/checker_fuel.py.

To rebuild the PDF with an installed TeX Live distribution:

  python3 build_pdf.py

The PDF source is standalone. The script compiles in a temporary directory
with shell escape disabled. Rebuilding can change PDF metadata and its hash;
the checksum manifest describes the originally delivered payload.

EXECUTED EVIDENCE
-----------------
All 15 accepted cases (13 substantive fixtures + 2 nullary-payload contract
checks), 36 adversarial rejections, 15 exact-goal translation round trips,
116 ordinary/optimized-Python CLI checks, and one open sequent passed.
There are independently checked translations in BOTH directions between the
new calculus and the matched separate-elimination/transport calculus.

The main replay suite also passed 221 normal-form, 660 numerical-evaluation,
and 440 binder-opening comparisons. A larger independent named-normalizer
audit passed 2505 exact normal forms, 15027 numerical comparisons, 1000 bound
substitutions, 500 free-name substitutions, 400 nested-formula substitutions,
and 17 malformed-term rejections. Three numerical evaluations exceeded that
audit's stated resource bound and were skipped; no exact-normal-form check
was skipped. The optional fuel checkers passed 28 examples, their exact and
one-unit-short budgets, 12 malformed-budget rejections and 112 CLI checks.

These finite checks support the implementation. They do not replace the
general written mathematical proofs.

FILE MAP
--------
code/checker.py                Readable complete acceptance checker.
code/checker_normalized.py     Measured source, same AST; gzip also supplied.
code/checker_fuel.py           Complete primitive-recursive certificate variant.
code/control_separate.py       Matched separate elimination/transport control.
code/control_separate_fuel.py  Matched bounded control.
FORMAT.txt                    Public syntax, scope and instruction contract.
validation/                   Untrusted proof constructors and translators,
                              independent replay and numerical semantics,
                              positive and adversarial certificates.
evidence/                     Exact measurements, test results and design audits.
reference/                    Attributed source proofs and frozen checker sources.
SOURCE_PROVENANCE.json         Frozen revisions, original paths and hashes.
CLAIMS.json                   Explicit claim boundaries.
MANIFEST.json                 SHA-256 hashes of all other delivered payload files.

PROVENANCE
----------
Repository: https://github.com/VladimirReshetnikov/ProveIt
Snapshot: 0ebd0c6b358f38bb0ad2883faf775421599c8aae
Path: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA
Also inspected: 443cff49563457a48ee0f663012d56c4bdb58fa0 (NativeZeroStep).
The inherited source uses the included MIT No Attribution license.
New materials may be used under the same terms.
