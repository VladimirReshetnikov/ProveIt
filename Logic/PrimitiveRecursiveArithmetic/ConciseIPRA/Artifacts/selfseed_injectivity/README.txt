SELF-SEEDED iPRA WITHOUT PRIMITIVE SUCCESSOR INJECTIVITY
Research package for Vladimir Reshetnikov, 12 November 2026

OPEN FIRST
  selfseed_ipra.pdf
  selfseed_ipra.tex

MAIN MATHEMATICAL RESULT
The self-seeded theory T_F^- in the current ConciseIPRA article proves
S(a)=S(b) -> a=b. The extra successor-injectivity axiom in T_F is redundant.

The proof uses two stopping orbits A_a and A_b. A hypothetical collision
forces each to avoid the other's stop. One literal-equation induction
synchronizes them; at a stop it yields a=b. Every update is an actual
original-language term. No successor cancellation, order, independent
initializer, or arbitrary graph-defined recursor body is assumed.

The report gives every logical/nonlogical axiom and inference rule,
reproves the necessary preparations before injectivity, and supplies
the complete new proof. The old and new theories prove the same open
sequents. The repository's existing full first-order iPRA bi-interpretation,
including both formula round trips and identity numerical comparison
maps, therefore transfers unchanged.

FORMAL CHECK
formal/StoppingOrbits.lean compiles in Lean 4.24.0 without Mathlib,
sorry, added axioms, or classical choice. Lean reports:
  'SelfSeed.successor_injective' does not depend on any axioms

This file checks the central ABSTRACT ALGEBRAIC theorem. Its structure
assumes the recurrence, stopping invariant, coverage and cycle exclusion
proved in the report, and equation induction ONLY for the stopping-orbit
equality family. It is not a deep formalization of the whole iPRA syntax,
preliminary term constructions, compiler, or Python checker.

CHECKERS AND SIZES
Whole-module CPython 3.12.14 normalization by ast.unparse plus one LF.
Gzip is level 9, timestamp zero, applied to normalized source.

Actual self-seeded theory:
                                  tokens  AST   bytes   gzip9
  Old T_F control                  1947  2247    8896    2199
  New T_F^- checker                1897  2192    8698    2172
  Savings                            50    55     198      27

The exact code difference is the injectivity-axiom recognition branch.
Both programs fully validate their specified theorem/proof JSON format.
The package does not contain a full ND certificate of the main theorem.

SEPARATE COMPACT COMPANION
compact/checker468.py implements the ESTABLISHED guarded scalar calculus,
not the new self-seeded theory. A composition of the shared-leaf protocol
and the even binding-depth offset gives:
                                  tokens  AST   bytes   gzip9
  Initial matched control           272   306     469     309
  Shifted companion / final tie     271   305     468     309

Its contract assumes canonical closed guarded public goals and finite
exact-integer/list data. It is not a validator of arbitrary JSON syntax.
It consumes a whole JSON array. The independent token and AST records
use JSON Lines. A final refresh authenticated four newly incoming archives,
including a BYTE-IDENTICAL 468-byte program. Our companion is thus an
independently reconstructed existing composition, NOT a current strict
record or new checker. The final cross-framing envelope is 240/261/468,
attained by DIFFERENT programs, versus 241/262/469 at the initial snapshot.

The byte saving and the mathematical axiom deletion are distinct results.
The requested single checker below every coordinate of the proposal
envelope, and absolute simplestness, are NOT established.

REPRODUCE
  python3 reproduce.py
  python3 reproduce.py --lean /path/to/lean
  python3 reproduce.py --pdf
  python3 reproduce.py --manifest-only

Or individually:
  python3 selfseed/verify.py
  python3 compact/verify.py
  lean formal/StoppingOrbits.lean

The PDF is already compiled. Standard TeX rebuild:
  pdflatex -interaction=nonstopmode -halt-on-error selfseed_ipra.tex
  pdflatex -interaction=nonstopmode -halt-on-error selfseed_ipra.tex

build_pdf.py can also generate a private TeX format from installed TeX
sources when system caches are absent. It downloads nothing and makes
no global configuration change. That helper is attributed MIT-0 code.

CONTENTS
  selfseed_ipra.tex / .pdf          Complete report
  formal/                          Compiled central theorem source
  selfseed/                        Two complete ND checkers and 35 fixtures
  compact/                         468-byte checker, controls, proof, fixtures
  reference/                       Exact upstream chapter and source identity
  review/                          Independent proof and implementation audits
  evidence/                        Source censuses and execution receipts
  CLAIMS.json                      Exact established claims and limitations
  MANIFEST.sha256                  Checksums of delivered files
  LICENSE.txt                      MIT No Attribution

The numerical claims were checked by 140 self-seeded checker executions
and 126 compact checker executions, ordinary and -O, with no unexpected
outcomes. Finite tests support implementation checks; they are not proofs
of universal mathematical soundness.

BASELINE
VladimirReshetnikov/ProveIt
Logic/PrimitiveRecursiveArithmetic/ConciseIPRA
Pinned commit: 78edba03ee060644464f76e388578584b356520a
All 19 incoming archives at that snapshot were authenticated and examined.
The article explicitly leaves general successor injectivity in T_F^- open.
Novelty is claimed relative to the inspected repository, not all literature.

Final refresh: 96c398c189048d713bc692720e6d72416fde40a7
Commit time: 2026-11-13 04:02:24 UTC.
Four additional incoming archives were authenticated and examined.
The self-seeded chapter is unchanged and the new submissions contain
no paired stopping-orbit argument or equivalent self-seeded axiom deletion.
The final refresh DOES supersede the implementation-record claim for
the independently reconstructed 468-byte companion. See
evidence/final_freshness.json and evidence/final_freshness.txt.

No remote repository changes are part of this deliverable.

