FIVE-RULE PRESENTATIONS OF INTUITIONISTIC PRIMITIVE RECURSIVE ARITHMETIC
Closure erasure, introduction guards, and substitution
Prepared November 11, 2026

READ FIRST

report.pdf is the complete  research report; report.tex is its single-file
LaTeX source. The primary construction is a raw Eq/D clause calculus with
five inference families, compared with the current six-family, directly
substitution-stable native calculus SPrf.

The construction removes Q from the formula language and combines ordinary
hypothesis use and closure elimination into reusable-clause use. It retains
ordinary capture-avoiding substitution, the existing two-case Eval, and the
existing diagonal introduction. Substitution preserves the entire proof tree.
Both proof translations and both formula round trips are proved in writing;
the arithmetic bi-interpretation composes with the pinned repository's
existing verified native/scalar/iPRA bridge. Both numerical domains remain
whole and the numerical composite graphs are x=y.

THE LIMITATION IS MATERIAL

This is not a new repository-wide size minimum and not a proof of a globally
simplest axiomatization. The exact components are inherited; the proposed
result is their combined interface and its structural theorem. An existing
witness-mode clause checker is smaller, and other compact encodings are much
smaller. The requested global improvement remains unestablished in this run.

Complete matched-module measurements (CPython 3.12.14, remove all actual
docstrings, ast.unparse, append one line feed):

                                      bytes    tokens    AST nodes
  Matched native diagonal control      3395       975         1138
  Proposed diagonal clause checker     3056       872         1013
  Existing witness clause control      2956       837          977
  Optional mirror clause checker       3059       874         1012

The controlled native reduction is 339 bytes (9.99%), 103 tokens and 125
AST nodes. The existing witness-mode clause checker is 100 bytes smaller
than the proposed primary checker. It has substitution admissibility, but
the same proof tree need not remain valid after a variable witness becomes
zero. The new diagonal policy eliminates that particular repair requirement.

CONTENTS

  report.tex / report.pdf
      Complete syntax and rules; equality bootstrap; numerical cases and
      equation induction; all logical macros; exact native equivalence;
      both formula composites; arithmetic interpretation maps; guard theorem;
      comparisons, verification limits, and further research questions.

  diagonal/
      checker.py: standalone trusted primary checker.
      native_diagonal_control.py: independently structured matched native control.
      witness_control.py: exact pinned upstream raw two-case clause checker.
      proof_tools.py: untrusted proof producers, substitution, and translation.
      verify.py: tests, fixtures, and source metrics.
      FORMAT.md: precise certificate syntax and scope contract.
      results.json, examples/, source_provenance.json, exact diffs, license.

  mirror/
      Secondary full-language one-sided guard variant. It is equivalent to
      iPRA, but substitutions can create its guard and require a local proof
      repair. Includes explicit naive-failure and repaired-success examples.

  evidence/
      Reproduction receipts and PDF review metadata.

  CLAIMS.json / PROVENANCE.json
      Exact supported claims, limitations, pinned sources, and attribution.

REPRODUCE

  python3 reproduce.py
  python3 reproduce.py --pdf
  python3 diagonal/checker.py < diagonal/examples/zero_computation.json

Successful public proof checking means exit status 0 and exactly ACCEPT on
standard output. A failed check prints REJECT and exits nonzero. Neither
standalone checker imports producer/test code or uses assert for acceptance.

To rebuild just the document, run pdflatex twice (a third pass may be needed
after contents-page changes):

  pdflatex -interaction=nonstopmode -halt-on-error report.tex

No shell escape, external bibliography tool, or network access is required.
The proof checkers and reproduction suites use Python's standard library.

VALIDATION BOUNDARIES

Primary: 12 positive proofs, 17 rejected inputs, 12 checked translations to
the native control, 5 parameter substitutions, 600 guard-invariance cases,
4 explicit capture controls, and 82 normal/optimized command-line checks.
Mirror: 13 positive and 13 negative certificates, 300 preservation cases,
52 command-line checks, and 5 guard-creation substitutions with explicit repair.

These are implementation tests, not a proof-assistant verification of all
mathematics. No Lean executable was available in this run. No new Lean or
Rocq verification is claimed. The executable translator handles closed
primary certificates into the native control; the full reverse and general
context translations are written metatheorems.

SOURCE AND NOVELTY

Repository: https://github.com/VladimirReshetnikov/ProveIt
Commit: 443cff49563457a48ee0f663012d56c4bdb58fa0
Project: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

The two-case Eval, diagonal guard, clause interface, and mirror guard are
inherited. The general one-way guard-preservation repair method also appears
in reflexive_base/proof.tex and is credited. The report gives the full
unrestricted-language combinations and their equivalence/substitution proofs.

No repository changes were published.
