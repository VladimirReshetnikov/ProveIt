SEED EVALUATION FOR CONCISE iPRA
Research note and reproducible proof-checking artifacts
Comparison baseline: ProveIt commit 443cff49563457a48ee0f663012d56c4bdb58fa0
Date: November 11, 2026 (America/Los_Angeles)

The main result is a local replacement of the arithmetic/equality inference:

  a = b,  I(S c, a; u.h) = r
  --------------------------  SeedEval
       r = h[I(c,b;u.h)/u]

All substitutions and iterator construction use the existing zero-only
normalization. No successor computation is performed by the normalizer.
Together with reflexivity, SeedEval is equivalent to the preceding Step rule
without using any logical rule, case distinction, or induction. The complete
five-scheme clause calculus and its whole-domain bi-interpretation with
first-order intuitionistic PRA are explained in the PDF and LaTeX source.

STATUS AND COMPARISON

This is a modest local simplification, not an absolute minimum claim. The
paper separates the effect of the rule change from a shared syntax-walker
refactoring. The rule change alone ties the original checker in one matched
implementation and saves two normalized bytes and two tokens in another.
It does not improve the repository's historical compact-checker frontier.
Direct successor-computation certificates avoid a duplicate predecessor
iterator in their reflexivity premise. No claim covers all shortest proofs.

The mathematical equivalence is a written proof. Executable certificates
and adversarial tests supplement that proof; they are not a Lean or Rocq
verification. The inherited bi-interpretation theorem is cited at the pinned
repository commit. This package does not claim to have rebuilt that Lean
development in the present environment.

CONTENTS

  ipra_seed_evaluation.pdf     Main report.
  ipra_seed_evaluation.tex     Self-contained source for the main report.
  goal_code/                  Late goal-directed checker comparison.
  reproduce.py                Re-run both SeedEval comparisons and the unit experiment.
  code/                       Standalone checker, controls, translators,
                              fixtures, and reproduction scripts.
  evidence/                   Measurements, validation results, provenance.
  reference/                  Selected pinned upstream sources and license.
  notes/                      Further mathematical reduction: fixed-unit
                              evaluation, its source, 83 fixtures, and measurements.
  CLAIMS.json                 Machine-readable scope of the claims.
  MANIFEST.sha256             Checksums for every other package file.

REPRODUCTION

Use CPython 3.12.14 for exactly matching the reported normalized-source
measurements. Other recent Python 3.10+ versions can run the checker; AST
unparse formatting and counts may differ.

  python3 reproduce.py
  python3 code/checker.py < code/examples/computation.json
  python3 -O code/checker.py < code/examples/computation.json

To rebuild the PDF, run pdflatex twice from this directory:

  pdflatex -interaction=nonstopmode -halt-on-error ipra_seed_evaluation.tex
  pdflatex -interaction=nonstopmode -halt-on-error ipra_seed_evaluation.tex

The supplied checker uses no assert statements for trust decisions and no
external runtime package beyond Python's standard library. A zero exit
status together with the line ACCEPT is its successful public result.

See the paper for precise syntax, scope conventions, rule side conditions,
interpretations, proof dependencies, measured limitations, and further
research questions.

LATE CHECK

The repository advanced to 56aafa39cf53a47dc4ae9f3a030fd8ac279a5624.
The newly filed selected goal checker and its direct SeedEval adaptation
both measure 2283 normalized bytes, 741 tokens, and 826 AST nodes.
See goal_code/ for that matched comparison and its source contract.
The included shared-traversal versions both measure 2265 bytes, 709 tokens,
and 787 AST nodes. The same 18-byte reduction applies to both arithmetic
rules, so it is a common implementation improvement, not a SeedEval gain.
