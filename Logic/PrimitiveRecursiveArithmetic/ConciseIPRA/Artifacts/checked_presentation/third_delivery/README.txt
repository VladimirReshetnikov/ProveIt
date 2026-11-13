TWO SMALLER CHECKED PRESENTATIONS OF iPRA
November 12, 2026

Main result
-----------
Two standalone Python modules improve the observed compact checker envelope
at ProveIt commit 1156099ffe30f7497d2c11ab20271f46cffcd115:

                                      tokens   AST nodes   normalized bytes
  exact inherited matched control       240       266             551
  code/token239.py                      239       261             549
  code/checker.py                       246       257             589

The prior corpus minima were 240 / 259 / 462, from separate programs.
The new envelope is 239 / 257 / 462, still from separate programs.
The byte record is unchanged. No global simplicity lower bound is proved.
This is a program-level refinement of the inherited guarded-source
presentation, with no new deletion of an arithmetic or logical axiom.

Start with ipra_checked_presentation.pdf. The complete new LaTeX source is
report.tex plus results.tex, refinement.tex and verification.tex.

Contents
--------
code/                  Two measured standalone modules and a readable one.
controls/              Exact matched control and other coordinate incumbents.
fixtures/              Positive and adversarial JSON Lines certificates.
verify.py              Metrics, CLI tests and quotient-trace comparisons.
verification.json      Saved complete executable-test evidence.
audit/                 Pinned corpus census, fingerprints and novelty script.
reference/article/     Full inherited source article, at the pinned commit.
reference/             Inherited allocation proof and independent proof audit.
PROVENANCE.json        Exact source identities, transformations and scope.
CLAIMS.json            Machine-readable claims and limitations.
build_report.py        Rebuild the new PDF (pdflatex required).
MANIFEST.sha256        SHA-256 hashes of every other packaged file.

Reproduction
------------
Use CPython 3.12.14 for exactly comparable normalized source measurements.
From this directory:

  python3 verify.py
  python3 audit/check_candidate_novelty.py code/token239.py code/checker.py
  python3 build_report.py

To check one example:

  python3 code/checker.py < fixtures/global_computation_zero.jsonl

Acceptance is successful termination with the output ACCEPT. An exception
rejects. Input consists of one JSON goal on the first line and one
three-field packet per subsequent consumed line. Unread suffixes are allowed.

Contract and mathematical status
--------------------------------
The compact contract uses finite exact-integer/list trees and canonical
closed guarded Eq/D public goals. These modules implement scope and proof
checking, but do not independently validate every promised public-grammar
condition or arbitrary JSON types. They are compared with the same compact
contract; goal-validated and fully typed interfaces have separate baselines.

The new expression preserves the control's behavior under the explicit
relation identifying internally generated False with integer zero. It
preserves packet consumption and fresh-name allocation. The AST profile
also composes definition-time initialization and sequence-pattern binding.
The source simulation proof is in refinement.tex and the PDF.

The mathematical presentation is equiconsistent and bi-interpretable with
full first-order intuitionistic PRA through the inherited scalar bridge:
whole numerical domains, actual equality, identity graph x=y for both
composites, and both formula round trips. The source dependencies are stated
in the report and included as reference material. The new Python simulation
has a written proof and finite regression evidence; no new Lean/Rocq
formalization is claimed.

Validation already completed
----------------------------
256 isolated normal/optimized CLI executions passed.
224 typed mutation/fixture trace comparisons passed modulo False=0.
Structural source-delta checks passed.
The source audit covers 3,601 occurrences and 1,813 distinct normalized
modules, including all 16 incoming ZIPs. Both new normalized modules are
absent. Archive identities match the pinned Git blobs.

The source census is an observed comparison, not a proof that no smaller
checker exists. Finite tests support rather than replace the written proofs.
