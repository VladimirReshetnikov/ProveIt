Three-family raw diagonal iPRA calculus
======================================

Read THEORY.txt for the complete rule inventory, the partial-rho covariance
proof, the explicit KPrf/uniform-clause bridge, both proof translations,
the inherited bi-interpretation, and the exact limitations.

Run all finite checks and reproduce source metrics:

    python3 verify.py

Check a supplied positive certificate:

    python3 checker.py < tests/accept/diagonal_progress_nonzero_witness.json

Files:
  checker.py             New three-family standalone checker.
  checker_normalized.py  Complete executable profile measured literally.
  control_split.py       Matched four-family diagonal checker.
  control_inherited.py   Untouched inherited witness-dependent E3 checker.
  *_normalized.py        Runnable profiles; no hidden checker dependencies.
  translations.py        Untrusted exact-goal proof compilers.
  verify.py              Certificate generation, round trips and regressions.
  measure.py             Complete normalized-source metrics.
  THEORY.txt             Mathematical argument and limitations.
  PROVENANCE.json        Pinned source URLs, hashes and adaptation history.
  LICENSE-upstream.txt   Upstream MIT-0 license.
  tests/                 Positive and negative JSON certificates.
  evidence/              Results and complete normalized checker sources.

Status: written mathematical proofs with finite implementation checks. No
new Lean theorem or proof-assistant verification of the Python checker is
claimed. This result DOES NOT beat the repository's complete-checker
envelope. Its point is the combination of three rule families, raw terms,
and direct substitution; its matched split control is modestly larger.
