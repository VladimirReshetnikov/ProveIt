FINITE FROBENIUS CERTIFICATES FOR THE THETA EXPONENT
=================================================

Main recommendation
-------------------
Retain the exact theta-product factorization with its raw integral exponent.
Replace the complete double-indexed coupling normal form by two direct
certificates: finite null-moment vanishing for divisibility, and a first-gradient
signature with unit coefficients for inert-prime sharpness.

The report proves the replacement mathematics, explains why both contracts
are necessary, matches them to the actual source consumers, and compares the
proposal against all 18 existing proposal directories at the pinned commit.

Source baseline
---------------
Repository: VladimirReshetnikov/ProveIt
Commit:     9050b04000647d588d0c78d945180abcd3b0bcf7
Source:     Analysis/GeneralizedRiemannHypothesis/Lean/grh
Guide:      Analysis/GeneralizedRiemannHypothesis/docs/guide
Proposals:  Analysis/GeneralizedRiemannHypothesis/docs/proposals

Read first
----------
grh_frobenius_jet_simplification.pdf  Compiled full report.
grh_frobenius_jet_simplification.tex Editable LaTeX source of the same report.

Other artifacts
---------------
formal/
  FrobeniusJets.lean   Standalone, compiled algebraic core (314 lines).
  lakefile.toml        Exact pinned mathlib dependency.
  lean-toolchain      Lean 4.35.0.
  README.txt          Clean setup, theorem descriptions, integration limits.
  validation.txt      Actual successful command, versions, hash and axiom output.

checks/
  check_finite_jets.py      Exact finite-ring regression checks; standard library.
  finite_jet_results.json   PASS: 2,614 assertion groups, including negative controls.
  verify_source_snapshot.py Read-only verification of the pinned source objects.
  audit_source_interfaces.py Reproduce the 803-file lexical/range audit.
  source_snapshot_results.json PASS: 85 source/proposal files and range counts.

audit/
  source_manifest.json     Commit and byte hashes for cited sources and all 64
                           textual proposal files used in the exclusion audit.
  source_audit.json        Exact affected ranges, declarations and lexical callers.
  proposal_inventory.tsv   18-row mechanism and duplicate-exclusion table.
  proposal_inventory.txt   Full inventory, including proposed future directions.
  migration_audit.txt      Detailed retain/replace/remove plan with pinned links.
  independent_review.txt   Independent mathematical and consumer stress test.
  validation_summary.txt   Final validation and artifact-scope statement.

SHA256SUMS.txt             Checksums of all other files in this archive.

Reproduce
---------
From this directory:

  python3 checks/check_finite_jets.py
  python3 checks/verify_source_snapshot.py /path/to/ProveIt
  python3 checks/audit_source_interfaces.py /path/to/ProveIt --output /tmp/source_audit.json
  latexmk -pdf -interaction=nonstopmode grh_frobenius_jet_simplification.tex

The source verifier reads pinned Git objects without changing the checkout.
For an exported source directory, add --working-tree. The supplied checkout
must contain the pinned objects or the matching exported files.

For Lean, follow formal/README.txt. A clean installation needs network access
to obtain the pinned Lean and mathlib dependencies. The actual validation used
an existing cache at exactly those versions, with exit status zero.

Precisely what is established
----------------------------
* The finite algebraic core compiles with only propext, Classical.choice and
  Quot.sound in the printed theorem dependencies. No sorry or new axiom.
* The mathematical report proves the finite-jet, exponential-integrality and
  gradient/leading-coefficient arguments, and audits their current call sites.
* The finite-ring regressions pass, including in a nonreduced coefficient ring.
* The primary affected source regions total 752 physical lines; 84 further
  helper lines are optional cleanup candidates. Neither number is net savings.

This is a mathematical simplification proposal with a checked reusable core.
It is not an applied ProveIt patch, a whole-project replay, or an independently
completed formal verification of RH/GRH. The remaining adapters and integration
steps are stated explicitly in the report. No remote repository was modified.

The novelty comparison is relative to the supplied proposal corpus, not a claim
of historical novelty for the elementary Frobenius identities themselves.
