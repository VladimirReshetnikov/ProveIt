# One integral presentation instead of three local arguments

Proposal for the auxiliary CM-field arithmetic in the readable proof of RH and Dirichlet GRH. This is a mathematical replacement and migration plan, not a compiled Lean patch or independent verification of the main theorem.

## Contents

- `report.tex` / `report.pdf` — self-contained mathematical arguments, source links, compatibility and limitations.
- `lean_plan.md` — staged implementation and validation plan.
- `check_field_model.py` / `checks.txt` — exact finite tests and actual output.
- `source_anchors.tsv` — pinned source blob IDs and inspected ranges.
- `proposal_audit.tsv` / `proposal_tex_inventory.tsv` — topic audit of 24 proposal directories and inventory of all 34 TeX blobs.
- `verify_sources.py` — optional reproducible check against a local Git checkout of the pinned commit.
- `SHA256SUMS` — integrity manifest.

## Reproduce

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex
python -m pip install sympy==1.14.0
python check_field_model.py
sha256sum -c SHA256SUMS  # before modifying any archived file
```

The check script uses exact integer, finite-polynomial and rational-matrix calculations. It does not build Lean. `verify_sources.py /path/to/ProveIt` verifies the source identifiers from the repository history and re-runs the proposal keyword screen. It has not been run against a local clone here.

## Audit scope

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned commit: `fd695fd462aa31b25af3335e2a9c3b6e014b055f`.

Proposal tree: `7fd24ac9ab5506bf6d0d21fd52034010a4f72243`, untruncated recursive inventory. All 24 README summaries were inspected and all 34 TeX blobs fetched through the GitHub connector. Case-insensitive screening pattern (matches checked line by line):

```
PrimeDecomposition|relDifferentGen|differentGenPhase|codifferent|coprime discriminant|trace.dual|reciprocal polynomial|residue.orbit|two.generator|smul_eq_iff_exists_frobElem_pow
```

No hits were returned by this targeted screen. The closest proposals were additionally inspected for thematic overlap. This is a targeted nonduplication audit, not an exhaustive semantic comparison of every sentence or a literature-priority claim.

The mathematical replacement is conditional only on the standard algebraic number theory inputs explicitly identified in the paper, not on a new assumption about RH. The source theorem interfaces are intended to be preserved; no theorem about the proposed Lean port has been mechanically established. The current source reports independent verification of the original proof, which was not independently reproduced here. No files on GitHub were changed. Net source savings remain unmeasured; 471 lines is the total size of five candidate ranges, not a predicted deletion count.
