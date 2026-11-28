# Real samples and nearest poles

Read `report.pdf` (9 pages) or `report.tex`. The proposal targets the final analytic step of the supplied Dirichlet GRH proof. The main result is an interface-preserving mathematical replacement for `New.IsPolar.landau` using finite differences and radial Taylor majorization, with a second-stage real-only transform contract and localized twist-selection criterion. It is not an independent proof of RH/GRH or a verified Lean patch.

## Contents and reproduction

- `report.tex`, `report.pdf`: mathematical report, source links, proofs, caveats, and further questions.
- `LEAN_PLAN.md`: formalization specifications and acceptance gates (not compiled code).
- `check_real_samples.py`, `tests.txt`: finite exact rational checks, with actual test output.
- `source_anchors.tsv`, `proposal_audit.tsv`: source blobs, anchors, and targeted comparison.
- `verify_source_blobs.py`: optional local Git comparison of observed blob hashes.
- `SHA256SUMS`: checksums of the distributed files.

Compile twice with `pdflatex -halt-on-error report.tex`; run `python3 check_real_samples.py`. The tests use only the Python standard library. A Lean toolchain was unavailable; no build, kernel replay, or net line-count measurement was performed. No GitHub files were changed.

## Retrieval scope and reproducibility

The GitHub connector listed the readable `src` tree (observed tree SHA `11aeaa21a903fa887084342d33908671dd273231`; 950 entries including directories) and the untruncated proposal tree (observed tree SHA `7fd24ac9ab5506bf6d0d21fd52034010a4f72243`; 24 top-level directories, 34 TeX files). The separately reported main head was `a96fd3f7b682add165f649414b90e243bc18b101` with root tree `68758149335810beaf3e5ffdb9d4dda98100baab`. Because retrieval used moving main URLs, whole-tree consistency at that commit is not certified. The tables identify observed individual file blobs, rather than claiming a fully pinned checkout. The most relevant guide sections and source declarations were inspected directly. Other proof layers were examined at architectural level, not independently reverified.

Proposal screen: case-insensitive terms `Landau|Pringsheim|nearest pole|closest pole|finite difference|nonnegative.{0,20}coefficient|positive.{0,20}coefficient|abscissa of convergence|pole radius`; relevant endpoint sections inspected. 33/34 TeX files retrieved; `robust_theta_labels` TeX returned 404, so its README was used. Directory summaries and the closest endpoint proposals were compared, not every auxiliary artifact semantically reviewed. No matching replacement was found. Classical nearest-pole reasoning is not claimed to be novel mathematics.

To compare source blobs with a checkout: `python3 verify_source_blobs.py /path/to/ProveIt --rev main`. Mismatches identify version drift or retrieval discrepancies, not mathematical errors. This verification script was not run against an actual local repository because one was not available.
