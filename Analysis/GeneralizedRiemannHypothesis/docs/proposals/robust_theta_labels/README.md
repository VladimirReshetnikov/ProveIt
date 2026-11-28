# Three power tests instead of primitive labels

A distinct mathematical simplification of the local finite-field labels used by the readable Alpöge–Claude Dirichlet GRH proof. It replaces primitive generators by robust roots satisfying three power tests, proves an exact witness count, and shows how to preserve the Galois and spanning contracts. All original admissible data and the arithmetic/analytic endpoint remain unchanged.

## Contents

- `robust_theta_labels.pdf` — compiled mathematical report, including proofs, source links and nonduplication analysis.
- `robust_theta_labels.tex` — standalone LaTeX source.
- `LEAN_PLAN.md` — proposed file-by-file integration blueprint, not elaborated Lean code.
- `check_labels.py`, `checks.txt` — executable exact cyclic-group regressions and actual output. The tests are finite, not a formal verification of the general theorems.
- `source_audit.tsv`, `proposal_audit.tsv`, `verify_sources.py` — source and proposal provenance and a local Git verification script. The selected files and eight proposal trees were retrieved through the GitHub connector; no complete project checkout or local verification of the manifest was performed here.

## Reproduce

```sh
pdflatex -halt-on-error robust_theta_labels.tex
pdflatex -halt-on-error robust_theta_labels.tex
pdflatex -halt-on-error robust_theta_labels.tex
python3 check_labels.py
python3 verify_sources.py /path/to/ProveIt
```

The relevant baseline is commit `ee10f937fedac0955d28b7b860f4c44fab508204`. No repository changes were made. The proposal is mathematically proved at the local replacement level; a full integrated Lean proof and kernel replay have not been performed. No line-count or build-time reduction has been measured. The original proof's independent checks are reported by the repository and linked in the report; they do not certify this new variant.
