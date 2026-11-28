# Projective incidence instead of additive Fourier analysis

Start with `report.pdf`, a six-page mathematical proposal for shortening the finite-field positive-type component of the second-moment argument in the readable RH/Dirichlet GRH Lean development. It preserves the original theorem's precise constant and proves an extra corank-tail bound. The proof uses projective point–hyperplane intersection numbers and elementary Hilbert-space Cauchy–Schwarz rather than Fourier characters and tensor products. This is a local change, not a new independent proof or a measured whole-project shortening.

- `report.tex`, `report.pdf`: standalone paper and compiled PDF.
- `LEAN_PLAN.md`: staged implementation plan with exact compatibility and verification gates; no compiled Lean patch.
- `check_incidence.py`, `checks.txt`: actual exact finite regressions with Python 3 standard library. These check prime fields and F4, positive-type weights, degeneracies and a counterexample without positive type.
- `source_audit.tsv`, `proposal_audit.tsv`: Git object identifiers, source anchors and targeted comparison of the 24 folders observed in proposal tree `7fd24ac9ab5506bf6d0d21fd52034010a4f72243`. The targeted scan searched main papers and selected sections for `PositiveType`, `card_mul_sum_det_eq_zero_le`, `leadingMinor`, positive type, projective, incidence, and singular minor; selected older scans also included stabilizer. The audit is not an exhaustive semantic reading of every file; some source/proposal reads occurred at moving main. Two central Lean files were rechecked at commit `a96fd3f7b682add165f649414b90e243bc18b101`. No whole-tree verification was performed.
- `verify_sources.py`: optional local Git object audit; not run against a local checkout in this session.
- `SHA256SUMS`: archive contents checksums (except itself).

Reproduce:

```sh
sha256sum -c SHA256SUMS
python3 check_incidence.py
pdflatex -halt-on-error report.tex
pdflatex -halt-on-error report.tex
python3 verify_sources.py /path/to/ProveIt
```

No source was modified on GitHub. The original proof's verification is reported by the guide, including https://math.mit.edu/~drew/shortgrh/ . The new substitution has a complete paper-level proof, but was not elaborated in Lean; the net code size/build performance have not been measured. The existing proposal audit is targeted, not a global novelty claim.
