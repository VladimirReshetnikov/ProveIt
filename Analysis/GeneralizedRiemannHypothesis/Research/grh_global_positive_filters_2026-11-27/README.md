# Positive filters for the full Dirichlet zero spectrum

Research note for ProveIt, 27 November 2026.

- `paper.tex`, `paper.pdf`: self-contained proof and source discussion (classical analytic identities and Dirichlet GRH used as inputs).
- `SOURCE_AUDIT.md`: inspected sources, blob identifiers, proof boundary, and comparison with the merged article.
- `check_examples.py`, `examples_output.txt`: optional floating-point checks of theta normalization, selected zeros of zeta and Dirichlet beta, and a signed-kernel smoothing example. The computation is illustrative, not a certificate and not used by the proof.
- `SHA256SUMS`: integrity hashes of the other delivered files.

## Reproduce

```sh
sha256sum -c SHA256SUMS  # check original archive before rebuilding
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
python -m pip install scipy mpmath  # only if not present; optional numerical examples
python check_examples.py
```

The source was compiled with pdfTeX (TeX Live 2024). No Lean proof or upstream kernel replay was performed. The result is proved on paper using the Dirichlet GRH theorem exported by the vendored development as input; it does not assert other versions of GRH or independent formal certification. The claimed novelty is provisional, not a priority determination. No changes were made to the GitHub repository.
