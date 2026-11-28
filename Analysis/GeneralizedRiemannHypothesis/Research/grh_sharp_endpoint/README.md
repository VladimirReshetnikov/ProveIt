# The sharp endpoint for full-spectrum positive Dirichlet zero filters

Research extension of ProveIt, 27 November 2026.

## Main result

For a conjugation-closed multiset of `d` primitive Dirichlet characters, let `Q_*` be the geometric mean of their conductors. Assume the Dirichlet critical-line statement used by ProveIt. A probability measure whose Fourier transform cancels the whole noncentral zero divisor, including multiplicities, can have a finite moment

    integral exp(b exp(2 |t| / d)) dmu(t)

only if `b <= pi d / Q_*`. This improves the previously stated upper bound `2 pi d / Q_*` by a factor of two. At equality the bilateral Laplace transform is `P(w) B(w)`, where `B` is the central-zero-removed completed product and `P` is a real polynomial. Its degree must satisfy `deg(P) + k < -1/2`, where `k = 2r - d/4 + sum(parities)/2 - m`, with `r` the number of zeta factors and `m` the central vanishing order. The paper gives an exact positivity criterion for these polynomial multipliers.

For `r` zeta factors, `s` Dirichlet-beta factors and `u` conductor-five quadratic factors, the improved coefficient is the exact supremum. The endpoint is attained exactly when `u > 7r + s + 2`. If it is attained, it is unique for `u <= 7r + s + 10`, and there are infinitely many distinct endpoint measures otherwise.

## Files

- `paper.pdf`: the complete nine-page paper, with proofs and further questions.
- `paper.tex`: self-contained LaTeX source, using standard TeX Live packages.
- `SOURCE_AUDIT.md`: source revision, original open question, and scope of inspection.
- `verify_examples.py`: standard-library exact-rational check of the exponent and degree bookkeeping, plus the concrete examples; not a checker of the analytic proof.
- `verification.json`: output from the included checker.
- `build.sh`: rebuild PDF and repeat the arithmetic check.
- `SHA256SUMS`: checksums of these deliverables.

Run `sh build.sh` from this directory with Python 3 and pdfLaTeX installed. To verify the original bundle, before rebuilding run `sha256sum -c SHA256SUMS`.

The analytic proofs use the specified RH/Dirichlet-GRH input. They do not establish nonabelian GRH or another classical named conjecture. The exact sharpness for arbitrary character families remains open, as does positivity of their endpoint kernels. We did not independently rebuild the upstream Lean proof, formalize the new proofs in Lean, or establish global publication priority. No repository files were modified.
