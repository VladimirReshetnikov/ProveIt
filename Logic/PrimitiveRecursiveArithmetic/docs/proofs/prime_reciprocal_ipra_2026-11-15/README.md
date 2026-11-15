# Constructive divergence of the reciprocal-prime sum in iPRA

This archive contains a fully developed human-readable proof of the explicit
quantitative theorem

\[
  \sum_{p\le 2^{2\cdot 4^k},\ p\text{ prime}}\frac1p>k
\]

and an audit showing how the proof is formalized in intuitionistic primitive
recursive arithmetic using only primitive recursive functions and
quantifier-free induction.

## Contents

- `prime_reciprocal_ipra.tex` - LaTeX source.
- `prime_reciprocal_ipra.pdf` - compiled paper.
- `lean/PrimeReciprocalIPRA.lean` - Lean theorem-signature scaffold with
  `sorry` placeholders.
- `lean/FORMALIZATION_PLAN.md` - obligation-by-obligation path to a complete
  `PRAAx` proof and transfer to the ConciseIPRA scalar core.
- `scripts/check_finite_lemmas.py` - exact finite sanity checks.
- `artifacts/verification_report.txt` - generated checker output.
- `artifacts/theorem_spec.json` - machine-readable theorem/dependency summary.
- `references/repo_snapshot.txt` - repository snapshot and relevant paths.
- `Makefile` - rebuild and check commands.
- `manifest.sha256` - checksums for the delivered files.

## Rebuild

Requirements: Python 3, `latexmk`, and a standard TeX Live installation.

```bash
make check
make pdf
```

For Lean, place `lean/PrimeReciprocalIPRA.lean` in the ProveIt root workspace
or a new library that imports `ConciseIPRA`. The file is an outline, not a
completed formalization. Completion criteria are listed in
`lean/FORMALIZATION_PLAN.md`.

## Main proof idea

Let `Q_n` be the product of primes at most `n`, `R_n = sum Q_n/p`, and let
`H_n` be the harmonic sum. A finite Euler-product argument gives
`H_n <= product p/(p-1)`. The elementary integer inequality
`p^p <= 4 (p-1)^p` implies that `R_n <= k Q_n` forces `H_n <= 4^k`.
But `H_(2^(2*4^k)) >= 1+4^k`, a contradiction. All fractions are cleared to
natural-number inequalities in the iPRA formulation.
