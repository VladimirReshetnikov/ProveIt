# When blurred Dirichlet zeros determine their sources

The paper proves a sharp recovery theorem for a sum of independently convolved zero-counting measures of primitive Dirichlet L-functions. It also constructs one smooth positive probability law that erases the arithmetic prime-frequency data of every primitive character. It gives the complete below-threshold family classification, identifies the invariants of finite packets under the common law, and proves quantitative and localized recovery statements.

## Files

- `dirichlet-zero-recovery.pdf` is the complete paper.
- `dirichlet-zero-recovery.tex` is its self-contained LaTeX source, including the bibliography.
- `verify.py` runs finite illustrative checks using only the Python standard library.
- `verification.txt` records the output of those checks.
- `SHA256SUMS` contains the SHA-256 checksums of the four preceding files and this README.

## Reproduction

Run these commands in the extracted directory with a standard TeX Live installation and Python 3.9 or later.

```sh
pdflatex -halt-on-error dirichlet-zero-recovery.tex
pdflatex -halt-on-error dirichlet-zero-recovery.tex
python3 verify.py
```

The two passes resolve references and the embedded bibliography. Numerical output uses ordinary floating-point arithmetic. Exact checks in the script cover finite group orthogonality, rational disk interpolation, and the Laurent polynomial identity behind the zeta-pole example. The integral calculations illustrate the signed multiplier. The existence and tail behavior of the positive common density are established analytically in the paper.

## Mathematical inputs

The paper uses the primitive critical-strip zero-location theorem exported in the readable Lean development vendored at ProveIt commit `2a9f8e3ee74a1824d57546f0b1b4f1cef5df93d6` (upstream commit `72fead102f663d5c7a407964a13dc0cf9d977207`). Source links and exact statements appear in the paper. The paper also uses the classical Guinand–Weil formula, Mertens' theorem in arithmetic progressions, the disk zero condition, and two explicitly identified kernel lemmas from the merged Article for the sparse-window extension. The new theorems have mathematical proofs. The code checks finite examples. The upstream Lean build was not rerun and the new theorems were not formalized in Lean.
