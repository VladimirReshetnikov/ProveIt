# Exact polynomial windows from Rvachev `up`

This archive accompanies the report `rvachev_up_polynomial_representation.pdf`.

## Contents

- `rvachev_up_polynomial_representation.tex` - complete LaTeX source.
- `rvachev_up_polynomial_representation.pdf` - rendered report.
- `up_polynomial_representation.py` - exact symbolic construction and independent numerical verification.
- `generated/quartic_atoms.csv` - exact ten-atom representation of the worked quartic.
- `generated/quartic_numerical_check.csv` - 1001-point FFT-based check.
- `generated/numerical_summary.txt` - exact coefficients and error statistics.
- `generated/quartic_reconstruction.png` and `generated/quartic_residual.png` - report figures.

## Reproduce the numerical experiment

Python 3 with `sympy`, `numpy`, and `matplotlib` is required.

```bash
python up_polynomial_representation.py --output-dir generated
```

The symbolic construction uses exact rational arithmetic. The numerical check is independent: it evaluates the Rvachev function by inverse FFT of its infinite sinc-product Fourier transform, truncated after 44 factors on a `2^20` grid.

## Compile the report

From this directory:

```bash
latexmk -pdf rvachev_up_polynomial_representation.tex
```
