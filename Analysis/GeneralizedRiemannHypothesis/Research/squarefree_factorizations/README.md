# Simultaneous congruences for factors of a squarefree integer

The nine-page paper is in **factorizations.pdf**. Its full LaTeX source is **factorizations.tex**.

Theorem 1.1 gives uniform counts for ordered factorizations using every surviving prime, with independently chosen moduli and prescribed factor sizes. Theorem 5.2 proves the lower bound on the number of primes required for balanced factors at power-saving relative accuracy. Theorem 6.1 classifies the extra obstructions when only a fixed positive fraction of the eligible primes survives. Its residual quotient has sharp maximal order.

## Build and reproduce

Use a standard TeX Live installation with Latin Modern fonts. The checks use the Python 3.10+ standard library. From this directory, run

```sh
pdflatex -halt-on-error factorizations.tex
pdflatex -halt-on-error factorizations.tex
python3 check.py
python3 test_lower.py
python3 check_quotient.py
```

- **check.py** enumerates the two three-factor examples in Section 7 and checks 304 Fourier coefficients against a separate polynomial calculation. The counts are integers. The coefficient comparison uses complex floating-point arithmetic. The program also demonstrates failure at the half-deletion threshold.
- **test_lower.py** uses rational arithmetic to check the recurrence for products of signs and its lower bound through populations of size 80.
- **check_quotient.py** counts a mixed-sign example with three factors modulo 5, both directly and by dynamic programming on the residual quotient.
- **check_output.txt**, **test_lower_output.txt**, and **check_quotient_output.txt** record the corresponding runs.
- **source_inventory.md** identifies the reviewed repository objects and the closest earlier results.
- **SHA256SUMS** contains the digests of all other files in the archive. Run `sha256sum -c SHA256SUMS` to check them.

The Dirichlet GRH input is taken from the published Lean development. The new theorems are proved in the paper. The prime-set selection is an existence proof, and the programs check finite instances.
