# Numerical regeneration

The delivered environment did not generate the numerical companions. Its
failure record is preserved as `arrival_numerical_generation_error.txt`.
The script also used the removed `mp.one` and `mp.zero` aliases; those calls
were replaced by `mp.mpf(1)` and `mp.mpf(0)` without changing the formulas.

The current payload was regenerated successfully on 2026-08-30 with Python
3.13.14, mpmath 1.4.1, Matplotlib 3.11.1, and 80-decimal-digit mpmath
precision:

```sh
uv run --with-requirements requirements.txt \
  python numerical_experiments.py --output-dir .
```

The run completed with exit status zero. Its hard checks verified the exact
digit-sum zero count at `M = 1, 2, 3, 7, 32, 257, 1024` and compared the sinc
and canonical products at `z = 1.2 + 0.7i` to the script's prescribed
tolerance. It generated `numerical_results.tex`, `numerical_summary.txt`, and
all three PNG figures referenced by the report. These are consistency checks,
not substitutes for proof.
