# Optional floating diagnostics

These scripts are not invoked by mandatory exact verification or the builder.
They use Python's standard-library binary64 `math` routines. No nonstandard
package is needed. Run from an intact package, directing output outside it:

```
python -I -S -B optional/run_diagnostics.py > /tmp/report182-diagnostics.json
```

The script only reads package files and writes JSON to standard output. It
checks frozen reference hashes before using exact p(k) and a(n) input vectors.
Its outputs are not interval-certified. Last bits may vary with the platform's
math library. All phase roots, remainders, and carrier ratios here are
numerical diagnostics, not additional proof claims.

The diagnostics show smooth-carrier crossover locations, the slow positive
centering correction to 9/16, logistic scaling, finite-product normalization,
and the poor finite-n performance of the eventual two-charge coefficient
carrier. At n=5000 the leading/exact ratio is about 0.00177838 and the
first-corrected/exact ratio about 0.00486243. This is a limitation, not an
accuracy validation. There is no effective onset or finite-n accuracy theorem.

`frozen_float_diagnostics.py` and `reference_results.json` preserve the
independent diagnostic source and its historical output. The frozen script
writes alongside itself and expects colocated partition data; it is a
provenance copy, not the supported package command. Use `run_diagnostics.py`.
The adapted command preserves the original crossover and finite-product
calculations and adds the clearly labeled poor-performance benchmark.
