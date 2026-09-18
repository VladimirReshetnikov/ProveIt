# fastunknot 0.2.0

Exact recognition of classical one-component knots. Python >=3.10, standard
library only. This is the improved package; the unchanged source is in
`../baseline/`. See `../README.md` and `../report/report.pdf` for proofs,
measurements, limitations, and reproduction instructions.

```sh
python -m fastunknot recognize examples/conway.json
python -m fastunknot recognize examples/conway.json --output result.json
python -m fastunknot verify examples/conway.json result.json
python -m fastunknot khovanov examples/conway.json
python -m fastunknot khovanov examples/conway.json --no-factor
```

Default recognition combines R1/R2, descending diagrams, visible sum cuts,
bounded modular Jones obstruction, Alexander, and a cached sparse F2 Khovanov
scan. A modular mismatch proves knottedness; equality is inconclusive. The
`khovanov` command returns factored ranks unless `--no-factor` requests a raw scan.

The global worst case is exponential, not quasipolynomial. Resource exhaustion
returns UNKNOWN. Time limits are cooperative and object limits do not bound
all memory. `by_degree` reports raw cube homological degree, not quantum degree.

Install from the containing archive root with `python -m pip install ./fast`,
or run directly from this directory without installing anything.
