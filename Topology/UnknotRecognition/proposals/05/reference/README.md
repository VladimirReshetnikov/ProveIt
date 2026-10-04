# Preserved baseline

`baseline_fastunknot/` contains all seven original `.py` files from
`Knots.zip/fast/fastunknot/`, byte-for-byte unchanged. Only the containing package
directory is renamed so it can coexist with the optimized `fastunknot` package.

`test_fastunknot_original.py`, `benchmark.py`, `pyproject.toml`, and
`original_fast_README.md` are unchanged copies of their original counterparts.
They are archival reference material, not the commands to run the new benchmark.
In particular, the old README's claims about scan width do not describe guarantees
of this delivery; the new report explains the multiplicity obstruction.

Use `../benchmarks/run.py` for a fair paired measurement. It imports this baseline
under its renamed package name in a separate fresh subprocess for each trial.
The old test file still imports `fastunknot` and is preserved for inspection;
the actively run inherited tests are in `../tests/test_fastunknot.py`.
