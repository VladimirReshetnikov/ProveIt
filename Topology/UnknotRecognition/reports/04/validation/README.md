# Validation records

`unittest.log` is the output of 62 test methods, many containing multiple cases.
`results.json` records the 12 example-knot calculations and three ball patterns.
The timings are one execution on the recorded environment, not benchmark
claims or evidence of a quasi-polynomial algorithm.

`archive_check.log` records the suite executed again from a clean ZIP extraction.

Reproduce the mathematical checks from the archive root with:

```sh
python run_validation.py
```

The test suite uses only Python's standard library. No dependency installation,
network access, external topology executable, proof-assistant kernel, or
precomputed answer service is used at runtime. The external PD fixtures and
the expected ranks derived from published integral-homology tables are
attributed in `docs/fixture_sources.json` and `docs/report.pdf`.

Important: the stored output explicitly says that the recognizer has no
quasi-polynomial guarantee. The graph-pattern outputs require an already
established 3-ball hypothesis. Unit tests do not certify those missing
geometric constructions or formalize the program's correctness.
