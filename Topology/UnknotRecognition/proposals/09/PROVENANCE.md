# Provenance and artifact map

Input: the user's `Knots.zip`, supplied in this conversation.

- `baseline_fastunknot/*.py`: byte-for-byte copies of the seven original
  `fast/fastunknot/*.py` files. Only the containing directory name changes, to
  permit both versions to be imported by one benchmark harness. No baseline
  source optimizations have been applied.
- `fastunknot/diagram.py`, `alexander.py`, `simplify.py`, `scan.py`,
  `recognize.py`, `__main__.py`, `__init__.py`: derived from the corresponding
  original files, with changes explained in the report.
- `fastunknot/jones.py`, `determinant_filter.py`, `ordering.py`, `factors.py`:
  added implementations.
- `examples/*.json`: the ten original examples, unmodified.
- `examples/stress/original_random_5_braid_36.json`: the precise 36-crossing
  5-strand braid word recorded in the input archive's `fast/results/benchmark.json`.
- `tests/test_legacy.py`: original 19 test methods, with an explicit adapter
  disabling new default filters where the original assertions check the old
  method name, and one matching CLI flag. Assertions are retained.
- `tests/test_accelerated.py`: added differential, independent-reference,
  metamorphic, resource, certificate, and CLI tests.
- `results/benchmark.json`: 65 fresh case/task/implementation records on the
  same machine; successful records normally contain five samples.
- `results/stress_60.json`: a separate baseline-only 60-second cooperative
  raw-homology cutoff. It is not a completed rank computation.
- `results/stress_simplified_crosscheck.json`: an additional unsuccessful
  10-second attempt to compute the stress rank using the original scanner on
  its 24-crossing R2-reduced diagram. It establishes no new independent rank.
- `results/baseline_tests.txt`, `legacy_tests.txt`: initial test logs, kept
  separately from the final complete test log `results/test_output.txt`.
- `docs/report.tex`, `docs/benchmark_tables.tex`, `docs/report.pdf`: new article,
  automatically generated numerical tables, and compiled PDF.

The supplied Lackenby source and slides were read and compared with the public
primary sources. They are cited in the article, not redistributed here. This
archive is a solution package, not a copy of the entire input archive.

The inherited MIT No Attribution license is in `LICENSE`. The same license
covers the added code and documentation in this solution. No external runtime
package, executable, database, or undocumented recognition oracle is required.
