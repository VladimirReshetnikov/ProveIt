# Result provenance

- `benchmark.json`, `benchmark.csv`, and `benchmark_parts/*.json` contain the
  final complete replay. Each case has seven shuffled paired rounds, using its
  recorded deterministic case seed. Cases were run in separate commands to fit
  execution limits. Source hashes are stored per case.
- `benchmark_initial.json` is an earlier complete run with the same timed
  algorithms and a shared shuffle generator. It precedes input-immutability and
  certificate-schema hardening (outside the timed paths), and the addition of
  per-case persistence and source-hash reporting. Its raw data remain available;
  it is not silently substituted for the final replay.
- `benchmark_partial_rerun.txt` is an interrupted intermediate rerun. It contains
  only printed summaries, not a completed dataset, and is NOT used for tables.
- `audit.json` and `audit_stdout.txt` contain the completed independent algebra
  audit. `unittest.txt` is the completed local 39-test log. No upstream suite or
  knot-recognizer timing is included.
- `latex-pass*.txt` record PDF compilation. `pdf_quality.json` records the final
  PDF's page count, text-layout checks, and visual inspection scope.

Ratios use complete setup-plus-query median times. The full raw samples, control
arms, and slower cases are retained. Certificate checking and independent answer
comparison are outside recorded timing intervals. The algorithms' output values
were independently checked before the timings were reported.
