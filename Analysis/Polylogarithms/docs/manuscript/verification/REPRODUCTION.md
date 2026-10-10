# Fresh continuation replay commands

Run from `docs/manuscript`, with Python, mpmath and sympy available. These
commands preserve the historical code and receipts, writing only into the
manuscript verification directory. Core, build and render commands are in
the [manuscript README](../README.md).

```powershell
python ../reports/rational-grid-distribution-ranks/code/10-exact-structure-verify_mixed_and_euler.py --quick --output verification/inverse-euler-results.json
python verification/replay_ranks.py
python verification/replay_spectral.py
python ../reports/rational-grid-distribution-ranks/code/10-exact-structure-modular_rows.py --dps 65 --rows 36 --output verification/modular-row-results.json
python ../reports/alternating-harmonic-polylogarithms/code/11-reflection-transition-polylog_research.py --full --output verification/harmonic-replay
python ../reports/stieltjes-derivative-zeros/code/06-zero-geometry-exact_verify.py --input ../reports/stieltjes-derivative-zeros/data/06-zero-geometry-certificates.json --output verification/zero-sign-results.json
python ../reports/corpus-corrections/code/12-relation-spaces-verify_cubic_class_numbers.py --output verification/cubic-class-results.json
python verification/replay_cyclotomic.py
python ../reports/herglotz-cyclotomic-obstructions/code/verify_J_evaluations.py --digits 65 --max-even-m 40 --output verification/J-evaluation-results.json
python ../reports/herglotz-cyclotomic-obstructions/code/certified_intervals.py --output verification/Herglotz-interval-results.json
python ../reports/herglotz-cyclotomic-obstructions/code/verify_truncation.py --quick --digits 55 --output verification/Herglotz-truncation-results.json
```

The rank wrapper checks q<=20 and bridge orders through 3. The cyclotomic
wrapper performs exact elimination through q=40 and checks the rank and J
criteria through q=1000. The spectral wrapper uses the bounded `--quick
--no-figure` configuration and redirects the source module's output root.
The harmonic `--full` run uses its longer exact-certificate configuration.
Counts and arithmetic scopes are in [VALIDATION.md](../VALIDATION.md).

The SHA manifests pin a particular reviewed release. Replaying may change
execution-time or environment metadata. Do not refresh hashes to disguise a
changed source, failed check or unreviewed PDF; perform the relevant checks
and rendered review before recording a new release.

## Gaussian parity, ladders, moments and certified evaluation

```powershell
python verification/replay_gaussian.py --part 14
python verification/replay_gaussian.py --part 16
python verification/replay_gaussian.py --part 17
```

These runs restore the delivered filenames inside the ignored, isolated
`verification/.scratch-gaussian/` directory. Historical placed files are read
only. Fresh reports are copied to `verification/gaussian-replay/`. Part 14
replays the word algebra, exact depth and ladder substitutions, cubic moment
certificate and independent numerical depth/ladder checks. It bypasses the
delivery's plotting dependency, which its original driver required even in
fast mode. Part 16 tests interval arithmetic, symbolic specialization and 89
interval residuals with eight independent quadratures. Part 17 replays its
symbolic solver and six positive-measure midpoint certificates. The source
hashes and restored-file maps are recorded for each part.
