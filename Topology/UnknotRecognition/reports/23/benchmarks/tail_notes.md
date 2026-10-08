# Finite-cap homology measurements

`long_tail_benchmark.json` records seven seeded, shuffled paired rounds on
sixteen signed-run inputs. Every round computes the ordinary macro homology
twice (an A/A control) and the finite-cap homology once. Each timed answer
is compared in every homological degree. Input construction is excluded;
complex construction and exact rank work are included. The finite-cap arm
also checks the interior matrix square. No word simplification or homology
cache is used.

These are **raw homology measurements**. The existing structural criteria
already decide all of these long-tail knots. The finite-cap speedups must
not be reported as new recognition coverage or as speedups of hard unknot
instances.

`long_tail_summary.csv` gives median times, median paired speedups, median
A/A ratios, and the chain basis sizes. A median paired speedup is not
necessarily the ratio of the two median times. The shared virtual execution
environment was uncontrolled; the A/A medians range from approximately
0.827 to 1.194. The final measured kernel SHA-256 is recorded in the raw
JSON and matches the bundled `fastunknot/twist/long_tail.py`.

The bundled benchmark driver changes only import and default output paths
from the measured driver. Its hash is recorded separately as
`portable_driver_sha256`; `benchmark_sha256` identifies the measured driver.
The timed functions, cases, budgets, seed, and comparison protocol are
unchanged. The relative-path driver is runnable from any current directory.

From the package root, repeat the benchmark with:

```bash
python benchmarks/benchmark_long_tail.py --rounds 7
```

The default output is `benchmarks/long_tail_benchmark.json`, resolved relative
to the driver itself. Use `--output` to retain the delivered measurements.
Reproduced timing values will differ between runs and machines.

The full signed-run homology verification is:

```bash
cd implementation/fast
python -m unittest discover -s tests -p test_long_tail.py -v
```

The twelve test methods include 240 full degree-profile comparisons, 80
checks of the earlier scalar-rank threshold, 32 exact interior-matrix
comparisons, and 24 independent crossing-cube comparisons. They also cover
both selected signs, arbitrary selected positions, cap component parity,
resource guards, certificate tampering, and 20,001-bit exponents without
expanding their output intervals. Counts are presentations or contexts,
not distinct knots.

## Runnable enormous examples

Both files below use the exact integer `M = 10^100 + 1` as an ordinary JSON
number. They contain only a finite list of signed runs; no expanded word or
PD diagram is constructed by the symbolic CLI.

`examples/four_strand_tail.json` represents

```text
sigma_2^-1 sigma_1 sigma_2 sigma_3^M sigma_2^-1 sigma_1 sigma_3^-1.
```

Its context crossing count is six. The homology algorithm uses exponent
eight, builds 1,650 basis elements, and reconstructs the exact original rank
`3*10^100 + 1` together with all homological degrees as eleven points and
one constant interval. The capped braid is a two-component link; the input
is a knot. This distinction is intentional and checked.

From `implementation/fast`, run:

```bash
python -m fastunknot.symbolic_braid ../../examples/four_strand_tail.json --mode homology --check-d2
```

`examples/balanced_four_runs.json` is the five-strand closure

```text
sigma_1^M sigma_2^-M sigma_3^M sigma_4^-M.
```

Its total writhe is zero and none of its four runs dominates the rest. The
signed Seifert graph is homogeneous and has canonical genus `2*10^100`,
so the symbolic structural frontend certifies `KNOTTED` directly. This is
an evaluation of the existing homogeneous-diagram criterion on succinct
input, not an application of the one-run cap theorem.

From `implementation/fast`, run:

```bash
python -m fastunknot.symbolic_braid ../../examples/balanced_four_runs.json --mode certificate
```
