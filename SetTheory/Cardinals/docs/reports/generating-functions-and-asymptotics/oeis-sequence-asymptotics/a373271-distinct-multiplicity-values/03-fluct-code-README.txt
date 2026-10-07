# Independent finite verification

Run from the article directory:

    python3 code/verify.py

The checked environment uses Python 3.12.14, NumPy 2.3.5, and mpmath 1.3.0.
The latter two dependencies are listed in requirements.txt. The program never
downloads or installs anything.

The default run writes four named outputs under data/:

- checks.json: exact finite checks, numerical identities, moving-window
  diagnostics, and simulation summaries;
- exact_partition_moments.csv: exact first and second raw moment totals;
- boltzmann_samples.csv: the 6,000 seeded finite-row samples;
- boltzmann_histograms.json: fixed-bin histograms of the recorded samples.

The default exact enumeration covers every ordinary partition of every n from
0 through 40: 215,308 partitions in total. Its D0, D1, D2 first and second
moments and D0-D1 cross moment must agree exactly with a separate positive
generating-function DP forbidding one or two exact multiplicity values.
Euler's pentagonal recurrence separately checks the partition numbers.
The first ten displayed values of A373271 and A373273 are checked.

The floating-point section independently evaluates the covariance integral
reduction, its closed constant, regularized Mellin integrals, and Gumbel
moments. It also compares exact finite Bernoulli-product formulae (with a
documented part-size cutoff) against the limiting covariance kernel on the
moving multiplicity window 0.75 <= sqrt(t) m <= 2.5. These calculations are
not directed-rounding interval certificates.

The simulation uses independent geometric multiplicities for part sizes
j <= ceil(40/sqrt(t)), at t = 10^-4, 10^-5, and 10^-6. Each t has 2,000
samples from NumPy PCG64 with recorded seeds. These are unconditioned,
finite-row Boltzmann samples; they are not uniform partitions of an exact
integer. Omitted rows are not simulated. The critical one-half exponent
converges only logarithmically, so visible finite-size variance discrepancies
are expected and are retained in the outputs. No seed or sample is selected
or discarded according to whether it matches the theorem.

Use --samples to change the sample count and --seed to change the seed.
Such a run intentionally produces different diagnostics. With the default
parameters, deterministic byte reproduction is expected for the same Python,
NumPy, and mpmath versions, subject to platform floating-point behavior.

For a quicker exact-and-analytic replay without simulations:

    python3 -O code/verify.py --skip-simulations --output-dir /tmp/partition-checks

Choose the output directory yourself. The directory is created if necessary.
The program replaces only its documented output filenames in that directory.
No correctness or input-range check depends on Python assert.

Finite computations verify their finite statements and the implementation.
The all-size assertions depend on the proofs in the article.

Publication figures can be regenerated independently with:

    python3 code/make_figures.py

This also requires Matplotlib 3.10.8, recorded in requirements.txt. It reads
the existing checks and sample CSV without changing them, verifies the V0
integral against the closed expression and the recorded constant, and writes
two vector PDFs to figures/. Its empirical CDFs retain every recorded sample.
The code docstring records the exact dependencies and optional visual-preview
command. No TeX installation, raster asset, or image-generation tool is used.
