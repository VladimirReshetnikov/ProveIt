# Optional numerical diagnostics

Nothing in this directory is imported or executed by the core exact verifier or
normal build. The builder only checks the preserved scout scripts' SHA-256 pins
and includes their bytes. The core uses Python's standard library and TeX.

The `scout/` directory contains unmodified frozen originals:

- `verify_nested_partitions.py`: integer-packed coefficients, direct small product
  and composition comparisons, floating-point free energy and saddle/Edgeworth diagnostics
- `verify_marked.py`: integer-packed block-count moments and numerical comparisons
- `verify_maximum.py`: integer-packed maximum-leader counts and numerical Gumbel comparisons

These originals require mpmath, contain removable `assert` statements, and write
results beside their own files. Do not run them in the release package. Use:

    python -B optional/run_diagnostics.py --output /existing/parent/new-diagnostics

The wrapper copies the scripts to temporary storage, runs them there, and
publishes diagnostic JSON, text and logs to a new external directory. It refuses
an existing output or an output inside the package. Optional outputs include
wall-clock timings and are not expected to be byte-identical. Installing optional
requirements is a separate user action; the build never installs software or uses
the network.

The frozen numerical results shipped under `data/references/` are historical
records. Their decimal values do not have certified roundoff or tail enclosures.
They do not prove minor-arc estimates, differentiated remainders, saddle errors,
conditioned limit laws, inverse estimates, global novelty, or any asymptotic
statement. The proofs are in `Report181.tex`; the finite exact independent checks
are in `code/`, with scope documented in `README_CODE.md`.
