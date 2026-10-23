# Concrete equation in seventeen unrestricted integers

This folder contains a new signed-domain specialization of the fully fixed
Jones construction in ProveIt package `18-jones9`, pinned to commit
`ae3007ca4467011e0e051c84acb4a1dd13971b0e`.

The ordinary mathematical proof establishes, using the existing package's
Jones ratio, compiler, and K215 calibration theorems,

\[
\mathrm{ZFC}\vdash
\bigl(\nexists\mathbf z\in\mathbb Z^{17}:P_{17}(\mathbf z)=0\bigr)
\longleftrightarrow\operatorname{Con}(\mathrm{ZFC}).
\]

The polynomial uses exactly 17 unrestricted integer variables. Its exact
degree is `424296*5^33+53824`, and its division-free arithmetic DAG has 20,607
binary operations (672 additions, 26 subtractions, 19,909 multiplications).
Coefficient construction is outside that evaluation-gate count. This is a
concrete variable-count improvement within the inspected compiler family;
it is neither a universal-variable record nor a low-degree improvement.

## Files

- `SIGNED17_PROOF.md`: full definitions, seven new lemmas, equivalence proof,
  degree argument, source boundaries, and limitations.
- `signed17_section.tex`: the same proof converted to LaTeX for incorporation
  in the parent report; it is an input section, not a standalone document.
- `build_signed17.py`: standard-library generator and finite diagnostic checks.
- `generated/signed17.json`: the complete finite polynomial DAG, including
  all literal leaves, variable names, and exact references for fixed leaves.
- `generated/signed17_checks.json`: generated check receipt, not a proof-assistant
  certificate.
- `SOURCE_PINS.json`: Git blob hashes and SHA-256 hashes for all nineteen
  imported source files.
- `upstream/`: the byte-exact source modules, coefficient recipes, ordered
  tile list, quartic, provenance, and licenses needed to rebuild the DAG.

## Rebuild

Run from any working directory:

```sh
python3 -B /path/to/this/folder/build_signed17.py
```

The script checks every source pin, rebuilds the DAG, certifies the exact
degree through a nonzero diagonal leading coefficient, and runs deterministic
finite diagnostics. These include actual fixed-instance modular evaluations,
the eight-factor norm identity, small-modulus intersectivity tests, the
consecutive-square inequality, and the signed-coordinate symmetry.

The construction uses the complete original T4 coefficient tuple. The smaller
943-tile tuple is not substituted into individual ports. Any future rebinding
must prove the full quartic/compiler interface for the new tuple.

The upstream license and attribution files are preserved in `upstream/`.
