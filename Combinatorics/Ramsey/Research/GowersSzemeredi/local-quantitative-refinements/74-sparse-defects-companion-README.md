# Report286 exact companion

Run from any working directory with Python 3.10 or later on POSIX/Linux:

    python -B /path/to/Report286/companion/exact_checks.py
    python -O -B /path/to/Report286/companion/exact_checks.py
    python -B -m unittest discover -s /path/to/Report286/tests -p test_companion.py

Only the standard library is used. The two diagnostic commands emit byte-identical,
key-sorted JSON to standard output. They accept no arguments, write no files, use no
network, and do not invoke Lean. All checks use explicit exceptions rather than
Python `assert`, so optimization preserves them. The regression suite also runs
both modes from an unrelated temporary working directory.

## What is checked

- Every subgroup coset for moduli 6 through 120, with every permitted interval
  alphabet, and every nonzero value step, intercept and prefix of length at most
  the modulus for moduli 6 through 40
- Exact binomial lower/upper tails, including strict integer endpoint conventions.
  Each of 105 certificates gives an exact probability and rational base/exponent
  with `probability <= base^1024 <= exp(-x)`. The second inequality follows from
  `log(1-u) <= -u`; no numerical exponential is used
- All 1,282,400 unordered one- and two-entry affine lists, with repetition, on one
  fixed nonunit-step progression modulo 40. This checks the optimum, stability
  deficit, nonzero-slope constant restrictions, duplicates and outside-alphabet
  constants. This particular word is below the universal threshold and is not
  represented as a witness for the simultaneous-progression theorem
- All 5,440 binary subgroup-alphabet words at moduli 6, 8, 10 and 12, demonstrating
  why arbitrary-alphabet optimizer rigidity fails
- 9,664 finite sparse-map/binary-weight energy cases at moduli 2 through 7 and
  15 rational-weight examples, including composite moduli, noninterval support,
  empty support and zero weights. Independent four-index tests check ordered
  quadruple normalization. Empty map families impose no additivity condition;
  repeated nonempty families impose the same condition as a single map
- The exact multivariate polynomial factorization behind the optimized Holder
  bound, a sharp rational equality case, and rational cube-root enclosures
- The local `5Q/(4R) <= 5/16 < 1/2` mass accounting, including separate input
  graph-count bounds, summing over unequal two-axis cells and general dimensions
- Exact k=1 cube, remainder, good-domain and character-cancellation identities;
  general Boolean signs and counting identities for k=1 through 8; tractable
  exponent comparisons for k=1 through 32. Large arrangement sets are counted
  from their free coordinates, not exhaustively generated
- The coefficient-one affine rigidity boundary on all 3,413 one-variable maps
  at moduli 1 through 5, using exact ordered additive energy
- Six explicit logarithm ceilings and nonvacuity examples using rational
  atanh-series enclosures. Astronomical theorem parameters are never instantiated
- Bundled source bytes, fixed source identities, canonical RFC4648 base64 hashes,
  and raw Git blob hashes where applicable. Canonical base64 is a derived
  representation, not an original transport receipt. External archives are not
  bundled, and their membership is not reverified by this offline companion

These finite calculations support and guard the written proofs. They do not prove
universal existence by search, construct an astronomical universal word, certify
all real weights computationally, establish publication priority, or constitute
formal verification of the recorded Lean predicates.

## Bounded public helpers

The supported mathematical helpers are `rational`, `ceil_fraction`,
`ln_unit_bounds`, `ln_integer_bounds`, `exact_L0`,
`active_position_certificate`, `affine_list_coverage`,
`binomial_probability`, `cube_root_bounds`, `respected_energy`,
`sparse_energy_certificate`, `simultaneous_energy`, `dimension_certificate`,
and `local_cover_ratio`. Their docstrings describe their mathematical roles.
`run_all()` and the zero-argument `check_*()` functions run fixed diagnostic sets.

Inputs are built-in integers and `fractions.Fraction` values only: booleans,
floats, strings, arbitrary iterators and integer-like subclasses are rejected.
Rational inputs have numerator and denominator bit lengths at most 256.
Residue inputs must already be canonical; they are not silently reduced.
Lists/tuples must meet explicit length bounds before enumeration begins.

Enumeration bounds are modulus 256 for affine arithmetic, prefix length 4,096,
64 affine branches, energy modulus 16 and eight simultaneous maps. Binomial
inputs allow at most 1,024 trials and alphabet size 64. Logarithm series use
1 through 128 terms; their integer arguments have at most 256 bits. The
threshold helper allows modulus through `2^40`, and the dimension helper allows
1 through 32. Cube-root grid precision is between zero and 64 bits. Exact
computed outputs can exceed the input bit budget, by design.

Improper progressions, unsupported zero value steps, negative weights, repeated
support entries, nonzero values outside the declared sparse support, nonexact
values and oversized inputs fail explicitly. An empty sparse support is valid
only for a zero map. A singleton affine restriction is constant even when its
ambient slope is nonzero; an empty affine list is also supported.

Provenance reads are byte-bounded, single-link regular-file reads through
no-follow directory descriptors. Manifest and snapshot retargeting, symlinks,
hard links, FIFOs and oversized manifests are rejected. Fixed manifest pins
are part of the companion, so changing a source and coherently rewriting its
manifest does not silently replace the source identity.
