# Exact finite verification

This directory accompanies *Uniform avoidance of geometric progressions and
exponential-polynomial patterns*. It contains a deterministic, standard-library
Python program and its machine-readable output:

- `verify_exact.py` implements the checks.
- `results.json` records the complete summary of the successful run.

Run from the article directory with Python 3.10 or later:

```bash
python3 verification/verify_exact.py
```

To write the result somewhere else:

```bash
python3 verification/verify_exact.py --output /tmp/uniform-avoidance-results.json
```

The program uses `fractions.Fraction` and arbitrary-precision integers. It
does not use floating-point logarithms, numerical optimization, random
sampling, or a Monte Carlo estimate. A failed condition raises an exception;
the checks remain active when Python is invoked with `-O`. The output is
deterministic and omits timestamps and machine-dependent timing data.

## What was checked

The accompanying run passed **91,759 exact conditions**. This number counts
individual equality, inequality, address, and combinatorial checks; it does
not count each enumerated probability-space assignment as a separate theorem
check.

| Part of the argument | Finite coverage |
| --- | --- |
| First-crossing subsequence | 24 levels for 53, 79, and 35 rational ratios in three compact bands: 4,008 ratio–level cases, with overlap between the bands |
| Exponent jump boundaries | 24 exact equalities at `q = 1/2`, with a rational point on each side; the equality uses the smaller exponent |
| Positive mixtures | Five rational mixtures, each through 24 synchronized levels; zero coefficients and repeated bases are included |
| Preorder windows | 162 choices of branching, height, gap, initial window length, and starting index; 3,312 edge instances |
| Common grids | 80 nested dyadic grid levels; 1,800 rational point configurations for separation and preservation of earlier keys |
| Half-open conventions | 20 cases at or beside an exact boundary, distinguishing departure from a left boundary from arrival at the next boundary |
| Conditional routing | Two full probability-space enumerations, of 256 and 262,144 assignments; all joint test-outcome probabilities are checked at `p = 1/3, 2/5, 1/2` |
| Center route | Six complete finite center-selector enumerations; the largest has 32,768 assignments; the first-default distribution is checked at every depth |
| Periodic assembly | 256 exact budget cases, 28 signed contraction cases, translated unit-interval checks, and 350 signed scale normalizations |

### Synchronization and grids

The least exponent `nu` satisfying `q**nu <= Q**j` is found by integer binary
search and exact rational powers. The program checks minimality, the strict
lower and weak upper spatial bounds, the exponent bound `nu <= T*j`, strict
growth with the level, separation of successive synchronized values, and
monotonicity of the exponent in the ratio. The jump tests specifically check
the convention at an equality.

The common grid size is the least power of two above its rational target.
Grid keys are computed from the floor of `N*z`, reduced modulo `N`; this
also handles negative points and wraparound. The stability test finds the
next grid boundary strictly to the right of the center and checks whether
the translated interval reaches it. Actual earlier keys, pairwise test-point
keys, and finest-subtree keys are then compared.

For the window checks, the program builds an explicit preorder edge list,
places all intervals with their intervening gaps, identifies each descendant
block by its path, and checks its contiguity and span. The largest endpoint
is also compared with the displayed affine formula in the initial window
length. Thus the check compares the concrete list of assigned windows with
the global formula.

### Adaptive terminal routing

The first routing enumeration is the compressed table-address pattern of
two test points: each has an independent gate and a selector choosing one
of two leaves. Each potential terminal entry is enumerated, including
entries on leaves not selected in a given selector realization.

The second enumeration deliberately allows additional dependence. In each
of two child subtrees, two points share a subtree selector, and each point's
selected leaf also depends on the other point's gate. Each point retains
its own key within every possible leaf. The selected terminal addresses are
therefore distinct for every selector realization. This stress case is an
abstract test of the conditioning argument; the extra dependence is not
claimed to be an instance of every geometric routing constraint.

All `2^6` selector assignments and `2^12` terminal assignments in this model
are enumerated. Terminal assignments with different numbers of ones receive
their exact Bernoulli weights for each specified `p`. For all 16 joint test
outcomes, the resulting probability agrees with that of four independent
Bernoulli-`p/2` tests. In particular, the all-failure probabilities are:

| `p` | Exact probability | Formula |
| --- | --- | --- |
| `1/3` | `625/1296` | `(1-p/2)^4` |
| `2/5` | `256/625` | `(1-p/2)^4` |
| `1/2` | `81/256` | `(1-p/2)^4` |

The exposed center entries are held fixed and do not alias the unexposed
gate entries in these models. This is the condition supplied by grid
separation in the proof.

An **intentional negative control** gives two tests a common terminal
entry. Its all-failure probability is `1-3*p/4`, exceeding the claimed
independent-address expression by `p*(1-p)/4`. The program requires this
inequality to hold. This verifies that the check detects the precise
terminal-aliasing error that the proof must exclude; the negative control
is an expected failure of the identity under a violated hypothesis.

### Periodic density and scale normalization

The density tests compute exact lengths of unions of rational intervals,
including overlaps, reflections, dyadic contractions, and translated unit
intervals. A dyadic contraction of a 1-periodic set has the **same unit
density**, because the unit interval contains more periods. The check does
not insert an erroneous additional density factor of `2^-k`.

The rectangular budget sum and its omitted tail are compared exactly:

```text
full signed density budget = eta/2
tail beyond m <= M, k <= K
  = (eta/2)*(2^-M + 2^-(K+1) - 2^-(M+K+1))
  <= (eta/2)*(2^-M + 2^-(K+1)).
```

The scale tests verify the equality transporting a hit at normalized scale
back to a tail of the original signed affine progression.

## Scope and limitations

These computations provide independently reproducible finite checks of
selected arithmetic identities, indexing conventions, probability laws,
and density bookkeeping used in the manuscript. They are useful for
detecting implementation or transcription errors at those points.

They do **not** establish the universal quantifiers in the theorem, prove
the line-arrangement or polynomial sign-condition bounds, instantiate the
large probabilistic construction, run real quantifier elimination, build
the infinite avoiding set, certify publication priority, or constitute Lean
formalization. The manuscript supplies the proofs of the mathematical
statements. In particular, finite samples of ratios and centers are not
presented as evidence sufficient for simultaneous avoidance over all real
parameters.
