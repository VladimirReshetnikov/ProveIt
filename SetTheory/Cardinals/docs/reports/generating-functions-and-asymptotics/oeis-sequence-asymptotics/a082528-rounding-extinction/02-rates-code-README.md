# Exact replay code

This is original Python standard-library code for the finite checks in Report188.
Python 3.10 or later is sufficient. No network access or third-party dependency
is needed. Paths are resolved from the scripts, so the commands work from any
current working directory when the script path is absolute.

From the source root:

```sh
python3 -I -S -B code/check_exact.py --output ../report188-exact-normal.json
python3 -I -S -B -O code/check_exact.py --output ../report188-exact-optimized.json
cmp ../report188-exact-normal.json ../report188-exact-optimized.json
```

Choose a fresh `--output` file outside the source package, in an existing parent
directory. Existing files, output paths inside the package, and symlink paths
are rejected. Relative paths are resolved before checking the package boundary;
the `../` examples above put results beside the source directory. The checker
writes the JSON file and the same JSON to stdout; without `--output` it only
writes stdout. Both scripts disable bytecode creation before importing their
sibling module, including when run with plain `python3 -I`. They create no cache,
fetch no data, and change no source files. A failure raises an explicit exception and exits nonzero. Optimization
mode does not remove the checks: no Python `assert` statement is used.

## Files and arithmetic

- `exact_rounding.py`: validated exact rational-power forward and reverse maps,
  positive terminal-mass thresholds, stopping indices, rational finite products,
  `exp(I_p(u))`, and the rational inverse profile `U_p(t)`
- `check_exact.py`: required finite replay suite and an independent reference
  that finds each forward quotient and then the initial threshold by binary
  search; the reference does not call the production root or reverse algorithms
- `diagnose_float.py`: optional, separate floating Gamma/ratio diagnostics;
  never imported or called by the required checker
- `../data/oeis_fixtures.json`: 342 bounded, attributed integer reference terms

`rational_power(a, b)` requires strictly positive integer numerator and
denominator and reduces the fraction. The numeric APIs otherwise accept exact
positive `int` or `fractions.Fraction` powers. Floats, bools, and nonpositive
powers are rejected. Integer indices and masses are likewise checked, including
bool rejection. `n=0` is valid and has stopping index 1. Threshold routines require
`k>=1` and `h>=1`; they deliberately reject `h=0`, outside the positive-terminal
threshold theorem. `invariant_exp` allows `u=0`; the profile API requires
`0<t<=1`, excluding the Gamma-valued endpoint at zero.

For `p=a/b`, rounding uses only integer inequalities such as
`j**a * r**b >= (j+1)**a * q**b`. The production root routine uses integer Newton
iteration (`isqrt` for degree 2). The independent reference uses binary search.
All mandatory profile calculations use `Fraction`; because `H_p(t)` itself need
not be rational, `profile_mass_power` returns its exact `b`th power. No Gamma,
logarithm, floating root, or floating exponential is used in the required suite.

## Finite domains and limits

The mandatory suite records its domains and actual check counts in its JSON:

- 342 OEIS terms from four sequences, with fixed offsets and counts
- Exact floor/ceiling roots for `0<=A<=80`, `1<=B<=13`, `1<=b<=7`
- Nine powers `1/3,1/2,2/3,1,3/2,2,5/2,3,4`, every minimal trajectory through
  `1<=k<=60`, both adjacent stopping boundaries, and every trajectory entry
- Drift sandwiches for those trajectories; exact telescoping residue/tail
  checks for the integer powers among them
- Positive terminal profiles through `1<=k<=30` with distinct
  `h` in `{1,2,max(1,k//2),k,2*k}`, both boundaries, full forward realization,
  and independently searched thresholds
- Independent forward comparisons for every `0<=n<=80`, `1<=k<=12`
- Thirty product cells per power, both formulas at shared endpoints, and exact
  inverse/profile checks at endpoints and quarter-cell rational points
- Intentional fixture/profile corruption and strict input-domain rejection
- Exact threshold sample computations for six powers at `k=100,1000,10000`

The threshold samples are computed outputs, not a separately certified database.
The tests verify bounded arithmetic identities and conventions. They do not
constitute a formal proof of the asymptotic theorems, verify an infinite-domain
error bound, establish novelty, or certify floating Gamma intervals. The general
real-power theorem is analytic; executable rounding here has rational `p` only.

Optional diagnostics, kept outside the mandatory certificate:

```sh
python3 -I -S -B code/diagnose_float.py --output ../report188-floating-diagnostics.json
```

These floating values are explicitly diagnostic and may depend on the platform's
`libm`. In particular, they do not claim rigorous decimal enclosures for Gamma
constants or the all-index analytic threshold envelope.
