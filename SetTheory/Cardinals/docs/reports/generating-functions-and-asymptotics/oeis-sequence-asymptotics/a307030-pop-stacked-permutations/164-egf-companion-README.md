# Report164 exact companion

This self-contained Python 3 companion uses only the standard library. It
computes exact pop-stacked permutation counts (OEIS A307030), checks them by an
independent branch-free generating-function calculation, and verifies rational
intervals for the first positive pole and its amplitude.

## Run

From the package root:

```sh
python -B companion/pop_egf.py counts --n 70
python -B companion/pop_egf.py verify --n 70
python -B companion/pop_egf.py certify
python -B -m unittest discover -s companion -v
```

Each successful computation prints one deterministic JSON object to standard
output. The program does not create output files. Shell redirection may be used
if you choose to save an output. Invalid command-line inputs fail with status 2,
an explanatory message on standard error, and no JSON on standard output.
There are no path, upload, network, or output-file options.

Use `-B` to suppress Python's own bytecode-cache files. The module itself
performs no application file reads or writes and prints nothing on import.
Neither importing nor calling it starts a network connection. The exact gates
are ordinary conditional checks, not `assert`, and remain enabled with `-O`.

## Public functions and bounds

- `count_coefficients(n)` returns integer counts from p₀ through pₙ, inclusive;
  n must be a built-in integer from 0 through 400
- `quotient_coefficients(n)` independently computes those counts using rational
  ordinary power series of the branch-free quotient; n is restricted to 0…70
- `verify(n=70)` compares both routes with the frozen source fixture, includes
  divisibility and integrality checks, and checks a nonzero resultant
  specialization; n is restricted to 0…70
- `certify_constants()` returns the fixed exact interval certificate
- `resultant_nonzero_check()` computes the 4×4 Sylvester determinant at
  (z, P, P′, P″) = (0, 1, 0, 0), obtaining −12
- `main(argv=None)` is the command-line entry point

All three indexed functions reject booleans, strings, floats, integer-like
objects and out-of-range integers before allocating coefficient arrays or
starting coefficient work. Failures raise `TypeError`, `ValueError`, or
`VerificationError`. The count and verification limits also apply at the CLI.
In a Python session, add `companion` to the module search path and import
`pop_egf`; no package installation is needed.

## Methods and provenance

The count route extracts EGF coefficients from the exact Riccati equation in
Report164. Four sums are evaluated with binomial coefficients generated one at
a time; the implementation stores count, square-convolution and
weighted-square-convolution sequences. Through pₙ this costs O(N²) arithmetic
operations and O(N) scalar entries. These are not bit-complexity or byte-memory
bounds: exact integers become larger as N increases.

The independent check constructs exp(z), exp(z/2), exp(−z), H and J₀ as rational
ordinary series, performs formal quotient division, then multiplies the nth
coefficient by n!. It never calls the Riccati recurrence. The slower quotient
route is deliberately limited to degree 70.

`../data/counts_p0_p70.json` contains the 71 frozen reference values and their
provenance. The same values are embedded in the module so computations need no
runtime data-file access. The source is the existing Report161 count artifact,
computed from the published Claesson–Gudmundsson–Pantone endpoint recurrence.
Only p₁…p₂₅ are the posted OEIS terms checked in that earlier package; p₂₆…p₇₀
are earlier endpoint-recurrence computations, not additional posted OEIS data.
p₀ = 1 is the empty-permutation convention. The original artifact's SHA-256 is
recorded in the fixture and verification output. Report161 is unchanged.

Primary references:

- [OEIS A307030](https://oeis.org/A307030)
- [Counting pop-stacked permutations in polynomial time](https://arxiv.org/abs/1908.08910)

## Exact interval certificate

The certificate uses `Fraction` throughout, with a degree-200 positive Taylor
bound for exp, an integer-square-root enclosure on a 10⁻¹²⁰ grid, and
alternating sine/cosine Taylor bounds through index 60. It verifies the
hypotheses, opposite strict denominator signs at the endpoints, propagation of
the amplitude formula, and outward decimal rounding. No binary floating point,
third-party numerical package, numerical fitting, or trusted approximate
transcendental constant is used.

The strict enclosures verified are:

```text
1.11343904173672704376166152691808324014139016583344946615 < rho
  < 1.11343904173672704376166152691808324014139016583344946616

0.695688549070635767995703168724110156574198350721 < C
  < 0.695688549070635767995703168724110156574198350722
```

Identifying this denominator sign change with the first positive pole uses the
phase-monotonicity proof in Report164. The finite computations do not replace
that proof. They do not locate nonreal poles, certify a numerical next-pole
modulus, provide an effective coefficient-error constant or onset, or establish
convergence of an infinite pole sum. The one resultant specialization proves
that the displayed resultant polynomial is not identically zero; it does not
prove a minimal differential order or a uniqueness characterization.

## Tests

The tests cover all public numerical bounds, rejection before computation,
clean import, source-fixture parity, both independent routes through degree 70,
counts through degree 400, exact interval signs, resultant specialization,
deterministic JSON, and byte-for-byte equality of normal and `-O` CLI output.
They also deliberately violate certificate and recurrence checks to ensure the
gates stay active. The test runner reads only its own fixed fixture and source
for these checks; unlike the computation CLI, it starts local Python subprocesses.
