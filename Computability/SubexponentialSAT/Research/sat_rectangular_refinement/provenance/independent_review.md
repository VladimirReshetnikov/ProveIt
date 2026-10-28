# Independent finite-certificate review

The frozen support certificates and the fully paid new schedule passed an
independent reconstruction. This review does not re-prove the imported
SAT reduction, deformation identities, or external matrix algorithms.
The separate quadratic appendix is a final-triangle-only result and is not
used in the global time or space coefficients.

## Self-contained reproduction

From the archive root, run:

```sh
python3 code/independent_audit.py
python3 -O code/independent_audit.py
```

The default input is `data/certificate.json`, located relative to the script.
An alternative data path can be selected with `--data PATH`. No source checkout,
network connection, third-party package, proof assistant, or other archive
module is required. The script reads only that selected JSON file, writes no
files, and prints one JSON object on standard output. Redirect the output if
a new result file is desired. Exceptions and explicit checks remain active
under Python optimization.

The work is finite and CPU-bound. A run checks 31,352,832 support triples at
the root, as well as all remaining pair certificates and rational schedule
inequalities. In particular, the thirteen-group cyclic menu checks 764,478
pairs of supports. Runtime depends on the interpreter and CPU; these are
certificate checks, with no SAT instance as input and no SAT runtime benchmark.

The delivered `results/independent_incoming_audit.json` records the complete
independent run. Its negative-control subobject is also presented separately
in `results/independent_negative_controls.json`. Normal and `-O` executions
produced identical JSON objects during preparation of this archive.

## Independent reconstruction

`code/independent_audit.py` imports no code from the main checker. It builds
the contraction operations using ordinary vertex-label maps, independently
of the main checker's bit-set representation. It then recomputes all seven
new exact squared coefficients from the supplied plans, coefficient triples,
and integer mixing weights. Every expected rational coefficient matched.

Each plan includes exactly r-3 internal merges and one final triangle, for
r-2 operations in total. All nine coefficient permutations of the two
backend branches are included for every operation. This gives 9(r-2)
supports per plan. Internal block construction is therefore part of these
certificates.

For q=9, each squared norm occurs in C(8,2)=28 triple brackets. Each pair
dot product occurs in seven triples and is multiplied by q-1=8, giving 56
before division by 28 and the required factor two afterward. Thus the
cross multiplier eight and denominator 28 W^2 are correct. Taking separate
triple maxima gives an upper bound; simultaneous attainment is not assumed.

## Paid schedule and exact arithmetic

The independent code rebuilds the child masses, prefix cache contributions,
local aggregation bounds, entire geometric tail, and local space maxima.
It confirms that the new time maximum is the infinite cache tail and that
the space maximum is the root. The time and space upper endpoints are
strictly below the frozen safe coefficients 28.434 and 28.306, respectively.

It also verifies each rational logarithm bound by integer powers, each strict
old-side degree gate, the cumulative taper fractions, the fresh-side gate,
and the tail-ratio inequalities needed for the depth bootstrap. The final
cumulative fraction is 499999/10000000, strictly below 1/20.

For the independent numerical enclosures, pi is bounded using alternating
arctangent series and Machin's identity; log(2) is bounded by the positive
atanh series with its geometric remainder. Integer square roots give rational
square-root enclosures. These use different truncation lengths and precision
from the main checker. No floating-point value is an acceptance condition.

The analytic explanation in the paper separately charges floor errors,
logarithmic precision guards, input access, original and fresh entry
routines, and direct leaves. The finite code verifies the constants and
strict gates used by that argument; it is not a formal proof of all
asymptotic statements.

## Negative controls

The independent script actually executes and catches the expected failures:

- Removing the input/output branch from a rectangular envelope leaves the
  dimensions (1,1,0) unpaid and is rejected.
- Replacing the safe time claim by 28.43 is rejected by the rational interval
  acceptance test.
- Replacing the root upper bound on log2(10) by 3.32 is rejected by the
  integer-power test.
- A partition containing a duplicate vertex and missing another vertex is
  rejected before support construction.

The recorded error messages are checked, so an unrelated exception does not
count as successful rejection.

## Limits of the verification

The positive conclusions concern the certified exponential coefficients
in the normalized tensor-network interface. They establish neither a
smaller logarithmic exponent order for unrestricted 3-SAT nor an end-to-end
implemented SAT solver. The checks do not establish a practical speedup or
a Lean formalization. The new local quadratic lemma has its own exact
algebraic checker and remains outside the fully paid coefficient calculation.
