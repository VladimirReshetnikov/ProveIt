# Independent review of the paid double-exponential input

PASS on the frozen [author source](three_mass_double_exponential_input.py),
[receipt](three_mass_double_exponential_input.json), and
[proof](three_mass_double_exponential_input.md), with source SHA256
`cd595535905dc3302144de243d3cc5430294c453f0bc5110b8eff973d4049070`.
No correction is requested. The [independent checker](review_three_mass_double_exponential_input.py)
authenticates those three files and all six parent files before executing
only the current author's definitions for public-interface checks.
Its [receipt](review_three_mass_double_exponential_input.json) records
independent complete-source reconstruction and bounded evaluations.

## The mathematical interface

Write the first exponent component's computed output as
`Q1=48x+delta1` and unit product as `U1`. On every permitted supplied tuple,
`x,delta1>=1`, so `Q1>=49`. For every fixed positive integer `C`, the virtual
input `C*Q1` of the single-layer parent therefore satisfies that parent's
positive input contract before any equation is assumed.

The complete new polynomial is exactly

    Fdouble = (U1-1)^2 + Fsingle(C*Q1,y,T).

The complete parent is already a sum of 21 squared residuals. The new
polynomial is their sum, after substitution, plus the first exponent square.
Consequently its natural/positive zeros require each exponent unit separately
at +1 and every history residual at zero. The inherited exponent relations give
`Q1=2^(96x)` and `Q2=2^(96*C*Q1)`. The reverse direction first extends the
first exponent, then the second at its positive input, then a true first-halting
raw history at payload `Q2`. Fresh private coordinates share only the stated
computed interface. This is an existential extension theorem, not a uniqueness
claim or a bijection with arbitrary raw-input histories.

The sole actual consumer of the parent's input is `exp__r=48*x`, with no
comparison directly consuming that parameter. Replacing it by
`exp__r=(48*C)*first__Q` is the all-value identity
`48*(C*Q1)=(48*C)*Q1`. The checker verifies the literal parent row, the actual
first two exponent rows, and the coefficient vectors in `x,first__delta`.
It then compares every complete downstream expression in a common exact
expression table, using this proved affine identity as its sole cut. All
168 retained comparison pairs in the eight emitted forms are preserved.

This identity applies also to signed and rational assignments. Semantic
positive extensions still require the documented integer domains. `C` is a
fixed compiler numeral, so folding `48C` charges one constant multiplication.
A variable program input would require a different paid interface.

## Independent complete counts

Both emitted fixed multipliers, C=1 and C=3, have these counts:

|Source|Certificate M+A|Complete M+A|Complete total|Private positive witnesses|Degree upper bound|
|---|---:|---:|---:|---:|---:|
|INC2;DEC2|278+362|300+405|705|83|2344|
|Prime-three zero test|223+292|245+335|580|81|1192|
|No-op|221+292|243+335|578|81|1192|
|Prime-three positive test|228+288|250+331|581|81|1192|

Each complete source has 22 squared residuals. The added 51-gate exponent
certificate and three finalizer gates cost exactly 54=32M+22A, with 12 new
positive witnesses. All 4,888 gates across the eight full sources were
independently recounted and checked for topological closure and liveness,
including liveness of every supplied coordinate. The first square has degree
108; the virtual input substitution is affine. Thus the inherited upper bounds
remain 2344/1192. These are upper bounds, not independently established exact
degrees. Quantifying the supplied natural output and clock as positive
witnesses adds two witnesses; at these accepted histories both are positive.

## Separate exponent signs are necessary

The exponent parent's proved negative-unit extension gives, on positive
inputs, `U1=U2=-1`,
`Q1=2^(96x-4)`, and `Q2=2^(96*C*Q1-4)`. For example at x=C=1, the second
exponent is positive and congruent 92 modulo 96. The raw no-op source accepts
that payload and has a positive history extension. An unchecked finalizer
`U1*U2*(1+S_history)-1` would therefore be zero, while the actual two exponent
squares sum to eight. This counterexample follows from the inherited positive
extension theorems; the enormous full Pell tuple was not materialized.

An additional compiled divide96 prefix could reject the second negative
branch. None of the four measured tables contains that prefix, so it cannot
justify removing a constraint from these sources.

## Scope and reproducibility

The source valuations are `(96*C*2^(96x),0)`. The separate
[prime-power input theorem](three_mass_prime_power_input_theorem.md) supplies a
source-language construction, including an outer divide96 and a different
virtual divide96 before prime compression. Neither that program nor a universal
instruction table is hidden in the four measured examples. The existing clock
counts physical evolution after initialization; arithmetic generation of the
initial payload contributes no physical ticks. Adding source preprocessing
requires a new complete table and clock relation.

The independent checker reconstructs every full source from the pinned parent
JSON instead of invoking the author's rewrite or verification functions. It
checks eight exact output identities, 96 independent full-output and 22-square
sum evaluations (32 rational), 80 malformed input rejections, eight defensive
copies, six modified-parent pin failures, and three additional fixed positive
multipliers. It uses the authenticated author's build/check/evaluate functions
only for public API checks. General semantic equivalence uses the proofs above
and the inherited positive-extension theorems, rather than the finite tests.

Reproduce with Python's standard library, supplying explicit paths:

```sh
python review_three_mass_double_exponential_input.py \
  --source three_mass_double_exponential_input.py \
  --receipt three_mass_double_exponential_input.json \
  --note three_mass_double_exponential_input.md \
  --root /path/to/native-stream-queue \
  --expect review_three_mass_double_exponential_input.json
```

The review does not fetch the internet, replay historical author suites,
execute parent Python modules, or modify repository files.
