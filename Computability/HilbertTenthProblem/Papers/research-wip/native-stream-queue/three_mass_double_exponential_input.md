# Paid double-exponential input for unbounded three-mass histories

The [complete source](three_mass_double_exponential_input.py) supplies the
prime-power scale needed by the source-input theorem in
[the companion protocol note](three_mass_prime_power_input_theorem.md).
It adds a second positive exponent component to the already reviewed
[single-layer bridge](three_mass_exponential_input_bridge.md). For a fixed
positive integer C and positive ordinary input x, the exact initial payload is

    Q1=2^(96x),       N0=Q2=2^(96*C*Q1).

Thus the source counter valuations are `(96*C*2^(96x),0)`. Four complete
nonuniversal source examples cost **705/580/578/581** operations, with no
external time horizon. Their degree upper bounds remain2344/1192. The
[receipt](three_mass_double_exponential_input.json) emits every gate for
each example at C=1 and C=3. These are fully measured input/history examples;
the division prefix and the reversible universal simulation are separate
source programs and are not included in these four totals.

## 1. A positive intermediate input, with its whole source paid

Let the first copy of the [52-operation exponent component](pell_fixed_affine_exponent52.md)
have unit product U1 and computed output

    Q1=48x+delta1.

Use all51 of its certificate gates and its12 positive private witnesses,
with a fresh `first__` prefix. On every permitted supplied tuple, Q1>=49.
Consequently the virtual input z=C*Q1 to the parent single-layer bridge
is a positive integer before any equation is used.

Let F_single(z,y,T) be that parent's complete default polynomial. It is
the sum of21 squared residuals: its second exponent residual and all20
unbounded history/clock residuals. The new complete polynomial is

    F_double=(U1-1)^2+F_single(C*Q1,y,T).                 (1)

The source contains every gate of both terms. The last three gates compute
U1-1, its square, and addition of the full parent polynomial. Equation(1)
vanishes exactly when U1=1 and F_single=0. The two inherited exponent
theorems therefore give

    Q1=2^(96x),       Q2=2^(96*C*Q1).

Conversely every x>0 has positive first-exponent witnesses. The positive
integer C*Q1 then has positive second-exponent witnesses. For any actual
first-halting source trajectory at payload Q2, the inherited unbounded
history theorem supplies the remaining positive coordinates. Their only
shared interfaces are the computed powers. This proves both existential
directions; no uniqueness or arbitrary-raw-history bijection is asserted.

The external y and T remain natural integers. Positive final payload is
still imposed by the inherited comparison. Every accepted source here has
at least one transition, so T is positive at a zero as well. Quantifying
y,T as positive witnesses gives a one-parameter halting predicate and adds
two witnesses, with no arithmetic gate change.

## 2. Fixed program coefficients require no additional product

The entire parent's only consumer of z is the actual row

    exp__r=48*z.

It has no direct comparison consumer. Replace it by

    exp__r=(48*C)*Q1.                                  (2)

C is a fixed positive compiler numeral. The coefficient48C is computed
when the source is emitted, and its multiplication by Q1 costs one gate,
just as the old multiplication by48 did. The exact identity
`48*(C*Q1)=(48*C)*Q1` holds on all supplied tuples. No separate register
for C*Q1 is needed. Every other parent register and comparison is retained.
The checker verifies the literal sole-consumer row and uses this proved
identity as its only cut in the complete expression-DAG comparison.

This does not treat multiplication of a variable program input by Q1 as
free. The emitted API has parameters x,y,T and a **fixed** builder argument
`program_multiplier=C`. In the optional uniform source protocol C=3^e,
where e is the fixed program index. The valid coefficient recipe is48*3^e.
The arithmetic loader itself works for every fixed positive C; a different
C does not automatically carry that program interpretation. The C=1 and
C=3 examples do not instantiate a numerical universal source table.

## 3. Complete counts and degree bounds

Each form adds54=32M+22A and12 positive witnesses to the corresponding
single-layer bridge, hence108=64M+44A and24 witnesses to the factored raw
clock source. It retains22 conceptual comparisons. Every source gate and
every supplied coordinate is live, and every numeral multiplication is
charged. Both saved values of C have the same ledgers:

|Fixed source|Certificate M+A|Full M+A|Full total|Positive private witnesses|Degree upper bound|
|---|---:|---:|---:|---:|---:|
|INC2;DEC2|278+362=640|300+405|705|83|2344|
|Prime-three zero test|223+292=515|245+335|580|81|1192|
|No-op|221+292=513|243+335|578|81|1192|
|Prime-three positive test|228+288=516|250+331|581|81|1192|

The three supplied coordinates x,y,T are excluded from the witness column.
With y,T existential, the positive witness counts are85/83/83/83.

The first unit product has exact degree54. Substitution of the affine
expression C*(48x+delta1) for z cannot raise the parent's total degree,
since C is fixed. Therefore (1) has degree at most
`max(108,degree(F_single))`, giving the displayed inherited upper bounds.
Literal propagation agrees with those bounds. No exact degree claim for
these complete history polynomials is made.

## 4. Why both positive unit branches remain enforced

The safe conjunction in(1) excludes each exponent component's negative-unit
branch. Multiplying U1 and U2 together without another sign argument would
not do so. In fact the exponent theorem supplies positive witnesses with

    U1=U2=-1,
    Q1=2^(96x-4),       Q2=2^(96*C*Q1-4).

The no-op raw source still halts at that positive payload and has a positive
unbounded history extension. Thus `U1*U2*(1+S_history)-1` would accept such
an incorrectly loaded history. This is an existence counterexample using
the proved signed exponent extensions, not a materialized enormous tuple.

A separately compiled divide96 prefix would reject the second negative
branch because its initial first counter is congruent92 modulo96. That
observation cannot justify removing a sign constraint from any of the four
emitted circuits: none contains that prefix. A future compiler that uses
such a rejection argument must include and charge the actual source table.

## 5. Source universality and the measured examples

The source-input theorem explains the composition: divide the loaded first
counter by96 to obtain C*2^(96x), then use a reversible two-counter simulator
whose prime-power interface represents virtual counters initialized at
`(96x,e,0,...)` when C=3^e. A separate virtual divide96 preprocessor restores
the intended ordinary x while preserving e. That companion proof supplies
the source protocol; it does not make any of these four toy sources universal.

For these particular fixtures, put N=2^(96*C*2^(96x)). The inherited exact
relations are y=N,T=600N+16 for increment/decrement, y=N,T=192N+8 for the
prime-three zero test and no-op, and no acceptance for the prime-three
positive test. T counts physical evolution after initialization. The
ordinary-input conversion is an existential Diophantine constraint, and
does not add physical ticks to T. A newly inserted source preprocessor
would contribute its actual ticks and requires a new complete table.

## 6. Reproduction and evidence

The standalone standard-library tool authenticates six parent
source/receipt/note files before reading their two JSON descriptions. It
imports no parent Python module. The guarded API `build(variant,
program_multiplier=C,root=...)` accepts exactly the four variant strings
and any strict positive integer C. `checked` requires recursive exact-type
equality with a freshly rebuilt canonical packet; `evaluate` also checks
the exact parameter/witness keys and integer domains. Its `signed=True`
option is an algebraic evaluator, not a wider semantic theorem. Returned
data are fresh, and optimized `-O` execution is rejected.

    python three_mass_double_exponential_input.py \
      --root /path/to/native-stream-queue \
      --expect three_mass_double_exponential_input.json

The receipt records eight full structural polynomial identities and168
retained comparison identities;160 full-output evaluations,
including80 signed and16 rational cases;160 complete22-residual SOS
evaluations;16 public evaluations;116 rejected malformed callers; and
eight defensive-copy checks. Three additional fixed multipliers2,5,27
receive the structural check. Exact DAG identities and the inherited
positive extension theorems, rather than those finite samples, prove the
result. The huge correctly loaded payload and full Pell witnesses are not
materialized. `--output` writes a fresh receipt; `--expect` compares all
saved data with exact scalar types. Frozen parent bytes remain unchanged.
