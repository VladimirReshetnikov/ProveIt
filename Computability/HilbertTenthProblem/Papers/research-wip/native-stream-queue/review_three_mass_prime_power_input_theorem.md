# Independent review of the prime-power input theorem

PASS on the frozen [source evidence](three_mass_prime_power_input_theorem.py),
[receipt](three_mass_prime_power_input_theorem.json), and
[theorem note](three_mass_prime_power_input_theorem.md). Source SHA256:
`836c86ce4aff428750aab5af9372f1ba9c85e0c10618293ddb74394f0b348170`.
No correction is requested. The theorem closes the input convention at the
level of an effective source construction; it does not supply a numerical
universal table or its arithmetic operation count.

## Primary theorem and input preservation

I read the relevant definitions, both theorem statements and their actual
constructions in Kenichi Morita, *Universality of a reversible two-counter
machine*, Theoretical Computer Science168(1996),303–320,
[DOI](https://doi.org/10.1016/S0304-3975(96)00081-3), using the pinned
[primary paper copy](https://www.mobt3ath.com/uplode/book/book-94727.pdf?download=1).
The PDF hash is
`81677dd609d5b2c111c83fc5768382dbc14b54b1bf212a0b3fe828aca1b6c999`.
The displayed formulas on printed pages308 and313 were also inspected visually.

Theorem3.1 preserves the initial k-counter tuple and adds two zero counters;
it permits a final natural history counter and returns its work counter to
zero. The proof's no-incoming initial-state assumption is satisfied by adding
a fresh initial no-op before the deterministic recognizer. This is an actual
source modification preserving its input tuple, rather than an unspecified
input recoding. Lemma3.1's preliminary reduction of incoming-state degree also
preserves the tuple.

Theorem4.1 uses the exact initial two-counter tuple
`(product_i p_i^m_i,0)` for the original tuple `(m1,...,mk)`. Its multiplication,
exact division, and restored divisibility-test constructions on pp314–316
establish more than an unqualified assertion of Turing completeness. They
supply the precise exponential input convention required here.

## Independent general proof check

For each recursively enumerable set S, choose a deterministic unary Turing
recognizer. A deterministic three-counter implementation is sufficient before
reversible compression: two base-b stacks and a work counter simulate the tape,
with the current symbol in finite control. Push maps A to bA+d and clears
scratch; pop returns A mod b in finite control and replaces A by floor(A/b),
again clearing scratch. Blank-zero ambiguity represents the same infinite
blank tail. Starting at `(x,0,0)`, consumption of the first counter while
pushing ones onto the second constructs the unary input and releases the
first register for the left stack. This proves an ordinary input interface
for the multicounter machine without assuming a unary two-counter theorem.

Prepending the literal divide96 on the first and a zero scratch counter
converts `(96x,0,0)` to `(x,0,0)`. In division state Li the invariant is
`C0+96*Cscratch+i=96x`; completed blocks increase scratch by one, and the
transfer loop preserves `C0+Cscratch=x`. Nonmultiples get stuck away from the
exit. Morita's two constructions therefore produce a separated reversible
two-counter source accepting `(2^(96x),0)` exactly when x belongs to S.

The argument correctly addresses arbitrary final outputs. At every original
label of the prime simulator, its first counter is a positive product of the
designated primes and its second is zero. A valid simulated increment,
decrement, or test terminates its private macro at the corresponding original
label with the represented tuple. A failed decrement/test cannot reach that
label. Fresh internal labels are not accepting states. Similarly, the history
simulation reaches old labels with a natural history and zero work. Induction
therefore rules out a spurious visit to the accepting label with an unencoded
output. The exact primary configuration relations apply to every such visit.

Fresh no-incoming initial labels and terminal accepting labels can be retained
through both constructions. The primitive source syntax has disjoint forward
and reverse guards, as required by the three-mass compiler. Attaching the
physical divide96 prefix to a source with no incoming entry preserves those
conditions: its exit is identified with that entry, introducing no competing
incoming source instruction.

The optional fixed interpreter also has a valid exact recipe. A fixed
five-counter initialization starting at `(x,e,0,0,0)` pushes e ones, then a
separator2, then x ones. Its least-significant-first tape word is
`1^x 2 1^e`, and the two input counters and scratch are cleared. An initial
divide96 on counters0 and2 preserves e. The two Morita transformations now
start the physical two-counter interpreter at `(2^(96x)*3^e,0)`. No numerical
expansion of that interpreter is present, and none is needed for this existence
and effective-construction theorem.

## Composition with the paid arithmetic loader

The separately reviewed double loader supplies three-mass payload
`N0=2^(96*C*2^(96x))`, whose counter valuations are
`(96*C*2^(96x),0)`. An actual physical divide96 prefix leaves
`(C*2^(96x),0)`. For the fixed interpreter, the coefficient recipe C=3^e
is exactly the prime encoding of its virtual tuple `(96x,e,0,...)`.
The second divide96 is virtual and lies inside the program before reversible
compression. Both occurrences are finite source programs. Their actual
executions, including simulation overhead, belong in any compiled physical
clock; they are not free arithmetic decoding operations.

C is fixed for each language slice. Folding the exponent coefficient to48C
is legitimate for that fixed numeral and does not make a variable product
free. The four paid toy-source counts in the double-loader packet exclude
these unexpanded universal programs and prefixes. Consequently the theorem
supports ordinary-input universality of an effectively compiled family and
an optional fixed source construction, but it supplies no new numerical
universal Diophantine complexity bound.

## Bounded independent evidence

The [review checker](review_three_mass_prime_power_input_theorem.py) authenticates
all three author artifacts and the primary PDF before loading the source via
`compile` on those bytes. It uses the actual author macro emitters to obtain
finite instruction tables, but its interpreter, syntax checks, inverse,
prime encodings, and expected input words are independent. It never calls the
author's `verify` or `run` functions.

The [review receipt](review_three_mass_prime_power_input_theorem.json) records:

- 30 separated reversible primitive tables, 270 forward cases, and191 successful inverse runs, including cases outside the author's 1..64 range;
- Four complete runs of the independently transcribed seven-instruction primary example, with42 exact original-state boundaries in its93-instruction compilation;
- Eleven divide96 boundary cases and four inverse runs, preserving a nonzero program register;
- Eight unary loads,32 composed divide96/paired-loader cases,40 push cases, and14 pop cases;
- Nine exact nested-input recipe calculations, without constructing the doubly exponential physical mass.

These finite checks support the inspected implementation and interface; the
general theorem follows from the preceding construction and primary results.
This is not an independent exhaustive rerun of the author's larger suite or a
complete implementation of a universal machine. The helper's macro interface
is research evidence, not a hardened arbitrary-machine compiler API. No giant
native Pell zero or complete universal physical trajectory is materialized.

Run with explicit portable paths and Python's standard library:

```sh
python review_three_mass_prime_power_input_theorem.py \
  --source three_mass_prime_power_input_theorem.py \
  --receipt three_mass_prime_power_input_theorem.json \
  --note three_mass_prime_power_input_theorem.md \
  --paper /path/to/morita_1996_primary.pdf \
  --expect review_three_mass_prime_power_input_theorem.json
```

The primary PDF must already be available; this review replay does not fetch
it. Exact type-sensitive receipt comparison and optimized-mode rejection are
retained. All original source and repository files remain untouched.
