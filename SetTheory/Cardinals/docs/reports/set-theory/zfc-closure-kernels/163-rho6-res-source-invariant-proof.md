# A source invariant for the exact K217 program

This is an ordinary mathematical argument for a finite invariant certificate,
not a Lean/Rocq proof. Its source is the accepted `sites217.json`, SHA-256
`9eac900e83742470893ea433cb0868e9ff6296f905cd6f3359b7a2c0e3114655`.
The exact finite certificate is `source-invariant.json` and is checked again
as a postfixed point by `specialized_runtime.py`.

## Abstract values and their meaning

There are nine buckets, numbered 0 through 8. Bucket k<8 denotes the singleton
{k}; bucket 8 denotes every natural number at least 8. A nonempty bit mask
denotes the union of its buckets. A nine-tuple of masks denotes the Cartesian
product of the nine represented sets. A missing tuple denotes the empty set.
Thus the calculation is not a simulation truncated at register value 8.

Let S_i denote the Cartesian set stored at source ordinal i. The root seed is
the tuple (3,0,0,0,3,0,0,0,0), which belongs to S_0. This is the logical register
tuple in the accepted complete blank initialization frame.

## Sound primitive transfers

For an increment, bucket k<8 moves to bucket min(k+1,8), and bucket 8 remains 8.
The implemented mask operation is the union of these images. It therefore
contains the exact image under natural addition by one.

A decrement has two guards. Its zero guard is allowed exactly when bucket 0
is present and leaves that register zero. On its positive guard, each singleton
bucket k in 1..7 moves to k-1. Bucket 8 moves to the union of bucket 7 and bucket
8: subtracting one from an arbitrary n>=8 yields either 7 or a number >=8.
The other eight registers are unchanged. Break and continue leave registers
unchanged and use the exact literal source successor. Halt has no successor.

The checker computes successors independently by the full-tree interval
resolver and the binary-address arithmetic resolver, and requires equality.
For each allowed source guard, every resulting abstract register mask is a
subset of the stored mask at its target. This is a finite postfixed-point
check; it is checked after the work-list calculation rather than inferred
merely from termination of that calculation.

## Unbounded conclusion

Induction on the number of source steps proves that every source execution
from the accepted root seed remains in S_i at its current ordinal i. The base
case is the explicit seed membership. The inductive step follows from the
sound transfer just proved and the checked containment at the successor.
There is no bound on the number of steps or on any represented register.

The checked closure has 6,170 guarded successor edges. Ordinals 4614, 4726 and
4727 denote the empty set and are therefore unreachable. At ordinals 4613
and 4725 the tested decrement register is exactly zero, so its positive guard
is unreachable. No other positive/zero guard is excluded by this Cartesian
certificate. These claims concern this exact source and seed, and do not
assert unreachability from arbitrary initial registers.

## Specializing the binary primitive contracts

At any ordinal with a singleton mask below bucket 8, the corresponding register
has that exact natural value. In the specialized symbolic checker it is a
constant. Every other register is widened to an independent arbitrary natural;
the decrement register is additionally split into zero or 1+n as appropriate.
This widening contains every actual source configuration admitted by the
invariant. The tape gap remains an arbitrary natural. The spare file remains
an arbitrary nonempty finite list of natural values; its stronger actual
startup form is not needed for this specialization.

For each admitted source guard, a successful symbolic proof establishes the
complete binary tape endpoint and the exact source successor. The proof rules
are literal table transitions, unary-length induction, and finite-list
induction through a separately checked one-block traversal. For a one-block
traversal the exact signed displacement is its width v+2. Its computed affine
duration must dominate v+2 coefficientwise. List traversal may consequently
use total width as a valid duration lower bound even if a candidate inserts
additional local steps. Every returned primitive duration lower bound has a
positive constant term, which excludes an infinite source execution collapsing
to finitely many binary steps.

If a candidate passes these specialized contracts and has a separately proved
blank initialization into this seed, induction gives forward binary simulation
of every reachable source step. Determinism, the complete endpoints, and finite
positive matching blocks give the converse halting implication. Composing with
the inherited source/calculus calibration then preserves the desired blank
halting equivalence. This paragraph states a conditional method: the baseline
control run and each candidate run must be reported separately, and a sampled
window search is not such a certificate.

## Exact-value interface

`known_values.json` contains `known[i][r]`, an integer for an exact singleton
and null for a widened arbitrary natural. `guards[i]` lists the admissible
Boolean decrement guards (or the singleton false for a non-decrement); the
empty list denotes an unreachable ordinal. There are 4,311 exact register
constants across all reachable ordinal tuples. Bucket 8 is never misidentified
as the exact value 8.

## Joint zero/nonzero information

The relational extension stores a set P_i of nine-bit patterns at each ordinal.
Bit r is one exactly when register r is positive. Each retained pattern is
intersected with the independently proved Cartesian set S_i. The initial
pattern is 17, since precisely registers 0 and 4 are positive in the seed.
Increment sets its bit. A zero decrement keeps its bit zero. A positive
decrement can clear its bit only if the tested bucket mask admits the exact
value 1, and can leave its bit set only if that mask admits a value at least 2.
Other bits are preserved. Identity control transfers keep the pattern.

The finite certificate checks closure under these transfers whenever the
target pattern is compatible with the target Cartesian mask. Discarding an
incompatible target is sound: the independent Cartesian invariant already
proves that no actual execution reaches such a target. Simultaneous induction
therefore establishes membership in S_i and P_i along the unbounded run.

The current relational certificate contains 341,024 ordinal/pattern pairs and
405,264 checked edges. It rules out 170,592 Cartesian patterns at 2,582 source
ordinals. In particular, at ordinal 4579 it proves that registers 5 and 6
cannot both be positive. This is a finite abstract interpretation result; it
does not assume nonhalting or the consistency of any object theory.

## The actual spare file and gap

The accepted complete root frame has gap 80 and exactly 130 spare registers,
each of value 1. Inspecting every primitive's complete-tape contract gives:

* Increment preserves the old spare list and appends one spare of value 1.
* Positive decrement, zero decrement, break and continue preserve the old
  spare list exactly. A halt needs no subsequent frame.
* The gap changes by the sum of two nonnegative quantities: 1 for a positive
  decrement (otherwise 0), and the address-increment overflow flag.

Consequently, every later source boundary has an all-ones spare list of length
at least 130 and gap at least 80. This is induction on source primitives using
the already stated endpoint equations, not extrapolation from a tape sample.

`specialized_runtime_ones.py` uses these facts. Its finite-list induction is
proved for the fixed block value 1, so an opaque spare tail denotes repetitions
of B(1)=011 (or its transformed family C(1)=101). The tape endpoint identities
used by the symbolic normalizer remain valid for this subclass of lists.
Its `--spare-minimum` parameter writes that many fixed B(1) blocks before the
opaque tail, whose length is any natural including zero. With minimum 1 this
proves a stronger contract than is needed for the actual minimum 130; a larger
minimum can be selected if a physical optimization depends on the spare file
not ending nearby. The head displacement of a one-block traversal is exactly
3, and finite-list induction therefore gives its exact total-width displacement.
The gap is represented as `gap_minimum+n` for arbitrary natural n, defaulting
to the proved lower bound 80.

All strengthened binary contracts still need their own literal table check.
In particular, replacing the old arbitrary-value list lemma by a value-one
lemma requires re-proving its block trace on the candidate's actual rows.
