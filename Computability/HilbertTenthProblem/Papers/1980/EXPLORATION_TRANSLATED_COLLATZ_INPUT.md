# Translated one-number maps: the raw-input and stopping contracts

Status: bounded primary-source audit and an original obstruction lemma.
No new universal operation bound is claimed. Fixed numerals are free, but
the variable input loader and the finite-history verifier are counted.

## 1. The most concrete published candidate has a weaker input contract

Kaščák's [*Small universal one-state linear operator algorithm* (1992)](https://link.springer.com/chapter/10.1007/3-540-55808-X_31)
constructs a universal one-state linear operator algorithm of modulus 396.
A branch is chosen by `n mod m`; it either stops or updates the single
nonnegative integer by an affine expression followed by integer division.
Translations are explicitly allowed.

The publisher's [primary preview, printed pages 327--328](https://page-one.springer.com/pdf/preview/10.1007/3-540-55808-X_31)
contains the decisive definitions. Definition 2.1 allows an arbitrary
recursive binary code `c(program,input)` in the universality equation.
Definitions 2.2--2.3 make stopping depend on a selected residue's zero
denominator, not on reaching a separately specified numerical value. Thus
the source does not promise a raw input, or even a polynomial loader. The
full nine-page transition construction was not accessible in this audit;
the abstract and these two definition pages were inspected. The lemma
below shows why their weaker input convention is substantive.

Two other boundaries delimit the search:

* Kurtz and Simon's [2007 published theorem](https://doi.org/10.1007/978-3-540-72504-6_49)
  concerns whether **every** initial value eventually reaches 1. This global
  totality predicate is Pi-2 complete. It is not a fixed-map theorem saying
  that iteration from the raw query `x` recognizes every recursively
  enumerable set. The cached author PDF at
  `tmp/fractran_research/collatz.pdf` is a six-page December 2006 draft with
  unfinished sections and references; it must not be described as a full
  audit of the twelve-page published proof. Its introduction explicitly
  discusses the encoded initial values `2^k` in Conway's simulation.
* Ben-Amram's [*Mortality of Iterated Piecewise Affine Functions over the
  Integers* (STACS 2013)](https://drops.dagstuhl.de/opus/volltexte/2013/3961/pdf/49.pdf)
  makes the distinction between residue guards and ordinary interval guards
  precise. For finitely many interval pieces in one integer dimension,
  section 5 proves decidability; section 7 also states PSPACE-completeness
  for the specified-initial-point zero-reaching problem. The two-dimensional
  construction has undecidable reachability, but its Compass simulation
  encodes counters as `p*2^r1*3^r2+i` (Lemma 14). That is not a cheap raw
  one-number input convention either.

The bounded audit found no positive source result with all three properties:
one numerical state, a fixed polynomial connection to the original input,
and a complete universal finite-halting reduction. This is not a claim that
the larger architecture with a point-target test is impossible.

## 2. Translations do not repair residue-only stopping

The following is our deduction, not a theorem attributed to those papers.

Consider a fixed program on nonnegative integers. A residue modulo `m`
chooses either EXIT or one of finitely many rules

    n <- floor((a_i*n+b_i)/c_i),
    a_i >= 0, c_i > 0, b_i an integer.                 (1)

Assume the prescribed rules define valid nonnegative successors. Exact
affine divisions are a special case. No extra equality, inequality, or
invalid-state stopping test is included. These are precisely the features
needed in the following argument; it is not asserted for arbitrary guarded
maps.

**Finite-itinerary lemma.** If the program halts from `n0` after `t` updates,
then there is an effectively determined `M>0` such that it follows exactly
the same residue/EXIT itinerary from every `n0+M*z`, `z>=0`.

Choose an integer `D>=1` divisible by `m` and every positive denominator
`c_i`, and take `M=D^(t+1)`. Let `n_j` be the original run and `n'_j` the
shifted one. Inductively,

    n'_j-n_j >= 0,
    D^(t+1-j) divides n'_j-n_j,       0<=j<=t.          (2)

At `j=0` this is the chosen shift. For `j<t`, (2) implies equality of the
residues modulo `m`, so both runs select the same nonhalting branch. The
difference in their divided numerators is a multiple of `c_i`, hence the
floor operation gives the exact difference

    n'_(j+1)-n_(j+1) = a_i*(n'_j-n_j)/c_i.

It remains nonnegative and divisible by `D^(t-j)`. Both states therefore
remain valid, and induction continues. At `j=t`, the difference is still
divisible by `D`, so both states choose the same EXIT residue. No finite
cutoff is used to classify an infinite run.

**Polynomial-loader consequence.** Fix an integer polynomial `F(x)` and
initialize this program at `F(x)` when that number is positive. If its
accepted raw-input language is infinite, `F` must be eventually positive
(including the positive constant case). Fix an accepted `x0` and its
finite-itinerary modulus `M`. Polynomial congruence gives

    F(x0+M*z) = F(x0) modulo M.

For all sufficiently large `z`, this value is also at least `F(x0)`.
The finite-itinerary lemma therefore accepts every sufficiently large member
of the progression `x0+M*z`. In particular, no such architecture recognizes
exactly the powers of two. Every infinite arithmetic progression contains
numbers outside that set.

This extends the specific homogeneous FRACTRAN obstruction in
[the raw-input audit](EXPLORATION_RAW_INPUT_TRACKS.md). For FRACTRAN,
finite prime valuations preserve the *entire* instruction sequence.
For translated maps the argument only preserves one specified finite
halting itinerary; that already suffices for the conclusion. Each target
language may choose its own fixed program and polynomial loader: the
obstruction still applies separately to that choice.

The nonnegative-slope condition is natural for a branch which is defined on
an entire nonnegative residue class and always maps it into nonnegative
integers. A negative slope cannot have that global property. If a proposed
model has bounded interval exceptions, point guards, a rejection state, or
extra terminal arithmetic, those features require a separate analysis.

## 3. Why reaching a point is a real escape

Take the total residue-affine map

    g(n)=n/2 if n is even,
    g(n)=n   if n is odd,

and accept exactly when some iterate is the value 1. On positive inputs
this recognizes the powers of two. It has two homogeneous update branches;
the new resource is the **point-target test**, not translation. A shifted
finite itinerary need not reach the same point even when it follows the
same update branches.

Consequently the finite-itinerary lemma does not refute a generalized
Collatz construction with a fixed point target. Such a construction remains
a plausible direction only after its raw-input universality theorem is
proved or sourced. The target equality itself costs no arithmetic if its
two sides are already available, but enforcing a variable-length history,
the selected residue at every step, and its initial raw value remains the
substantial missing certificate.

This also explains why replacing residue EXIT by a point target cannot be
treated as a cosmetic alteration in either direction. The Kaščák definition
and the Kurtz--Simon target convention differ exactly where the obstruction
applies.

## 4. Focused verification

The companion [checker](../verification/explore_translated_collatz_input.py)
enumerates small translated residue maps, verifies preserved finite EXIT
itineraries on the stated arithmetic progressions, checks polynomial
loaders, and verifies the point-target example over a complete finite range.
Its [receipt](../verification/explore_translated_collatz_input.json) is
finite corroboration of the unbounded proof above, not a universality
receipt. Frozen universal and finite-history certificates are unchanged.
