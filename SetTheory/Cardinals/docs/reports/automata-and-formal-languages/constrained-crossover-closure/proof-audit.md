# Proof and edge-case audit

This is an internal mathematical audit accompanying the draft, not an
independent referee report or a machine-checked proof.

## Definitions

- The two crossover constraints force equal complete parent lengths AND
  identical cut positions. Dropping either changes the operation.
- Every compatible fragment is aligned and extends to a complete seed of the
  target length. Ordinary factor occurrence is not enough.
- Empty slices remain empty; epsilon is present in the hull exactly when it
  is present in the seed. Epsilon has rank 1 rather than rank 0 when present.
- Parallel iteration uses two previous-generation parents. Frozen-source
  iteration uses one seed parent and allows both children. Its clock is
  linear in rank, not logarithmic.

## Exact rank

A fragment of a one-cut child splits into at most two nonempty seed fragments.
Conversely, pairing consecutive compatible fragments works because the two
full witnesses have equal length and can be crossed at their shared boundary.
Together these directions give exact contraction, not merely an upper bound.

The no-gap proof replaces a word's suffix by the kth seed witness. A cheaper
representation of the replacement would shorten the original representation
after restricting to the shared prefix. This is not an insertion-mask proof.

For the frozen clock, a rank-r word is obtained by crossing a rank-(at most
r-1) full word with the last seed. Endpoint and rank-one cases are covered.

## Undecidability reductions

Padding every omission by 00 avoids the unrepairable length-zero and
length-one cases. The two parents of an omitted word each contain @ but
inherit disjoint unguarded sides of the repair cut.

The one-step guard construction always stabilizes by generation 1, so it
cannot alone prove undecidability of eventual stabilization.

In block amplification, each forbidden block charges a distinct internal
partition cut in a closed integer interval [s_j,t_j]. Adjacent intervals are
disjoint because the intervening separator has length one. If no such cut
exists, a single fragment contains the whole forbidden block together with
its adjacent separators (or the actual full-word endpoints). This forces a
bad complete block in ANY matching seed; arbitrary separator placement
outside the fragment cannot evade the argument.

For the upper bound, cut strictly inside every bad block. Completing any
resulting fragment with guards outside it leaves at least one guard in every
block. The exact rank is r+1.

The eventual-stabilization index set is only stated to be Sigma^0_2 and
Pi^0_1-hard. Sigma^0_2-completeness is not proved or claimed.

## Automata

The DFA one-step graph tracks BOTH parents as well as the child. A single
parent-child graph would omit the equal-total-length extension requirement.
The bound 2s^3-1 is an existence bound from a simple graph path; the verifier
uses ordinary BFS, not an assertion that its witness minimizes word length.

In the distance automaton, the guessed V_i are uniquely forced on any
accepting path by V_n=F and V_i=Pre(V_{i+1}). U_i is fixed by forward reachability.
A reset checks that the prior fragment can be completed, and chooses a new
state reachable after a prefix of the exact boundary length. Resetting before
the first letter is redundant and cannot improve the minimum cost. Epsilon
acceptance has value zero exactly when epsilon belongs to the seed.

The EXPSPACE bound counts the exponential explicit automaton size followed
by a PSPACE limitedness algorithm. It is not a claimed lower bound or a
practical complexity estimate. The verifier tests accepted-word values, not
the imported universal limitedness algorithm.

## Rational counting

Marked occurrences and effective Parikh images make each two-coordinate
support E_a semilinear. Boolean combinations distinguish exact allowed-letter
sets at positions. Presburger counting is applied to these position TYPES,
not to whole output words.

Counts are O(n), so eventual quasipolynomials have degree at most one.
Their increments on a suitably refined arithmetic progression are integers
and cannot be negative forever. This yields nonnegative polynomial exponents
in the rational weighted formula. Empty lengths are separated explicitly by
the eventually periodic length set; otherwise the product over nonempty
coordinate types could incorrectly count one word on an empty slice.

The enumerator uses commuting weights. Rationality of this series does not
imply regularity or context-freeness of the language.

## Linear seed and recurrence

The position inequalities allow ones precisely in the first and last
floor(n/q) places. Intersecting with 1+0+1+ gives two inequalities, both tight
at 1^p 0^((q-2)p) 1^p. Pumping up AND down forces equal increments in the
outer blocks, while a pumping window cannot touch both. This contradiction
works for every q>=3.

For a finite generation, the binomial polynomial b_D(m) has leading
coefficient 2^D/D!, so its numerator at t=1 is 2^D. After t=z^q substitution,
this nonzero value rules out any further cancellation at every denominator
root. The recurrence order is therefore minimal, not just an annihilating
order guessed from a finite prefix.

## Executable and formal boundaries

All finite tests are exact, use no oracle for undecidable problems, and
raise exceptions explicitly rather than rely on optimization-sensitive
assert statements. Their receipts are included. No Lean or Rocq proof has
been run. The article supplies the universal proofs, and the code audits
finite specializations of the mechanisms.
