# Independent review of the exact observation extension

Review date: 2026-10-03. The earlier boundary packet was read but not modified.

## Verdict and scope

The arithmetic construction is correct on its stated valid-input domain. It
closes the previously unimplemented exact first-hit subroutine using only Python
standard-library integer arithmetic. No general Presburger engine is needed.
The review found no defect in the atom algebra, existential lane projection,
strict chronology, colour reconstruction, or first-hit minimum.

One API hazard was found in the initial reviewed revision: a one-shot iterator
supplied as a `Clause` field was consumed by validation, silently changing the
query. The author fixed it by eagerly normalizing all fields to immutable tuples.
Independent normal and optimized regression checks now pass. No unresolved
correctness finding remains on the stated valid-input domain.

The lower-level `first_hit` contract explicitly requires a certified `Result`
from the same rule, tile, defects, start, and heading. This is a real precondition,
not something the function independently verifies. The public `solve` wrapper
constructs the result and query from the same inputs, and is the appropriate
end-to-end interface. Manually changed, uncertified, or mismatched results remain
outside the claim.

## 1. Exact set algebra and minimum

An atom represents the nonnegative integers in one residue class between an
inclusive first point and an optional inclusive last point. The `atom` factory
clamps the lower limit at zero, advances to the first admissible residue, retreats
to the last admissible residue, removes empty sets, and canonicalizes a singleton
to step one. Canonicalization does not alter the represented set.

Two atoms intersect in one atom or the empty set. The implemented generalized
CRT first checks divisibility of the residue difference by the gcd, then solves
the reduced coprime congruence and intersects the bounds. Negative residues,
non-coprime moduli, modulus one, singleton intersections, and empty intervals
are handled correctly.

Each `IndexSet` represents an indicator as a finite integer-weighted sum of atom
indicators. Public construction starts from a single atom or the empty set.
Intersection uses multiplication, complement uses one minus the indicator,
and union uses `F + G - F*G`. These identities preserve pointwise values in
`{0,1}`. Combining identical atoms is a representation simplification, not an
additional mathematical assumption.

The Boolean-indicator invariant is indispensable. A zero signed sum over an
interval would not establish emptiness for an arbitrary integer-valued function.
The public constructors and Boolean operations preserve the necessary invariant;
manually injecting coefficients through private implementation details is outside
the supported interface.

Counting an atom on a finite interval requires only finding its first admissible
point and one integer division. Linearity therefore gives exact counts for any
constructed Boolean set, even though individual coefficients may be negative.
The final count is a nonnegative integer and prefix counts are monotone.

Let `B` be the maximum of zero, all unbounded-atom first points, and all
bounded-atom last points plus one. Let `Q` be the lcm of all unbounded-atom steps,
or one when there are none. At every index at least `B`, bounded terms vanish
and each unbounded term is an unrestricted congruence. The full indicator is
therefore `Q`-periodic from `B` onward. Consequently:

- `[0, B+Q-1]` contains every exceptional prefix point and one complete tail period
- Zero count on this interval is equivalent to global emptiness
- A positive count brackets the exact minimum, found by monotone prefix-count bisection

No residue period, huge endpoint, or time interval is enumerated. The code
enumerates finite expression terms and performs a logarithmic number of count
calls in the numerical bracket size. The number of signed terms can grow
exponentially; this review makes no polynomial complexity claim for observation
queries.

## 2. Existential projection of lane intersections

For a shifted head lane and an old lane, the two coordinate equations are linear
in the new index `n` and old index `k`. The implementation handles every rank:

- Rank two: Cramer's rule gives the sole rational candidate; divisibility,
  nonnegative indices, inclusive endpoints, and strict chronology are checked
- Rank one: extended gcd provides one solution and a one-parameter integer
  family; every bound becomes a lower or upper bound on that parameter
- Rank zero: equal stationary positions allow the earliest old index `k=0`,
  since old times increase strictly with their positive period; chronology is
  a contiguous threshold on `n`

The rank-one feasible parameter set is an integer interval. Its image under the
new-index affine map is an interval-congruence atom. Positive and negative new
index steps require opposite endpoint choices; the implementation makes those
choices correctly. A zero new-index step yields a singleton, never modulus zero.

The strict comparison is translated to an integer lower bound with the necessary
minus one. Equal-time spatial matches are excluded, including an index compared
with itself. At a first repeated arrival, the earlier departure is included.
Stationary old lanes, negative spatial drift, finite and infinite endpoints, and
negative auxiliary lane time bases are all handled consistently.

## 3. From observations to index sets

Shifting a head lane changes its spatial base and preserves its timestamps,
period, endpoint, and heading. This is exactly what a head-relative colour offset
requires.

The initial-colour compiler gives defects precedence over the periodic tile:
matching defects are included, while the background predicate is masked by the
complement of all defects. Redundant defects are valid. Linear coordinate
congruences reduce by a gcd and modular inverse; zero coefficients and modulus
one are covered.

Visited-before is the union of strict chronological lane relations. The returned
compressed path may contain future points, but these cannot satisfy that strict
comparison. On the certified domain, each cell has been departed from at most
once before the observation, so its colour is its initial colour plus this
Boolean visit indicator modulo the palette size. This remains correct for a
one-colour palette and at the first repeated arrival before its departure.

Heading tests are constant on each lane. Finite head sites are unions of point
relations. The final conjunction retains the head lane's endpoint restriction.
An empty stencil imposes no condition; an empty heading/site set is impossible;
an empty union of clauses has no hit. Duplicate and contradictory stencil
entries retain their normal logical meanings.

The first index on each lane is its first time because the lane period is
positive. Taking the minimum time across all lanes and clauses gives the first
global observation. The returned position, heading, lane witness, and clause
witness are consistent with that event. No claim is made after first revisit.

## 4. Independent executable checks

The independent checker is `independent_checks.py`. It does not use the release
`collision`, `colour_at`, `brute`, or `snapshot_head` functions as correctness
oracles. It instead uses direct congruence evaluation, independent Boolean truth
tables, direct per-index spatial geometry, and a separately written evolving-
board simulator.

Successful normal and optimized logs are `independent-normal.txt` and
`independent-optimized.txt`. Both completed the following seven groups against
the final reviewed implementation:

- 1,470 exhaustive small atom inputs and 8,000 independently checked CRT intersections
- 350 arbitrary Boolean truth tables of four predicates, independently compiled
  as disjunctive normal forms and compared pointwise, by counts, and by minimum
- 18,000 lane pairs, deliberately balanced at 6,000 each of ranks zero, one, and
  two, with 2,448,000 direct membership checks; each chronology mode is checked
- 356 separate evolving-board runs with multiple clauses per run, including
  exhaustive constant one-cell rules through palette size three, defects,
  current-site and offset stencils, heading/site restrictions, and clause unions
- Huge exact cases with 251-digit endpoints and a 501-digit CRT product,
  positive/negative drifts, equal-time exclusion, and a first-revisit colour hit
- 17 invalid-input checks using non-removable `unittest` assertions
- Iterator normalization for all four clause fields, nested iterators, repeated
  queries, immutable snapshots, and malformed iterable rejection

Finite-revisit simulator comparisons inspect the entire certified domain.
Infinite-run differential comparisons inspect a finite prefix and any manageable
returned first hit; they are not themselves proofs of nonoccurrence forever.
Global emptiness is separately covered by the exact Boolean-period oracle and
analytic impossible infinite examples. Tests supplement the proof rather than
replace it.

The release modules contain explicit runtime guards rather than removable
assertion statements. Normal and `python -O` outputs agree on all tested valid
inputs and guard cases. The checker itself uses `unittest` methods, so optimized
mode does not discard its checks.

## 5. API finding and resolution status

The initial revision accepted these constructions without rejection:

```
Clause(stencil=iter(((0, 0, 1),)))
Clause(congruences=iter(((1, 0, 1, 2),)))
Clause(headings=iter((1,)))
Clause(sites=iter(((1, 0),)))
```

On the `RL` checkerboard starting north at the origin, the corresponding tuple
forms all first match at time one. Validation exhausted the iterators: stencil
and congruence variants incorrectly matched at zero; heading and site variants
incorrectly returned no hit.

The fields are annotated as tuples, so this does not invalidate the mathematical
theorem on valid tuple inputs. Nevertheless, silent acceptance is a practical
hazard. Normalize fields once to immutable tuples, or reject unsupported
container types explicitly before consuming them. Nested coordinate entries
should also be normalized or validated consistently.

**Resolved.** `Clause.__post_init__` now materializes every field and its nested
entries exactly once as immutable tuples. Invalid non-iterable shapes raise an
explicit `ValueError`. The independent regression reproduces each original case
using outer and nested one-shot iterators, reuses each clause in repeated calls,
and confirms time one in every case. It also confirms that mutating the original
nested source list after construction cannot mutate the frozen clause.

The final normal suite ran seven groups in 6.080 seconds; the optimized suite ran
the same seven groups in 7.428 seconds. Both report `OK`. Execution times are
environment-specific and are not performance guarantees.

Reviewed and tested file fingerprints (SHA-256):

```
a9f951d4c12df99d0d78bf6eca3fdeee55539eb1bd3938e6e4fd71ae027b5210  observations.py
6b2bc54678a5a4c18db8eec23e37195a3c526d7f152863a1fb3a1f8d682429f7  one_visit.py
315c792208e0fa64ba5223f6950792c9a94484602451f2f653079d1b4e1aa981  independent_checks.py
```

The companion `PROOF.md` was also reviewed against these implementations. Its
mathematical claims and stated API precondition match the checked construction.
The separate optional first-revisit bit-complexity note was outside this review's
assignment and is not certified by this report.
