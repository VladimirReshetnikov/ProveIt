# Review of the dimension-independent four-mass decision theorem

The placed Report29 [proof](../../../../../SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/signal-machine-collision-certificates/19-mass-four-zd-PROOF.md)
passes this mathematical review. Its scope is a deterministic, finite-range,
translation-equivariant cellular automaton on finite-dimensional integer
space, with quiescent vacuum, strictly positive integer weights on every
nonvacuum symbol, conserved finite mass, and **at most one weight-one symbol**.
For finite inputs of mass at most four, exact configuration reachability and
finite-pattern occurrence are decidable, with or without translation. Zeros
prescribed by a pattern are included in the decision problem.

Thus this class cannot supply a universal halting encoding through an
effective finite-input/finite-observation loader at mass four, even in a
plane or higher dimension. This is a restriction on a particular substrate,
not an arithmetic-circuit lower bound or a claim about every particle model.
The [planar shuttle](review_binary_planar_four_particle31.md) fits this class;
its quadratic section times and nonperiodic geometry are consistent with
decidable reachability.

The [helper](review_dimension_independent_four_mass.py) and its
[receipt](review_dimension_independent_four_mass.json) pin the placed proof
and its source-lineage record. They supply new exact arithmetic checks,
not a general CA analyzer. No archived Python, original exhaustive suite,
or historical builder executes. The full proof, including its no-unit-symbol
case and absolute-frame observation argument, was read directly.

## Why higher dimension does not supply a second usable counter

With a unique unit symbol, an isolated unit moves by one fixed vector each
step. Removing that common drift makes every separated unit stationary.
Components separated by more than twice the new radius evolve independently
until their first contact, including the first-contact configuration itself.
Positivity and conservation then keep every mass-two packet within bounded
diameter. It has a finite transient followed by a finite set of shapes
translated by integer multiples of one vector.

The mass-three analysis uses a finite core and exact first-return calculations
for a dimer and one stationary unit. Every normalized core return either
repeats a complete configuration up to translation or eventually enters an
independent tail. This gives a finite encounter library built from the
original bounded mass-three seeds. Its prefix/phase bound B is computed
before the mass-four core; the threshold construction is not circular.
A compact translating triple either misses the fourth unit or meets it in
a bounded full configuration. All intermediate phases are included.

For a moving dimer with phase shapes Q_r, period p and nonzero displacement D,
first contact with a target at v is determined by finitely many exact tests

    v=a+kD, k≥0, a in Q_r+[-2S,2S]^d,
    contact time=r+pk.

Testing actual occupied support, rather than its convex hull or motion in one
coordinate, is essential. An unsuccessful flight is an independent terminal
tail. Multiple candidates are resolved by the least actual integer time.
A zero-drift periodic dimer is handled directly over its finite phase list;
no division by a zero drift is required.

After a successful crossing the contacted marker changes by a bounded library
vector c. If the following flight also succeeds, its target vector is
v'=−v−c, so two successive drift vectors satisfy

    kD+k'D'=−(a+a'+c).

For nonparallel D,D', choose two coordinates with nonzero determinant.
Cramer's rule gives at most one rational pair k,k' for each finite right side.
Nonnegative integrality and every remaining coordinate equation are checked.
All such switches therefore occur in a computably bounded region. In
particular, an extra spatial coordinate cannot be queried as an independent
unbounded register by repeatedly turning toward another marker.

Outside that region, continuing flights use one fixed rational line. A
primitive direction nu and a Bezout functional lambda(nu)=1 split the marker
vector as x*nu+z, with z in a finite set. The finite mode records the line,
source side, phase/seed data and z. Adding x modulo a common drift modulus
makes each continuation a fixed counter increment, a fixed anchor translation
and an affine positive flight time. The anchor vector is output data; it
does not influence the next transition.

## Termination, timing and observations

The large-gap threshold first bounds finite offsets, marker updates and
exceptional switches. Only then is the ordinary mass-four core chosen to
contain all remaining small successful launches. Arbitrary component
partitions of total mass four are dispatched: connected states, a triple
and unit, two dimers, a dimer and two units, or four separated units.
Transient phases, simultaneous contacts and failed encounters are covered.
Each core step and each distant live flight consumes positive time.

At repetition of an enlarged live mode, a zero total counter increment gives
translation-periodic dynamics; a positive increment repeats an expanding
shuttle forever; a negative increment permits only a computable number of
cycles before a lower-bound guard fails. Repeated ordinary normalized states
also imply translation-periodicity of the entire future, including excursions.
This proves termination of the analysis without mistaking a bounded search
for an unbounded decider.

For an expanding shuttle, section gaps and anchors are affine in the cycle
number. Free-flight positions are affine in that number and an additional
bounded flight-period variable. This yields the stated fixed-input untimed
Presburger description in the stationary-unit frame. Section times are
quadratic with positive leading coefficient; a timed Presburger description
of every mass-four orbit is not asserted.

Translation-invariant observations transfer between frames immediately.
For an absolute finite window with nonzero original singleton drift, its
quadratic accumulated translation eventually dominates the linear spatial
extent of every phase in a shuttle cycle. A computable cutoff excludes all
later nonzero hits; an all-zero window is eventually satisfied. Earlier times
form a finite effective search. This avoids an unrestricted quadratic
Diophantine decision step. In periodic/independent alternatives, common
phases already describe time and position affinely.

If no weight-one symbol exists, mass at most four occupies at most two sites.
Weights two and three cannot split. A weight-four site may split into two
finite-state weight-two walkers. Their finite-core return analysis gives a
periodic or independent eventual profile and closes this separate case.

## Independent bounded evidence and the computational boundary

The new helper checks an explicitly specified three-dimensional arithmetic
packet profile against direct support contact for 216 targets. It verifies
125 exact ray translations by one million periods, the primitive-direction
residue/transverse decomposition, and a marker missed despite movement toward
one of its coordinates. The profile is an arithmetic fixture; no particular
CA realizing it is claimed.

Six pairs of nonparallel vectors are checked on 1,470 integer right sides
against an independent complete bounded search. They include a pair whose
first two coordinate determinant vanishes, forcing use of a later coordinate,
and overdetermined three-dimensional systems. A parallel opposing pair is
explicitly rejected by the finite-switch solver and has arbitrarily large
solutions, illustrating why the nonparallel premise matters. Three guarded
counter cycles exercise expanding, zero-change and descending alternatives.
None of these finite cases substitutes for the proof over all admissible CAs.

The theorem's hypotheses are necessary to the argument. Multiple unit labels
can have different isolated drifts; zero-cost nonvacuum symbols, active vacuum,
infinite alphabets, infinite inputs, spatially varying rules and time-dependent
rules are outside its scope. The five-particle upper bound in the report is
inherited from separate universal-source and CA compilation proofs, then
embedded linewise into higher dimensions. This review does not reprove that
upper bound or assign an arithmetic cost to the effective decision argument.
No complete universal polynomial or smaller witness bound follows here.

Replay from any directory:

    python3 /absolute/path/review_dimension_independent_four_mass.py \
      --repo-root /absolute/path/Proofs \
      --expect /absolute/path/review_dimension_independent_four_mass.json

All checks use explicit exceptions and remain active under optimized Python.
