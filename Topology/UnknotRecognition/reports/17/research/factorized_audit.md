# Audit of processed-component Potts factorization

Reviewed `work/fast/fastunknot/potts_factorized.py` and
`work/fast/tests/test_potts_factorized.py`, read-only, in the current session.
The high-level specialization is modular q=5, independently of the exact
quadratic q=6 backend. Its q=5 weaving blind family remains inconclusive.

## Invariant and correct merge coefficient

At a prefix, sum spins on forgotten vertices separately inside each connected
component of the processed Tait graph. The resulting boundary tensor factors
as a product over those components. Each component has its own simultaneous
permutation symmetry of the q spin names. Its table coefficient C(alpha)
aggregates all labelled boundary assignments with equality pattern alpha.
For a pattern with k classes, the orbit size is (q)_k and symmetry makes its
value per assignment C(alpha)/(q)_k.

When a new edge joins two processed components with k and ell active color
classes, a global equality pattern corresponds exactly to a partial bijection
between the two sets of classes. Classes within either component must remain
distinct. If a particular alignment produces K global classes, its aggregate
coefficient, before the edge factor, is

    C_left C_right (q)_K / ((q)_k (q)_ell).

This is precisely the implemented normalization and reaggregation. The
inequality 1<=q<PRIME makes every occurring falling factorial a unit modulo
PRIME. The code must not apply this division formula at characteristics where
one of these orbit sizes vanishes. The restriction is checked.

The recursive alignment enumeration is complete and duplicate-free: each
right class either matches one previously unused left class or becomes the
next canonical fresh class. The number of alignments is

    sum_(s=max(0,k+ell-q))^min(k,ell) binom(k,s) binom(ell,s) s!,

and is at most q!, since these orbits are the double-coset possibilities in
the finite group of q spin-name permutations. At q=5 and q=6 this gives the
claimed 120 and 720 bounds. The test suite checks all class-count pairs for
q<=6 against exact orbit cardinalities, not merely the final invariant.

After inserting the edge, forgetting vertices and canonicalizing the remaining
classes pushes forward the labelled-assignment sum. A component whose frontier
becomes empty contributes a scalar factor. Isolated graph vertices contribute
q each. An identically zero component table can remain active until later
edges; its empty table correctly makes all resulting contributions zero.

The union-find deliberately remembers connectivity through forgotten vertices.
Discarding such connections would be unsound: the boundary tensor may retain
correlations mediated by those summed-out vertices. The implementation retains
the correct processed-graph components.

## Complexity and resource scope

Fix q. Let g be the maximum number of active vertices in any one processed
component just after an edge step. A merge sees at most g+2 active vertices,
because only its two incident endpoints can be forgotten at that step.
There are at most q^(g+2) pairs of component equality patterns before merging,
and each pair produces at most q! relative alignments. Thus a conservative
bound is

    n * poly(g, log n) * q! * q^(g+2)

modular word operations, in addition to polynomial preprocessing and
bookkeeping. Logical stored table keys are at most O(n q^g); there may be
linearly many independent components. This is an execution-parameter bound,
not a universal bound on g for arbitrary knot diagrams or arbitrary orders.

The implementation's state budget bounds the sum of represented table keys,
including temporarily introduced singleton components. Old input tables remain
allocated while a replacement is constructed. Consequently the counter is not
a hard memory bound and is not directly comparable to a single-tensor peak
that counts only the replacement table. Transition counts include one update
per relative alignment, or one update per state for an internal edge, and are
checked before performing that update. Resource exhaustion raises FilterLimit
and cannot justify a knot verdict.

The finite q<=6 alignment cache is bounded by class-count triples and has
constant size for fixed q. For larger q the generator is lazy, but q! is not
polynomial in a variable q. Only fixed-q exponential-width claims are supported.

## Findings and validation

No mathematical defect was found in component factorization, partial-bijection
enumeration, aggregate merge coefficients, forgetting, isolated vertices, or
zero-component handling. The original generic graph API accepted noninteger
explicit equal-spin weights; this was reported promptly, and a subsequent
probe confirmed rejection after the implementation was updated. The high-level
default weights were integers throughout and were unaffected.

In addition to reviewing the supplied tests, 432 independent direct-labelled-
spin comparisons were executed for q=1,...,6 with loops, isolated vertices,
disconnected graphs, forward/reverse orders, zero and negative weights, and
weights chosen so that an active tensor becomes identically zero before a
later merge. Every partition function agreed. These checks supplement, rather
than replace, the author's tests and the independent whole-cube Jones oracle.

This is an exact modular filter optimization. It does not improve its chosen
specialization's ability to distinguish knots, and in particular does not fix
the q=5 odd-weaving collision. The exact q=6 backend and this modular q=5
factorization must remain clearly distinguished in the report and benchmarks.

## Subsequent audit: exact integer-pair component tensors

The later `potts_factorized_exact.py` implements the same factorization over
Z[x]/(x^2-(q-2)x+1), with q>=5 and default q=6. This is a genuinely exact
integer-pair backend; it has no finite-prime orbit-denominator restriction.

The integer normalization is valid coordinatewise. For a boundary equality
pattern with k classes, the S_q action is transitive on its (q)_k labelled
assignments. Every assignment has the same conditioned tensor value as an
element of the quadratic ring. Hence the aggregate is (q)_k times that value.
The ring is free as a Z-module on {1,x}; reduction to this basis is Z-linear,
so both integer coordinates are divisible by (q)_k. The code checks both
remainders before integer division. Negative coefficients cause no ambiguity:
when the remainder is zero, Python's integer quotient is the exact quotient.

The subsequent multiplication, relative-orbit factor (q)_K, edge factor, and
forgetting are the same proven pushforward as in the modular argument. Empty
tables and exact cancellation are retained correctly. Completed component
scalars multiply in the same quadratic ring. There is no additional floating
point or approximate step.

The g+2 combinatorial bound is unchanged. For a component with v_C introduced
vertices and e_C processed edges, each aggregate has coefficient norm at most
q^(v_C)(q-1)^(e_C). Completed scalar products satisfy the global bound
q^v(q-1)^n. All coordinate lengths are O((v+n)log q), or O(n log q) for a
connected nonempty Tait graph. Exact ring products therefore add a polynomial
bit-cost factor to the same q^(g+2) exponential parameter dependence. The
reported coefficient-length statistic concerns stored table/scalar values,
not every transient integer multiplication temporary.

Input checks reject noninteger q, graph sizes, endpoints, and signed edge
labels. State and transition limits retain the modular backend's logical-key
and orbit-update meaning. Deadline checks are cooperative at edge boundaries,
periodic updates, and selected preprocessing boundaries; postprocessing and
individual integer operations are not subject to a hard process deadline.
The shade heuristic minimizes the global active-face profile in the supplied
order, not the new component parameter g.

No defect was found in this exact extension. The independent full-smoothing
Laurent-Jones checker was extended to it and passed 4,464 color/shade/order
comparisons over 248 diagrams at q=5,6,7, plus 45 weaving trace comparisons up
to 98 crossings. It also checked the exact coefficient bound and that the
maximum component frontier does not exceed the total frontier. The raw record
is `potts_independent_checks.json` and the source is
`check_potts_independent.py`. These are in addition to the unchanged 4,464
single-tensor comparisons against the same independently built polynomials.

## Exact witness serialization and replay

The obstruction wrappers subsequently adopted canonical signed hexadecimal
strings for `partition_function_hex` and `unknot_partition_hex`. Raw
evaluators retain integer pairs. The common `witness_from_exact` helper tests
the actual pairs, not a supplied truthy `differs` flag, and formats both
coordinates with Python's hexadecimal conversion. This avoids the decimal
integer-conversion ceiling without changing a process-global setting.

The certificate replayer now supports both exact witness kinds and chooses
the corresponding raw evaluator. It decodes and validates canonical signed
hexadecimal strings, recomputes the diagram value, checks actual inequality,
and compares all fields of the newly serialized evidence. It rejects old
integer-pair evidence and alternate/noncanonical representations such as
`+0x1`, `0X1`, or `-0x0`. This is a replay of production computation, not a
separate independent algorithm.

Its final self-test verified both witness kinds, rejected 21 tamper cases,
and classified resource exhaustion as UNVERIFIED. It also round-tripped
synthetic coordinates exceeding 20,000 bits while rejecting their forged
mathematical claim. An additional real test constructed and replayed a
12,002-crossing weaving-knot certificate using exact component tensors; the
largest pair coordinate had 21,791 bits. The process-global decimal conversion
limit was checked unchanged. This establishes functioning large-integer
serialization/replay, not a new knot-family recognition algorithm or a
performance comparison. The record is `potts_certificate_selftest.json`.
