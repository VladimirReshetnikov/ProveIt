# Caching and sparse balancing audit

## Exact weight caching

The incoming joint-Cauchy report Section 8 supplies an explicit exponential-
space summation method, not a polynomial-space oracle. Its global budget
accounting is sound. Fix a bounded grouping alphabet r. For each directed
group pair e, let b_e be the exact total mode weight on that pair. Enumerating
arrays b with ∑_e b_e<p partitions all feasible mode tuples, with no overlap
and no missed global constraint. There are at most (p+1)^(r(r−1)) arrays,
which is polynomial because r is fixed and p is polynomial in global size.
The same statement applies to schedules drawing r from a fixed finite set;
it must not silently be used for r growing with input size.

For each pair and each exact weight, the ordinary unbounded-knapsack count
table indexed by (mode prefix, exact weight) has polynomially many entries
of polynomial bit length. It provides emptiness checks, rank/unrank, and
polynomial-delay enumeration even at small or zero budgets. This avoids
mistakenly applying a large-budget partition asymptotic separately to every
pair. Pair lists of weight zero contain their unique all-zero mode tuple;
empty lists for positive impossible weights make that whole array zero.

For a fixed array, a group g depends only on the directed pair indices
incident with g: incoming indices specify target coefficient extraction,
outgoing indices specify source-form powers. The original packet-group
definition contains no other indices. Hence all entries of that group's
function can be cached using actual recursive child contractions. The cost
must include the number of incident assignments times the child cost. No
cheap oracle for the high-degree abstract group tensor is presumed.

Partition the groups into three blocks. Each block table sums the product
of its cached group functions over its internal pair indices, retaining
the boundary pair indices. Contracting the three tables on a triangle is
an exact finite sum over the fixed pair-weight array. Summing all arrays
therefore recovers the original strict-budget sum. Nilpotents, negative
entries, and working modulo a power of two do not affect these identities.

Strassen's seven-product identity uses only ring additions, subtractions,
and multiplications, so it is legitimate here. If triangle dimensions are
d₁,d₂,d₃, square blocking with side min(d₁,d₂,d₃), padding each dimension
by a factor below two, gives cost

    O(d₁d₂d₃ min(d₁,d₂,d₃)^(ω−3) polylog(max d_j)), ω=log₂7.

Input, output, and temporary blocks fit within the claimed boundary-table
space. Exact-index integer arithmetic and ring-entry bit costs are polynomial
factors. The report's sequential record enumeration argument accounts for
rewinds by charging them to full suffix traversals; sorting/reblocking costs
also add only polynomial factors. This is not an assumption of unit-cost
random access to an exponential table.

## Reusable coefficient formulas

With near-unit equal padding, a directed pair has at most
(2+o(1))M/(r²D) modes per q. Precision P≤(6+o(1))MD/u and slope four
give the common scale

    K₀(M,u) = (π/ln 2)√2 M/√u.

For any fixed nonnegative pair weights α_e, the weighted entropy bound is

    ∑_e α_e log₂ |pair list e|
        ≤ [√(∑_e α_e²/r²)+o(1)] K₀(M,u).

This follows directly from the single global budget by setting the pair
generating-function parameter to θ/α_e. It holds uniformly when some
b_e are small, unlike an unjustified pairwise large-budget asymptotic.

For block sizes k₁+k₂+k₃=r, define

    a(r) = √[2(r−1)]/r,
    t(k) = max_j √[2rk_j−k_j²−k_j]/r,
    m(k) = max_j √[2k_j(r−k_j)]/r,
    b(k) = √[2∑_{j<l} k_jk_l
               −(1−(ω−2)²)·2 min_{j<l}k_jk_l]/r.

The group-cache recurrence is

    T_d ≤ poly · (2^[(a(r_d)+o(1))K₀,d] r_d T_(d+1)
                  +2^[(max(t(k),b(k))+o(1))K₀,d]).

The memory exponent at that call is at most (m(k)+o(1))K₀,d.
Ancestor storage must also be included; summing polynomially many tables
does not sum their exponents. These formulas allow the incoming optional
tradeoff to be combined with newer packing without copying its obsolete
6M/(r²D) envelope. No new smaller-order theorem is obtained, and no new
numerical optimum is certified in this audit.

## Independent review of the root authored incremental balancer

Files reviewed: `research_balancing/incremental.py`, `proof.md`,
`verify_incremental.py`, and the incoming packet's `code/packet_packing.py`
as source text only. The incoming packet already caches row power sums;
calling that caching itself new would be wrong. The root's comparator
appropriately implements this stronger baseline, sharing the power table
and even giving it streaming future products rather than the original
suffix-product table.

For fixed row labels and the same rational z, let U_a be the future
product, S_a=∑_b z^(X_ab), and f_aj=(Q−1+z^(w_aj))/Q. The new sparse
formula

    B = E + ∑_{a active}(U_a/f_aj−U_a)S_a,
    δ_b = ∑_{a active}(U_a/f_aj)z^(X_ab)(z^(w_aj)−1)

is exactly the candidate conditional expectation B+δ_b. Subtracting B
preserves all minimizers and the least-label tie break. Averaging all
candidates returns E, so the chosen expectation cannot increase. Updating
U, S, and the chosen cell load restores the invariant. Empty columns
choose zero and do not change the potential. Parallel edges are bundled
before labels are assigned; no false independence is introduced.

The post-weight score step uses exactly QD candidate terms, D=∑_j|A_j|,
instead of nQ² for the cached dense comparator. Including scans and updates
gives O(QD+nQ) arithmetic operations. Since D≤min(M,nQ), this improves
sparse-support operation counts but not dense-support asymptotic order.
Exact Fraction arithmetic preserves the identities, and the explicit
product expressions bound numerator/denominator bit lengths polynomially.
This is an arithmetic-count result; it does not prove the same ratio in
bit time or a SAT runtime speedup.

Two audit clarifications were sent to the root:

1. The delivered matrix prototype also scans Q current row-bin totals for
   every input row. Thus preprocessing includes O(n_rows·Q+n_rows·n), not
   just the adjacency-matrix scan O(n_rows·n). The claimed score-step bound
   is unaffected; initialization after the weights are constructed is also
   unaffected. A heap-based row-label phase is possible but was not assumed.
2. Upstream `packet_packing.py` chooses z using the two-sided maximum degree
   Δ; the asymmetric prototype uses the column maximum C. Exact equality
   of decisions holds with matched z, row labels, and vertex order, not
   necessarily against an upstream run with a different z. The benchmark's
   three fresh engines correctly share the same z and preprocessing.

`audit_incremental_independent.py` independently enumerates completions for
all 2×2 matrices over {0,1,2}, Q=1,2,3,4, h=2,5, plus six additional
empty/parallel/nontrivial fixtures. All 696 fixture configurations passed
across 2,088 engine runs. It checks 3,480 exact candidate means against
7,600 literal completions and checks QD versus nQ² candidate-term counts.
Normal and optimized Python results are identical. It imports only the
root-authored component, not any incoming executable program.

The benchmark fairly compares matched component implementations, includes
setup and invariant checking in both, and alternates execution order.
Its measured speedups remain selected-fixture, component-only observations.
They are not timing results for the upstream program or the full SAT solver.
No denied, pending, or uncertain tool operation occurred in this audit.
