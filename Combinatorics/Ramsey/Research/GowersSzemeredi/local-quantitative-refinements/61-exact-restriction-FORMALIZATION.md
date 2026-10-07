# Formalization plan — not a checked Lean implementation

No Lean compiler or proof-assistant verification was used for this delivery.
The identifiers below are proposed names, not declarations known to exist in
Mathlib or the repository. No `sorry`-bearing pseudo-proof is shipped.

## 1. Separate finite combinatorics from harmonic analysis

Prove a generic finite halving theorem first. Given a finite defect set D and a
finite test set T, assume each defect survives at most half the tests. Select a
test minimizing survivors and iterate. After `ceil(log_2(|D|+1))` steps no defect
survives. A version with an explicit integer `r` and `|D| < 2^r` avoids real logs
in the constructive statement.

Proposed interface: `exists_separating_tests_of_half_survival`.

The proof uses finite averaging only. There is no independence assumption on
different defects and no probabilistic limit.

## 2. Prove the finite-character input

For `h ≠ 0` of order q in a finite abelian group, character evaluation is uniform
on the q-th roots. Two possible routes:

- General finite abelian character duality and an evaluation-surjectivity lemma.
- Explicit products of cyclic groups, with integer character numerators,
  followed by transport across the finite-group classification isomorphism.

The root-grid count is `2 * ceil(q/5) - 1`, with a *strict* radius test.
Prove it for every integer q ≥ 2. Handle q = 2,...,9 explicitly and use the
linear inequality for q ≥ 10. In a product presentation with common denominator
Q, the exact test is `5 * min(v, Q-v) < Q`.

Proposed interface: `character_small_ball_card_le_half`.

## 3. Formalize the interval-cell implication

Represent circle values in `[0,1)`, partition into `5m` half-open intervals, and
show that a difference of two m-term sums from one cell has circle norm
strictly less than 1/5. The strictness is needed at fifth roots of unity.

Proposed interfaces: `same_arc_balanced_sum_small` and
`higher_order_avoidance_partition_exists`.

Retain a theorem in terms of the actual number of defects. The uniform power
of K should be a later corollary.

## 4. Graph packing and growth

Define the vertical-defect set as all h such that `(0,h) ∈ mΓ - mΓ`. It contains
zero for a nonempty graph. The map `(x,h) ↦ (x,phi(x)+h)` is injective and its
range lies in `(m+1)Γ - mΓ`.

Proposed interface: `vertical_defect_card_mul_graph_card_le`.

Apply a checked Plünnecke–Ruzsa theorem, or formalize the included minimal-growth
proof and triangle injection, to obtain `|D0| ≤ K^(2m+1)`. The graph property is
what removes the unwanted factor `|B|`.

## 5. Exact Freiman partitions

Pull the avoidance coloring back through phi. An equal-sum tuple in one cell
has vertical defect in D0. Avoidance excludes every nonzero defect, hence the
map respects the relation exactly.

Proposed interface: `graph_freiman_partition_exists`.

Prove the equivalence with the repository's Freiman relation interface rather
than assuming the tuple conventions agree. Repetitions are permitted. Padding
with one fixed point proves monotonicity in the order.

## 6. Retained energy

Identify ordered relation counts with squared convolution norms. For the
largest-cell argument only Cauchy–Schwarz and a sumset support bound are needed.
The stronger weighted-partition statement uses the Fourier L^(2s) triangle
inequality and Hölder. For a complex weight on an exact cell, the graph and
base energies agree by a direct bijection of weighted relation tuples.

Proposed interfaces: `energy_ge_card_pow_div_sumset_card`,
`energy_partition_lower_bound`, and `graph_energy_eq_of_freiman`.

Do not claim that the same cell is favorable for all weights and all moments.
The simultaneous size/energy theorem has a separate largest-cell proof.

## 7. Conservative BSG and modular substitution

The included finite proof uses ordered bad pairs and allows repeated vertices
in its four-edge walks. Preserve those conventions in the code. Formalize the
score with denominator `delta*n`, establish its positivity, and keep the
original graph size n distinct from the selected size M.

Result: `M ≥ alpha*n/8` and selected ratio `K ≤ 2^24*alpha^(-10)`.
Alternatively, invoke a stronger independently checked BSG theorem and use the
modular transfer statement in Section 7.1. Do not import an unrefereed numerical
claim as an axiom.

## 8. Cyclic specialization

Identify `E_8(B)` with `additiveTupleCount 8 B` and graph E_8 with
`phiAdditiveTupleCount 8 B phi`. Exactness gives equality of those counts and
implies the required `GammaHomOfOrder` inequality.

The two numerical checks can be separated from the analytic proof:

- `40^17 < 2^91` and the integer arithmetic yielding 2193, 911, 35277, 14655.
- For `0 < alpha, eta ≤ 1`,
  `(alpha*eta/4)^(2^19) ≤ 2^(-35277)*alpha^14655`.

Choose N0 = 1. Derive alpha ≤ 1 from the maximal relation count, rather than
adding it as a new hypothesis to the repository's Lemma 9.3 interface.

## 9. Independent obstruction formalization

For `(ZMod (2^e))^r`, prove that every nonzero difference can be multiplied by
some `q ≤ 2^(e-1)` to reach a nonzero element of the two-torsion subgroup. This
is the singleton-coloring obstruction. Formalize the finite parameterized
statement first; derive the universal exponent lower bound by letting r grow.

For the canonical section modulo L into modulo 2L, formalize the interval
difference count and additive energy polynomial `(2L^3+L)/3`. The unrespected
relation uses at most L copies and pads to m.

These finite algebraic statements do not depend on BSG or Fourier analysis.
