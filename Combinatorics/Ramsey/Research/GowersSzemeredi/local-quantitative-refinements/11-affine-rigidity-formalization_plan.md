# Formalization plan: affine rigidity at the Section 6 graph-energy interface

This is a proof-engineering plan, **not compiled Lean code**. No new theorem in
this package has been checked by Lean, and no existing repository file was edited.
Suggested names below are proposals, not claims about current Mathlib APIs.

## Inspected source interface

Repository: VladimirReshetnikov/ProveIt  
Commit: `40f885098a74607b423909dbcb8f070993b7c2a8`  
Directory: `Combinatorics/Ramsey/Lean/GowersSzemeredi`

`Sections06_07.lean` explicitly records numbered paper statements as `Prop`-valued
definitions, rather than asserting them. It defines `functionGraph`,
`proposition_6_1`, and `lemma_6_2`. Its graph-energy statement uses
`Finset.addEnergy`, and partial maps are represented by a total map and a finite
set on which the map is considered. `Proofs05_10.lean` supplies related proofs;
the inspected excerpt includes the Fourier expansion at Proposition 6.1.

The new layer should preserve ordered quadruple counts, including degeneracies,
and the unnormalized Fourier transform. A factor of N at this boundary would
invalidate the high-correlation corollary.

## Layer 1: finite group combinatorics

Work first over finite additive commutative groups G and W. Represent affine maps
as an additive homomorphism plus a constant. The target need not be a field.

Proposed lemmas:

1. `graph_energy_eq_derivative_collisions`: the graph energy is the sum, over
   directions h and target values w, of the squares of derivative fiber sizes.
2. `graph_energy_sub_affine`: subtracting an affine map preserves graph energy.
3. `graph_energy_eq_card_cube_iff_affine`: characterize the full-energy endpoint.
4. `set_energy_le_card_cube` and `set_energy_eq_card_cube_iff_coset`: the latter
   assumes nonempty support and proves the exact equality case.

Use explicit equivalences between G³ and additive quadruples. Every coefficient
in the defining relation is 1 or −1, so these changes of variables are bijective
without restrictions on characteristic or torsion.

## Layer 2: exact support-pattern identities

Classify a quadruple by which of its four **positions** are in S; positions, not
distinct values, are the relevant objects. Use six classes: zero, one, two on
opposite sides, two on the same side, three, and four positions in S.

The three necessary counts are

```text
Q1      = 4sN² − 12s²N + 12s³ − 4E(S)
Q3      = 4s³ − 4E(S)
Q2same  = 2s²N − 4s³ + 2E(S).
```

Prove these as integer equalities, or equivalent natural-number equalities with
negative terms moved to the other side. Do not rely on truncated subtraction in
natural numbers. Derive the two exact one-valued-error energy formulas from these
counts by splitting on `b + b = 0`.

## Layer 3: error-value comparisons

For nonzero error fibers of sizes c_b, define

```text
M = Σ c_b²
A = s² − M
C = Σ c_b c_(−b)
J = M − C.
```

Prove `2T ≤ 3sA`, `C ≤ M`, and, under the explicit no-nonzero-two-torsion
hypothesis, `C ≤ A`. The identity `2J = Σ(c_b − c_(−b))²` is useful.

Count opposite-side and same-side assignments separately. This produces

```text
E(g0) − E(g) ≥ 2(N − 7s)A                           [odd target]
E(g0) − E(g) ≥ 6(N − 3s)A + 2(N − 2s)J              [involution target].
```

The second statement takes a specified nonzero involution and assumes 3s < N.
The first comparison is valid as an integer inequality without 7s < N; that
inequality is used when deriving nonnegative remainder terms and equality.

Combining with Layer 2 gives the two master inequalities. Equality classification
should be extracted from vanishing nonnegative summands, not from a separate
combinatorial argument. This reduces the equality case to one error value and
the set-energy coset theorem; in the second case J = 0 forces the value to be
an involution.

## Layer 4: normalized inequalities and correction

Only after the exact counting layer, define real densities and divide by N³.
An additive group is nonempty, so N > 0 is available. Prove the cubics are strictly
increasing on [0,1/7] and that their ranges cover [0,1/9].

A practical first formalization can avoid defining analytic inverse functions:
state the conclusion as the existence of a unique t in [0,1/7] satisfying the
cubic equation and an upper bound d(f) ≤ t. The series expansion is an independent
optional layer.

For correction, follow the finite averaging proof in Section 7:

* Select an anchor whose additivity-test failure is no worse than the average.
* Show every derivative distribution has collision probability at least 1−2ρ.
* Take its unique mode. Three modal events have total failure probability at
  most 6ρ < 1, so the derivative cocycle proves additivity of the modes.
* Average the failed tests on points where the function disagrees with its mode.

Prove the half-domain separation bound for distinct affine maps. It gives
uniqueness both in the full-domain theorem and after restricting to a dense
partial domain.

## Layer 5: exact gap and the existing Proposition 6.1

Discreteness of Hamming distance gives the exact non-affine maximum once the
one-point defect lies below 1/9. The cutoff N ≥ 34 requires only elementary
rational inequalities and monotonicity.

The partial-domain theorem starts from graph energy at least (1−ε)N³, **not**
(1−ε)|B|³. Any completion preserves the lower bound. Uniqueness on B follows from
an agreement set larger than N/2. This makes the recovered affine map independent
of completion.

Instantiate this result over `ZMod N`, with N an odd prime, after
`proposition_6_1`. Its input αN³ yields graph energy at least α⁴N³; require
α⁴ > 8/9 and obtain at most D0(1−α⁴)N exceptional points on B.

## Separate vector-space file

The proof for all finite vector-space sizes can be separate from the general
stability theorem. It needs constant-derivative subspaces, extension of a linear
map from a subspace, quotient lifting, zero-sum histogram bounds, and the small
cardinality cases 3, 4, and 5. Those linear-algebra assumptions should not leak
into the general finite-abelian-group theorem.

The recorded exhaustive examples can be converted into regression tests, but
finite checks cannot replace universal proof obligations. Compile each layer
against the actual pinned repository toolchain and inspect theorem dependencies
before making any kernel-verification claim.
