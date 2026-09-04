import FabiusFunction.FiniteQBinomialCore
import FabiusFunction.QMultinomial
import FabiusFunction.BoxPartitions
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Logic.Equiv.Sum
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# Gaussian coefficients count subspaces

This module proves the finite-field interpretation of the Gaussian coefficient: over a finite
field (indeed over any finite division ring) `K` with `Q = |K|`, the number of `k`-dimensional
subspaces of an `n`-dimensional `K`-vector space is `[n, k]_Q`.

## The division-free identity underneath

The textbook argument counts ordered independent `k`-tuples in two ways and *divides*.  The
quotient is meaningless at `q = 0`, at roots of unity, in positive characteristic, or in the
presence of zero divisors, so the first section isolates the polynomial identity that the
division hides:

`[n, k]_q · ∏_{i<k} (q^k - q^i) = ∏_{i<k} (q^n - q^i)`   for `k ≤ n`,

valid in *every* commutative ring (`gaussianBinomial_mul_prod_pow_sub_pow`).  The proof factors
`∏_{i<k}(q^m - q^i) = (-1)^k (∏_{i<k} q^i) (q^{m-k+1}; q)_k`, in which the monomial prefix
`∏_{i<k} q^i` is left unevaluated because it is the same for `m = n` and `m = k` and therefore
cancels symbolically; the remaining content is the cleared q-factorial identity
`(q;q)_k [n,k]_q = (q^{n-k+1};q)_k` already available in `FiniteQBinomialCore`.  The
natural-number form with truncated subtraction, which is what the counting argument produces,
is `gaussianBinomial_nat_mul_prod_pow_sub_pow`.

## The count

`card_submodule_finrank_eq_gaussianBinomial` is the main theorem.  It is stated for an arbitrary
finite division ring `K` and an arbitrary finite `K`-module `V`, and for **every** `k : ℕ`:

`Nat.card {W : Submodule K V // finrank K W = k} = [finrank K V, k]_{|K|}`.

Three ways in which this is stronger than the source statement "the number of `k`-dimensional
subspaces of `F_Q^n` is `[n,k]_Q` for `Q` a prime power":

* `Q` a prime power is never used.  Nothing in the argument sees the characteristic; Mathlib's
  `card_linearIndependent` is already stated for a division ring, so commutativity is free too.
* The ambient space is an arbitrary finite module, not `F_Q^n`.  The literal statement is
  recovered as `card_submodule_pi_finrank_eq_gaussianBinomial`.
* There is no hypothesis `k ≤ n`.  The source gives no range for `k`, and its proof silently
  assumes `0 ≤ k ≤ n`; here the case `n < k` is proved separately from
  `Submodule.finrank_le` and the zero-extension `gaussianBinomial_eq_zero_of_lt`.

The source's "dividing" step presupposes, without saying so, that all fibres of
(independent `k`-tuple) ↦ (its span) have the same cardinality.  Here that is an honest
fibration: `spanOfIndep` is the span map, `indepSpanningEquiv` identifies its fibre over `W`
with the independent `k`-tuples *inside* `W`, and `card_linearIndependent_eq_card_submodule_mul`
sums over the base with `Equiv.sigmaFiberEquiv`.  No division occurs anywhere; the final step is
a cancellation of a nonzero natural number.

## Flags: what is and is not proved

`card_two_step_flag` counts two-step flags `0 ⊆ U ⊆ W ⊆ V` with `dim U = j`, `dim W = m`, and
`card_two_step_flag_eq_qMultinomial` identifies the answer with a corpus q-multinomial
coefficient.  This is the case `r = 3` of the source's partial-flag theorem, and **only** that
case: the general `r`-step statement needs a dependent recursive `Flag : List ℕ → Type` whose
recursion descends into a bound subspace `↥W`, together with a hand-written finiteness proof and
an induction on the list.  That is a module of its own.

Two further caveats about the flag statement.

* In the source `n = n₁ + ⋯ + n_r` is not hypothesised but forced, by `V_r = F_Q^n` together
  with `dim(V_i / V_{i-1}) = n_i`; here the same constraint appears as `j ≤ m ≤ finrank K V`,
  which is why those two inequalities are the hypotheses of the q-multinomial form.
* The source reads the composition **bottom-up** (`n₁ = dim V₁`), giving `[j, m-j, n-m]`, while
  the induction that avoids quotient spaces (pick the top subspace first, then recurse inside
  it) produces the **top-down** composition `[n-m, m-j, j]`, which is what is stated here.  The
  two agree, because `qMultinomial` is invariant under permuting its parts; but that invariance
  is not proved anywhere in the corpus (`QMultinomial` has only nil/cons/singleton/pair/map/
  eval₂/factorial/quotient lemmas), and it cannot be obtained by cancelling in the factorial
  form, which degenerates at `q = 1`.  It is a worthwhile separate lemma.

## Poincaré polynomial of the Grassmannian: algebraic core only

`sum_pow_two_boxSize_eq_gaussianBinomial` and its graded restatement
`sum_card_boxPartitions_mul_pow_eq_gaussianBinomial` prove, over every semiring and for every
`t`, the entire *algebraic* content of the Poincaré-polynomial theorem:

`∑_{λ ⊆ k×(n-k)} (t²)^{|λ|} = [n, k]_{t²}`,   equivalently
`∑_j #{λ ⊆ k×(n-k) : |λ| = j} · t^{2j} = [n, k]_{t²}`.

The *topological* input is not formalized and cannot be: that the Schubert strata of the complex
Grassmannian form a CW decomposition with one real cell of dimension `2|λ|` per partition `λ` in
the `k × (n-k)` box, that all cells being even makes every cellular boundary map vanish, and
hence that `rank H^{2j}(Gr(k,n); ℤ) = #{λ ⊆ k×(n-k) : |λ| = j}`.  Mathlib's
`Module.Grassmannian` is a functor of points with no topology and no cohomology, so the Betti
numbers are not expressible at all.  What is proved here is exactly the last line of the source
proof ("Apply the rectangle-partition theorem with `q = t²`"), in greater generality than the
source, which takes `t` to be a formal variable over `ℤ`.

## Main declarations

* `gaussianBinomial_mul_prod_pow_sub_pow`, `gaussianBinomial_nat_mul_prod_pow_sub_pow`:
  the division-free bridge, over a commutative ring and over `ℕ`.
* `spanOfIndep`, `indepSpanningEquiv`, `card_indep_span_eq`: the fibration and its fibre count.
* `card_linearIndependent_eq_card_submodule_mul`: base × fibre = total.
* `card_submodule_finrank_eq_gaussianBinomial`: the theorem.
* `card_submodule_pi_finrank_eq_gaussianBinomial`: its `K^n` specialisation.
* `card_two_step_flag`, `card_two_step_flag_eq_qMultinomial`: two-step flags.
* `sum_pow_two_boxSize_eq_gaussianBinomial`,
  `sum_card_boxPartitions_mul_pow_eq_gaussianBinomial`: the Grassmannian Poincaré identity.

Two auxiliary `Finite` instances are exported: `instFiniteSubmoduleCarrier` (a submodule of a
finite module is finite -- Mathlib proves the analogue for `Subgroup` by hand) and
`instFiniteSubmodule` (a finite module has finitely many submodules, since a submodule is
determined by its underlying set).  The second is genuinely needed: it is what makes the inner
Grassmannian of `card_two_step_flag` finite.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

section AlgebraicBridge

variable {R : Type*} [CommRing R]

/-- The falling product `∏_{i<k} (q^m - q^i)` in factored form: a monomial prefix, a sign, and
the top `k` factors of `(q;q)_m`.  The prefix `∏_{i<k} q^i` is deliberately left unevaluated,
since it does not depend on `m` and therefore cancels in
`gaussianBinomial_mul_prod_pow_sub_pow`. -/
private theorem prod_pow_sub_pow_eq (q : R) {k m : ℕ} (hkm : k ≤ m) :
    ∏ i ∈ Finset.range k, (q ^ m - q ^ i)
      = (-1) ^ k * (∏ i ∈ Finset.range k, q ^ i) *
          finiteQPochhammerIn (q ^ (m - k + 1)) q k := by
  have hfactor : ∀ i ∈ Finset.range k,
      q ^ m - q ^ i = q ^ i * (-1 * (1 - q ^ (m - i))) := by
    intro i hi
    have hik : i < k := Finset.mem_range.mp hi
    have hsum : i + (m - i) = m := by omega
    calc q ^ m - q ^ i = q ^ (i + (m - i)) - q ^ i := by rw [hsum]
      _ = q ^ i * (-1 * (1 - q ^ (m - i))) := by rw [pow_add]; ring
  -- `rw [← pow_add]` and not `rw [pow_add]`: the forward direction would fire on the
  -- exponent `m - k + 1`, which is itself an addition, and split it as `q ^ (m-k) * q ^ 1`.
  have hstep : ∀ j ∈ Finset.range k,
      (1 : R) - q ^ (m - k + 1) * q ^ j = 1 - q ^ (m - k + 1 + j) := by
    intro j _
    rw [← pow_add]
  have hpoch : finiteQPochhammerIn (q ^ (m - k + 1)) q k
      = ∏ i ∈ Finset.range k, (1 - q ^ (m - i)) := by
    calc finiteQPochhammerIn (q ^ (m - k + 1)) q k
        = ∏ j ∈ Finset.range k, (1 - q ^ (m - k + 1) * q ^ j) := rfl
      _ = ∏ j ∈ Finset.range k, (1 - q ^ (m - k + 1 + j)) := Finset.prod_congr rfl hstep
      _ = ∏ j ∈ Finset.range k, (1 - q ^ (m - k + 1 + (k - 1 - j))) :=
          (Finset.prod_range_reflect (fun j => 1 - q ^ (m - k + 1 + j)) k).symm
      _ = ∏ i ∈ Finset.range k, (1 - q ^ (m - i)) := by
          refine Finset.prod_congr rfl fun i hi => ?_
          have hik : i < k := Finset.mem_range.mp hi
          have hexp : m - k + 1 + (k - 1 - i) = m - i := by omega
          rw [hexp]
  calc ∏ i ∈ Finset.range k, (q ^ m - q ^ i)
      = ∏ i ∈ Finset.range k, (q ^ i * (-1 * (1 - q ^ (m - i)))) :=
        Finset.prod_congr rfl hfactor
    _ = (∏ i ∈ Finset.range k, q ^ i) *
          ∏ i ∈ Finset.range k, (-1 * (1 - q ^ (m - i))) := Finset.prod_mul_distrib
    _ = (∏ i ∈ Finset.range k, q ^ i) *
          ((∏ _i ∈ Finset.range k, (-1 : R)) *
            ∏ i ∈ Finset.range k, (1 - q ^ (m - i))) := by
        rw [Finset.prod_mul_distrib]
    _ = (-1) ^ k * (∏ i ∈ Finset.range k, q ^ i) *
          ∏ i ∈ Finset.range k, (1 - q ^ (m - i)) := by
        rw [Finset.prod_const, Finset.card_range]
        ring
    _ = (-1) ^ k * (∏ i ∈ Finset.range k, q ^ i) *
          finiteQPochhammerIn (q ^ (m - k + 1)) q k := by rw [hpoch]

/-- **The division-free subspace-count identity.**  Over every commutative ring and for `k ≤ n`,

`[n, k]_q · ∏_{i<k} (q^k - q^i) = ∏_{i<k} (q^n - q^i)`.

Read over a finite field this says "(ordered bases of a `k`-space) × (number of `k`-spaces) =
(independent `k`-tuples)", but no division, no regularity and no finiteness is involved, so the
identity also holds at `q = 0`, at roots of unity, in positive characteristic and in the
presence of zero divisors. -/
theorem gaussianBinomial_mul_prod_pow_sub_pow (q : R) {n k : ℕ} (hk : k ≤ n) :
    gaussianBinomial q n k * ∏ i ∈ Finset.range k, (q ^ k - q ^ i)
      = ∏ i ∈ Finset.range k, (q ^ n - q ^ i) := by
  have hself : finiteQPochhammerIn (q ^ (k - k + 1)) q k = finiteQPochhammerIn q q k := by
    rw [Nat.sub_self, Nat.zero_add, pow_one]
  calc gaussianBinomial q n k * ∏ i ∈ Finset.range k, (q ^ k - q ^ i)
      = gaussianBinomial q n k *
          ((-1) ^ k * (∏ i ∈ Finset.range k, q ^ i) * finiteQPochhammerIn q q k) := by
        rw [prod_pow_sub_pow_eq q (le_refl k), hself]
    _ = (-1) ^ k * (∏ i ∈ Finset.range k, q ^ i) *
          (finiteQPochhammerIn q q k * gaussianBinomial q n k) := by ring
    _ = (-1) ^ k * (∏ i ∈ Finset.range k, q ^ i) *
          finiteQPochhammerIn (q ^ (n - k + 1)) q k := by
        rw [finiteQPochhammerIn_self_mul_gaussianBinomial q hk]
    _ = ∏ i ∈ Finset.range k, (q ^ n - q ^ i) := (prod_pow_sub_pow_eq q hk).symm

end AlgebraicBridge

/-- The same identity over `ℕ`, where the differences are truncated subtractions.  This is the
form produced by the counting argument.  The hypothesis `0 < Q` is what makes truncation
harmless: it gives `Q ^ i ≤ Q ^ m` for `i ≤ m`, so every difference casts to `ℤ` verbatim. -/
theorem gaussianBinomial_nat_mul_prod_pow_sub_pow {Q : ℕ} (hQ : 0 < Q) {n k : ℕ}
    (hk : k ≤ n) :
    gaussianBinomial Q n k * ∏ i ∈ Finset.range k, (Q ^ k - Q ^ i)
      = ∏ i ∈ Finset.range k, (Q ^ n - Q ^ i) := by
  have hcast : ∀ m : ℕ, k ≤ m →
      ((∏ i ∈ Finset.range k, (Q ^ m - Q ^ i) : ℕ) : ℤ)
        = ∏ i ∈ Finset.range k, ((Q : ℤ) ^ m - (Q : ℤ) ^ i) := by
    intro m hm
    rw [Nat.cast_prod]
    refine Finset.prod_congr rfl fun i hi => ?_
    have him : i ≤ m := le_of_lt (lt_of_lt_of_le (Finset.mem_range.mp hi) hm)
    rw [Nat.cast_sub (Nat.pow_le_pow_right hQ him)]
    simp only [Nat.cast_pow]
  have hgb : ((gaussianBinomial Q n k : ℕ) : ℤ) = gaussianBinomial (Q : ℤ) n k := by
    simpa using map_gaussianBinomial (Nat.castRingHom ℤ) Q n k
  have hZ : ((gaussianBinomial Q n k * ∏ i ∈ Finset.range k, (Q ^ k - Q ^ i) : ℕ) : ℤ)
      = ((∏ i ∈ Finset.range k, (Q ^ n - Q ^ i) : ℕ) : ℤ) := by
    rw [Nat.cast_mul, hgb, hcast k (le_refl k), hcast n hk]
    exact gaussianBinomial_mul_prod_pow_sub_pow (Q : ℤ) hk
  exact Nat.cast_injective hZ

/-- Every submodule of a finite module is finite. -/
instance instFiniteSubmoduleCarrier {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [Finite M] (p : Submodule R M) : Finite p :=
  Subtype.finite

/-- A finite module has only finitely many submodules, since a submodule is determined by its
underlying set. -/
instance instFiniteSubmodule {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [Finite M] : Finite (Submodule R M) :=
  Finite.of_injective (fun p : Submodule R M => (p : Set M)) SetLike.coe_injective

section Counting

variable {K V : Type*} [DivisionRing K] [Fintype K] [AddCommGroup V] [Module K V] [Finite V]

/-- The span map: a linearly independent `k`-tuple of `V` spans a `k`-dimensional subspace. -/
def spanOfIndep (k : ℕ) (s : {s : Fin k → V // LinearIndependent K s}) :
    {W : Submodule K V // Module.finrank K W = k} :=
  ⟨Submodule.span K (Set.range s.1), by
    rw [finrank_span_eq_card s.2, Fintype.card_fin]⟩

/-- Each vector of a family spanning `W` lies in `W`. -/
private theorem mem_of_span_range_eq {k : ℕ} {W : Submodule K V} {s : Fin k → V}
    (hs : Submodule.span K (Set.range s) = W) (i : Fin k) : s i ∈ W := by
  rw [← hs]
  exact Submodule.subset_span (Set.mem_range_self i)

/-- A family taking values in `W` is independent in `W` as soon as it is independent in `V`. -/
private theorem linearIndependent_mk {k : ℕ} {W : Submodule K V} {s : Fin k → V}
    (hmem : ∀ i, s i ∈ W) (hs : LinearIndependent K s) :
    LinearIndependent K fun i => (⟨s i, hmem i⟩ : W) := by
  refine LinearIndependent.of_comp W.subtype ?_
  have hcomp : (⇑W.subtype ∘ fun i => (⟨s i, hmem i⟩ : W)) = s := funext fun _ => rfl
  rw [hcomp]
  exact hs

/-- An independent `k`-tuple of a `k`-dimensional subspace `W` spans all of `W`. -/
private theorem span_range_subtype_eq {k : ℕ} {W : Submodule K V}
    (hW : Module.finrank K W = k) {t : Fin k → W} (ht : LinearIndependent K t) :
    Submodule.span K (Set.range (⇑W.subtype ∘ t)) = W := by
  have htop : Submodule.span K (Set.range t) = ⊤ :=
    ht.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, hW])
  rw [Set.range_comp, Submodule.span_image, htop, Submodule.map_top, Submodule.range_subtype]

/-- **The fibre of the span map.**  For a `k`-dimensional subspace `W`, the independent
`k`-tuples of `V` spanning `W` are exactly the ordered bases of `W`. -/
def indepSpanningEquiv {k : ℕ} (W : Submodule K V) (hW : Module.finrank K W = k) :
    {t : Fin k → W // LinearIndependent K t} ≃
      {s : Fin k → V // LinearIndependent K s ∧ Submodule.span K (Set.range s) = W} where
  toFun t :=
    ⟨⇑W.subtype ∘ t.1, t.2.map' W.subtype (Submodule.ker_subtype W),
      span_range_subtype_eq hW t.2⟩
  invFun s :=
    ⟨fun i => ⟨s.1 i, mem_of_span_range_eq s.2.2 i⟩,
      linearIndependent_mk (mem_of_span_range_eq s.2.2) s.2.1⟩
  left_inv _ := Subtype.ext (funext fun _ => Subtype.ext rfl)
  right_inv _ := Subtype.ext (funext fun _ => rfl)

/-- **The fibre count.**  A `k`-dimensional subspace of a vector space over a field with `Q`
elements has exactly `∏_{i<k} (Q^k - Q^i)` ordered bases. -/
theorem card_indep_span_eq {k : ℕ} (W : Submodule K V) (hW : Module.finrank K W = k) :
    Nat.card {s : {s : Fin k → V // LinearIndependent K s} //
        Submodule.span K (Set.range s.1) = W}
      = ∏ i ∈ Finset.range k, (Fintype.card K ^ k - Fintype.card K ^ i) := by
  have e : {s : {s : Fin k → V // LinearIndependent K s} //
      Submodule.span K (Set.range s.1) = W} ≃ {t : Fin k → W // LinearIndependent K t} :=
    (Equiv.subtypeSubtypeEquivSubtypeInter
        (fun s : Fin k → V => LinearIndependent K s)
        (fun s : Fin k → V => Submodule.span K (Set.range s) = W)).trans
      (indepSpanningEquiv W hW).symm
  calc Nat.card {s : {s : Fin k → V // LinearIndependent K s} //
          Submodule.span K (Set.range s.1) = W}
      = Nat.card {t : Fin k → W // LinearIndependent K t} := Nat.card_congr e
    _ = ∏ i : Fin k, (Fintype.card K ^ Module.finrank K W - Fintype.card K ^ (i : ℕ)) :=
        card_linearIndependent (le_of_eq hW.symm)
    _ = ∏ i : Fin k, (Fintype.card K ^ k - Fintype.card K ^ (i : ℕ)) := by rw [hW]
    _ = ∏ i ∈ Finset.range k, (Fintype.card K ^ k - Fintype.card K ^ i) :=
        Fin.prod_univ_eq_prod_range
          (fun i => Fintype.card K ^ k - Fintype.card K ^ i) k

/-- **The fibration over the Grassmannian.**  Counting the total space of the span map fibre by
fibre replaces the source's unjustified division by an honest product decomposition. -/
theorem card_linearIndependent_eq_card_submodule_mul (k : ℕ) :
    Nat.card {s : Fin k → V // LinearIndependent K s}
      = Nat.card {W : Submodule K V // Module.finrank K W = k}
          * ∏ i ∈ Finset.range k, (Fintype.card K ^ k - Fintype.card K ^ i) := by
  classical
  letI : Fintype {W : Submodule K V // Module.finrank K W = k} := Fintype.ofFinite _
  have hfib : ∀ W : {W : Submodule K V // Module.finrank K W = k},
      Nat.card {s : {s : Fin k → V // LinearIndependent K s} // spanOfIndep k s = W}
        = ∏ i ∈ Finset.range k, (Fintype.card K ^ k - Fintype.card K ^ i) := by
    intro W
    have e : {s : {s : Fin k → V // LinearIndependent K s} // spanOfIndep k s = W} ≃
        {s : {s : Fin k → V // LinearIndependent K s} //
          Submodule.span K (Set.range s.1) = W.1} :=
      Equiv.subtypeEquivRight fun _ =>
        ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    rw [Nat.card_congr e]
    exact card_indep_span_eq W.1 W.2
  calc Nat.card {s : Fin k → V // LinearIndependent K s}
      = Nat.card (Σ W : {W : Submodule K V // Module.finrank K W = k},
          {s : {s : Fin k → V // LinearIndependent K s} // spanOfIndep k s = W}) :=
        (Nat.card_congr (Equiv.sigmaFiberEquiv (spanOfIndep (K := K) (V := V) k))).symm
    _ = ∑ W : {W : Submodule K V // Module.finrank K W = k},
          Nat.card {s : {s : Fin k → V // LinearIndependent K s} // spanOfIndep k s = W} :=
        Nat.card_sigma
    _ = Nat.card {W : Submodule K V // Module.finrank K W = k} *
          ∏ i ∈ Finset.range k, (Fintype.card K ^ k - Fintype.card K ^ i) := by
        rw [Finset.sum_const_nat (fun W _ => hfib W), Finset.card_univ,
          Nat.card_eq_fintype_card]

/-- **Gaussian coefficients count subspaces.**  For every finite division ring `K` with
`Q = |K|`, every finite `K`-module `V` and every `k : ℕ`, the number of `k`-dimensional
subspaces of `V` is `[finrank K V, k]_Q`.

No primality, no commutativity and no bound on `k` is assumed: for `k > finrank K V` both sides
vanish, the left by `Submodule.finrank_le` and the right by the zero-extension of the recursive
Gaussian triangle. -/
theorem card_submodule_finrank_eq_gaussianBinomial (k : ℕ) :
    Nat.card {W : Submodule K V // Module.finrank K W = k}
      = gaussianBinomial (Fintype.card K) (Module.finrank K V) k := by
  rcases le_or_gt k (Module.finrank K V) with hk | hk
  · have hQ : 1 < Fintype.card K := Fintype.one_lt_card
    have hQpos : 0 < Fintype.card K := lt_trans Nat.zero_lt_one hQ
    have hne : ∏ i ∈ Finset.range k, (Fintype.card K ^ k - Fintype.card K ^ i) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro i hi
      exact Nat.sub_ne_zero_of_lt (Nat.pow_lt_pow_right hQ (Finset.mem_range.mp hi))
    have hfin : ∏ i : Fin k,
          (Fintype.card K ^ Module.finrank K V - Fintype.card K ^ (i : ℕ))
        = ∏ i ∈ Finset.range k,
            (Fintype.card K ^ Module.finrank K V - Fintype.card K ^ i) :=
      Fin.prod_univ_eq_prod_range
        (fun i => Fintype.card K ^ Module.finrank K V - Fintype.card K ^ i) k
    have hli : Nat.card {s : Fin k → V // LinearIndependent K s}
        = ∏ i ∈ Finset.range k,
            (Fintype.card K ^ Module.finrank K V - Fintype.card K ^ i) := by
      rw [card_linearIndependent hk]
      exact hfin
    refine mul_right_cancel₀ hne ?_
    rw [← card_linearIndependent_eq_card_submodule_mul k, hli,
      gaussianBinomial_nat_mul_prod_pow_sub_pow hQpos hk]
  · haveI : IsEmpty {W : Submodule K V // Module.finrank K W = k} :=
      ⟨fun W => by
        have hle : Module.finrank K W.1 ≤ Module.finrank K V := W.1.finrank_le
        have hWk : Module.finrank K W.1 = k := W.2
        omega⟩
    rw [Nat.card_of_isEmpty, gaussianBinomial_eq_zero_of_lt _ hk]

/-- The literal source statement: the number of `k`-dimensional subspaces of `K^n` is
`[n, k]_{|K|}`. -/
theorem card_submodule_pi_finrank_eq_gaussianBinomial (n k : ℕ) :
    Nat.card {W : Submodule K (Fin n → K) // Module.finrank K W = k}
      = gaussianBinomial (Fintype.card K) n k := by
  have h := card_submodule_finrank_eq_gaussianBinomial (K := K) (V := Fin n → K) k
  rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h

/-- **Two-step flags.**  The number of pairs `U ⊆ W ⊆ V` with `dim W = m` and `dim U = j` is
`[n, m]_Q · [m, j]_Q`, where `n = finrank K V`.  This is the case `r = 3` of the source's
partial-flag theorem; no bound relating `j`, `m` and `n` is needed, because the zero-extended
Gaussian coefficients make the degenerate cases true. -/
theorem card_two_step_flag (m j : ℕ) :
    Nat.card (Σ W : {W : Submodule K V // Module.finrank K W = m},
        {U : Submodule K W.1 // Module.finrank K U = j})
      = gaussianBinomial (Fintype.card K) (Module.finrank K V) m
        * gaussianBinomial (Fintype.card K) m j := by
  classical
  letI : Fintype {W : Submodule K V // Module.finrank K W = m} := Fintype.ofFinite _
  have hinner : ∀ W : {W : Submodule K V // Module.finrank K W = m},
      Nat.card {U : Submodule K W.1 // Module.finrank K U = j}
        = gaussianBinomial (Fintype.card K) m j := by
    intro W
    have h := card_submodule_finrank_eq_gaussianBinomial (K := K) (V := ↥W.1) j
    rwa [W.2] at h
  calc Nat.card (Σ W : {W : Submodule K V // Module.finrank K W = m},
        {U : Submodule K W.1 // Module.finrank K U = j})
      = ∑ W : {W : Submodule K V // Module.finrank K W = m},
          Nat.card {U : Submodule K W.1 // Module.finrank K U = j} := Nat.card_sigma
    _ = Nat.card {W : Submodule K V // Module.finrank K W = m}
          * gaussianBinomial (Fintype.card K) m j := by
        rw [Finset.sum_const_nat (fun W _ => hinner W), Finset.card_univ,
          Nat.card_eq_fintype_card]
    _ = gaussianBinomial (Fintype.card K) (Module.finrank K V) m
          * gaussianBinomial (Fintype.card K) m j := by
        rw [card_submodule_finrank_eq_gaussianBinomial]

/-- The two-step flag count as a q-multinomial coefficient.  The composition is read
**top-down**, `[n - m, m - j, j]`, matching the induction that stays inside subspaces; the
source writes the bottom-up composition `[j, m - j, n - m]`, which is the same number but whose
identification would require permutation invariance of `qMultinomial`, a lemma the corpus does
not yet contain. -/
theorem card_two_step_flag_eq_qMultinomial {m j : ℕ} (hj : j ≤ m)
    (hm : m ≤ Module.finrank K V) :
    Nat.card (Σ W : {W : Submodule K V // Module.finrank K W = m},
        {U : Submodule K W.1 // Module.finrank K U = j})
      = qMultinomial (Fintype.card K) [Module.finrank K V - m, m - j, j] := by
  have h1 : m - j + j = m := Nat.sub_add_cancel hj
  have h2 : Module.finrank K V - m + m = Module.finrank K V := Nat.sub_add_cancel hm
  rw [card_two_step_flag, qMultinomial_cons, qMultinomial_cons, qMultinomial_singleton]
  simp only [List.sum_cons, List.sum_nil, add_zero, mul_one]
  rw [h1, h2, gaussianBinomial_symm _ hm, gaussianBinomial_symm _ hj]

end Counting

section Poincare

variable {R : Type*} [Semiring R]

/-- **The algebraic core of the Grassmannian Poincaré polynomial.**  For `k ≤ n` and every `t`
in every semiring,

`∑_{λ ⊆ k×(n-k)} (t²)^{|λ|} = [n, k]_{t²}`.

The topological identification of the left side with `∑_j rank H^{2j}(Gr(k,n); ℤ) t^{2j}` --
the Schubert CW decomposition, the vanishing of all cellular boundary maps, and cellular
cohomology itself -- is not formalized, and cannot be: Mathlib has no cohomology of
Grassmannians. -/
theorem sum_pow_two_boxSize_eq_gaussianBinomial (t : R) {n k : ℕ} (hk : k ≤ n) :
    ∑ l ∈ boxPartitions k (n - k), (t ^ 2) ^ (∑ i, l i) = gaussianBinomial (t ^ 2) n k := by
  rw [sum_pow_boxSize_eq_gaussianBinomial (t ^ 2) k (n - k), Nat.sub_add_cancel hk]

/-- A partition inside a `k × m` box has size at most `k * m`. -/
private theorem boxSize_le {k m : ℕ} {l : Fin k → ℕ} (hl : l ∈ boxPartitions k m) :
    ∑ i, l i ≤ k * m := by
  calc ∑ i, l i ≤ ∑ _i : Fin k, m :=
        Finset.sum_le_sum fun i _ => (mem_boxPartitions.mp hl).1 i
    _ = k * m := by
        rw [Finset.sum_const_nat (m := m) (f := fun _ : Fin k => m) (fun _ _ => rfl),
          Finset.card_univ, Fintype.card_fin]

/-- **The graded form.**  Collecting the box partitions by size exhibits the Gaussian
coefficient at `t²` as the generating polynomial whose coefficient of `t^{2d}` is the number of
partitions of size `d` in the `k × (n-k)` box.  Granting the Schubert cell decomposition, that
coefficient is `rank H^{2d}(Gr(k,n); ℤ)`, so this is the Poincaré polynomial identity with its
one topological input excised. -/
theorem sum_card_boxPartitions_mul_pow_eq_gaussianBinomial (t : R) {n k : ℕ} (hk : k ≤ n) :
    ∑ d ∈ Finset.range (k * (n - k) + 1),
        (((boxPartitions k (n - k)).filter fun l => ∑ i, l i = d).card : R) * t ^ (2 * d)
      = gaussianBinomial (t ^ 2) n k := by
  have hmaps : ∀ l ∈ boxPartitions k (n - k),
      (∑ i, l i) ∈ Finset.range (k * (n - k) + 1) := fun l hl =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (boxSize_le hl))
  have hfiber : ∀ d ∈ Finset.range (k * (n - k) + 1),
      (((boxPartitions k (n - k)).filter fun l => ∑ i, l i = d).card : R) * t ^ (2 * d)
        = ∑ l ∈ ((boxPartitions k (n - k)).filter fun l => ∑ i, l i = d),
            (t ^ 2) ^ (∑ i, l i) := by
    intro d _
    calc (((boxPartitions k (n - k)).filter fun l => ∑ i, l i = d).card : R) * t ^ (2 * d)
        = ∑ _l ∈ ((boxPartitions k (n - k)).filter fun l => ∑ i, l i = d), t ^ (2 * d) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = ∑ l ∈ ((boxPartitions k (n - k)).filter fun l => ∑ i, l i = d),
            (t ^ 2) ^ (∑ i, l i) :=
          Finset.sum_congr rfl fun l hl => by
            have hld : ∑ i, l i = d := (Finset.mem_filter.mp hl).2
            rw [hld, ← pow_mul]
  calc ∑ d ∈ Finset.range (k * (n - k) + 1),
        (((boxPartitions k (n - k)).filter fun l => ∑ i, l i = d).card : R) * t ^ (2 * d)
      = ∑ d ∈ Finset.range (k * (n - k) + 1),
          ∑ l ∈ ((boxPartitions k (n - k)).filter fun l => ∑ i, l i = d),
            (t ^ 2) ^ (∑ i, l i) := Finset.sum_congr rfl hfiber
    _ = ∑ l ∈ boxPartitions k (n - k), (t ^ 2) ^ (∑ i, l i) :=
        Finset.sum_fiberwise_of_maps_to hmaps _
    _ = gaussianBinomial (t ^ 2) n k := sum_pow_two_boxSize_eq_gaussianBinomial t hk

end Poincare

end Fabius
