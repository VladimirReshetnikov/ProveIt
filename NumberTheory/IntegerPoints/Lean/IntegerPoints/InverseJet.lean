import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Ordered partitions and normalized inverse jets

This module isolates the finite combinatorics and algebra behind the inverse-derivative
calculation in Graham--Kolesnik Lemma 3.9.  It has no dependency on the analytic-number-theory
development: an ordered partition records one term of the one-variable Faà di Bruno formula,
and `normalizedRecurrenceAt` is the resulting algebraic inverse-jet equation.

The distinguished one-block partition is separated from all other terms.  Every block in a
remaining partition is strictly smaller than the ambient derivative order; this is the
triangularity needed for induction on inverse jets.
-/

open scoped BigOperators Topology
open Finset

namespace LeanProofs.IntegerPoints

namespace InverseJet

/-! ## Ordered-finpartition combinatorics -/

/-- The sum of the block sizes of an ordered finpartition is its ambient size. -/
theorem sum_partSize {p : ℕ} (c : OrderedFinpartition p) :
    ∑ j : Fin c.length, c.partSize j = p := by
  simpa only [Fintype.card_sigma, Fintype.card_fin] using
    Fintype.card_congr c.equivSigma

/-- The ordered finpartition with one block containing every element of `Fin (p + 1)`. -/
def oneBlock (p : ℕ) : OrderedFinpartition (p + 1) where
  length := 1
  partSize _ := p + 1
  partSize_pos _ := Nat.succ_pos p
  emb _ i := i
  emb_strictMono _ := strictMono_id
  parts_strictMono := Subsingleton.strictMono _
  disjoint := by
    intro i _ j _ hij
    exact (hij (Subsingleton.elim i j)).elim
  cover i := ⟨0, i, rfl⟩

@[simp]
theorem oneBlock_length (p : ℕ) : (oneBlock p).length = 1 := rfl

@[simp]
theorem oneBlock_partSize (p : ℕ) (j : Fin (oneBlock p).length) :
    (oneBlock p).partSize j = p + 1 := rfl

@[simp]
theorem oneBlock_emb (p : ℕ) (j : Fin (oneBlock p).length)
    (i : Fin ((oneBlock p).partSize j)) : (oneBlock p).emb j i = i := rfl

/-- A positive-size ordered finpartition of length one is the distinguished one-block
partition. -/
theorem eq_oneBlock_of_length_eq_one {p : ℕ} (c : OrderedFinpartition (p + 1))
    (hc : c.length = 1) : c = oneBlock p := by
  have hsum := sum_partSize c
  rcases c with ⟨length, partSize, partSize_pos, emb, emb_strictMono,
    parts_strictMono, disjoint, cover⟩
  dsimp at hc hsum ⊢
  subst length
  have hpartSize : partSize = fun _ : Fin 1 ↦ p + 1 := by
    funext i
    simpa [Fin.eq_zero i] using hsum
  subst partSize
  have hemb (i : Fin 1) (j : Fin (p + 1)) : emb i j = j :=
    le_antisymm (emb_strictMono i).apply_le (emb_strictMono i).le_apply
  simpa [oneBlock, OrderedFinpartition.ext_iff, funext_iff, Fin.forall_fin_one] using
    hemb 0

/-- Characterization of the unique one-block ordered finpartition. -/
theorem eq_oneBlock_iff_length_eq_one {p : ℕ} (c : OrderedFinpartition (p + 1)) :
    c = oneBlock p ↔ c.length = 1 := by
  constructor
  · rintro rfl
    rfl
  · exact eq_oneBlock_of_length_eq_one c

/-- If a finpartition has at least two blocks, each individual block is strictly smaller than
the ambient set. -/
theorem partSize_lt_of_one_lt_length {p : ℕ} (c : OrderedFinpartition p)
    (hc : 1 < c.length) (j : Fin c.length) : c.partSize j < p := by
  obtain ⟨k, hkj⟩ := Fintype.exists_ne_of_one_lt_card (by simpa using hc) j
  have hrest : 0 < ∑ i ∈ (Finset.univ : Finset (Fin c.length)).erase j, c.partSize i := by
    apply Finset.sum_pos
    · intro i _
      exact c.partSize_pos i
    · exact ⟨k, Finset.mem_erase.mpr ⟨hkj, Finset.mem_univ k⟩⟩
  calc
    c.partSize j <
        (∑ i ∈ (Finset.univ : Finset (Fin c.length)).erase j, c.partSize i) +
          c.partSize j := by omega
    _ = ∑ i : Fin c.length, c.partSize i :=
      Finset.sum_erase_add Finset.univ _ (Finset.mem_univ j)
    _ = p := sum_partSize c

/-- All ordered finpartitions except the one-block term. -/
noncomputable def remainderPartitions (p : ℕ) :
    Finset (OrderedFinpartition (p + 1)) :=
  Finset.univ.erase (oneBlock p)

theorem mem_remainderPartitions_iff {p : ℕ} {c : OrderedFinpartition (p + 1)} :
    c ∈ remainderPartitions p ↔ 1 < c.length := by
  classical
  rw [remainderPartitions, Finset.mem_erase]
  simp only [Finset.mem_univ, and_true]
  constructor
  · intro hc
    have hpos : 0 < c.length := c.length_pos (Nat.succ_pos p)
    have hne : c.length ≠ 1 := fun h ↦ hc (eq_oneBlock_of_length_eq_one c h)
    omega
  · intro hc hEq
    subst c
    simp at hc

theorem partSize_lt_of_mem_remainderPartitions {p : ℕ}
    {c : OrderedFinpartition (p + 1)} (hc : c ∈ remainderPartitions p)
    (j : Fin c.length) : c.partSize j < p + 1 :=
  partSize_lt_of_one_lt_length c (mem_remainderPartitions_iff.mp hc) j

/-! ## The triangular inverse-jet recurrence -/

/-- The monomial indexed by one ordered finpartition in the scalar Faà di Bruno formula. -/
def partitionTerm {R : Type*} [CommMonoid R] (u z : ℕ → R) {p : ℕ}
    (c : OrderedFinpartition p) : R :=
  u c.length * ∏ j, z (c.partSize j)

@[simp]
theorem partitionTerm_oneBlock {R : Type*} [CommMonoid R] (u z : ℕ → R) (p : ℕ) :
    partitionTerm u z (oneBlock p) = u 1 * z (p + 1) := by
  simp [partitionTerm, oneBlock]

/-- Split the top inverse jet from the terms involving only lower inverse jets. -/
theorem sum_partitionTerm_eq_top_add_remainder {R : Type*} [CommSemiring R]
    (u z : ℕ → R) (p : ℕ) :
    (∑ c : OrderedFinpartition (p + 1), partitionTerm u z c) =
      u 1 * z (p + 1) +
        ∑ c ∈ remainderPartitions p, partitionTerm u z c := by
  classical
  simpa only [remainderPartitions, partitionTerm_oneBlock, add_comm] using
    (Finset.sum_erase_add Finset.univ (partitionTerm u z)
      (Finset.mem_univ (oneBlock p))).symm

/-- The normalized inverse-jet recurrence at order `p`.  For positive `p`, its right-hand side
is the `p`-th derivative of the identity function at `1`. -/
def normalizedRecurrenceAt (u z : ℕ → ℝ) (p : ℕ) : Prop :=
  ∑ c : OrderedFinpartition p, partitionTerm u z c = if p = 1 then 1 else 0

/-- A nonzero first forward jet determines the next inverse jet from lower-order terms. -/
theorem eq_top_of_normalizedRecurrenceAt {u z : ℕ → ℝ} {p : ℕ}
    (hu : u 1 ≠ 0) (hrec : normalizedRecurrenceAt u z (p + 1)) :
    z (p + 1) =
      ((if p + 1 = 1 then 1 else 0) -
          ∑ c ∈ remainderPartitions p, partitionTerm u z c) / u 1 := by
  rw [normalizedRecurrenceAt, sum_partitionTerm_eq_top_add_remainder] at hrec
  apply (eq_div_iff hu).2
  rw [mul_comm]
  exact eq_sub_of_add_eq hrec

/-! ## Exact power-model coefficients -/

/-- Rising-Pochhammer coefficient `(s)_p`. -/
def risingCoeff (s : ℝ) (p : ℕ) : ℝ :=
  ∏ i ∈ Finset.range p, (s + i)

/-- The normalized `p`-th derivative of `x ↦ x⁻ˢ` at `x = 1`. -/
def forwardCoeff (s : ℝ) (p : ℕ) : ℝ :=
  (-1 : ℝ) ^ p * risingCoeff s p

/-- The normalized `p`-th derivative of the inverse power `x ↦ x⁻¹⁄ˢ` at `x = 1`. -/
noncomputable def inverseCoeff (s : ℝ) (p : ℕ) : ℝ :=
  (-1 : ℝ) ^ p * risingCoeff (1 / s) p

@[simp]
theorem risingCoeff_zero (s : ℝ) : risingCoeff s 0 = 1 := by
  simp [risingCoeff]

theorem risingCoeff_succ (s : ℝ) (p : ℕ) :
    risingCoeff s (p + 1) = risingCoeff s p * (s + p) := by
  simp [risingCoeff, Finset.prod_range_succ]

theorem risingCoeff_pos {s : ℝ} (hs : 0 < s) (p : ℕ) : 0 < risingCoeff s p := by
  apply Finset.prod_pos
  intro i hi
  have hi0 : (0 : ℝ) ≤ i := by positivity
  exact add_pos_of_pos_of_nonneg hs hi0

@[simp]
theorem forwardCoeff_one_div (s : ℝ) (p : ℕ) :
    forwardCoeff (1 / s) p = inverseCoeff s p := rfl

/-- Evaluating the descending Pochhammer polynomial at `-s` gives the signed rising
coefficient used by the forward power jet. -/
theorem descPochhammer_eval_neg (s : ℝ) (p : ℕ) :
    (descPochhammer ℝ p).eval (-s) = forwardCoeff s p := by
  rw [descPochhammer_eval_eq_prod_range]
  simp_rw [show ∀ i : ℕ, -s - (i : ℝ) = -(s + i) by intro i; ring]
  rw [Finset.prod_neg]
  simp [forwardCoeff, risingCoeff]

/-- The all-orders derivative formula for the forward model, specialized at `1`. -/
@[simp]
theorem iteratedDeriv_rpow_neg_at_one (s : ℝ) (p : ℕ) :
    iteratedDeriv p (fun x : ℝ ↦ x ^ (-s)) 1 = forwardCoeff s p := by
  rw [iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const, descPochhammer_eval_neg]
  simp

/-- The inverse power model really is a local inverse of the forward power model at `1`. -/
theorem forward_comp_inverse_eventuallyEq_id {s : ℝ} (hs : s ≠ 0) :
    ((fun x : ℝ ↦ x ^ (-s)) ∘ (fun x : ℝ ↦ x ^ (-(1 / s)))) =ᶠ[𝓝 1] id := by
  filter_upwards [eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)] with x hx
  change (x ^ (-(1 / s))) ^ (-s) = x
  rw [← Real.rpow_mul hx.le]
  have hpow : (-(1 / s)) * (-s) = 1 := by
    field_simp
  rw [hpow, Real.rpow_one]

/-- The forward and inverse model coefficients solve every positive normalized inverse-jet
recurrence exactly. -/
theorem model_normalizedRecurrenceAt {s : ℝ} (hs : 0 < s) {p : ℕ} (hp : 0 < p) :
    normalizedRecurrenceAt (forwardCoeff s) (inverseCoeff s) p := by
  let outer : ℝ → ℝ := fun x ↦ x ^ (-s)
  let inner : ℝ → ℝ := fun x ↦ x ^ (-(1 / s))
  have hinner : ContDiffAt ℝ p inner 1 := by
    exact Real.contDiffAt_rpow_const_of_ne one_ne_zero
  have houter : ContDiffAt ℝ p outer (inner 1) := by
    simpa [outer, inner] using
      (Real.contDiffAt_rpow_const_of_ne (x := (1 : ℝ)) (p := -s) (n := p) one_ne_zero)
  have hfaa := iteratedDeriv_comp_eq_sum_orderedFinpartition (i := p) houter hinner (by simp)
  have hlocal : (outer ∘ inner) =ᶠ[𝓝 1] id := by
    simpa [outer, inner] using forward_comp_inverse_eventuallyEq_id hs.ne'
  have hlhs : iteratedDeriv p (outer ∘ inner) 1 = if p = 1 then 1 else 0 := by
    rw [Filter.EventuallyEq.iteratedDeriv_eq p hlocal]
    simp [iteratedDeriv_id, hp.ne']
  rw [normalizedRecurrenceAt]
  calc
    (∑ c : OrderedFinpartition p, partitionTerm (forwardCoeff s) (inverseCoeff s) c) =
        iteratedDeriv p (outer ∘ inner) 1 := by
      rw [hfaa]
      simp [partitionTerm, outer, inner, forwardCoeff, inverseCoeff]
    _ = if p = 1 then 1 else 0 := hlhs

end InverseJet

end LeanProofs.IntegerPoints
