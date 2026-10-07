/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.PhysicalBoundaryLabels
import OAI.Combinatorics.Progressions.Estimates.RealFiniteZeroExtension
import OAI.Combinatorics.Progressions.Estimates.WeightedSmoothSampledError
import OAI.Combinatorics.Progressions.Probability.LargeDivisorPairProbability
import OAI.Combinatorics.Progressions.Probability.RelativeFullSliceLaw

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem interval_event_probability (a b : ℤ) (hab : a < b) (E : ℤ → Prop)
    [DecidablePred E] :
    (intervalUniformWeights a b hab).eventProbability (fun x => E (x : ℤ)) =
      ((Finset.filter E (Finset.Ico a b)).card : ℝ) / ((b - a : ℤ) : ℝ) := by
  unfold FiniteProbabilityWeights.eventProbability
  rw [intervalUniformWeights_mean]
  convert integerInterval_indicator_expect a b hab.le E using 1
  congr 1
  funext x
  split_ifs <;> rfl

theorem interval_near_probability (a b v : ℤ) (hab : a < b) (r : ℕ) :
    (intervalUniformWeights a b hab).eventProbability (fun x => |(x : ℤ) - v| ≤ (r : ℤ)) ≤
      (2 * (r : ℝ) + 1) / ((b - a : ℤ) : ℝ) := by
  rw [interval_event_probability a b hab (fun x => |x - v| ≤ (r : ℤ))]
  have hsub : (Finset.filter (fun x => |x - v| ≤ (r : ℤ)) (Finset.Ico a b)) ⊆
      Finset.Icc (v - (r : ℤ)) (v + (r : ℤ)) := by
    intro x hx
    have h := abs_le.mp (Finset.mem_filter.mp hx).2
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have he : (Finset.Icc (v - (r : ℤ)) (v + (r : ℤ))).card = 2 * r + 1 := by
    rw [Int.card_Icc]
    omega
  have hc : ((Finset.filter (fun x => |x - v| ≤ (r : ℤ)) (Finset.Ico a b)).card : ℝ) ≤
      2 * (r : ℝ) + 1 := by
    have h := Finset.card_le_card hsub
    rw [he] at h
    exact_mod_cast h
  exact div_le_div_of_nonneg_right hc (by exact_mod_cast (sub_pos.mpr hab).le)

theorem integer_box_near_probability {J : Type*} [Fintype J] [DecidableEq J]
    (lo hi : J → ℤ) (hlen : ∀ j, lo j < hi j) (v : J → ℤ) (r : ℕ) :
    (integerBoxUniformWeights lo hi hlen).eventProbability
        (fun y => ∀ j, |(y j : ℤ) - v j| ≤ (r : ℤ)) ≤
      ∏ j, (2 * (r : ℝ) + 1) / ((hi j - lo j : ℤ) : ℝ) := by
  rw [integerBoxUniformWeights, FiniteProbabilityWeights.eventProbability_pi
    (fun j => intervalUniformWeights (lo j) (hi j) (hlen j))
    (fun j (y : Finset.Ico (lo j) (hi j)) => |(y : ℤ) - v j| ≤ (r : ℤ))]
  apply Finset.prod_le_prod₀
  · intro j _
    exact FiniteProbabilityWeights.eventProbability_nonneg _ _
  · intro j _
    exact interval_near_probability (lo j) (hi j) (v j) (hlen j) r

theorem integer_box_pair_near_probability {J : Type*} [Fintype J] [DecidableEq J]
    (lo hi : J → ℤ) (hlen : ∀ j, lo j < hi j) (r : ℕ) :
    ((integerBoxUniformWeights lo hi hlen).prod (integerBoxUniformWeights lo hi hlen)).eventProbability
        (fun xy => ∀ j, |(xy.2 j : ℤ) - (xy.1 j : ℤ)| ≤ (r : ℤ)) ≤
      ∏ j, (2 * (r : ℝ) + 1) / ((hi j - lo j : ℤ) : ℝ) := by
  unfold FiniteProbabilityWeights.eventProbability
  rw [FiniteProbabilityWeights.mean_prod]
  apply (FiniteProbabilityWeights.mean_mono _ ?_).trans_eq (FiniteProbabilityWeights.mean_const _ _)
  intro x
  exact integer_box_near_probability lo hi hlen (fun j => (x j : ℤ)) r

theorem integer_box_pair_near_probability_of_lengths {J : Type*}
    [Fintype J] [DecidableEq J] (lo hi : J → ℤ) (hlen : ∀ j, lo j < hi j)
    (r : ℕ) {L : ℝ} (hL : 0 < L) (hside : ∀ j, L ≤ ((hi j - lo j : ℤ) : ℝ)) :
    ((integerBoxUniformWeights lo hi hlen).prod (integerBoxUniformWeights lo hi hlen)).eventProbability
        (fun xy => ∀ j, |(xy.2 j : ℤ) - (xy.1 j : ℤ)| ≤ (r : ℤ)) ≤
      ((2 * (r : ℝ) + 1) / L) ^ Fintype.card J := by
  apply (integer_box_pair_near_probability lo hi hlen r).trans
  calc
    _ ≤ ∏ _j : J, (2 * (r : ℝ) + 1) / L := by
      apply Finset.prod_le_prod₀
      · intro j _
        have hj : (0 : ℝ) < ((hi j - lo j : ℤ) : ℝ) := hL.trans_le (hside j)
        positivity
      · intro j _
        exact div_le_div_of_nonneg_left (by positivity) hL (hside j)
    _ = _ := by simp [div_pow]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem integer_vector_content_natAbs_scale {J : Type*} [Fintype J]
    (D : ℕ) (z : J → ℤ) :
    (BohrLattice.Primitive.content (fun j => (D : ℤ) * z j)).natAbs =
      D * (BohrLattice.Primitive.content z).natAbs := by
  simp only [BohrLattice.Primitive.content, Finset.gcd_mul_left, Int.normalize_coe_nat,
    Int.natAbs_mul, Int.natAbs_natCast]

theorem affine_parameter_difference_gcd {J : Type*} [Fintype J]
    (D : ℕ) (a x y : J → ℤ) :
    (BohrLattice.Primitive.content (fun j => (a j + (D : ℤ) * y j) -
      (a j + (D : ℤ) * x j))).natAbs =
      D * (BohrLattice.Primitive.content (fun j => y j - x j)).natAbs := by
  have he : (fun j => (a j + (D : ℤ) * y j) - (a j + (D : ℤ) * x j)) =
      (fun j => (D : ℤ) * (y j - x j)) := by funext j; ring
  rw [he, integer_vector_content_natAbs_scale]

theorem integer_box_pair_gcd_probability {J : Type*}
    [Fintype J] [DecidableEq J] (lo hi : J → ℤ) (hlen : ∀ j, lo j < hi j)
    (B R : ℕ) (hB : 0 < B) (hdim : 2 ≤ Fintype.card J)
    {L : ℝ} (hL : 0 < L) (hside : ∀ j, L ≤ ((hi j - lo j : ℤ) : ℝ))
    (hwidth : ∀ j, hi j - lo j ≤ (R : ℤ)) :
    ((integerBoxUniformWeights lo hi hlen).prod (integerBoxUniformWeights lo hi hlen)).eventProbability
        (fun xy => B < (BohrLattice.Primitive.content
          (fun j => (xy.2 j : ℤ) - (xy.1 j : ℤ))).natAbs) ≤
      2 ^ (Fintype.card J - 1) *
        (1 / (B : ℝ) ^ (Fintype.card J - 1) + (R : ℝ) / L ^ Fintype.card J) := by
  apply (FiniteProbabilityWeights.eventProbability_mono _ _ _ ?_).trans
    (integer_box_pair_nonzero_large_divisor_probability lo hi hlen B R hB hdim hL hside hwidth)
  intro xy h
  refine ⟨?_, (BohrLattice.Primitive.content (fun j => (xy.2 j : ℤ) - (xy.1 j : ℤ))).natAbs, h, ?_⟩
  · intro he
    have hz : Finset.univ.gcd (fun _ : J => (0 : ℤ)) = 0 :=
      Finset.gcd_eq_zero_iff.mpr (fun _ _ => rfl)
    simp [he, BohrLattice.Primitive.content, hz] at h
  · intro j
    exact Int.natAbs_dvd.mpr (BohrLattice.Primitive.content_dvd _ j)

theorem affine_parameter_pair_gcd_probability {J : Type*}
    [Fintype J] [DecidableEq J] (lo hi : J → ℤ) (hlen : ∀ j, lo j < hi j)
    (D Q B R : ℕ) (a : J → ℤ) (hBQ : D * B ≤ Q) (hB : 0 < B)
    (hdim : 2 ≤ Fintype.card J) {L : ℝ} (hL : 0 < L)
    (hside : ∀ j, L ≤ ((hi j - lo j : ℤ) : ℝ))
    (hwidth : ∀ j, hi j - lo j ≤ (R : ℤ)) :
    ((integerBoxUniformWeights lo hi hlen).prod (integerBoxUniformWeights lo hi hlen)).eventProbability
        (fun xy => Q < (BohrLattice.Primitive.content
          (fun j => (a j + (D : ℤ) * (xy.2 j : ℤ)) -
            (a j + (D : ℤ) * (xy.1 j : ℤ)))).natAbs) ≤
      2 ^ (Fintype.card J - 1) *
        (1 / (B : ℝ) ^ (Fintype.card J - 1) + (R : ℝ) / L ^ Fintype.card J) := by
  apply (FiniteProbabilityWeights.eventProbability_mono _ _ _ ?_).trans
    (integer_box_pair_gcd_probability lo hi hlen B R hB hdim hL hside hwidth)
  intro xy h
  rw [affine_parameter_difference_gcd] at h
  exact Nat.lt_of_mul_lt_mul_left (hBQ.trans_lt h)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem integerBoxUniformWeights_mean {J : Type*} [Fintype J] [DecidableEq J]
    (lo hi : J → ℤ) (hlen : ∀ j, lo j < hi j)
    (f : (∀ j, Finset.Ico (lo j) (hi j)) → ℝ) :
    (integerBoxUniformWeights lo hi hlen).mean f = 𝔼 x, f x := by
  let : ∀ j, Nonempty (Finset.Ico (lo j) (hi j)) :=
    fun j => ⟨⟨lo j, Finset.mem_Ico.mpr ⟨le_rfl, hlen j⟩⟩⟩
  have he : integerBoxUniformWeights lo hi hlen =
      FiniteProbabilityWeights.uniform (∀ j, Finset.Ico (lo j) (hi j)) := by
    apply FiniteProbabilityWeights.eq_of_weight_eq
    intro x
    change (∏ j, (Fintype.card (Finset.Ico (lo j) (hi j)) : ℝ)⁻¹) =
      (Fintype.card (∀ j, Finset.Ico (lo j) (hi j)) : ℝ)⁻¹
    rw [Fintype.card_pi, Nat.cast_prod, Finset.prod_inv_distrib]
  rw [he, FiniteProbabilityWeights.uniform_mean]

theorem finite_event_probability_or_le {X : Type*} [Fintype X]
    (p : FiniteProbabilityWeights X) (A B : X → Prop) :
    p.eventProbability (fun x => A x ∨ B x) ≤ p.eventProbability A + p.eventProbability B := by
  have hpoint (x : X) : (@ite ℝ (A x ∨ B x) (Classical.propDecidable _) 1 0) ≤
      (@ite ℝ (A x) (Classical.propDecidable _) 1 0) +
      (@ite ℝ (B x) (Classical.propDecidable _) 1 0) := by
    by_cases ha : A x <;> by_cases hb : B x <;> simp [ha, hb]
  exact (p.mean_mono hpoint).trans_eq (p.mean_add _ _)

def affineParameterBadPair {J : Type*} [Fintype J]
    (D Q r : ℕ) (a x y : J → ℤ) : Prop :=
  Q < (BohrLattice.Primitive.content
    (fun j => (a j + (D : ℤ) * y j) - (a j + (D : ℤ) * x j))).natAbs ∨
    ∀ j, |y j - x j| ≤ (r : ℤ)

noncomputable def integerBoxBadPairBudget (d B R r : ℕ) (L : ℝ) : ℝ :=
  2 ^ (d - 1) * (1 / (B : ℝ) ^ (d - 1) + (R : ℝ) / L ^ d) +
    ((2 * (r : ℝ) + 1) / L) ^ d

theorem affine_parameter_bad_pair_probability {J : Type*}
    [Fintype J] [DecidableEq J] (lo hi : J → ℤ) (hlen : ∀ j, lo j < hi j)
    (D Q B R r : ℕ) (a : J → ℤ) (hBQ : D * B ≤ Q) (hB : 0 < B)
    (hdim : 2 ≤ Fintype.card J) {L : ℝ} (hL : 0 < L)
    (hside : ∀ j, L ≤ ((hi j - lo j : ℤ) : ℝ))
    (hwidth : ∀ j, hi j - lo j ≤ (R : ℤ)) :
    ((integerBoxUniformWeights lo hi hlen).prod (integerBoxUniformWeights lo hi hlen)).eventProbability
      (fun xy => affineParameterBadPair D Q r a
        (fun j => (xy.1 j : ℤ)) (fun j => (xy.2 j : ℤ))) ≤
      integerBoxBadPairBudget (Fintype.card J) B R r L := by
  unfold affineParameterBadPair integerBoxBadPairBudget
  apply (finite_event_probability_or_le _ _ _).trans
  exact add_le_add
    (affine_parameter_pair_gcd_probability lo hi hlen D Q B R a hBQ hB hdim hL hside hwidth)
    (integer_box_pair_near_probability_of_lengths lo hi hlen r hL hside)

theorem sampled_affine_integer_box_error {Ω J : Type*}
    [Fintype Ω] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights Ω) (lo hi : J → ℤ) (hlen : ∀ j, lo j < hi j)
    (D Q B R r : ℕ) (a : J → ℤ) (hBQ : D * B ≤ Q) (hB : 0 < B)
    (hdim : 2 ≤ Fintype.card J) {L : ℝ} (hL : 0 < L)
    (hside : ∀ j, L ≤ ((hi j - lo j : ℤ) : ℝ))
    (hwidth : ∀ j, hi j - lo j ≤ (R : ℤ))
    (e : Ω → (∀ j, Finset.Ico (lo j) (hi j)) → ℝ)
    {C epsilon : ℝ} (hC : 0 ≤ C) (hepsilon : 0 ≤ epsilon)
    (henergy : ∀ t, p.mean (fun x => e x t ^ 2) ≤ C)
    (hgood : ∀ (t u : ∀ j, Finset.Ico (lo j) (hi j)), ¬ affineParameterBadPair D Q r a (fun j => (t j : ℤ)) (fun j => (u j : ℤ)) →
      |p.mean (fun x => e x t * e x u)| ≤ epsilon)
    (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x ∧ w x ≤ 1) :
    |p.mean (fun x => w x * (𝔼 t, e x t))| ≤
      Real.sqrt (C * integerBoxBadPairBudget (Fintype.card J) B R r L + epsilon) := by
  have h := sampled_weighted_error_of_energy p (integerBoxUniformWeights lo hi hlen) e
    (fun tu => affineParameterBadPair D Q r a (fun j => (tu.1 j : ℤ)) (fun j => (tu.2 j : ℤ)))
    hC hepsilon henergy
    (affine_parameter_bad_pair_probability lo hi hlen D Q B R r a hBQ hB hdim hL hside hwidth)
    (fun tu htu => hgood tu.1 tu.2 htu) w hw
  simpa only [integerBoxUniformWeights_mean] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem expect_le_of_dependent_coordinate_slices {I : Type*} [Fintype I] [DecidableEq I]
    {X : I → Type*} [∀ i, Fintype (X i)] [∀ i, Nonempty (X i)]
    (i : I) (f : (∀ j, X j) → ℝ) (C : ℝ)
    (hslice : ∀ x : ∀ j, X j, (𝔼 a : X i, f (Function.update x i a)) ≤ C) :
    (𝔼 x : ∀ j, X j, f x) ≤ C := by
  let e := Equiv.piSplitAt i X
  have he := Fintype.expect_equiv e f (fun p => f (e.symm p)) (fun x => by simp)
  rw [he, ← Finset.univ_product_univ, Finset.expect_product, Finset.expect_comm]
  apply Finset.expect_le Finset.univ_nonempty
  intro r _
  let x : ∀ j, X j := e.symm (Classical.choice inferInstance, r)
  have hupdate (a : X i) : e.symm (a, r) = Function.update x i a := by
    funext j
    by_cases hj : j = i
    · subst j
      simp [e, Equiv.piSplitAt]
    · simp [e, x, Equiv.piSplitAt, hj]
  simpa only [hupdate] using hslice x

theorem integer_box_affine_near_probability {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (lo hi : Option J × I → ℤ) (hlen : ∀ j, lo j < hi j)
    (t : J → ℤ) (i : I) (b : ℤ) (r : ℕ) :
    (integerBoxUniformWeights lo hi hlen).eventProbability
      (fun z => |smoothAffineSample t (fun j => (z j : ℤ)) i - b| ≤ (r : ℤ)) ≤
      (2 * (r : ℝ) + 1) / ((hi (none, i) - lo (none, i) : ℤ) : ℝ) := by
  let : ∀ j, Nonempty (Finset.Ico (lo j) (hi j)) :=
    fun j => ⟨⟨lo j, Finset.mem_Ico.mpr ⟨le_rfl, hlen j⟩⟩⟩
  unfold FiniteProbabilityWeights.eventProbability
  rw [integerBoxUniformWeights_mean]
  apply expect_le_of_dependent_coordinate_slices (none, i)
  intro z
  have h := interval_near_probability (lo (none, i)) (hi (none, i))
    (b - ∑ j, t j * (z (some j, i) : ℤ)) (hlen (none, i)) r
  unfold FiniteProbabilityWeights.eventProbability at h
  rw [intervalUniformWeights_mean] at h
  convert h using 1
  apply Finset.expect_congr rfl
  intro a _
  have he : smoothAffineSample t (fun j => ((Function.update z (none, i) a) j : ℤ)) i - b =
      (a : ℤ) - (b - ∑ j, t j * (z (some j, i) : ℤ)) := by
    simp [smoothAffineSample, Function.update]
    ring
  dsimp only
  simp only [he]
  split_ifs <;> rfl

end Erdos3

end

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators Classical

variable {X : Type*} [Fintype X] [DecidableEq X] {N : X → ℕ} {q : ℕ}

theorem fullSliceLaw_mean_eq_rectangle (S : ResidueBoxSlice N q)
    (hlen : ∀ i, 0 < S.length i) (f : (X → ℤ) → ℝ) :
    (S.fullSliceLaw hlen).mean (fun x => f x.val) =
      (integerBoxUniformWeights (fun _ : X => 0) (fun i => (S.length i : ℤ))
        (fun i => by exact_mod_cast hlen i)).mean
        (fun t => f (fun i => (S.start i : ℤ) + (q : ℤ) * (t i).val)) := by
  rw [fullSliceLaw_mean, integerBoxUniformWeights_mean]
  let forward (u : ∀ i, Fin (S.length i)) :
      ∀ i, Finset.Ico (0 : ℤ) (S.length i : ℤ) := fun i =>
    ⟨((u i).val : ℤ), Finset.mem_Ico.mpr ⟨Int.natCast_nonneg _, by exact_mod_cast (u i).isLt⟩⟩
  apply Finset.expect_bij (fun u _ => forward u)
  · intro u _
    exact Finset.mem_univ _
  · intro u _
    simp only [forward, fullSlicePointInIntegerBox, point, Nat.cast_add, Nat.cast_mul]
  · intro u _ v _ he
    funext i
    apply Fin.ext
    have hi := congrArg (fun t => (t i).val) he
    dsimp only [forward] at hi
    exact_mod_cast hi
  · intro t _
    let u : ∀ i, Fin (S.length i) := fun i =>
      ⟨(t i).val.toNat, by have := Finset.mem_Ico.mp (t i).property; omega⟩
    refine ⟨u, Finset.mem_univ _, ?_⟩
    funext i
    apply Subtype.ext
    change (((t i).val.toNat : ℕ) : ℤ) = (t i).val
    exact Int.toNat_of_nonneg (Finset.mem_Ico.mp (t i).property).1

omit [Fintype X] [DecidableEq X] in
theorem fullSliceRectangle_endpoint_bounds (S : ResidueBoxSlice N q)
    (hlen : ∀ i, 0 < S.length i) {L C : ℝ} (hL : 0 < L)
    (hN : ∀ i, (N i : ℝ) ≤ C * L) (i : X) :
    |(S.start i : ℝ) / L| ≤ C ∧
      |((S.start i : ℝ) + (q : ℝ) * S.length i) / L| ≤ C + q / L := by
  have hstart : S.start i < N i := by simpa using S.inside i 0 (hlen i)
  have hlast := S.inside i (S.length i - 1) (by have := hlen i; omega)
  have hend : S.start i + q * S.length i < N i + q := by
    have he : S.start i + q * S.length i =
        (S.start i + q * (S.length i - 1)) + q := by
      have hl : S.length i = (S.length i - 1) + 1 := by have := hlen i; omega
      conv_lhs => rw [hl]
      ring
    rw [he]
    omega
  have hstartR : (S.start i : ℝ) < N i := by exact_mod_cast hstart
  have hendR : (S.start i : ℝ) + (q : ℝ) * S.length i < (N i : ℝ) + q := by
    exact_mod_cast hend
  constructor
  · rw [abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hL.le)]
    exact (div_le_iff₀ hL).mpr (hstartR.le.trans (hN i))
  · rw [abs_of_nonneg (by positivity)]
    apply (div_le_iff₀ hL).mpr
    rw [add_mul, div_mul_cancel₀ _ hL.ne']
    linarith [hN i]

omit [Fintype X] [DecidableEq X] in
theorem fullSliceRectangle_endpoint_bounds_two (S : ResidueBoxSlice N q)
    (hlen : ∀ i, 2 ≤ S.length i) {L C : ℝ} (hL : 0 < L)
    (hN : ∀ i, (N i : ℝ) ≤ C * L) (i : X) :
    |(S.start i : ℝ) / L| ≤ C ∧
      |((S.start i : ℝ) + (q : ℝ) * S.length i) / L| ≤ 2 * C := by
  have hbase := fullSliceRectangle_endpoint_bounds S (fun i => by have := hlen i; omega) hL hN i
  have hqN : q < N i := by
    have h := S.inside i 1 (by have := hlen i; omega)
    omega
  have hqR : (q : ℝ) ≤ C * L :=
    (show (q : ℝ) ≤ (N i : ℝ) by exact_mod_cast hqN.le).trans (hN i)
  have hqL : (q : ℝ) / L ≤ C := (div_le_iff₀ hL).mpr hqR
  exact ⟨hbase.1, hbase.2.trans (by linarith)⟩

end Erdos3.ResidueBoxSlice

end

section

namespace Erdos3

theorem integerBoxBadPairBudget_nonneg (d B R r : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    0 ≤ integerBoxBadPairBudget d B R r M := by
  unfold integerBoxBadPairBudget
  positivity

theorem integerBoxBadPairBudget_le_separated (d B R r : ℕ) {M C nu : ℝ}
    (hd : 2 ≤ d) (hB : 0 < B) (hBM : (B : ℝ) ≤ M) (hC : 0 ≤ C)
    (hR : (R : ℝ) ≤ C * M) (hr : (r : ℝ) ≤ nu * M)
    (hinv : 1 / M ≤ nu) :
    integerBoxBadPairBudget d B R r M ≤
      2 ^ (d - 1) * (1 + C) / (B : ℝ) ^ (d - 1) + (3 * nu) ^ d := by
  have hBp : (0 : ℝ) < B := by exact_mod_cast hB
  have hM : 0 < M := hBp.trans_le hBM
  have hpow : (B : ℝ) ^ (d - 1) ≤ M ^ (d - 1) :=
    pow_le_pow_left₀ hBp.le hBM _
  have hR' : (R : ℝ) / M ^ d ≤ C / (B : ℝ) ^ (d - 1) := by
    calc
      _ ≤ (C * M) / M ^ d := div_le_div_of_nonneg_right hR (by positivity)
      _ = C / M ^ (d - 1) := by
        conv_lhs => rw [show d = (d - 1) + 1 by omega, pow_succ]
        field_simp
      _ ≤ C / (B : ℝ) ^ (d - 1) := div_le_div_of_nonneg_left hC (by positivity) hpow
  have hnear : (2 * (r : ℝ) + 1) / M ≤ 3 * nu := by
    have hrr : (r : ℝ) / M ≤ nu := (div_le_iff₀ hM).mpr hr
    calc
      _ = 2 * ((r : ℝ) / M) + 1 / M := by ring
      _ ≤ 3 * nu := by linarith
  unfold integerBoxBadPairBudget
  calc
    _ ≤ 2 ^ (d - 1) * (1 / (B : ℝ) ^ (d - 1) + C / (B : ℝ) ^ (d - 1)) +
        (3 * nu) ^ d := add_le_add
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl hR') (by positivity))
      (pow_le_pow_left₀ (by positivity) hnear d)
    _ = _ := by ring

theorem integerBoxBadPairBudget_le_linear (d B R r : ℕ) {M C nu : ℝ}
    (hd : 2 ≤ d) (hB : 0 < B) (hBM : (B : ℝ) ≤ M) (hC : 0 ≤ C)
    (hR : (R : ℝ) ≤ C * M) (hr : (r : ℝ) ≤ nu * M)
    (hinv : 1 / M ≤ nu) (hnu : nu ≤ 1) :
    integerBoxBadPairBudget d B R r M ≤
      2 ^ (d - 1) * (1 + C) / (B : ℝ) + 3 ^ d * nu := by
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hBp : (0 : ℝ) < B := by exact_mod_cast hB
  have hM : 0 < M := hBp.trans_le hBM
  have hnu0 : 0 ≤ nu := (by positivity : 0 ≤ 1 / M).trans hinv
  have hpow : (B : ℝ) ≤ (B : ℝ) ^ (d - 1) := by
    simpa only [pow_one] using pow_le_pow_right₀ hB1 (show 1 ≤ d - 1 by omega)
  have hnpow : nu ^ d ≤ nu := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show d ≠ 0 by omega)
    rw [pow_succ]
    exact (mul_le_mul_of_nonneg_right (pow_le_one₀ hnu0 hnu) hnu0).trans_eq (one_mul nu)
  apply (integerBoxBadPairBudget_le_separated d B R r hd hB hBM hC hR hr hinv).trans
  apply add_le_add
  · exact div_le_div_of_nonneg_left (by positivity) hBp hpow
  · rw [mul_pow]
    exact mul_le_mul_of_nonneg_left hnpow (by positivity)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem integerBox_weighted_joint_mean
    {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (lo hi : I → ℤ) (hsource : ∀ i, lo i < hi i)
    (parLo parHi : J → ℤ) (hparam : ∀ j, parLo j < parHi j)
    (w : (I → ℤ) → ℝ) (f : (I → ℤ) → (∀ j, Finset.Ico (parLo j) (parHi j)) → ℝ) :
    ((integerBoxUniformWeights parLo parHi hparam).prod
      (integerBoxUniformWeights lo hi hsource)).mean
        (fun tx => w (fun i => (tx.2 i).val) * f (fun i => (tx.2 i).val) tx.1) =
      𝔼 z ∈ Fintype.piFinset (fun i => Finset.Ico (lo i) (hi i)), w z * (𝔼 t, f z t) := by
  rw [FiniteProbabilityWeights.mean_prod, FiniteProbabilityWeights.mean_comm]
  simp only [FiniteProbabilityWeights.mean_const_mul, integerBoxUniformWeights_mean]
  rw [← finiteBoxPoints_expect (fun i => Finset.Ico (lo i) (hi i)) (fun z => w z * (𝔼 t, f z t))]
  simp only [Finset.expect_eq_sum_div_card, Finset.card_univ, Fintype.card_coe]
  congr 1
  simpa only [Finset.expect_eq_sum_div_card, Finset.card_univ] using
    Finset.sum_coe_sort (Fintype.piFinset (fun i => Finset.Ico (lo i) (hi i)))
      (fun z => w z * (𝔼 t, f z t))

theorem integerBox_joint_error_of_window_tests
    {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (lo hi : I → ℤ) (hsource : ∀ i, lo i < hi i)
    (parLo parHi : J → ℤ) (hparam : ∀ j, parLo j < parHi j)
    (f : (I → ℤ) → (∀ j, Finset.Ico (parLo j) (parHi j)) → ℝ) (accuracy : ℝ)
    (htest : ∀ v : (I → ℤ) → ℝ, (∀ z, 0 ≤ v z ∧ v z ≤ 1) →
      |𝔼 z ∈ Fintype.piFinset (fun i => Finset.Ico (lo i) (hi i)), v z * (𝔼 t, f z t)| ≤ accuracy)
    (w : (I → ℤ) → ℝ)
    (hw : ∀ z : (∀ i, Finset.Ico (lo i) (hi i)),
      0 ≤ w (fun i => (z i).val) ∧ w (fun i => (z i).val) ≤ 1) :
    |((integerBoxUniformWeights parLo parHi hparam).prod
      (integerBoxUniformWeights lo hi hsource)).mean
        (fun tx => w (fun i => (tx.2 i).val) * f (fun i => (tx.2 i).val) tx.1)| ≤ accuracy := by
  let W := Fintype.piFinset (fun i => Finset.Ico (lo i) (hi i))
  have hwW (z) (hz : z ∈ W) : 0 ≤ w z ∧ w z ≤ 1 := by
    exact hw (fun i => ⟨z i, Fintype.mem_piFinset.mp hz i⟩)
  have h := htest (realZeroExtendFinset W w) (realZeroExtendFinset_unit W w hwW)
  rw [integerBox_weighted_joint_mean lo hi hsource parLo parHi hparam w f]
  convert h using 2
  apply Finset.expect_congr rfl
  intro z hz
  rw [realZeroExtendFinset_on W w hz]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def physicalBoundaryBudget {I : Type*} [Fintype I]
    (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i)) (r : I → ℕ) (width : I → ℝ) : ℝ :=
  ∑ i, 2 * (Fintype.card (P i).Label : ℝ) * (2 * (r i : ℝ) + 1) / width i

theorem integer_box_physical_boundary_probability {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (sourceLo sourceHi : Option J × I → ℤ) (hsource : ∀ j, sourceLo j < sourceHi j)
    (t : J → ℤ) (lo : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (r : I → ℕ) :
    (integerBoxUniformWeights sourceLo sourceHi hsource).eventProbability
      (fun z => physicalBoundaryNear lo N P r (smoothAffineSample t (fun j => (z j : ℤ)))) ≤
      physicalBoundaryBudget N P r (fun i => ((sourceHi (none, i) - sourceLo (none, i) : ℤ) : ℝ)) := by
  let p := integerBoxUniformWeights sourceLo sourceHi hsource
  let E := fun (e : Σ i, (P i).Label) (z : ∀ j, Finset.Ico (sourceLo j) (sourceHi j)) =>
    |smoothAffineSample t (fun j => (z j : ℤ)) e.1 - intervalCellLower (lo e.1) (P e.1) e.2| ≤ (r e.1 : ℤ) ∨
    |smoothAffineSample t (fun j => (z j : ℤ)) e.1 - intervalCellUpper (lo e.1) (P e.1) e.2| ≤ (r e.1 : ℤ)
  have hE (e : Σ i, (P i).Label) : p.eventProbability (E e) ≤
      2 * ((2 * (r e.1 : ℝ) + 1) / ((sourceHi (none, e.1) - sourceLo (none, e.1) : ℤ) : ℝ)) := by
    apply (p.eventProbability_or_le _ _).trans
    have hleft := integer_box_affine_near_probability sourceLo sourceHi hsource t e.1
      (intervalCellLower (lo e.1) (P e.1) e.2) (r e.1)
    have hright := integer_box_affine_near_probability sourceLo sourceHi hsource t e.1
      (intervalCellUpper (lo e.1) (P e.1) e.2) (r e.1)
    linarith
  have hcover (z : ∀ j, Finset.Ico (sourceLo j) (sourceHi j))
      (h : physicalBoundaryNear lo N P r (smoothAffineSample t (fun j => (z j : ℤ)))) : ∃ e, E e z := by
    obtain ⟨i, c, hc⟩ := h
    exact ⟨⟨i, c⟩, hc⟩
  apply (p.eventProbability_union_bound _ E hcover).trans
  calc
    _ ≤ ∑ e : Σ i, (P i).Label,
        2 * ((2 * (r e.1 : ℝ) + 1) / ((sourceHi (none, e.1) - sourceLo (none, e.1) : ℤ) : ℝ)) :=
      Finset.sum_le_sum (fun e _ => hE e)
    _ = _ := by
      rw [Fintype.sum_sigma]
      unfold physicalBoundaryBudget
      apply Finset.sum_congr rfl
      intro i _
      dsimp only
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

theorem sampled_physical_boundary_probability {J I T : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I] [Fintype T]
    (parameterLaw : FiniteProbabilityWeights T) (parameter : T → J → ℤ)
    (sourceLo sourceHi : Option J × I → ℤ) (hsource : ∀ j, sourceLo j < sourceHi j)
    (lo : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i)) (r : I → ℕ) :
    (parameterLaw.prod (integerBoxUniformWeights sourceLo sourceHi hsource)).eventProbability
      (fun tz => physicalBoundaryNear lo N P r (smoothAffineSample (parameter tz.1) (fun j => (tz.2 j : ℤ)))) ≤
      physicalBoundaryBudget N P r (fun i => ((sourceHi (none, i) - sourceLo (none, i) : ℤ) : ℝ)) := by
  unfold FiniteProbabilityWeights.eventProbability
  rw [FiniteProbabilityWeights.mean_prod]
  apply (parameterLaw.mean_mono (fun t =>
    integer_box_physical_boundary_probability sourceLo sourceHi hsource (parameter t) lo N P r)).trans_eq
  exact parameterLaw.mean_const _

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def physicalMeshCrossing {I X M : Type*} [Fintype I] [DecidableEq I]
    (lo : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (mesh : X → M) (location : X → I → ℤ) (x : X) : Prop :=
  ∃ y, mesh y = mesh x ∧ physicalBoxClassify lo N P (location x) ≠ physicalBoxClassify lo N P (location y)

theorem retained_mesh_cell_constant {I X M : Type*} [Fintype I] [DecidableEq I]
    (lo : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (mesh : X → M) (location : X → I → ℤ) (x : X)
    (hx : ¬ physicalMeshCrossing lo N P mesh location x) :
    ∀ y, mesh y = mesh x → physicalBoxClassify lo N P (location y) = physicalBoxClassify lo N P (location x) := by
  intro y hy
  by_contra h
  exact hx ⟨y, hy, Ne.symm h⟩

theorem physicalMeshCrossing_congr {I X M : Type*} [Fintype I] [DecidableEq I]
    (lo : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (mesh : X → M) (location : X → I → ℤ) {x y : X} (hxy : mesh x = mesh y) :
    physicalMeshCrossing lo N P mesh location x ↔ physicalMeshCrossing lo N P mesh location y := by
  have transfer (u v : X) (huv : mesh u = mesh v)
      (hu : physicalMeshCrossing lo N P mesh location u) : physicalMeshCrossing lo N P mesh location v := by
    obtain ⟨z, hz, huz⟩ := hu
    by_cases hvz : physicalBoxClassify lo N P (location v) = physicalBoxClassify lo N P (location z)
    · exact ⟨u, huv, fun hvu => huz (hvu.symm.trans hvz)⟩
    · exact ⟨z, hz.trans huv, hvz⟩
  exact ⟨transfer x y hxy, transfer y x hxy.symm⟩

theorem physicalMeshCrossing_subset_boundary {I X M : Type*} [Fintype I] [DecidableEq I]
    (lo : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (hstep : ∀ i c, (P i).step c = 1) (hpos : ∀ i c, 0 < (P i).length c)
    (mesh : X → M) (location : X → I → ℤ) (r : I → ℕ)
    (hmove : ∀ x y, mesh y = mesh x → ∀ i, |location x i - location y i| ≤ (r i : ℤ))
    (x : X) (hx : physicalMeshCrossing lo N P mesh location x) :
    physicalBoundaryNear lo N P r (location x) := by
  by_contra hn
  obtain ⟨y, hy, hxy⟩ := hx
  exact hxy (physicalBoxClassify_stable lo N P hstep hpos r (location x) (location y) (hmove x y hy) hn)

theorem affine_mesh_crossing_probability {J I T SCell TCell : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I] [Fintype T]
    (parameterLaw : FiniteProbabilityWeights T) (parameter : T → J → ℤ)
    (sourceLo sourceHi : Option J × I → ℤ) (hsource : ∀ j, sourceLo j < sourceHi j)
    (sourceCell : (∀ j, Finset.Ico (sourceLo j) (sourceHi j)) → SCell) (parameterCell : T → TCell)
    (lo : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (hstep : ∀ i c, (P i).step c = 1) (hpos : ∀ i c, 0 < (P i).length c)
    (r : I → ℕ) (r0 rV V : I → ℝ) (Tcap rt : ℝ) (hT : 0 ≤ Tcap) (hV : ∀ i, 0 ≤ V i)
    (ht : ∀ t j, |(parameter t j : ℝ)| ≤ Tcap)
    (hv : ∀ (z : ∀ j, Finset.Ico (sourceLo j) (sourceHi j)) j i, |((z (some j, i) : ℤ) : ℝ)| ≤ V i)
    (hbase : ∀ z w, sourceCell w = sourceCell z → ∀ i,
      |((z (none, i) : ℤ) : ℝ) - ((w (none, i) : ℤ) : ℝ)| ≤ r0 i)
    (hdir : ∀ z w, sourceCell w = sourceCell z → ∀ j i,
      |((z (some j, i) : ℤ) : ℝ) - ((w (some j, i) : ℤ) : ℝ)| ≤ rV i)
    (hparam : ∀ t u, parameterCell u = parameterCell t → ∀ j,
      |(parameter t j : ℝ) - parameter u j| ≤ rt)
    (hbudget : ∀ i, r0 i + (Fintype.card J : ℝ) * (Tcap * rV i + V i * rt) ≤ (r i : ℝ)) :
    (parameterLaw.prod (integerBoxUniformWeights sourceLo sourceHi hsource)).eventProbability
      (physicalMeshCrossing lo N P
        (fun tz => (sourceCell tz.2, parameterCell tz.1))
        (fun tz => smoothAffineSample (parameter tz.1) (fun j => (tz.2 j : ℤ)))) ≤
      physicalBoundaryBudget N P r (fun i => ((sourceHi (none, i) - sourceLo (none, i) : ℤ) : ℝ)) := by
  let mesh := fun tz : T × (∀ j, Finset.Ico (sourceLo j) (sourceHi j)) =>
    (sourceCell tz.2, parameterCell tz.1)
  let location := fun tz : T × (∀ j, Finset.Ico (sourceLo j) (sourceHi j)) =>
    smoothAffineSample (parameter tz.1) (fun j => (tz.2 j : ℤ))
  have hmove (x y : T × (∀ j, Finset.Ico (sourceLo j) (sourceHi j))) (he : mesh y = mesh x) (i : I) :
      |location x i - location y i| ≤ (r i : ℤ) := by
    have hs : sourceCell y.2 = sourceCell x.2 := congrArg Prod.fst he
    have hp : parameterCell y.1 = parameterCell x.1 := congrArg Prod.snd he
    have h := (smoothAffineSample_variation (parameter x.1) (parameter y.1)
      (fun j => (x.2 j : ℤ)) (fun j => (y.2 j : ℤ)) i hT (hV i) (ht x.1) (fun j => hv y.2 j i)
      (hbase x.2 y.2 hs i) (fun j => hdir x.2 y.2 hs j i) (hparam x.1 y.1 hp)).trans (hbudget i)
    exact_mod_cast h
  apply (FiniteProbabilityWeights.eventProbability_mono _ _ _
    (physicalMeshCrossing_subset_boundary lo N P hstep hpos mesh location r hmove)).trans
  exact sampled_physical_boundary_probability parameterLaw parameter sourceLo sourceHi hsource lo N P r

end Erdos3

end

end OAI
