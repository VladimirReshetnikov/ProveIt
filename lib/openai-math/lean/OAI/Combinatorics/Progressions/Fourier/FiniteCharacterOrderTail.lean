import OAI.Combinatorics.Progressions.Estimates.DenseProductApproximation
import OAI.Combinatorics.Progressions.Fourier.CharacterCoordinateScale
import OAI.Combinatorics.Progressions.Fourier.PrimePowerCharacterScaling

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

variable {I H : Type*} [Fintype I]
  [AddCommGroup H] [Fintype H]

theorem finiteCharacter_exactOrder_card_le
    (π : (I → ℤ) →+ H) (hπ : Function.Surjective π) (q : ℕ) (hq : 0 < q) :
    (Finset.univ.filter (fun χ : AddChar H ℂ => orderOf χ = q)).card ≤ q ^ Fintype.card I := by
  let : NeZero q := ⟨hq.ne'⟩
  let f : {χ : AddChar H ℂ // orderOf χ = q} → TorsionLatticeCharacter I q :=
    fun χ => ⟨characterPullback π χ.val, by
      simpa only [map_pow, map_one, χ.property] using
        congrArg (characterPullback π) (pow_orderOf_eq_one χ.val)⟩
  have hf : Function.Injective f := by
    intro χ ψ h
    apply Subtype.ext
    exact AddChar.compAddMonoidHom_injective_left π hπ (congrArg Subtype.val h)
  have hc := (Fintype.card_le_of_injective f hf).trans (torsionLatticeCharacter_card_le I q)
  simpa only [Fintype.card_subtype] using hc

theorem finiteCharacter_boundedOrder_card_le
    (π : (I → ℤ) →+ H) (hπ : Function.Surjective π) (T : ℕ) :
    (Finset.univ.filter (fun χ : AddChar H ℂ => orderOf χ ≤ T)).card ≤
      T ^ (Fintype.card I + 1) := by
  let S := Finset.univ.filter (fun χ : AddChar H ℂ => orderOf χ ≤ T)
  have hmap : (S : Set (AddChar H ℂ)).MapsTo orderOf (Finset.Icc 1 T) := by
    intro χ hχ
    exact Finset.mem_Icc.mpr ⟨(isOfFinOrder_of_finite χ).orderOf_pos,
      (Finset.mem_filter.mp hχ).2⟩
  change S.card ≤ _
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  calc
    _ ≤ ∑ q ∈ Finset.Icc 1 T, T ^ Fintype.card I := by
      apply Finset.sum_le_sum
      intro q hq
      have hq0 : 0 < q := (Finset.mem_Icc.mp hq).1
      have hc := finiteCharacter_exactOrder_card_le π hπ q hq0
      have hsub : S.filter (fun χ => orderOf χ = q) ⊆
          Finset.univ.filter (fun χ : AddChar H ℂ => orderOf χ = q) := by
        intro χ hχ
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hχ).2⟩
      exact (Finset.card_le_card hsub).trans
        (hc.trans (Nat.pow_le_pow_left (Finset.mem_Icc.mp hq).2 _))
    _ = T ^ (Fintype.card I + 1) := by
      rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, pow_succ]
      simp only [Nat.add_sub_cancel]
      exact Nat.mul_comm _ _

theorem finiteImage_boundedOrder_coefficient_mass {X : Type*} [Fintype X]
    (π : (I → ℤ) →+ H) (hπ : Function.Surjective π)
    (p : FiniteProbabilityWeights X) (Y : X → H) (T : ℕ) :
    (∑ χ ∈ Finset.univ.filter (fun χ : AddChar H ℂ => orderOf χ ≤ T),
      ‖finiteImageCharacteristic p Y χ‖) ≤ (T : ℝ) ^ (Fintype.card I + 1) := by
  calc
    _ ≤ ∑ _χ ∈ Finset.univ.filter (fun χ : AddChar H ℂ => orderOf χ ≤ T), (1 : ℝ) :=
      Finset.sum_le_sum (fun χ _ => finiteImageCharacteristic_norm_le_one p Y χ)
    _ = ((Finset.univ.filter (fun χ : AddChar H ℂ => orderOf χ ≤ T)).card : ℝ) := by simp
    _ ≤ _ := by exact_mod_cast finiteCharacter_boundedOrder_card_le π hπ T

theorem finiteCharacter_order_tail
    (π : (I → ℤ) →+ H) (hπ : Function.Surjective π)
    (f : AddChar H ℂ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hdecay : ∀ χ, f χ ≤ C / (orderOf χ : ℝ) ^ (Fintype.card I + 2))
    (T : ℕ) (hT : 0 < T) :
    spectrumTail (Finset.univ.filter (fun χ : AddChar H ℂ => orderOf χ ≤ T)) f ≤ C / T := by
  let S := Finset.univ.filter (fun χ : AddChar H ℂ => T < orderOf χ)
  let orders := S.image (fun χ => orderOf χ)
  have heq : spectrumTail (Finset.univ.filter (fun χ : AddChar H ℂ => orderOf χ ≤ T)) f =
      ∑ χ ∈ S, f χ := by
    simp only [spectrumTail, S, Finset.sum_filter, Finset.mem_filter, Finset.mem_univ, true_and]
    apply Finset.sum_congr rfl
    intro χ _
    by_cases h : orderOf χ ≤ T <;> simp [h, Nat.not_lt.mpr, Nat.lt_of_not_ge]
  rw [heq, ← Finset.sum_fiberwise_of_maps_to (fun χ hχ => Finset.mem_image_of_mem (fun ψ => orderOf ψ) hχ) f]
  change (∑ q ∈ orders, ∑ χ ∈ S with orderOf χ = q, f χ) ≤ _
  have horders (q) (hq : q ∈ orders) : T < q := by
    obtain ⟨χ, hχ, rfl⟩ := Finset.mem_image.mp hq
    exact (Finset.mem_filter.mp hχ).2
  have hinner (q) (hq : q ∈ orders) :
      (∑ χ ∈ S with orderOf χ = q, f χ) ≤ C / (q : ℝ) ^ 2 := by
    have hqpos : 0 < q := hT.trans (horders q hq)
    have hqreal : (0 : ℝ) < q := Nat.cast_pos.mpr hqpos
    have hc : (S.filter (fun χ => orderOf χ = q)).card ≤ q ^ Fintype.card I :=
      (Finset.card_le_card (by
        intro χ hχ
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hχ).2⟩)).trans
          (finiteCharacter_exactOrder_card_le π hπ q hqpos)
    calc
      _ ≤ ∑ _χ ∈ S with orderOf _χ = q, C / (q : ℝ) ^ (Fintype.card I + 2) := by
        apply Finset.sum_le_sum
        intro χ hχ
        simpa only [(Finset.mem_filter.mp hχ).2] using hdecay χ
      _ = (S.filter (fun χ => orderOf χ = q)).card *
          (C / (q : ℝ) ^ (Fintype.card I + 2)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (q : ℝ) ^ Fintype.card I * (C / (q : ℝ) ^ (Fintype.card I + 2)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (by positivity)
      _ = C / (q : ℝ) ^ 2 := by rw [pow_add]; field_simp
  calc
    _ ≤ ∑ q ∈ orders, C / (q : ℝ) ^ 2 := Finset.sum_le_sum hinner
    _ = C * ∑ q ∈ orders, 1 / (q : ℝ) ^ 2 := by simp only [Finset.mul_sum, mul_one_div]
    _ ≤ C * (1 / (T : ℝ)) :=
      mul_le_mul_of_nonneg_left (finite_reciprocal_square_tail orders hT horders) hC
    _ = C / T := mul_one_div _ _

theorem finiteImage_density_order_truncation {X : Type*} [Fintype X] [DecidableEq H]
    (π : (I → ℤ) →+ H) (hπ : Function.Surjective π)
    (p : FiniteProbabilityWeights X) (Y : X → H) {C : ℝ} (hC : 0 ≤ C)
    (hdecay : ∀ χ, ‖finiteImageCharacteristic p Y χ‖ ≤
      C / (orderOf χ : ℝ) ^ (Fintype.card I + 2)) (T : ℕ) (hT : 0 < T) (z : H) :
    ‖(Fintype.card H : ℂ) * finiteImageMass p Y z -
      ∑ χ ∈ Finset.univ.filter (fun χ : AddChar H ℂ => orderOf χ ≤ T),
        finiteImageCharacteristic p Y χ * star (χ z)‖ ≤ C / T := by
  have he := finiteImageFourier_truncation p Y
    (Finset.univ.filter (fun χ : AddChar H ℂ => orderOf χ ≤ T)) z (Nat.cast_nonneg (Fintype.card H))
  have hcard : (Fintype.card H : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hcardC : (Fintype.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [Complex.ofReal_natCast, div_self hcard, div_self hcardC, one_mul] at he
  exact he.trans (finiteCharacter_order_tail π hπ _ hC hdecay T hT)

theorem finiteImage_density_bound_of_order_decay {X : Type*} [Fintype X] [DecidableEq H]
    (π : (I → ℤ) →+ H) (hπ : Function.Surjective π)
    (p : FiniteProbabilityWeights X) (Y : X → H) {C : ℝ} (hC : 0 ≤ C)
    (hdecay : ∀ χ, ‖finiteImageCharacteristic p Y χ‖ ≤
      C / (orderOf χ : ℝ) ^ (Fintype.card I + 2)) (z : H) :
    (Fintype.card H : ℝ) * finiteImageMass p Y z ≤ 1 + C := by
  have hset : Finset.univ.filter (fun χ : AddChar H ℂ => orderOf χ ≤ 1) = {1} := by
    ext χ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      exact orderOf_eq_one_iff.mp (Nat.le_antisymm h (isOfFinOrder_of_finite χ).orderOf_pos)
    · intro h
      subst χ
      simp
  have he := finiteImage_density_order_truncation π hπ p Y hC hdecay 1 zero_lt_one z
  rw [hset] at he
  simp only [Finset.sum_singleton, finiteImageCharacteristic, AddChar.one_apply,
    FiniteProbabilityWeights.complexMean_const, star_one, mul_one, Nat.cast_one, div_one] at he
  have hre : |(Fintype.card H : ℝ) * finiteImageMass p Y z - 1| ≤ C := by
    simpa only [← Complex.ofReal_natCast, ← Complex.ofReal_mul, ← Complex.ofReal_one,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using he
  linarith [(abs_le.mp hre).2]

theorem finiteCharacter_integer_decay_of_rpow {C P : ℝ} (hC : 0 ≤ C)
    (hP : ((Fintype.card I + 2 : ℕ) : ℝ) ≤ P) (f : AddChar H ℂ → ℝ)
    (hf : ∀ χ, f χ ≤ C * (orderOf χ : ℝ) ^ (-P)) :
    ∀ χ, f χ ≤ C / (orderOf χ : ℝ) ^ (Fintype.card I + 2) := by
  intro χ
  have hq : (1 : ℝ) ≤ orderOf χ := by
    exact_mod_cast (isOfFinOrder_of_finite χ).orderOf_pos
  have hq0 : 0 < (orderOf χ : ℝ) := lt_of_lt_of_le zero_lt_one hq
  have hpow : (orderOf χ : ℝ) ^ (Fintype.card I + 2) ≤ (orderOf χ : ℝ) ^ P := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hq hP
  apply (hf χ).trans
  rw [Real.rpow_neg hq0.le, ← div_eq_mul_inv]
  exact div_le_div_of_nonneg_left hC (pow_pos hq0 _) hpow

end Erdos3

end

end OAI
