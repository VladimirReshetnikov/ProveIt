import Mathlib
import OAI.Combinatorics.Progressions.Estimates.FiniteGraphEnergy
import OAI.Combinatorics.Progressions.Estimates.RoundingRecoveryScale
import OAI.Combinatorics.Progressions.Linear.CommonRankCoefficientCorrections

namespace OAI

section

namespace Erdos3

theorem floor_four_difference_bound (c x₀ x₁ x₂ x₃ : ℝ) (z : ℤ)
    (h : |c + (x₁ + x₂ - x₀ - x₃) - z| ≤ 1) :
    |⌊c⌋ + (⌊x₁⌋ + ⌊x₂⌋ - ⌊x₀⌋ - ⌊x₃⌋) - z| ≤ 6 := by
  have hc := Int.floor_le c
  have hc' := Int.sub_one_lt_floor c
  have h₀ := Int.floor_le x₀
  have h₀' := Int.sub_one_lt_floor x₀
  have h₁ := Int.floor_le x₁
  have h₁' := Int.sub_one_lt_floor x₁
  have h₂ := Int.floor_le x₂
  have h₂' := Int.sub_one_lt_floor x₂
  have h₃ := Int.floor_le x₃
  have h₃' := Int.sub_one_lt_floor x₃
  obtain ⟨hl, hu⟩ := abs_le.mp h
  have hh : |((⌊c⌋ + (⌊x₁⌋ + ⌊x₂⌋ - ⌊x₀⌋ - ⌊x₃⌋) - z : ℤ) : ℝ)| ≤ 6 := by
    rw [abs_le]
    push_cast
    constructor <;> linarith
  exact_mod_cast hh

noncomputable def roundedCoefficient {I : Type*} (M l : ℕ) (a : I → ℝ) : I → ZMod M :=
  fun i => ((⌊(M : ℝ) * l * a i⌋ : ℤ) : ZMod M)

noncomputable def coefficientRoundingErrors {I : Type*} [Fintype I]
    (M l : ℕ) (c : I → ℝ) : Finset (I → ZMod M) := by
  classical
  exact (Fintype.piFinset (fun _ : I => Finset.Icc (-6 : ℤ) 6)).image
    (fun b i => (b i : ZMod M) - ((⌊(M : ℝ) * l * c i⌋ : ℤ) : ZMod M))

theorem coefficientRoundingErrors_card_le {I : Type*} [Fintype I]
    (M l : ℕ) (c : I → ℝ) :
    (coefficientRoundingErrors M l c).card ≤ 13 ^ Fintype.card I := by
  classical
  calc
    _ ≤ (Fintype.piFinset (fun _ : I => Finset.Icc (-6 : ℤ) 6)).card := Finset.card_image_le
    _ = _ := by simp

theorem roundedCoefficient_four_mem {I : Type*} [Fintype I]
    (M l : ℕ) (c : I → ℝ) (a : Fin 4 → I → ℝ) (q : I → ℝ) {ε : ℝ}
    (hgrid : q ∈ realDenominatorGrid l)
    (hsmall : (M : ℝ) * l * ε ≤ 1)
    (herror : ‖c + (a 1 + a 2 - a 0 - a 3) - q‖ ≤ ε) :
    roundedCoefficient M l (a 1) + roundedCoefficient M l (a 2) -
      roundedCoefficient M l (a 0) - roundedCoefficient M l (a 3) ∈
        coefficientRoundingErrors M l c := by
  classical
  obtain ⟨z, hz⟩ := hgrid
  let k : ℝ := (M : ℝ) * l
  have hk : 0 ≤ k := by dsimp only [k]; positivity
  let b : I → ℤ := fun i => ⌊k * c i⌋ +
    (⌊k * a 1 i⌋ + ⌊k * a 2 i⌋ - ⌊k * a 0 i⌋ - ⌊k * a 3 i⌋) - (M : ℤ) * z i
  have hb (i : I) : b i ∈ Finset.Icc (-6 : ℤ) 6 := by
    have hi := (norm_le_pi_norm (c + (a 1 + a 2 - a 0 - a 3) - q) i).trans herror
    change ‖c i + (a 1 i + a 2 i - a 0 i - a 3 i) - q i‖ ≤ ε at hi
    rw [Real.norm_eq_abs] at hi
    have hz' : (z i : ℝ) = (l : ℝ) * q i := congrFun hz i
    have heq : k * (c i + (a 1 i + a 2 i - a 0 i - a 3 i) - q i) =
        k * c i + (k * a 1 i + k * a 2 i - k * a 0 i - k * a 3 i) -
          (M : ℝ) * z i := by
      rw [hz']
      dsimp only [k]
      ring
    have hh : |k * c i + (k * a 1 i + k * a 2 i - k * a 0 i - k * a 3 i) -
        (M : ℝ) * z i| ≤ 1 := by
      rw [← heq, abs_mul, abs_of_nonneg hk]
      exact (mul_le_mul_of_nonneg_left hi hk).trans hsmall
    have hf := floor_four_difference_bound (k * c i) (k * a 0 i) (k * a 1 i)
      (k * a 2 i) (k * a 3 i) ((M : ℤ) * z i)
      (by simpa only [Int.cast_mul, Int.cast_natCast] using hh)
    exact Finset.mem_Icc.mpr (abs_le.mp hf)
  apply Finset.mem_image.mpr
  refine ⟨b, Fintype.mem_piFinset.mpr hb, ?_⟩
  funext i
  simp only [Pi.sub_apply, Pi.add_apply, roundedCoefficient, b, k, Int.cast_sub,
    Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, sub_zero]
  ring

end Erdos3

end

section

namespace Erdos3

theorem exists_unrounded_scalar (M l : ℕ) [NeZero M] (hl : 0 < l)
    (a : ℝ) (u : ℤ) (h : ((⌊(M : ℝ) * l * a⌋ : ℤ) : ZMod M) = (u : ZMod M)) :
    ∃ k : ℤ, 0 ≤ a - (u : ℝ) / ((M : ℝ) * l) - (k : ℝ) / l ∧
      a - (u : ℝ) / ((M : ℝ) * l) - (k : ℝ) / l < 1 / ((M : ℝ) * l) := by
  have hM : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl
  obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub u ⌊(M : ℝ) * l * a⌋ M).mp h.symm
  have hkR : (⌊(M : ℝ) * l * a⌋ : ℝ) = (u : ℝ) + (M : ℝ) * k := by
    have he : (⌊(M : ℝ) * l * a⌋ : ℝ) - (u : ℝ) = (M : ℝ) * k := by exact_mod_cast hk
    linarith
  have heq : a - (u : ℝ) / ((M : ℝ) * l) - (k : ℝ) / l =
      ((M : ℝ) * l * a - ⌊(M : ℝ) * l * a⌋) / ((M : ℝ) * l) := by
    rw [hkR]
    field_simp
    ring
  refine ⟨k, ?_, ?_⟩
  · rw [heq]
    exact div_nonneg (sub_nonneg.mpr (Int.floor_le _)) (by positivity)
  · rw [heq]
    apply div_lt_div_of_pos_right _ (by positivity)
    linarith [Int.lt_floor_add_one ((M : ℝ) * l * a)]

theorem exists_unrounded_vector {I : Type*} [Fintype I]
    (M l : ℕ) [NeZero M] (hl : 0 < l) (a : I → ℝ) (u : I → ℤ)
    (h : roundedCoefficient M l a = fun i => (u i : ZMod M)) :
    ∃ q ∈ realDenominatorGrid l,
      ‖a - (fun i => (u i : ℝ) / ((M : ℝ) * l)) - q‖ ≤ 1 / ((M : ℝ) * l) := by
  have hM : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl
  have hi (i : I) := exists_unrounded_scalar M l hl (a i) (u i) (congrFun h i)
  choose k hk0 hk1 using hi
  let q : I → ℝ := fun i => (k i : ℝ) / l
  refine ⟨q, ?_, ?_⟩
  · refine ⟨k, ?_⟩
    funext i
    change (k i : ℝ) = (l : ℝ) * ((k i : ℝ) / l)
    field_simp
  · apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 1 / ((M : ℝ) * l))).mpr
    intro i
    change ‖a i - (u i : ℝ) / ((M : ℝ) * l) - (k i : ℝ) / l‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (hk0 i)]
    exact (hk1 i).le

end Erdos3

end

section

namespace Erdos3

variable {G I : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] [Fintype I]

theorem rounded_graph_energy (H : Finset G) (S : Finset (G × G × G))
    (a : G → I → ℝ) (c : I → ℝ) (M l : ℕ) [NeZero M] {ε : ℝ}
    (hH : ∀ t ∈ S, t.2.1 ∈ H ∧ t.2.1 - t.1 ∈ H ∧ t.2.2 ∈ H ∧ t.2.2 - t.1 ∈ H)
    (hsmall : (M : ℝ) * l * ε ≤ 1)
    (hnear : ∀ t ∈ S, ∃ q ∈ realDenominatorGrid l,
      ‖c + (a (t.2.1 - t.1) + a t.2.2 - a t.2.1 - a (t.2.2 - t.1)) - q‖ ≤ ε) :
    S.card ≤ 13 ^ Fintype.card I *
      Finset.addEnergy (additiveGraph H (fun h => roundedCoefficient M l (a h)))
        (additiveGraph H (fun h => roundedCoefficient M l (a h))) := by
  classical
  have h := graph_energy_of_few_quadruple_differences H S
    (fun h => roundedCoefficient M l (a h)) (coefficientRoundingErrors M l c) hH (by
      intro t ht
      obtain ⟨q, hq, herr⟩ := hnear t ht
      exact roundedCoefficient_four_mem M l c
        ![a t.2.1, a (t.2.1 - t.1), a t.2.2, a (t.2.2 - t.1)] q hq hsmall herr)
  exact h.trans (Nat.mul_le_mul_right _ (coefficientRoundingErrors_card_le M l c))

theorem rounded_graph_energy_density (H : Finset G) (S : Finset (G × G × G))
    (a : G → I → ℝ) (c : I → ℝ) (M l : ℕ) [NeZero M] {ε p : ℝ}
    (hH : ∀ t ∈ S, t.2.1 ∈ H ∧ t.2.1 - t.1 ∈ H ∧ t.2.2 ∈ H ∧ t.2.2 - t.1 ∈ H)
    (hsmall : (M : ℝ) * l * ε ≤ 1)
    (hnear : ∀ t ∈ S, ∃ q ∈ realDenominatorGrid l,
      ‖c + (a (t.2.1 - t.1) + a t.2.2 - a t.2.1 - a (t.2.2 - t.1)) - q‖ ≤ ε)
    (hdensity : Real.exp (-p) * (H.card : ℝ) ^ 3 ≤ S.card) :
    Real.exp (-(p + 13 * Fintype.card I)) * (H.card : ℝ) ^ 3 ≤
      (Finset.addEnergy (additiveGraph H (fun h => roundedCoefficient M l (a h)))
        (additiveGraph H (fun h => roundedCoefficient M l (a h))) : ℝ) := by
  classical
  let E := Finset.addEnergy (additiveGraph H (fun h => roundedCoefficient M l (a h)))
    (additiveGraph H (fun h => roundedCoefficient M l (a h)))
  have hcard := rounded_graph_energy H S a c M l hH hsmall hnear
  have hcount : (13 : ℝ) ^ Fintype.card I ≤ Real.exp (13 * Fintype.card I) := by
    calc
      _ ≤ (Real.exp 13) ^ Fintype.card I :=
        pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp (13 : ℝ)]) _
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hlarge : Real.exp (-p) * (H.card : ℝ) ^ 3 ≤
      Real.exp (13 * Fintype.card I) * E := by
    apply hdensity.trans
    have hc := (Nat.cast_le (α := ℝ)).mpr hcard
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hc
    exact hc.trans (mul_le_mul_of_nonneg_right hcount (Nat.cast_nonneg E))
  calc
    _ = Real.exp (-(13 * Fintype.card I)) * (Real.exp (-p) * (H.card : ℝ) ^ 3) := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp (-(13 * Fintype.card I)) * (Real.exp (13 * Fintype.card I) * E) :=
      mul_le_mul_of_nonneg_left hlarge (Real.exp_nonneg _)
    _ = E := by rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

end Erdos3

end

section

namespace Erdos3

def coordinateDenominatorGrid {I : Type*} (l : I → ℕ) : Set (I → ℝ) :=
  {q | ∃ z : I → ℤ, ∀ i, (z i : ℝ) = (l i : ℝ) * q i}

noncomputable def variableRoundedCoefficient {I : Type*} (M l : I → ℕ)
    (a : I → ℝ) : ∀ i, ZMod (M i) :=
  fun i => ((⌊(M i : ℝ) * l i * a i⌋ : ℤ) : ZMod (M i))

noncomputable def variableRoundingErrors {I : Type*} [Fintype I]
    (M l : I → ℕ) (c : I → ℝ) : Finset (∀ i, ZMod (M i)) := by
  classical
  exact (Fintype.piFinset (fun _ : I => Finset.Icc (-6 : ℤ) 6)).image
    (fun b i => (b i : ZMod (M i)) - ((⌊(M i : ℝ) * l i * c i⌋ : ℤ) : ZMod (M i)))

theorem variableRoundingErrors_card_le {I : Type*} [Fintype I]
    (M l : I → ℕ) (c : I → ℝ) :
    (variableRoundingErrors M l c).card ≤ 13 ^ Fintype.card I := by
  classical
  calc
    _ ≤ (Fintype.piFinset (fun _ : I => Finset.Icc (-6 : ℤ) 6)).card := Finset.card_image_le
    _ = _ := by simp

theorem variableRoundedCoefficient_four_mem {I : Type*} [Fintype I]
    (M l : I → ℕ) (c : I → ℝ) (a : Fin 4 → I → ℝ) (q ε : I → ℝ)
    (hgrid : q ∈ coordinateDenominatorGrid l)
    (hsmall : ∀ i, (M i : ℝ) * l i * ε i ≤ 1)
    (herror : ∀ i, |c i + (a 1 i + a 2 i - a 0 i - a 3 i) - q i| ≤ ε i) :
    variableRoundedCoefficient M l (a 1) + variableRoundedCoefficient M l (a 2) -
      variableRoundedCoefficient M l (a 0) - variableRoundedCoefficient M l (a 3) ∈
        variableRoundingErrors M l c := by
  classical
  obtain ⟨z, hz⟩ := hgrid
  let k : I → ℝ := fun i => (M i : ℝ) * l i
  let b : I → ℤ := fun i => ⌊k i * c i⌋ +
    (⌊k i * a 1 i⌋ + ⌊k i * a 2 i⌋ - ⌊k i * a 0 i⌋ - ⌊k i * a 3 i⌋) - (M i : ℤ) * z i
  have hb (i : I) : b i ∈ Finset.Icc (-6 : ℤ) 6 := by
    have hk : 0 ≤ k i := by dsimp [k]; positivity
    have heq : k i * (c i + (a 1 i + a 2 i - a 0 i - a 3 i) - q i) =
        k i * c i + (k i * a 1 i + k i * a 2 i - k i * a 0 i - k i * a 3 i) -
          (M i : ℝ) * z i := by
      rw [hz i]
      dsimp [k]
      ring
    have hh : |k i * c i + (k i * a 1 i + k i * a 2 i - k i * a 0 i - k i * a 3 i) -
        (M i : ℝ) * z i| ≤ 1 := by
      rw [← heq, abs_mul, abs_of_nonneg hk]
      exact (mul_le_mul_of_nonneg_left (herror i) hk).trans (hsmall i)
    have hf := floor_four_difference_bound (k i * c i) (k i * a 0 i) (k i * a 1 i)
      (k i * a 2 i) (k i * a 3 i) ((M i : ℤ) * z i)
      (by simpa only [Int.cast_mul, Int.cast_natCast] using hh)
    exact Finset.mem_Icc.mpr (abs_le.mp hf)
  apply Finset.mem_image.mpr
  refine ⟨b, Fintype.mem_piFinset.mpr hb, ?_⟩
  funext i
  simp only [Pi.sub_apply, Pi.add_apply, variableRoundedCoefficient, b, k, Int.cast_sub,
    Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, sub_zero]
  ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem map_integer_coordinates {r : ℕ} {G : Type*} [AddCommGroup G]
    (Φ : (Fin r → ℤ) →+ G) (x : Fin r → ℤ) :
    Φ x = ∑ j, x j • Φ (Pi.single j 1) := by
  have hx : x = ∑ j, x j • (Pi.single j 1 : Fin r → ℤ) := by
    funext i
    simp [Pi.single_apply]
  calc
    Φ x = Φ (∑ j, x j • (Pi.single j 1 : Fin r → ℤ)) := congrArg Φ hx
    _ = _ := by simp only [map_sum, map_zsmul]

noncomputable def finiteCoefficientLift {I : Type*} {M : ℕ}
    (l : ℕ) (b : I → ZMod M) : I → ℝ :=
  fun i => ((b i).val : ℝ) / ((M : ℝ) * l)

theorem finiteCoefficientLift_mem_Ico {I : Type*} {M : ℕ} [NeZero M]
    (l : ℕ) (hl : 0 < l) (b : I → ZMod M) (i : I) :
    finiteCoefficientLift l b i ∈ Set.Ico (0 : ℝ) (1 / l) := by
  have hM : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) (by positivity)
  · change ((b i).val : ℝ) / ((M : ℝ) * l) < 1 / l
    apply (div_lt_iff₀ (mul_pos hM hlR)).mpr
    have hv : ((b i).val : ℝ) < M := by exact_mod_cast (b i).val_lt
    have heq : (1 / (l : ℝ)) * ((M : ℝ) * l) = M := by field_simp
    rwa [heq]

theorem exists_unrounded_affine {I : Type*} [Fintype I] {M r : ℕ} [NeZero M]
    (l : ℕ) (hl : 0 < l) (b : I → ZMod M)
    (Φ : (Fin r → ℤ) →+ (I → ZMod M)) (x : Fin r → ℤ) (a : I → ℝ)
    (h : roundedCoefficient M l a = b + Φ x) :
    ∃ q ∈ realDenominatorGrid l,
      ‖a - (finiteCoefficientLift l b +
        ∑ j, (x j : ℝ) • finiteCoefficientLift l (Φ (Pi.single j 1))) - q‖ ≤
          1 / ((M : ℝ) * l) := by
  let u : I → ℤ := fun i => ((b i).val : ℤ) +
    ∑ j, x j * ((Φ (Pi.single j 1) i).val : ℤ)
  have hu : roundedCoefficient M l a = fun i => (u i : ZMod M) := by
    rw [h, map_integer_coordinates Φ x]
    funext i
    simp only [u, Pi.add_apply, Finset.sum_apply, Pi.smul_apply]
    simp only [zsmul_eq_mul, Int.cast_add, Int.cast_sum, Int.cast_mul,
      Int.cast_natCast, ZMod.natCast_zmod_val]
  have heq : (fun i => (u i : ℝ) / ((M : ℝ) * l)) =
      finiteCoefficientLift l b +
        ∑ j, (x j : ℝ) • finiteCoefficientLift l (Φ (Pi.single j 1)) := by
    funext i
    simp only [u, Int.cast_add, Int.cast_sum, Int.cast_mul, Int.cast_natCast,
      finiteCoefficientLift, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      add_div, Finset.sum_div, mul_div_assoc]
  obtain ⟨q, hq, herr⟩ := exists_unrounded_vector M l hl a u hu
  exact ⟨q, hq, heq ▸ herr⟩

end Erdos3

end

section

namespace Erdos3

variable {G I : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] [Fintype I]

theorem variable_graph_energy (H : Finset G) (S : Finset (G × G × G))
    (a : G → I → ℝ) (c : I → ℝ) (M l : I → ℕ) [∀ i, NeZero (M i)] (ε : I → ℝ)
    (hH : ∀ t ∈ S, t.2.1 ∈ H ∧ t.2.1 - t.1 ∈ H ∧ t.2.2 ∈ H ∧ t.2.2 - t.1 ∈ H)
    (hsmall : ∀ i, (M i : ℝ) * l i * ε i ≤ 1)
    (hnear : ∀ t ∈ S, ∃ q ∈ coordinateDenominatorGrid l,
      ∀ i, |c i + (a (t.2.1 - t.1) i + a t.2.2 i - a t.2.1 i - a (t.2.2 - t.1) i) - q i| ≤ ε i) :
    S.card ≤ 13 ^ Fintype.card I *
      Finset.addEnergy (additiveGraph H (fun h => variableRoundedCoefficient M l (a h)))
        (additiveGraph H (fun h => variableRoundedCoefficient M l (a h))) := by
  classical
  have h := graph_energy_of_few_quadruple_differences H S
    (fun h => variableRoundedCoefficient M l (a h)) (variableRoundingErrors M l c) hH (by
      intro t ht
      obtain ⟨q, hq, herr⟩ := hnear t ht
      exact variableRoundedCoefficient_four_mem M l c
        ![a t.2.1, a (t.2.1 - t.1), a t.2.2, a (t.2.2 - t.1)] q ε hq hsmall herr)
  exact h.trans (Nat.mul_le_mul_right _ (variableRoundingErrors_card_le M l c))

theorem variable_graph_energy_density (H : Finset G) (S : Finset (G × G × G))
    (a : G → I → ℝ) (c : I → ℝ) (M l : I → ℕ) [∀ i, NeZero (M i)] (ε : I → ℝ) {p : ℝ}
    (hH : ∀ t ∈ S, t.2.1 ∈ H ∧ t.2.1 - t.1 ∈ H ∧ t.2.2 ∈ H ∧ t.2.2 - t.1 ∈ H)
    (hsmall : ∀ i, (M i : ℝ) * l i * ε i ≤ 1)
    (hnear : ∀ t ∈ S, ∃ q ∈ coordinateDenominatorGrid l,
      ∀ i, |c i + (a (t.2.1 - t.1) i + a t.2.2 i - a t.2.1 i - a (t.2.2 - t.1) i) - q i| ≤ ε i)
    (hdensity : Real.exp (-p) * (H.card : ℝ) ^ 3 ≤ S.card) :
    Real.exp (-(p + 13 * Fintype.card I)) * (H.card : ℝ) ^ 3 ≤
      (Finset.addEnergy (additiveGraph H (fun h => variableRoundedCoefficient M l (a h)))
        (additiveGraph H (fun h => variableRoundedCoefficient M l (a h))) : ℝ) := by
  classical
  let E := Finset.addEnergy (additiveGraph H (fun h => variableRoundedCoefficient M l (a h)))
    (additiveGraph H (fun h => variableRoundedCoefficient M l (a h)))
  have hcard := variable_graph_energy H S a c M l ε hH hsmall hnear
  have hcount : (13 : ℝ) ^ Fintype.card I ≤ Real.exp (13 * Fintype.card I) := by
    calc
      _ ≤ (Real.exp 13) ^ Fintype.card I :=
        pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp (13 : ℝ)]) _
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hlarge : Real.exp (-p) * (H.card : ℝ) ^ 3 ≤
      Real.exp (13 * Fintype.card I) * E := by
    apply hdensity.trans
    have hc := (Nat.cast_le (α := ℝ)).mpr hcard
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hc
    exact hc.trans (mul_le_mul_of_nonneg_right hcount (Nat.cast_nonneg E))
  calc
    _ = Real.exp (-(13 * Fintype.card I)) * (Real.exp (-p) * (H.card : ℝ) ^ 3) := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp (-(13 * Fintype.card I)) * (Real.exp (13 * Fintype.card I) * E) :=
      mul_le_mul_of_nonneg_left hlarge (Real.exp_nonneg _)
    _ = E := by rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def variableCoefficientLift {I : Type*} {M : I → ℕ}
    (l : I → ℕ) (b : ∀ i, ZMod (M i)) : I → ℝ :=
  fun i => ((b i).val : ℝ) / ((M i : ℝ) * l i)

theorem variableCoefficientLift_mem_Ico {I : Type*} {M : I → ℕ} [∀ i, NeZero (M i)]
    (l : I → ℕ) (hl : ∀ i, 0 < l i) (b : ∀ i, ZMod (M i)) (i : I) :
    variableCoefficientLift l b i ∈ Set.Ico (0 : ℝ) (1 / l i) := by
  exact finiteCoefficientLift_mem_Ico (l i) (hl i) (fun _ : Unit => b i) ()

theorem exists_variable_unrounded_affine {I : Type*} {M : I → ℕ} {r : ℕ}
    [∀ i, NeZero (M i)] (l : I → ℕ) (hl : ∀ i, 0 < l i)
    (b : ∀ i, ZMod (M i)) (Φ : (Fin r → ℤ) →+ (∀ i, ZMod (M i)))
    (x : Fin r → ℤ) (a : I → ℝ) (h : variableRoundedCoefficient M l a = b + Φ x) :
    ∃ q ∈ coordinateDenominatorGrid l, ∀ i,
      |a i - (variableCoefficientLift l b +
        ∑ j, (x j : ℝ) • variableCoefficientLift l (Φ (Pi.single j 1))) i - q i| ≤
          1 / ((M i : ℝ) * l i) := by
  let u : I → ℤ := fun i => ((b i).val : ℤ) + ∑ j, x j * ((Φ (Pi.single j 1) i).val : ℤ)
  have hu : variableRoundedCoefficient M l a = fun i => (u i : ZMod (M i)) := by
    rw [h, map_integer_coordinates Φ x]
    funext i
    simp only [u, Pi.add_apply, Finset.sum_apply, Pi.smul_apply]
    simp only [zsmul_eq_mul, Int.cast_add, Int.cast_sum, Int.cast_mul,
      Int.cast_natCast, ZMod.natCast_zmod_val]
  have heq : (fun i => (u i : ℝ) / ((M i : ℝ) * l i)) = variableCoefficientLift l b +
      ∑ j, (x j : ℝ) • variableCoefficientLift l (Φ (Pi.single j 1)) := by
    funext i
    simp only [u, Int.cast_add, Int.cast_sum, Int.cast_mul, Int.cast_natCast,
      variableCoefficientLift, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      add_div, Finset.sum_div, mul_div_assoc]
  have hi (i : I) := exists_unrounded_scalar (M i) (l i) (hl i) (a i) (u i) (congrFun hu i)
  choose k hk0 hk1 using hi
  let q : I → ℝ := fun i => (k i : ℝ) / l i
  refine ⟨q, ⟨k, ?_⟩, ?_⟩
  · intro i
    have hlR : (0 : ℝ) < l i := by exact_mod_cast hl i
    dsimp [q]
    field_simp
  · intro i
    rw [← heq]
    change |a i - (u i : ℝ) / ((M i : ℝ) * l i) - (k i : ℝ) / l i| ≤ _
    rw [abs_of_nonneg (hk0 i)]
    exact (hk1 i).le

theorem exists_coordinate_rounding_moduli {I : Type*}
    (l : I → ℕ) (hl : ∀ i, 0 < l i) (ε : I → ℝ) (hε : ∀ i, 0 < ε i)
    (hsmall : ∀ i, 2 * (l i : ℝ) * ε i ≤ 1) :
    ∃ M : I → ℕ, (∀ i, 0 < M i) ∧ (∀ i, (M i : ℝ) * l i * ε i ≤ 1) ∧
      ∀ i, 1 / ((M i : ℝ) * l i) ≤ 2 * ε i := by
  have hi (i : I) := exists_rounding_modulus_with_recovery (l i) (hl i) (hε i) (hsmall i)
  choose M hM hscale herror using hi
  exact ⟨M, hM, hscale, herror⟩

end Erdos3

end

section

namespace Erdos3.NativeRankRelation.CommonData

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem rounded_coefficient_graph_energy {I : Type*} [Fintype I]
    (a : ZMod N → I → ℝ) (c : I → ℝ) (M l : ℕ) [NeZero M] {ε : ℝ}
    (hsmall : (M : ℝ) * l * ε ≤ 1)
    (hnear : ∀ t ∈ D.quadruples, ∃ q ∈ realDenominatorGrid l,
      ‖c + (a (rankQuadrupleParameters t 1) + a (rankQuadrupleParameters t 2) -
        a (rankQuadrupleParameters t 0) - a (rankQuadrupleParameters t 3)) - q‖ ≤ ε) :
    Real.exp (-(P + 13 * Fintype.card I)) * (H.card : ℝ) ^ 3 ≤
      (Finset.addEnergy (additiveGraph H (fun h => roundedCoefficient M l (a h)))
        (additiveGraph H (fun h => roundedCoefficient M l (a h))) : ℝ) := by
  apply rounded_graph_energy_density H D.quadruples a c M l _ hsmall _ _
  · intro t ht
    let J := R.interval ⟨t, D.subset ht⟩
    exact ⟨J.first_mem, J.second_mem, J.third_mem, J.fourth_mem⟩
  · intro t ht
    exact hnear t ht
  · have hcard : (H.card : ℝ) ≤ Fintype.card (ZMod N) := by
      exact_mod_cast Finset.card_le_univ H
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 3)
      (Real.exp_nonneg _)).trans D.density

theorem exists_rounded_coefficient_graph_energy {I : Type*} [Fintype I]
    (a : ZMod N → I → ℝ) (c : I → ℝ) (l : ℕ) (hl : 0 < l) {ε : ℝ}
    (hε : 0 < ε) (hsmall : 2 * (l : ℝ) * ε ≤ 1)
    (hnear : ∀ t ∈ D.quadruples, ∃ q ∈ realDenominatorGrid l,
      ‖c + (a (rankQuadrupleParameters t 1) + a (rankQuadrupleParameters t 2) -
        a (rankQuadrupleParameters t 0) - a (rankQuadrupleParameters t 3)) - q‖ ≤ ε) :
    ∃ M : ℕ, 0 < M ∧ 1 / (2 * (l : ℝ) * ε) ≤ (M : ℝ) ∧
      Real.exp (-(P + 13 * Fintype.card I)) * (H.card : ℝ) ^ 3 ≤
        (Finset.addEnergy (additiveGraph H (fun h => roundedCoefficient M l (a h)))
          (additiveGraph H (fun h => roundedCoefficient M l (a h))) : ℝ) := by
  obtain ⟨M, hM, hlow, hscale⟩ := exists_rounding_modulus l hl hε hsmall
  let : NeZero M := ⟨hM.ne'⟩
  exact ⟨M, hM, hlow, D.rounded_coefficient_graph_energy a c M l hscale hnear⟩

end Erdos3.NativeRankRelation.CommonData

end

end OAI
