import OAI.Combinatorics.Progressions.Estimates.GaussianNonzeroIndex
import OAI.Combinatorics.Progressions.Estimates.PrimitiveNormalDilation
import OAI.Combinatorics.Progressions.Estimates.TemperaturePrimitiveNormal
import OAI.Combinatorics.Progressions.Lattices.StandardLatticeGaussianBound
import OAI.Combinatorics.Progressions.Polynomial.MonomialSignedIndex
import OAI.Combinatorics.Progressions.Polynomial.PolynomialPartitionBudget
import OAI.Combinatorics.Progressions.Polynomial.SchmidtIntervalBudget

namespace OAI

section

namespace Erdos3

noncomputable def schmidtStepFactor (C e d : ℕ) (A : ℝ) : ℝ :=
  1 + (C : ℝ) * (8 * A) ^ e * (Real.exp Real.pi * A) *
    (schmidtRadiusFactor d A + (d : ℝ) + 1)

theorem schmidtStepFactor_bounds (C e d : ℕ) {A : ℝ} (hA : 1 ≤ A) :
    1 ≤ schmidtStepFactor C e d A ∧
    (C : ℝ) * (8 * A) ^ e ≤ schmidtStepFactor C e d A ∧
    (C : ℝ) * (8 * A) ^ e * (schmidtRadiusFactor d A * (Real.exp Real.pi * A)) ≤
      schmidtStepFactor C e d A ∧
    (C : ℝ) * (8 * A) ^ e * (Real.exp Real.pi * A) ≤
      ((d : ℝ) + 1)⁻¹ * schmidtStepFactor C e d A := by
  have hA0 : 0 ≤ A := by linarith
  have hB : 0 ≤ (C : ℝ) * (8 * A) ^ e := by positivity
  have hL : 1 ≤ schmidtRadiusFactor d A := by
    unfold schmidtRadiusFactor
    nlinarith [Real.log_nonneg hA, Nat.cast_nonneg (α := ℝ) d]
  have hS : 1 ≤ Real.exp Real.pi * A := by
    have he : 1 ≤ Real.exp Real.pi := by linarith [Real.add_one_le_exp Real.pi, Real.pi_pos]
    nlinarith
  have hR : 0 < (d : ℝ) + 1 := by positivity
  have hBS : 0 ≤ (C : ℝ) * (8 * A) ^ e * (Real.exp Real.pi * A) := by positivity
  have hQ : (C : ℝ) * (8 * A) ^ e * (schmidtRadiusFactor d A * (Real.exp Real.pi * A)) ≤
      schmidtStepFactor C e d A := by
    unfold schmidtStepFactor
    nlinarith [mul_nonneg hBS hR.le]
  refine ⟨?_, ?_, hQ, ?_⟩
  · unfold schmidtStepFactor
    have : 0 ≤ schmidtRadiusFactor d A + (d : ℝ) + 1 := by linarith
    nlinarith [mul_nonneg hBS this]
  · calc
      _ ≤ (C : ℝ) * (8 * A) ^ e * (Real.exp Real.pi * A) := le_mul_of_one_le_right hB hS
      _ ≤ ((C : ℝ) * (8 * A) ^ e * (Real.exp Real.pi * A)) * schmidtRadiusFactor d A :=
        le_mul_of_one_le_right hBS hL
      _ ≤ schmidtStepFactor C e d A := by nlinarith [hQ]
  · rw [inv_mul_eq_div]
    apply (le_div_iff₀ hR).mpr
    unfold schmidtStepFactor
    nlinarith [mul_nonneg hBS (by linarith : 0 ≤ schmidtRadiusFactor d A)]

theorem schmidt_step_epsilon_bounds (d : ℕ) :
    0 < ((d : ℝ) + 1)⁻¹ ∧ ((d : ℝ) + 1)⁻¹ ≤ 1 := by
  have hd : (1 : ℝ) ≤ (d : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) d; linarith
  exact ⟨inv_pos.mpr (by positivity), inv_le_one_of_one_le₀ hd⟩

theorem schmidt_step_epsilon_budget {r d : ℕ} (hr : r ≤ d) :
    (r : ℝ) * ((d : ℝ) + 1)⁻¹ ≤ 1 := by
  rw [← div_eq_mul_inv]
  apply (div_le_iff₀ (by positivity : 0 < (d : ℝ) + 1)).mpr
  have hr' : (r : ℝ) ≤ d := by exact_mod_cast hr
  linarith

end Erdos3

end

section

namespace Erdos3

theorem schmidtRadiusFactor_mono {d D : ℕ} {A U : ℝ} (hd : d ≤ D)
    (hA : 0 < A) (hAU : A ≤ U) :
    schmidtRadiusFactor d A ≤ schmidtRadiusFactor D U := by
  have hlog := Real.log_le_log hA hAU
  have hd' : (d : ℝ) ≤ D := by exact_mod_cast hd
  unfold schmidtRadiusFactor
  linarith

theorem schmidtStepFactor_mono (C e : ℕ) {d D : ℕ} {A U : ℝ} (hd : d ≤ D)
    (hA : 1 ≤ A) (hAU : A ≤ U) :
    schmidtStepFactor C e d A ≤ schmidtStepFactor C e D U := by
  have hA0 : 0 ≤ A := by linarith
  have hU0 : 0 ≤ U := hA0.trans hAU
  have hL0 := (schmidtRadiusFactor_pos d hA).le
  have hL := schmidtRadiusFactor_mono hd (by linarith : 0 < A) hAU
  have hd' : (d : ℝ) ≤ D := by exact_mod_cast hd
  have hB := pow_le_pow_left₀ (by positivity : 0 ≤ 8 * A)
    (by linarith : 8 * A ≤ 8 * U) e
  have hC := mul_le_mul_of_nonneg_left hB (Nat.cast_nonneg C : (0 : ℝ) ≤ C)
  have hS := mul_le_mul_of_nonneg_left hAU (Real.exp_pos Real.pi).le
  have hBS := mul_le_mul hC hS (by positivity) (by positivity)
  have hlast : schmidtRadiusFactor d A + (d : ℝ) + 1 ≤
      schmidtRadiusFactor D U + (D : ℝ) + 1 := by linarith
  unfold schmidtStepFactor
  exact add_le_add_right (mul_le_mul hBS hlast (by positivity) (by positivity)) 1

end Erdos3

end

section

namespace Erdos3

noncomputable def schmidtMassMultiplier (d : ℕ) (A : ℝ) : ℝ :=
  Real.exp 10 * ((d : ℝ) + Real.log A + 1) ^ 2

noncomputable def schmidtMassCeiling (d : ℕ) (A : ℝ) : ℝ :=
  A * (schmidtMassMultiplier d A) ^ d

theorem schmidtMassMultiplier_ge_one (d : ℕ) {A : ℝ} (hA : 1 ≤ A) :
    1 ≤ schmidtMassMultiplier d A := by
  have hZ : 1 ≤ (d : ℝ) + Real.log A + 1 := by
    have := Real.log_nonneg hA
    have := Nat.cast_nonneg (α := ℝ) d
    linarith
  have hsq : 1 ≤ ((d : ℝ) + Real.log A + 1) ^ 2 := one_le_pow₀ hZ
  have he : 1 ≤ Real.exp (10 : ℝ) := by linarith [Real.add_one_le_exp (10 : ℝ)]
  change 1 ≤ Real.exp 10 * ((d : ℝ) + Real.log A + 1) ^ 2
  nlinarith

theorem schmidtMassCeiling_ge (d : ℕ) {A : ℝ} (hA : 1 ≤ A) :
    A ≤ schmidtMassCeiling d A :=
  le_mul_of_one_le_right (by linarith) (one_le_pow₀ (schmidtMassMultiplier_ge_one d hA))

theorem schmidtMassBudget_closes (d : ℕ) {A : ℝ} (hA : 1 ≤ A) :
    Real.exp 1 * schmidtRadiusFactor d (schmidtMassCeiling d A) ≤
      schmidtMassMultiplier d A := by
  let Z := (d : ℝ) + Real.log A + 1
  have hApos : 0 < A := by linarith
  have hZ : 1 ≤ Z := by
    dsimp [Z]
    have := Real.log_nonneg hA
    have := Nat.cast_nonneg (α := ℝ) d
    linarith
  have hZpos : 0 < Z := by linarith
  have hDZ : (d : ℝ) ≤ Z := by dsimp [Z]; linarith [Real.log_nonneg hA]
  have hZsq : Z ≤ Z ^ 2 := by nlinarith
  have hDsq : (d : ℝ) ≤ Z ^ 2 := hDZ.trans hZsq
  have hDlog : (d : ℝ) * Real.log Z ≤ Z ^ 2 := by
    have h := mul_le_mul hDZ (Real.log_le_self hZpos.le) (Real.log_nonneg hZ) hZpos.le
    nlinarith
  have hMpos : 0 < schmidtMassMultiplier d A := by
    have := schmidtMassMultiplier_ge_one d hA
    linarith
  have hlogM : Real.log (schmidtMassMultiplier d A) = 10 + 2 * Real.log Z := by
    change Real.log (Real.exp 10 * Z ^ 2) = _
    rw [Real.log_mul (Real.exp_pos _).ne' (pow_pos hZpos 2).ne', Real.log_exp, Real.log_pow]
    norm_num
  have hlogU : Real.log (schmidtMassCeiling d A) = Real.log A + (d : ℝ) * (10 + 2 * Real.log Z) := by
    unfold schmidtMassCeiling
    rw [Real.log_mul hApos.ne' (pow_pos hMpos d).ne', Real.log_pow, hlogM]
  have hLU : schmidtRadiusFactor d (schmidtMassCeiling d A) ≤ 52 * Z ^ 2 := by
    unfold schmidtRadiusFactor
    rw [hlogU]
    have hZeq : (d : ℝ) + Real.log A + 1 = Z := rfl
    nlinarith
  have he : 52 * Real.exp (1 : ℝ) ≤ Real.exp (10 : ℝ) := by
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) htwo 9
    rw [← Real.exp_nat_mul] at hpow
    norm_num at hpow
    calc
      _ ≤ Real.exp 9 * Real.exp 1 := mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; norm_num
  calc
    _ ≤ Real.exp 1 * (52 * Z ^ 2) := mul_le_mul_of_nonneg_left hLU (Real.exp_pos _).le
    _ ≤ Real.exp 10 * Z ^ 2 := by nlinarith [mul_le_mul_of_nonneg_right he (sq_nonneg Z)]
    _ = _ := rfl

end Erdos3

end

section

namespace Erdos3

noncomputable def schmidtDegreeConstant (C e : ℕ) : ℝ :=
  (10 + 8 * Real.exp (4 * Real.pi + 1)) *
    (1 + 2 * Real.exp Real.pi * (C : ℝ) * (8 : ℝ) ^ e)

theorem schmidt_uniform_cost_bounds (C e d : ℕ) {U M : ℝ}
    (hU : 1 ≤ U) (hM : 1 ≤ M) (hLM : Real.exp 1 * schmidtRadiusFactor d U ≤ M) :
    let V := schmidtDegreeConstant C e * U ^ (e + 1) * M ^ 2
    2 ≤ V ∧ 4 * schmidtStepFactor C e d U + 1 ≤ V ∧
      2 * Real.exp (4 * Real.pi + 1) * schmidtRadiusFactor d U * schmidtStepFactor C e d U ≤ V := by
  let b := 2 * Real.exp Real.pi * (C : ℝ) * (8 : ℝ) ^ e
  let X := (1 + b) * U ^ (e + 1) * M
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hU0 : 0 ≤ U := by linarith
  have hM0 : 0 ≤ M := by linarith
  have hL0 := (schmidtRadiusFactor_pos d hU).le
  have he1 : 1 ≤ Real.exp (1 : ℝ) := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hL : schmidtRadiusFactor d U ≤ M := by nlinarith
  have hd : (d : ℝ) + 1 ≤ schmidtRadiusFactor d U := by
    unfold schmidtRadiusFactor
    have := Real.log_nonneg hU
    have := Nat.cast_nonneg (α := ℝ) d
    linarith
  have hpow : 1 ≤ U ^ (e + 1) := one_le_pow₀ hU
  have hUM : 1 ≤ U ^ (e + 1) * M := by nlinarith
  have hX : 1 ≤ X := by dsimp [X]; nlinarith
  have hK : schmidtStepFactor C e d U ≤ X := by
    have hfactor : schmidtRadiusFactor d U + (d : ℝ) + 1 ≤ 2 * M := by linarith
    have hmult := mul_le_mul_of_nonneg_left hfactor
      (show 0 ≤ (C : ℝ) * (8 * U) ^ e * (Real.exp Real.pi * U) by positivity)
    have hid : (C : ℝ) * (8 * U) ^ e * (Real.exp Real.pi * U) * (2 * M) =
        b * (U ^ (e + 1) * M) := by dsimp [b]; rw [mul_pow, pow_succ]; ring
    rw [hid] at hmult
    dsimp [schmidtStepFactor, X]
    nlinarith
  have hXM : X ≤ X * M := le_mul_of_one_le_right (by linarith) hM
  have hXM0 : 0 ≤ X * M := by positivity
  have hVeq : schmidtDegreeConstant C e * U ^ (e + 1) * M ^ 2 =
      (10 + 8 * Real.exp (4 * Real.pi + 1)) * (X * M) := by
    dsimp [schmidtDegreeConstant, X, b]
    ring
  dsimp only
  rw [hVeq]
  have hVlarge : 5 * X ≤ (10 + 8 * Real.exp (4 * Real.pi + 1)) * (X * M) := by
    nlinarith [mul_nonneg (Real.exp_pos (4 * Real.pi + 1)).le hXM0]
  refine ⟨by linarith, by linarith, ?_⟩
  have hK0 := (schmidtStepFactor_bounds C e d hU).1.trans' (by norm_num : (0 : ℝ) ≤ 1)
  have hLK := mul_le_mul hL hK hK0 hM0
  have hscaled := mul_le_mul_of_nonneg_left hLK
    (show 0 ≤ 2 * Real.exp (4 * Real.pi + 1) by positivity)
  nlinarith [mul_nonneg (Real.exp_pos (4 * Real.pi + 1)).le hXM0]

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem schmidt_primitive_dilation_room (α ξ ζ : E) (m p : ℤ) (q j H N : ℕ)
    (hξ : ξ = (m : ℝ) • ζ) (hζ : ζ ≠ 0) (hN : 0 < N)
    {t Q B S ε : ℝ} (hQ : 0 ≤ Q) (hB : 0 ≤ B) (hS : 0 ≤ S)
    (hs : Real.sqrt t ≤ ‖ζ‖ * S)
    (ha : |(((q : ℤ) * m : ℤ) : ℝ)| ≤ Q)
    (happrox : |(q : ℝ) * inner ℝ ξ α - p| ≤ B / (2 * (N : ℝ) + 1) ^ (j + 1))
    (hHQ : (H : ℝ) * Q ≤ N) (hHBS : (H : ℝ) * B * S ≤ ε * N) :
    Real.sqrt t * ((H : ℝ) ^ (j + 1) *
      (CircleFourier.integerDistance
        ((inner ℝ ζ ((((q : ℤ) * m : ℤ) : ℝ) ^ (j + 1) • α) : ℝ) : CircleFourier.Circle) /
        ‖ζ‖)) ≤ ε := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hnorm : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ
  have happrox' : |(q : ℝ) * inner ℝ ξ α - p| ≤ B / (N : ℝ) ^ (j + 1) := by
    apply happrox.trans
    exact div_le_div_of_nonneg_left hB (pow_pos hNR _) (pow_le_pow_left₀ hNR.le (by linarith) _)
  have herr := primitiveNormal_dilation_error α ξ ζ m p q j hξ happrox'
  have hs' : Real.sqrt t / ‖ζ‖ ≤ S := (div_le_iff₀ hnorm).mpr (by nlinarith [hs])
  have hpow := pow_le_pow_left₀ (abs_nonneg (((q : ℤ) * m : ℤ) : ℝ)) ha j
  have herr' := herr.trans (mul_le_mul_of_nonneg_right hpow (div_nonneg hB (pow_nonneg hNR.le _)))
  calc
    _ = ((H : ℝ) ^ (j + 1) * CircleFourier.integerDistance
        ((inner ℝ ζ ((((q : ℤ) * m : ℤ) : ℝ) ^ (j + 1) • α) : ℝ) : CircleFourier.Circle)) *
        (Real.sqrt t / ‖ζ‖) := by ring
    _ ≤ ((H : ℝ) ^ (j + 1) * (Q ^ j * (B / (N : ℝ) ^ (j + 1)))) * S := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left herr' (by positivity)
      · exact hs'
      · exact div_nonneg (Real.sqrt_nonneg _) hnorm.le
      · positivity
    _ = (H : ℝ) ^ (j + 1) * Q ^ j * (B / (N : ℝ) ^ (j + 1)) * S := by ring
    _ ≤ ε := schmidt_monomial_interval_budget j (Nat.cast_nonneg _) hNR hQ hB hS hHQ hHBS

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem exists_schmidt_dilated_mean_transfer
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (α ξ ζ w : E) (m p : ℤ) (q j H N : ℕ)
    (hm : m ≠ 0) (hq : 0 < q) (hξ : ξ = (m : ℝ) • ζ)
    (hζ : ζ ≠ 0) (hζdual : ζ ∈ euclideanDualLattice Λ) (hwΛ : w ∈ Λ) (hw : inner ℝ ζ w = 1)
    (hN : 0 < N) {t Q B S ε L K : ℝ}
    (ht : 0 < t) (hQ : 0 ≤ Q) (hB : 0 ≤ B) (hS : 0 ≤ S) (hL : 0 ≤ L)
    (hε : 0 ≤ ε) (hεone : ε ≤ 1)
    (hbudget : (Module.finrank ℝ (normalFunctional ζ).ker : ℝ) * ε ≤ 1)
    (hs : Real.sqrt t ≤ ‖ζ‖ * S) (hnorm : ‖ζ‖ ≤ Real.sqrt t * L)
    (ha : |(((q : ℤ) * m : ℤ) : ℝ)| ≤ Q)
    (happrox : |(q : ℝ) * inner ℝ ξ α - p| ≤ B / (2 * (N : ℝ) + 1) ^ (j + 1))
    (hHQ : (H : ℝ) * Q ≤ N) (hHBS : (H : ℝ) * B * S ≤ ε * N)
    (hK : 1 ≤ K) (hlength : (N : ℝ) ≤ 2 * K * H) :
    ∃ β : (normalFunctional ζ).ker,
      latticeGaussianMean (latticeHyperplane Λ (normalFunctional ζ))
          (t * (1 + ε) ^ 2) (j + 1) β H ≤
        (2 * Real.exp (4 * Real.pi + 1) * L * K) * latticeGaussianMean Λ t (j + 1) α N ∧
      normalizedLatticeGaussian (latticeHyperplane Λ (normalFunctional ζ))
          (t * (1 + ε) ^ 2) 0 ≤ Real.exp 1 * L * normalizedLatticeGaussian Λ t 0 := by
  have hroom := schmidt_primitive_dilation_room α ξ ζ m p q j H N hξ hζ hN
    hQ hB hS hs ha happrox hHQ hHBS
  obtain ⟨β, hmean, hmass⟩ := exists_schmidt_gaussian_mean_transfer Λ ζ hζ hζdual w hwΛ hw
    ((((q : ℤ) * m : ℤ) : ℝ) ^ (j + 1) • α) ht hε hεone hbudget hroom
  have ha0 : (q : ℤ) * m ≠ 0 := mul_ne_zero (by exact_mod_cast hq.ne') hm
  have hsize : |(((q : ℤ) * m : ℤ) : ℝ)| * H ≤ N := by
    calc
      _ ≤ Q * H := mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg _)
      _ ≤ N := by nlinarith [hHQ]
  have hdilate := latticeGaussianMean_dilation_loss Λ t (j + 1) α ((q : ℤ) * m) ha0 H N
    hsize hK hlength
  have hspos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hmean0 := latticeGaussianMean_nonneg Λ t (j + 1) α N
  have hmass0 := normalizedLatticeGaussian_nonneg Λ t 0
  have hnorm' := mul_le_mul_of_nonneg_left hnorm (Real.exp_pos 1).le
  have hmean' := hmean.trans (mul_le_mul hnorm' hdilate
    (latticeGaussianMean_nonneg Λ t (j + 1) _ H) (by positivity))
  have hmass' := hmass.trans (mul_le_mul_of_nonneg_right hnorm' hmass0)
  refine ⟨β, ?_, ?_⟩
  · have hh := mul_le_mul_of_nonneg_left hmean' (Real.exp_pos (4 * Real.pi)).le
    have he : Real.exp (4 * Real.pi) * Real.exp (-4 * Real.pi) = 1 := by
      rw [← Real.exp_add]
      ring_nf
      exact Real.exp_zero
    have he' : Real.exp (4 * Real.pi) * Real.exp 1 = Real.exp (4 * Real.pi + 1) :=
      (Real.exp_add _ _).symm
    have hleft : Real.exp (4 * Real.pi) *
        (Real.exp (-4 * Real.pi) * Real.sqrt t *
          latticeGaussianMean (latticeHyperplane Λ (normalFunctional ζ))
            (t * (1 + ε) ^ 2) (j + 1) β H) =
        Real.sqrt t * latticeGaussianMean (latticeHyperplane Λ (normalFunctional ζ))
          (t * (1 + ε) ^ 2) (j + 1) β H := by rw [← mul_assoc, ← mul_assoc, he, one_mul]
    rw [hleft] at hh
    have hright : Real.exp (4 * Real.pi) *
        (Real.exp 1 * (Real.sqrt t * L) * (2 * K * latticeGaussianMean Λ t (j + 1) α N)) =
        Real.sqrt t * ((2 * Real.exp (4 * Real.pi + 1) * L * K) *
          latticeGaussianMean Λ t (j + 1) α N) := by rw [← he']; ring
    rw [hright] at hh
    exact (mul_le_mul_iff_right₀ hspos).mp hh
  · have hright : Real.exp 1 * (Real.sqrt t * L) * normalizedLatticeGaussian Λ t 0 =
        Real.sqrt t * (Real.exp 1 * L * normalizedLatticeGaussian Λ t 0) := by ring
    rw [hright] at hmass'
    exact (mul_le_mul_iff_right₀ hspos).mp hmass'

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem PolynomialIntervalPowerBound.dimension_reduction {j C e : ℕ}
    (hW : PolynomialIntervalPowerBound (j + 1) C e)
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {t : ℝ} (ht : 0 < t) (α : E) (N : ℕ)
    (hN : 2 * schmidtStepFactor C e (Module.finrank ℝ E) (normalizedLatticeGaussian Λ t 0) ≤ N)
    (hsmall : latticeGaussianMean Λ t (j + 1) α N < 1 / 2) :
    let A := normalizedLatticeGaussian Λ t 0
    let d := Module.finrank ℝ E
    let L := schmidtRadiusFactor d A
    let K := schmidtStepFactor C e d A
    let ε := ((d : ℝ) + 1)⁻¹
    ∃ (ζ : E) (H : ℕ) (β : (normalFunctional ζ).ker),
      ζ ≠ 0 ∧ ζ ∈ euclideanDualLattice Λ ∧
      IsZLattice ℝ (latticeHyperplane Λ (normalFunctional ζ)) ∧
      Module.finrank ℝ (normalFunctional ζ).ker + 1 = d ∧
      0 < H ∧ K * H ≤ N ∧ (N : ℝ) ≤ 2 * K * H ∧
      latticeGaussianMean (latticeHyperplane Λ (normalFunctional ζ))
          (t * (1 + ε) ^ 2) (j + 1) β H ≤
        (2 * Real.exp (4 * Real.pi + 1) * L * K) * latticeGaussianMean Λ t (j + 1) α N ∧
      normalizedLatticeGaussian (latticeHyperplane Λ (normalFunctional ζ))
          (t * (1 + ε) ^ 2) 0 ≤ Real.exp 1 * L * A := by
  let A := normalizedLatticeGaussian Λ t 0
  let d := Module.finrank ℝ E
  let L := schmidtRadiusFactor d A
  let K := schmidtStepFactor C e d A
  let ε := ((d : ℝ) + 1)⁻¹
  let B := (C : ℝ) * (8 * A) ^ e
  let S := Real.exp Real.pi * A
  have hA : 1 ≤ A := normalizedLatticeGaussian_origin_ge_one Λ ht
  have hA0 : 0 ≤ A := by linarith
  have hL : 0 < L := schmidtRadiusFactor_pos d hA
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  obtain ⟨hK, hBK, hQK, hSK⟩ := schmidtStepFactor_bounds C e d hA
  change 1 ≤ K at hK
  change B ≤ K at hBK
  change B * (L * S) ≤ K at hQK
  change B * S ≤ ε * K at hSK
  change 2 * K ≤ N at hN
  have hKpos : 0 < K := by linarith
  have hNpos : 0 < N := by
    have : (0 : ℝ) < N := by linarith
    exact_mod_cast this
  have hsize : B ≤ 2 * (N : ℝ) + 1 := by linarith
  obtain ⟨ξ, hξdual, hξ, hξnorm, q, hq, hqB, p, hp⟩ :=
    hW.short_dual_vector Λ ht α N hsize hsmall
  obtain ⟨m, ζ, w, hm, hsplit, hζ, hζnorm, hζdual, hwΛ, hw, hs, hmLS⟩ :=
    exists_temperature_bounded_primitive_normal Λ ξ hξ hξdual ht hL.le hξnorm
  change Real.sqrt t ≤ ‖ζ‖ * S at hs
  change |(m : ℝ)| ≤ L * S at hmLS
  have hqB' : (q : ℝ) ≤ B := hqB
  have ha : |(((q : ℤ) * m : ℤ) : ℝ)| ≤ B * (L * S) := by
    rw [Int.cast_mul, Int.cast_natCast, abs_mul, Nat.abs_cast]
    exact mul_le_mul hqB' hmLS (abs_nonneg _) hB
  obtain ⟨H, hH, hHN, hNH⟩ := exists_schmidt_shorter_interval hKpos N hN
  have hHQ : (H : ℝ) * (B * (L * S)) ≤ N := by
    have hh := mul_le_mul_of_nonneg_left hQK (Nat.cast_nonneg H : (0 : ℝ) ≤ H)
    nlinarith [hh]
  obtain ⟨hε, hεone⟩ := schmidt_step_epsilon_bounds d
  have hHBS : (H : ℝ) * B * S ≤ ε * N := by
    have hh := mul_le_mul_of_nonneg_left hSK (Nat.cast_nonneg H : (0 : ℝ) ≤ H)
    have hh' := mul_le_mul_of_nonneg_left hHN hε.le
    nlinarith [hh, hh']
  have hdim : Module.finrank ℝ (normalFunctional ζ).ker + 1 = d :=
    hyperplane_finrank (normalFunctional ζ) w hw
  have hbudget : (Module.finrank ℝ (normalFunctional ζ).ker : ℝ) * ε ≤ 1 :=
    schmidt_step_epsilon_budget (by omega : Module.finrank ℝ (normalFunctional ζ).ker ≤ d)
  have hΓ := latticeHyperplane_isZLattice Λ (normalFunctional ζ)
    ((mem_euclideanDualLattice Λ ζ).mp hζdual) w hwΛ hw
  obtain ⟨β, hmean, hmass⟩ := exists_schmidt_dilated_mean_transfer Λ α ξ ζ w m p q j H N
    hm hq hsplit hζ hζdual hwΛ hw hNpos ht (by positivity) hB hS hL.le
    hε.le hεone hbudget hs hζnorm ha hp hHQ hHBS hK hNH
  exact ⟨ζ, H, β, hζ, hζdual, hΓ, hdim, hH, hHN, hNH, hmean, hmass⟩

end Erdos3

end

section

namespace Erdos3

theorem one_le_power_mul_of_one_le_mul {V F : ℝ} (hV : 1 ≤ V) (hF : 0 ≤ F)
    (h : 1 ≤ V * F) (d : ℕ) : 1 ≤ V ^ (d + 1) * F := by
  calc
    1 ≤ V * F := h
    _ ≤ V ^ d * (V * F) :=
      le_mul_of_one_le_left (mul_nonneg (by linarith) hF) (one_le_pow₀ hV)
    _ = V ^ (d + 1) * F := by rw [pow_succ]; ring

theorem PolynomialIntervalPowerBound.gaussian_mean_iteration
    {j C e D : ℕ} (hW : PolynomialIntervalPowerBound (j + 1) C e)
    {M U V : ℝ} (hM : 1 ≤ M) (hU : 1 ≤ U)
    (hLM : Real.exp 1 * schmidtRadiusFactor D U ≤ M)
    (hV : 2 ≤ V) (hKV : 4 * schmidtStepFactor C e D U + 1 ≤ V)
    (hTV : 2 * Real.exp (4 * Real.pi + 1) * schmidtRadiusFactor D U *
      schmidtStepFactor C e D U ≤ V) (d : ℕ) :
    ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
      (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
      {t : ℝ}, 0 < t → ∀ (α : E) (N : ℕ),
      Module.finrank ℝ E = d → d ≤ D →
      normalizedLatticeGaussian Λ t 0 * M ^ d ≤ U →
      1 ≤ V ^ (d + 1) * latticeGaussianMean Λ t (j + 1) α N := by
  have hVone : 1 ≤ V := by linarith
  have hV0 : 0 ≤ V := by linarith
  have hM0 : 0 ≤ M := by linarith
  induction d with
  | zero =>
    intro E _ _ _ _ _ Λ _ _ t ht α N hdim hd hmass
    rw [latticeGaussianMean_of_finrank_zero Λ hdim]
    simpa using hVone
  | succ d ih =>
    intro E _ _ _ _ _ Λ _ _ t ht α N hdim hd hmass
    have hA := normalizedLatticeGaussian_origin_ge_one Λ ht
    have hA0 : 0 ≤ normalizedLatticeGaussian Λ t 0 := by linarith
    have hAU : normalizedLatticeGaussian Λ t 0 ≤ U := by
      exact (le_mul_of_one_le_right hA0 (one_le_pow₀ hM)).trans hmass
    have hdimD : Module.finrank ℝ E ≤ D := by omega
    have hL := schmidtRadiusFactor_mono hdimD (by linarith : 0 < normalizedLatticeGaussian Λ t 0) hAU
    have hK := schmidtStepFactor_mono C e hdimD hA hAU
    have hF0 := latticeGaussianMean_nonneg Λ t (j + 1) α N
    by_cases hsmall : latticeGaussianMean Λ t (j + 1) α N < 1 / 2
    · by_cases hN : 2 * schmidtStepFactor C e (Module.finrank ℝ E)
          (normalizedLatticeGaussian Λ t 0) ≤ (N : ℝ)
      · obtain ⟨ζ, H, β, hζ, hζdual, hΓ, hdrop, hH, hHN, hNH, hmean, hmass'⟩ :=
          hW.dimension_reduction Λ ht α N hN hsmall
        let : IsZLattice ℝ (latticeHyperplane Λ (normalFunctional ζ)) := hΓ
        have hdim' : Module.finrank ℝ (normalFunctional ζ).ker = d := by omega
        have ht' : 0 < t * (1 + ((Module.finrank ℝ E : ℝ) + 1)⁻¹) ^ 2 := by positivity
        have hLM' : Real.exp 1 * schmidtRadiusFactor (Module.finrank ℝ E)
            (normalizedLatticeGaussian Λ t 0) ≤ M :=
          (mul_le_mul_of_nonneg_left hL (Real.exp_pos 1).le).trans hLM
        have hmassM := hmass'.trans (mul_le_mul_of_nonneg_right hLM' hA0)
        have hinvariant : normalizedLatticeGaussian (latticeHyperplane Λ (normalFunctional ζ))
            (t * (1 + ((Module.finrank ℝ E : ℝ) + 1)⁻¹) ^ 2) 0 * M ^ d ≤ U := by
          calc
            _ ≤ (M * normalizedLatticeGaussian Λ t 0) * M ^ d :=
              mul_le_mul_of_nonneg_right hmassM (pow_nonneg hM0 _)
            _ = normalizedLatticeGaussian Λ t 0 * M ^ (d + 1) := by rw [pow_succ]; ring
            _ ≤ U := hmass
        have hih := ih (normalFunctional ζ).ker (latticeHyperplane Λ (normalFunctional ζ))
          ht' β H hdim' (by omega) hinvariant
        have hT : 2 * Real.exp (4 * Real.pi + 1) *
            schmidtRadiusFactor (Module.finrank ℝ E) (normalizedLatticeGaussian Λ t 0) *
            schmidtStepFactor C e (Module.finrank ℝ E) (normalizedLatticeGaussian Λ t 0) ≤ V := by
          apply le_trans _ hTV
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left hL (by positivity)
          · exact hK
          · exact (schmidtStepFactor_bounds C e (Module.finrank ℝ E) hA).1.trans' (by norm_num)
          · have := (schmidtRadiusFactor_pos D hU).le; positivity
        have hmeanV := hmean.trans (mul_le_mul_of_nonneg_right hT hF0)
        calc
          1 ≤ V ^ (d + 1) * latticeGaussianMean (latticeHyperplane Λ (normalFunctional ζ))
              (t * (1 + ((Module.finrank ℝ E : ℝ) + 1)⁻¹) ^ 2) (j + 1) β H := hih
          _ ≤ V ^ (d + 1) * (V * latticeGaussianMean Λ t (j + 1) α N) :=
            mul_le_mul_of_nonneg_left hmeanV (pow_nonneg hV0 _)
          _ = V ^ (d + 1 + 1) * latticeGaussianMean Λ t (j + 1) α N := by rw [pow_succ]; ring
      · have hzero := hA.trans (latticeGaussianMean_zero_term Λ t j N α)
        have hNV : 2 * (N : ℝ) + 1 ≤ V := by linarith
        have hVF := hzero.trans (mul_le_mul_of_nonneg_right hNV hF0)
        exact one_le_power_mul_of_one_le_mul hVone hF0 hVF (d + 1)
    · have hVF : 1 ≤ V * latticeGaussianMean Λ t (j + 1) α N := by nlinarith
      exact one_le_power_mul_of_one_le_mul hVone hF0 hVF (d + 1)

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem PolynomialIntervalPowerBound.gaussian_mean_lower_bound {j C e : ℕ}
    (hW : PolynomialIntervalPowerBound (j + 1) C e)
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {t : ℝ} (ht : 0 < t) (α : E) (N : ℕ) :
    let A := normalizedLatticeGaussian Λ t 0
    let d := Module.finrank ℝ E
    let M := schmidtMassMultiplier d A
    1 ≤ (schmidtDegreeConstant C e * A ^ (e + 1) * M ^ (d * (e + 1) + 2)) ^ (d + 1) *
      latticeGaussianMean Λ t (j + 1) α N := by
  let A := normalizedLatticeGaussian Λ t 0
  let d := Module.finrank ℝ E
  let M := schmidtMassMultiplier d A
  let U := schmidtMassCeiling d A
  have hA : 1 ≤ A := normalizedLatticeGaussian_origin_ge_one Λ ht
  have hM : 1 ≤ M := schmidtMassMultiplier_ge_one d hA
  have hU : 1 ≤ U := hA.trans (schmidtMassCeiling_ge d hA)
  have hLM := schmidtMassBudget_closes d hA
  obtain ⟨hV, hKV, hTV⟩ := schmidt_uniform_cost_bounds C e d hU hM hLM
  have h := hW.gaussian_mean_iteration hM hU hLM hV hKV hTV d E Λ ht α N rfl le_rfl le_rfl
  have hid : schmidtDegreeConstant C e * U ^ (e + 1) * M ^ 2 =
      schmidtDegreeConstant C e * A ^ (e + 1) * M ^ (d * (e + 1) + 2) := by
    change schmidtDegreeConstant C e * (A * M ^ d) ^ (e + 1) * M ^ 2 = _
    rw [mul_pow, ← pow_mul, pow_add]
    ring
  rw [hid] at h
  exact h

theorem schmidt_gaussian_mean_lower_bound (j : ℕ) :
    ∃ C e : ℕ, 0 < C ∧ 0 < e ∧
      ∀ (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F]
        [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
        (Λ : Submodule ℤ F) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
        (t : ℝ) (α : F) (N : ℕ), 0 < t →
        let A := normalizedLatticeGaussian Λ t 0
        let d := Module.finrank ℝ F
        let M := schmidtMassMultiplier d A
        1 ≤ (schmidtDegreeConstant C e * A ^ (e + 1) * M ^ (d * (e + 1) + 2)) ^ (d + 1) *
          latticeGaussianMean Λ t (j + 1) α N := by
  obtain ⟨C, e, hC, he, hW⟩ := polynomial_weyl_inverse_power_interval j
  exact ⟨C, e, hC, he, fun F _ _ _ _ _ Λ _ _ t α N ht =>
    hW.gaussian_mean_lower_bound Λ ht α N⟩

end Erdos3

end

section

namespace Erdos3

noncomputable def schmidtMeanDenominator (C e d : ℕ) (A : ℝ) : ℝ :=
  (schmidtDegreeConstant C e * A ^ (e + 1) *
    (schmidtMassMultiplier d A) ^ (d * (e + 1) + 2)) ^ (d + 1)

theorem schmidtMeanDenominator_pos (C e d : ℕ) {A : ℝ} (hA : 1 ≤ A) :
    0 < schmidtMeanDenominator C e d A := by
  have hApos : 0 < A := by linarith
  have hMpos : 0 < schmidtMassMultiplier d A := by
    have := schmidtMassMultiplier_ge_one d hA
    linarith
  unfold schmidtMeanDenominator schmidtDegreeConstant
  positivity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem exists_positive_lattice_approx_of_gaussian_mean
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (α : E) (j N : ℕ) {t R D : ℝ} (ht : 0 < t) (hR : 0 ≤ R) (hD : 0 < D)
    (hmean : 1 ≤ D * latticeGaussianMean Λ t (j + 1) α N)
    (hlength : 2 * D * normalizedLatticeGaussian Λ t 0 < 2 * (N : ℝ) + 1)
    (htail : 2 * D * (Real.exp (-Real.pi * t * R ^ 2 / 2) *
      (2 : ℝ) ^ Module.finrank ℝ E * normalizedLatticeGaussian Λ t 0) < 1) :
    ∃ q : ℕ, 0 < q ∧ q ≤ N ∧ ∃ v ∈ Λ, ‖(q : ℝ) ^ (j + 1) • α - v‖ < R := by
  obtain ⟨n, hn, hnN, hscore⟩ := exists_nonzero_index_of_gaussian_mean Λ t α j N hD
    (show 0 ≤ Real.exp (-Real.pi * t * R ^ 2 / 2) *
      (2 : ℝ) ^ Module.finrank ℝ E * normalizedLatticeGaussian Λ t 0 from
      mul_nonneg (by positivity) (normalizedLatticeGaussian_nonneg Λ t 0)) hmean hlength htail
  have hnear : ∃ m : Λ, ‖(n : ℝ) ^ (j + 1) • α - (m : E)‖ < R := by
    by_contra! hfar
    exact (normalizedLatticeGaussian_le_of_far Λ ht hR _ hfar).not_gt hscore
  obtain ⟨m, hm⟩ := hnear
  exact exists_positive_monomial_index Λ α (j + 1) N n hn hnN (m : E) m.property hm

theorem PolynomialIntervalPowerBound.lattice_recurrence {j C e : ℕ}
    (hW : PolynomialIntervalPowerBound (j + 1) C e)
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (α : E) (N : ℕ) {t R : ℝ} (ht : 0 < t) (hR : 0 ≤ R)
    (hlength : 2 * schmidtMeanDenominator C e (Module.finrank ℝ E) (normalizedLatticeGaussian Λ t 0) *
      normalizedLatticeGaussian Λ t 0 < 2 * (N : ℝ) + 1)
    (htail : 2 * schmidtMeanDenominator C e (Module.finrank ℝ E) (normalizedLatticeGaussian Λ t 0) *
      (Real.exp (-Real.pi * t * R ^ 2 / 2) * (2 : ℝ) ^ Module.finrank ℝ E *
        normalizedLatticeGaussian Λ t 0) < 1) :
    ∃ q : ℕ, 0 < q ∧ q ≤ N ∧ ∃ v ∈ Λ, ‖(q : ℝ) ^ (j + 1) • α - v‖ < R := by
  exact exists_positive_lattice_approx_of_gaussian_mean Λ α j N ht hR
    (schmidtMeanDenominator_pos C e _ (normalizedLatticeGaussian_origin_ge_one Λ ht))
    (hW.gaussian_mean_lower_bound Λ ht α N) hlength htail

end Erdos3

end

section

namespace Erdos3

def schmidtRecurrenceExponent (e : ℕ) : ℕ := 15 * (e + 1) + 23

theorem schmidt_recurrence_mass_bounds (d : ℕ) {A X : ℝ}
    (hX : 2 ≤ X) (hd : (d : ℝ) + 1 ≤ X) (hconst : 121 * Real.exp 10 ≤ X)
    (hA : 1 ≤ A) (hAU : A ≤ (1 + 2 * X ^ 8) ^ d) :
    A ≤ X ^ (10 * d) ∧ schmidtMassMultiplier d A ≤ X ^ 5 := by
  have hX0 : 0 ≤ X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have hX8 : 1 ≤ X ^ 8 := one_le_pow₀ hX1
  have hX2 : 3 ≤ X ^ 2 := by nlinarith
  have hbase : 1 + 2 * X ^ 8 ≤ X ^ 10 := by
    have h := mul_le_mul_of_nonneg_right hX2 (pow_nonneg hX0 8)
    have heq : X ^ 2 * X ^ 8 = X ^ 10 := by ring
    rw [heq] at h
    nlinarith
  have hAX : A ≤ X ^ (10 * d) := by
    calc
      A ≤ (1 + 2 * X ^ 8) ^ d := hAU
      _ ≤ (X ^ 10) ^ d := pow_le_pow_left₀ (by positivity) hbase d
      _ = _ := (pow_mul X 10 d).symm
  refine ⟨hAX, ?_⟩
  have hApos : 0 < A := by linarith
  have hlogA : Real.log A ≤ (10 * (d : ℝ)) * Real.log X := by
    have h := Real.log_le_log hApos hAX
    simpa only [Real.log_pow, Nat.cast_mul, Nat.cast_ofNat] using h
  have hdX : (d : ℝ) ≤ X := by linarith
  have hlogX0 := Real.log_nonneg hX1
  have hprod : (d : ℝ) * Real.log X ≤ X ^ 2 := by
    have h := mul_le_mul hdX (Real.log_le_self hX0) hlogX0 hX0
    nlinarith
  have hZ0 : 0 ≤ (d : ℝ) + Real.log A + 1 := by
    have := Real.log_nonneg hA
    positivity
  have hZ : (d : ℝ) + Real.log A + 1 ≤ 11 * X ^ 2 := by nlinarith
  have hsq := pow_le_pow_left₀ hZ0 hZ 2
  calc
    schmidtMassMultiplier d A ≤ Real.exp 10 * (11 * X ^ 2) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (Real.exp_pos _).le
    _ = (121 * Real.exp 10) * X ^ 4 := by ring
    _ ≤ X * X ^ 4 := mul_le_mul_of_nonneg_right hconst (pow_nonneg hX0 4)
    _ = X ^ 5 := by ring

theorem schmidt_recurrence_denominator_bound (C e d : ℕ) {A X : ℝ}
    (hX : 2 ≤ X) (hA : 1 ≤ A) (hc : schmidtDegreeConstant C e ≤ X)
    (hAX : A ≤ X ^ (10 * d)) (hMX : schmidtMassMultiplier d A ≤ X ^ 5) :
    2 * schmidtMeanDenominator C e d A * (2 : ℝ) ^ d * A ≤
      X ^ (schmidtRecurrenceExponent e * (d + 1) ^ 2) := by
  have hX0 : 0 ≤ X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have hA0 : 0 ≤ A := by linarith
  have hc0 : 0 ≤ schmidtDegreeConstant C e := by unfold schmidtDegreeConstant; positivity
  have hM0 : 0 ≤ schmidtMassMultiplier d A := by unfold schmidtMassMultiplier; positivity
  have hinner : schmidtDegreeConstant C e * A ^ (e + 1) *
      schmidtMassMultiplier d A ^ (d * (e + 1) + 2) ≤ X ^ (15 * d * (e + 1) + 11) := by
    have hmul := mul_le_mul (mul_le_mul hc (pow_le_pow_left₀ hA0 hAX (e + 1))
      (pow_nonneg hA0 _) hX0)
      (pow_le_pow_left₀ hM0 hMX (d * (e + 1) + 2))
      (pow_nonneg hM0 _) (by positivity)
    calc
      _ ≤ X * (X ^ (10 * d)) ^ (e + 1) * (X ^ 5) ^ (d * (e + 1) + 2) := hmul
      _ = X ^ (15 * d * (e + 1) + 11) := by
        rw [← pow_mul, ← pow_mul, ← pow_succ', ← pow_add]
        congr 1
        ring
  have hD := pow_le_pow_left₀ (by positivity) hinner (d + 1)
  change schmidtMeanDenominator C e d A ≤ (X ^ (15 * d * (e + 1) + 11)) ^ (d + 1) at hD
  rw [← pow_mul] at hD
  have hD0 := (schmidtMeanDenominator_pos C e d hA).le
  have htwo := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hX d
  have htotal := mul_le_mul (mul_le_mul (mul_le_mul hX hD hD0 hX0) htwo
    (by positivity) (by positivity)) hAX hA0 (by positivity)
  calc
    _ ≤ X * X ^ ((15 * d * (e + 1) + 11) * (d + 1)) * X ^ d * X ^ (10 * d) := htotal
    _ = X ^ (((15 * d * (e + 1) + 11) * (d + 1) + 1) + d + 10 * d) := by
      rw [← pow_succ', ← pow_add, ← pow_add]
    _ ≤ _ := by
      apply pow_le_pow_right₀ hX1
      unfold schmidtRecurrenceExponent
      nlinarith

end Erdos3

end

section

namespace Erdos3

theorem monomial_recurrence_tail_budget (p d : ℕ) {X R : ℝ}
    (hX : 2 ≤ X) (hd : (d : ℝ) + 1 ≤ X) (hp : (p : ℝ) ≤ X)
    (hXR : 1 ≤ X * R) :
    X ^ (p * (d + 1) ^ 2) * Real.exp (-Real.pi * X ^ 8 * R ^ 2 / 2) < 1 := by
  have hX0 : 0 ≤ X := by linarith
  have hXpos : 0 < X := by linarith
  have hlog0 : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hlog : Real.log X ≤ X := Real.log_le_self hX0
  have hsq := pow_le_pow_left₀ (show 0 ≤ (d : ℝ) + 1 by positivity) hd 2
  have hdegree : (p : ℝ) * ((d : ℝ) + 1) ^ 2 ≤ X ^ 3 := by
    have h := mul_le_mul hp hsq (sq_nonneg _) hX0
    nlinarith
  have hexponent : ((p * (d + 1) ^ 2 : ℕ) : ℝ) * Real.log X ≤ X ^ 4 := by
    have h := mul_le_mul hdegree hlog hlog0 (pow_nonneg hX0 3)
    push_cast
    nlinarith
  have hpower : X ^ (p * (d + 1) ^ 2) ≤ Real.exp (X ^ 4) := by
    calc
      _ = Real.exp (((p * (d + 1) ^ 2 : ℕ) : ℝ) * Real.log X) := by
        rw [Real.exp_nat_mul, Real.exp_log hXpos]
      _ ≤ _ := Real.exp_le_exp.mpr hexponent
  have hXR2 : 1 ≤ (X * R) ^ 2 := one_le_pow₀ hXR
  have henergy : X ^ 6 ≤ X ^ 8 * R ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hXR2 (pow_nonneg hX0 6)
    nlinarith [show X ^ 6 * (X * R) ^ 2 = X ^ 8 * R ^ 2 by ring]
  have h6 : 4 * X ^ 4 ≤ X ^ 6 := by
    have hx2 : (4 : ℝ) ≤ X ^ 2 := by nlinarith
    have h := mul_le_mul_of_nonneg_right hx2 (pow_nonneg hX0 4)
    nlinarith [show X ^ 2 * X ^ 4 = X ^ 6 by ring]
  have hnegative : X ^ 4 + (-Real.pi * X ^ 8 * R ^ 2 / 2) < 0 := by
    have hE0 : 0 ≤ X ^ 8 * R ^ 2 := by positivity
    have hpi := mul_nonneg (show 0 ≤ Real.pi - 3 by linarith [Real.pi_gt_three]) hE0
    have h4 : 0 < X ^ 4 := pow_pos hXpos _
    nlinarith
  calc
    _ ≤ Real.exp (X ^ 4) * Real.exp (-Real.pi * X ^ 8 * R ^ 2 / 2) :=
      mul_le_mul_of_nonneg_right hpower (Real.exp_pos _).le
    _ = Real.exp (X ^ 4 + (-Real.pi * X ^ 8 * R ^ 2 / 2)) := (Real.exp_add _ _).symm
    _ < 1 := Real.exp_lt_one_iff.mpr hnegative

theorem schmidt_recurrence_numeric_conditions (C e d N : ℕ) {A X R : ℝ}
    (hX : 2 ≤ X) (hd : (d : ℝ) + 1 ≤ X) (hp : (schmidtRecurrenceExponent e : ℝ) ≤ X)
    (hconst : 121 * Real.exp 10 ≤ X) (hc : schmidtDegreeConstant C e ≤ X)
    (hXR : 1 ≤ X * R) (hA : 1 ≤ A) (hAU : A ≤ (1 + 2 * X ^ 8) ^ d)
    (hN : X ^ (schmidtRecurrenceExponent e * (d + 1) ^ 2) ≤ N) :
    2 * schmidtMeanDenominator C e d A * A < 2 * (N : ℝ) + 1 ∧
      2 * schmidtMeanDenominator C e d A *
        (Real.exp (-Real.pi * X ^ 8 * R ^ 2 / 2) * (2 : ℝ) ^ d * A) < 1 := by
  obtain ⟨hAX, hMX⟩ := schmidt_recurrence_mass_bounds d hX hd hconst hA hAU
  have hbound := schmidt_recurrence_denominator_bound C e d hX hA hc hAX hMX
  have hD0 := (schmidtMeanDenominator_pos C e d hA).le
  have hA0 : 0 ≤ A := by linarith
  constructor
  · have htwo : 1 ≤ (2 : ℝ) ^ d := one_le_pow₀ (by norm_num)
    have hmul := mul_le_mul_of_nonneg_left htwo (show 0 ≤ 2 * schmidtMeanDenominator C e d A * A by positivity)
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  · have hmul := mul_le_mul_of_nonneg_right hbound
      (Real.exp_pos (-Real.pi * X ^ 8 * R ^ 2 / 2)).le
    have htail := monomial_recurrence_tail_budget (schmidtRecurrenceExponent e) d hX hd hp hXR
    nlinarith

end Erdos3

end

section

namespace Erdos3

noncomputable def schmidtRecurrenceBase (C e : ℕ) : ℝ :=
  2 + 121 * Real.exp 10 + schmidtDegreeConstant C e + schmidtRecurrenceExponent e

theorem schmidtRecurrenceBase_bounds (C e : ℕ) :
    2 ≤ schmidtRecurrenceBase C e ∧ 121 * Real.exp 10 ≤ schmidtRecurrenceBase C e ∧
      schmidtDegreeConstant C e ≤ schmidtRecurrenceBase C e ∧
      (schmidtRecurrenceExponent e : ℝ) ≤ schmidtRecurrenceBase C e := by
  have hc : 0 ≤ schmidtDegreeConstant C e := by unfold schmidtDegreeConstant; positivity
  have hp : (0 : ℝ) ≤ schmidtRecurrenceExponent e := Nat.cast_nonneg _
  have he := (Real.exp_pos (10 : ℝ)).le
  unfold schmidtRecurrenceBase
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem PolynomialIntervalPowerBound.simultaneous_monomial_recurrence_at_scale
    {j C e : ℕ} (hW : PolynomialIntervalPowerBound (j + 1) C e)
    {ι : Type*} [Fintype ι] (α : ι → ℝ) (N : ℕ) {X R : ℝ}
    (hX : schmidtRecurrenceBase C e ≤ X) (hd : (Fintype.card ι : ℝ) + 1 ≤ X)
    (hR : 0 < R) (hXR : 1 ≤ X * R)
    (hN : X ^ (schmidtRecurrenceExponent e * (Fintype.card ι + 1) ^ 2) ≤ N) :
    ∃ q : ℕ, 0 < q ∧ q ≤ N ∧ ∃ m : ι → ℤ, ∀ i, |(q : ℝ) ^ (j + 1) * α i - m i| < R := by
  obtain ⟨h2, hconst, hc, hp⟩ := schmidtRecurrenceBase_bounds C e
  have hXpos : 0 < X := by linarith
  have ht : 0 < X ^ 8 := pow_pos hXpos _
  let a : EuclideanSpace ℝ ι := WithLp.toLp 2 α
  have hA := normalizedLatticeGaussian_origin_ge_one (standardEuclideanLattice ι) ht
  have hAU := standardLatticeGaussian_origin_bound ι ht
  obtain ⟨hlength, htail⟩ := schmidt_recurrence_numeric_conditions C e (Fintype.card ι) N
    (h2.trans hX) hd (hp.trans hX) (hconst.trans hX) (hc.trans hX) hXR hA hAU hN
  obtain ⟨q, hq, hqN, v, hv, hclose⟩ := hW.lattice_recurrence (standardEuclideanLattice ι) a N ht hR.le
    (by simpa only [finrank_euclideanSpace] using hlength)
    (by simpa only [finrank_euclideanSpace] using htail)
  choose m hm using (mem_standardEuclideanLattice ι v).mp hv
  refine ⟨q, hq, hqN, m, fun i => ?_⟩
  calc
    |(q : ℝ) ^ (j + 1) * α i - m i| = ‖((q : ℝ) ^ (j + 1) • a - v) i‖ := by
      change _ = |(q : ℝ) ^ (j + 1) * α i - v i|
      rw [hm i]
    _ ≤ ‖(q : ℝ) ^ (j + 1) • a - v‖ := PiLp.norm_apply_le _ i
    _ < R := hclose

theorem PolynomialIntervalPowerBound.simultaneous_monomial_recurrence
    {j C e : ℕ} (hW : PolynomialIntervalPowerBound (j + 1) C e)
    {ι : Type*} [Fintype ι] (α : ι → ℝ) (N : ℕ) {R : ℝ}
    (hR : 0 < R) (hR1 : R ≤ 1)
    (hN : (schmidtRecurrenceBase C e * ((Fintype.card ι : ℝ) + 1) / R) ^
      (schmidtRecurrenceExponent e * (Fintype.card ι + 1) ^ 2) ≤ N) :
    ∃ q : ℕ, 0 < q ∧ q ≤ N ∧ ∃ m : ι → ℤ, ∀ i, |(q : ℝ) ^ (j + 1) * α i - m i| < R := by
  have hK := (schmidtRecurrenceBase_bounds C e).1
  have hd : (1 : ℝ) ≤ (Fintype.card ι : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) (Fintype.card ι); linarith
  have hK0 : 0 ≤ schmidtRecurrenceBase C e := by linarith
  have hd0 : 0 ≤ (Fintype.card ι : ℝ) + 1 := by linarith
  have hbase : schmidtRecurrenceBase C e ≤
      schmidtRecurrenceBase C e * ((Fintype.card ι : ℝ) + 1) / R := by
    apply (le_div_iff₀ hR).mpr
    nlinarith
  have hdim : (Fintype.card ι : ℝ) + 1 ≤
      schmidtRecurrenceBase C e * ((Fintype.card ι : ℝ) + 1) / R := by
    apply (le_div_iff₀ hR).mpr
    nlinarith
  have hprod : 1 ≤ (schmidtRecurrenceBase C e * ((Fintype.card ι : ℝ) + 1) / R) * R := by
    rw [div_mul_cancel₀ _ hR.ne']
    nlinarith
  exact hW.simultaneous_monomial_recurrence_at_scale α N hbase hdim hR hprod hN

theorem simultaneous_monomial_recurrence (j : ℕ) :
    ∃ (K : ℝ) (p : ℕ), 1 ≤ K ∧ 0 < p ∧
      ∀ (ι : Type*) [Fintype ι] (α : ι → ℝ) (N : ℕ) (R : ℝ), 0 < R → R ≤ 1 →
        (K * ((Fintype.card ι : ℝ) + 1) / R) ^ (p * (Fintype.card ι + 1) ^ 2) ≤ N →
        ∃ q : ℕ, 0 < q ∧ q ≤ N ∧ ∃ m : ι → ℤ, ∀ i, |(q : ℝ) ^ (j + 1) * α i - m i| < R := by
  obtain ⟨C, e, hC, he, hW⟩ := polynomial_weyl_inverse_power_interval j
  refine ⟨schmidtRecurrenceBase C e, schmidtRecurrenceExponent e,
    (show 1 ≤ schmidtRecurrenceBase C e by linarith [(schmidtRecurrenceBase_bounds C e).1]), ?_, ?_⟩
  · unfold schmidtRecurrenceExponent
    omega
  · intro ι _ α N R hR hR1 hN
    exact hW.simultaneous_monomial_recurrence α N hR hR1 hN

end Erdos3

end

section

namespace Erdos3

open Polynomial

theorem PolynomialIntervalPowerBound.polynomial_coordinate_reduction
    {j C e : ℕ} (hW : PolynomialIntervalPowerBound (j + 1) C e)
    {ι : Type*} [Fintype ι] (P : ι → Polynomial ℝ)
    (hP : ∀ i, (P i).natDegree ≤ j + 1) (H : ℕ) (hH : 0 < H)
    (hsize : schmidtRecurrenceBase C e * ((Fintype.card ι : ℝ) + 1) ≤ H) :
    ∃ q : ℕ, 0 < q ∧
      q ≤ H ^ ((j + 3) * schmidtRecurrenceExponent e * (Fintype.card ι + 1) ^ 2) ∧
      ∃ m : ι → ℤ, ∀ a : ℝ, ∃ R : ι → Polynomial ℝ,
        (∀ i, (R i).natDegree ≤ j) ∧ ∀ n < H, ∀ i,
          |(P i).eval (a + q * n) -
            ((R i).eval (n : ℝ) + ((m i * (n : ℤ) ^ (j + 1) : ℤ) : ℝ))| ≤ 1 / (H : ℝ) := by
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  let τ := 1 / (H : ℝ) ^ (j + 2)
  let Q := H ^ ((j + 3) * schmidtRecurrenceExponent e * (Fintype.card ι + 1) ^ 2)
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτ1 : τ ≤ 1 := by
    dsimp [τ]
    have hp : (1 : ℝ) ≤ (H : ℝ) ^ (j + 2) := one_le_pow₀ hH1
    simpa only [div_one] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hp
  have hbase : schmidtRecurrenceBase C e * ((Fintype.card ι : ℝ) + 1) / τ ≤ (H : ℝ) ^ (j + 3) := by
    dsimp [τ]
    rw [one_div, div_inv_eq_mul]
    exact (mul_le_mul_of_nonneg_right hsize (pow_nonneg hHR.le (j + 2))).trans_eq
      (pow_succ' (H : ℝ) (j + 2)).symm
  have hQ : (schmidtRecurrenceBase C e * ((Fintype.card ι : ℝ) + 1) / τ) ^
      (schmidtRecurrenceExponent e * (Fintype.card ι + 1) ^ 2) ≤ (Q : ℝ) := by
    have hnonneg : 0 ≤ schmidtRecurrenceBase C e * ((Fintype.card ι : ℝ) + 1) / τ := by
      have := (schmidtRecurrenceBase_bounds C e).1
      positivity
    have h := pow_le_pow_left₀ hnonneg hbase (schmidtRecurrenceExponent e * (Fintype.card ι + 1) ^ 2)
    simpa only [Q, Nat.cast_pow, ← pow_mul, Nat.mul_assoc] using h
  obtain ⟨q, hq, hqQ, m, hm⟩ := hW.simultaneous_monomial_recurrence
    (fun i => (P i).coeff (j + 1)) Q hτ hτ1 hQ
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  refine ⟨q, hq, hqQ, m, fun a => ⟨(fun i => affinePhaseRemainder (P i) (j + 1) a q),
    (fun i => affinePhaseRemainder_degree (P i) (hP i) a q hqR), ?_⟩⟩
  intro n hn i
  have hm' : |(P i).coeff (j + 1) * (q : ℝ) ^ (j + 1) - m i| ≤ τ := by
    simpa only [mul_comm] using (hm i).le
  have h := affinePhaseRemainder_error (P i) (hP i) a q hqR (m i) hτ.le hm' hn
  have hid : τ * (H : ℝ) ^ (j + 1) = 1 / (H : ℝ) := by
    dsimp [τ]
    rw [show j + 2 = (j + 1) + 1 by omega, pow_succ]
    field_simp
  simpa only [hid] using h

end Erdos3

end

section

namespace Erdos3

open Polynomial
open scoped NNReal

theorem PolynomialIntervalPowerBound.polynomial_progression_reduction
    {j C e : ℕ} (hW : PolynomialIntervalPowerBound (j + 1) C e)
    {ι : Type*} [Fintype ι] (P : ι → Polynomial ℝ)
    (hP : ∀ i, (P i).natDegree ≤ j + 1) (H : ℕ) (hH : 0 < H)
    (hsize : schmidtRecurrenceBase C e * ((Fintype.card ι : ℝ) + 1) ≤ H)
    {F : (ι → ℝ) → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F)
    (hperiod : ∀ x : ι → ℝ, ∀ m : ι → ℤ, F (fun i => x i + m i) = F x) :
    ∃ q : ℕ, 0 < q ∧
      q ≤ H ^ ((j + 3) * schmidtRecurrenceExponent e * (Fintype.card ι + 1) ^ 2) ∧
      ∀ a : ℝ, ∃ R : ι → Polynomial ℝ, (∀ i, (R i).natDegree ≤ j) ∧
        ∀ n < H, dist (F (fun i => (P i).eval (a + q * n)))
          (F (fun i => (R i).eval (n : ℝ))) ≤ (L : ℝ) / H := by
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  let τ := 1 / (H : ℝ) ^ (j + 2)
  let Q := H ^ ((j + 3) * schmidtRecurrenceExponent e * (Fintype.card ι + 1) ^ 2)
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτ1 : τ ≤ 1 := by
    dsimp [τ]
    have hp : (1 : ℝ) ≤ (H : ℝ) ^ (j + 2) := one_le_pow₀ hH1
    simpa only [div_one] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hp
  have hbase : schmidtRecurrenceBase C e * ((Fintype.card ι : ℝ) + 1) / τ ≤ (H : ℝ) ^ (j + 3) := by
    dsimp [τ]
    rw [one_div, div_inv_eq_mul]
    calc
      _ ≤ (H : ℝ) * (H : ℝ) ^ (j + 2) :=
        mul_le_mul_of_nonneg_right hsize (pow_nonneg hHR.le (j + 2))
      _ = _ := (pow_succ' (H : ℝ) (j + 2)).symm
  have hQ : (schmidtRecurrenceBase C e * ((Fintype.card ι : ℝ) + 1) / τ) ^
      (schmidtRecurrenceExponent e * (Fintype.card ι + 1) ^ 2) ≤ (Q : ℝ) := by
    have hnonneg : 0 ≤ schmidtRecurrenceBase C e * ((Fintype.card ι : ℝ) + 1) / τ := by
      have := (schmidtRecurrenceBase_bounds C e).1
      positivity
    have h := pow_le_pow_left₀ hnonneg hbase (schmidtRecurrenceExponent e * (Fintype.card ι + 1) ^ 2)
    simpa only [Q, Nat.cast_pow, ← pow_mul, Nat.mul_assoc] using h
  obtain ⟨q, hq, hqQ, m, hm⟩ := hW.simultaneous_monomial_recurrence
    (fun i => (P i).coeff (j + 1)) Q hτ hτ1 hQ
  refine ⟨q, hq, hqQ, fun a => ?_⟩
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hm' (i : ι) : |(P i).coeff (j + 1) * (q : ℝ) ^ (j + 1) - m i| ≤ τ := by
    simpa only [mul_comm] using (hm i).le
  obtain ⟨R, hR, herror⟩ := polynomial_torus_degree_reduction P hP a (q : ℝ) hqR m hτ.le hm' hF hperiod
  refine ⟨R, hR, fun n hn => ?_⟩
  have herr := herror n hn
  have hid : (L : ℝ) * (τ * (H : ℝ) ^ (j + 1)) = (L : ℝ) / H := by
    dsimp [τ]
    rw [show j + 2 = (j + 1) + 1 by omega, pow_succ]
    field_simp
  simpa only [hid] using herr

end Erdos3

end

section

namespace Erdos3

universe u

open Polynomial

def PolynomialCoordinatePartitionBound (k : ℕ) (K : ℝ) (p : ℕ) : Prop :=
  ∀ (ι : Type u) [Fintype ι] (P : ι → Polynomial ℝ),
    (∀ i, (P i).natDegree ≤ k) → ∀ (N H : ℕ), 0 < H →
    K * ((Fintype.card ι : ℝ) + 1) ≤ H →
    H ^ (p * (Fintype.card ι + 1) ^ (2 * k)) ≤ N →
    ∃ (Q : FiniteProgressionPartition N) (z : Q.Label → ι → ℝ) (m : Q.Label → ℕ → ι → ℤ),
      Fintype.card Q.Label * H ≤ 2 ^ k * N ∧
      ∀ i n, n < Q.length i → ∀ j,
        |(P j).eval ((Q.start i + Q.step i * n : ℕ) : ℝ) - m i n j - z i j| ≤ (k : ℝ) / H

theorem polynomialCoordinatePartitionBound_zero : PolynomialCoordinatePartitionBound.{u} 0 1 1 := by
  intro ι _ P hP N H hH hscale hsize
  have hHN : H ≤ N := by simpa using hsize
  refine ⟨FiniteProgressionPartition.whole N, (fun _ j => (P j).coeff 0), (fun _ _ _ => 0), ?_, ?_⟩
  · have hcard : Fintype.card (FiniteProgressionPartition.whole N).Label = 1 := by
      let : Unique (FiniteProgressionPartition.whole N).Label := inferInstanceAs (Unique Unit)
      exact Fintype.card_unique
    rw [hcard]
    simpa using hHN
  · intro i n hn j
    have heq (x : ℝ) : (P j).eval x = (P j).coeff 0 := by
      simpa only [eval_C] using congrArg (fun Q : Polynomial ℝ => Q.eval x)
        (eq_C_of_natDegree_le_zero (hP j))
    rw [heq]
    simp

theorem PolynomialCoordinatePartitionBound.step {k p C e : ℕ} {K : ℝ}
    (hp : 0 < p) (hpartition : PolynomialCoordinatePartitionBound.{u} k K p)
    (hW : PolynomialIntervalPowerBound (k + 1) C e) :
    PolynomialCoordinatePartitionBound.{u} (k + 1) (max K (schmidtRecurrenceBase C e))
      (p * ((k + 3) * schmidtRecurrenceExponent e + 1)) := by
  intro ι _ P hP N H hH hscale hsize
  let d := Fintype.card ι
  let r := p * (d + 1) ^ (2 * k)
  let T := H ^ r
  have hr : 0 < r := Nat.mul_pos hp (pow_pos (by omega : 0 < d + 1) _)
  have hT : 0 < T := pow_pos hH _
  have hHT : H ≤ T := by
    simpa only [pow_one] using (show H ^ 1 ≤ H ^ r from pow_le_pow_right₀ (by omega) (by omega))
  have hscaleK : K * ((Fintype.card ι : ℝ) + 1) ≤ H :=
    (mul_le_mul_of_nonneg_right (le_max_left K _) (by positivity)).trans hscale
  have hscaleW : schmidtRecurrenceBase C e * ((Fintype.card ι : ℝ) + 1) ≤ T := by
    have h := (mul_le_mul_of_nonneg_right (le_max_right K _) (by positivity)).trans hscale
    exact h.trans (by exact_mod_cast hHT)
  have hsizeT : T ^ (((k + 3) * schmidtRecurrenceExponent e * (d + 1) ^ 2) + 1) ≤ N := by
    apply le_trans _ hsize
    change (H ^ r) ^ _ ≤ H ^ _
    rw [← pow_mul]
    exact pow_le_pow_right₀ (by omega) (polynomial_partition_exponent_step k p (schmidtRecurrenceExponent e) d)
  obtain ⟨q, hq, hqbound, top, hreduce⟩ := hW.polynomial_coordinate_reduction P hP T hT hscaleW
  have hfit : q * T ≤ N := by
    calc
      _ ≤ T ^ ((k + 3) * schmidtRecurrenceExponent e * (d + 1) ^ 2) * T :=
        Nat.mul_le_mul_right T hqbound
      _ = T ^ (((k + 3) * schmidtRecurrenceExponent e * (d + 1) ^ 2) + 1) := (pow_succ _ _).symm
      _ ≤ N := hsizeT
  let B := FiniteProgressionPartition.blocks N q T hq hT
  have hBlength (i : B.Label) : B.length i ≤ T := truncatedProgressionLength_le _ _ _ _
  have hBcard : Fintype.card B.Label * T ≤ 2 * N := progressionBlock_label_count_mul_le_twice hfit
  choose R hRdegree hRerror using (fun i : B.Label => hreduce (B.start i : ℝ))
  have hlocal (i : B.Label) := hpartition ι (R i) (hRdegree i) T H hH hscaleK le_rfl
  choose Q z m hQcard hQerror using hlocal
  let child (i : B.Label) := (Q i).restrict (B.length i) (hBlength i)
  let result := B.bind child
  let index (i : result.Label) (n : ℕ) := (child i.1).start i.2 + (child i.1).step i.2 * n
  let integers (i : result.Label) (n : ℕ) (j : ι) : ℤ :=
    top j * (index i n : ℤ) ^ (k + 1) + m i.1 i.2 n j
  refine ⟨result, (fun i => z i.1 i.2), integers, ?_, ?_⟩
  · have hchild (i : B.Label) : Fintype.card (child i).Label * H ≤ 2 ^ k * T := hQcard i
    calc
      Fintype.card result.Label * H ≤ Fintype.card B.Label * (2 ^ k * T) :=
        B.bind_card_mul_le child H _ hchild
      _ = 2 ^ k * (Fintype.card B.Label * T) := by ring
      _ ≤ 2 ^ k * (2 * N) := Nat.mul_le_mul_left _ hBcard
      _ = 2 ^ (k + 1) * N := by rw [pow_succ]; ring
  · rintro ⟨i, j⟩ n hn a
    let s := index ⟨i, j⟩ n
    have hsB : s < B.length i := (child i).point_lt j hn
    have hsT : s < T := hsB.trans_le (hBlength i)
    have houter := hRerror i s hsT a
    have hnQ : n < (Q i).length j := hn.trans_le ((Q i).restrict_length_le _ (hBlength i) j)
    have hinner := hQerror i j n hnQ a
    change |(R i a).eval (s : ℝ) - m i j n a - z i j a| ≤ (k : ℝ) / H at hinner
    have hindex : result.start ⟨i, j⟩ + result.step ⟨i, j⟩ * n = B.start i + q * s := by
      change (B.start i + q * (child i).start j) + (q * (child i).step j) * n = _
      dsimp [s, index]
      ring
    rw [hindex]
    have houter' : |(P a).eval ((B.start i + q * s : ℕ) : ℝ) -
        ((R i a).eval (s : ℝ) + ((top a * (s : ℤ) ^ (k + 1) : ℤ) : ℝ))| ≤ 1 / (T : ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_mul] using houter
    have hid : (P a).eval ((B.start i + q * s : ℕ) : ℝ) - integers ⟨i, j⟩ n a - z i j a =
        ((P a).eval ((B.start i + q * s : ℕ) : ℝ) -
          ((R i a).eval (s : ℝ) + ((top a * (s : ℤ) ^ (k + 1) : ℤ) : ℝ))) +
        ((R i a).eval (s : ℝ) - m i j n a - z i j a) := by
      dsimp [integers, s]
      push_cast
      ring
    rw [hid]
    calc
      _ ≤ |(P a).eval ((B.start i + q * s : ℕ) : ℝ) -
          ((R i a).eval (s : ℝ) + ((top a * (s : ℤ) ^ (k + 1) : ℤ) : ℝ))| +
          |(R i a).eval (s : ℝ) - m i j n a - z i j a| := abs_add_le _ _
      _ ≤ 1 / (T : ℝ) + (k : ℝ) / H := add_le_add houter' hinner
      _ ≤ _ := by simpa only [mul_one] using polynomial_partition_error_step k (by norm_num : (0 : ℝ) ≤ 1) hH hHT

theorem exists_polynomial_coordinate_partition_bound (k : ℕ) :
    ∃ (K : ℝ) (p : ℕ), 1 ≤ K ∧ 0 < p ∧ PolynomialCoordinatePartitionBound.{u} k K p := by
  induction k with
  | zero => exact ⟨1, 1, le_rfl, by decide, polynomialCoordinatePartitionBound_zero⟩
  | succ k ih =>
    obtain ⟨K, p, hK, hp, hpartition⟩ := ih
    obtain ⟨C, e, hC, he, hW⟩ := polynomial_weyl_inverse_power_interval k
    exact ⟨max K (schmidtRecurrenceBase C e), p * ((k + 3) * schmidtRecurrenceExponent e + 1),
      hK.trans (le_max_left _ _), Nat.mul_pos hp (by omega), hpartition.step hp hW⟩

end Erdos3

end

end OAI
