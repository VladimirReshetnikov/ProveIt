import OAI.Combinatorics.Progressions.Fourier.PolynomialWeightedCubeMajorArc

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical NNReal
open CircleFourier

theorem booleanBlockPhase_frequency_mul {G I : Type*} [Fintype G] [Fintype I] [DecidableEq I]
    (a : ℝ) (ξ : Finset I → ℝ) (x : G → Option I → ℝ) :
    booleanBlockPhase (fun S => a * ξ S) x = a * booleanBlockPhase ξ x := by
  simp only [booleanBlockPhase, Finset.mul_sum, mul_assoc]

theorem weighted_positiveCoefficient_major_arc {Ω I : Type*} [Fintype Ω]
    [Fintype I] [DecidableEq I] {n : ℕ}
    (p : FiniteProbabilityWeights Ω) (coefficient : Ω → ℤ)
    (s : Fin (n + 1) → NormalizedScalarCubeSource I)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U ζ a₀ T : ℝ}
    (h : ∀ j, ScalarCubePrimitiveBudget (s j) A U)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (ha₀ : 0 < a₀)
    (hcoefficient : ∀ z, p.weight z ≠ 0 → a₀ ≤ (coefficient z : ℝ) ∧ (coefficient z : ℝ) ≤ T)
    (hlen : ∀ j, localizedMajorArcLengthBudget n U ζ ≤ (s j).length)
    (ξ : Finset I → ℝ) (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    (hbias : ζ ≤ ‖p.complexMean (fun z =>
      (FiniteProbabilityWeights.pi (fun j => (s j).source)).complexMean
        (fun x => character (((coefficient z : ℝ) *
          booleanBlockPhase ξ (fun j i => (x j i : ℝ)) : ℝ) : CircleFourier.Circle)))‖) :
    ∃ D : ℕ, 0 < D ∧
      (D : ℝ) ≤ T * (localizedMajorArcBudget n U ζ * U ^ (n + 1)) ^ J.card ∧
      ∃ a : J → ℤ, ∀ S : J, |ξ S - (a S : ℝ) / D| ≤
        localizedMajorArcErrorBudget n U ζ / (a₀ * ∏ j, ((s j).length : ℝ)) := by
  obtain ⟨z, hz, hnorm⟩ := p.exists_positive_weight_norm_ge_mean (fun z =>
    (FiniteProbabilityWeights.pi (fun j => (s j).source)).complexMean
      (fun x => character (((coefficient z : ℝ) *
        booleanBlockPhase ξ (fun j i => (x j i : ℝ)) : ℝ) : CircleFourier.Circle)))
  have hcz := hcoefficient z hz.ne'
  have hcpos : 0 < (coefficient z : ℝ) := ha₀.trans_le hcz.1
  have hczpos : 0 < coefficient z := by exact_mod_cast hcpos
  let c : ℕ := (coefficient z).toNat
  have hcZ : (c : ℤ) = coefficient z := Int.toNat_of_nonneg hczpos.le
  have hcR : (c : ℝ) = (coefficient z : ℝ) := by exact_mod_cast hcZ
  have hc : 0 < c := Nat.cast_pos.mp (by rw [hcR]; exact hcpos)
  have hscaled : ζ ≤ ‖(FiniteProbabilityWeights.pi (fun j => (s j).source)).complexMean
      (fun x => character ((booleanBlockPhase (fun S => (coefficient z : ℝ) * ξ S)
        (fun j i => (x j i : ℝ)) : ℝ) : CircleFourier.Circle))‖ := by
    simpa only [booleanBlockPhase_frequency_mul] using hbias.trans hnorm
  obtain ⟨D, hD, hDb, a, happ⟩ := polynomial_weightedCubeBlock_major_arc s A hA h hζ hζ1 hlen
    (fun S => (coefficient z : ℝ) * ξ S) J hJ hscaled
  have hbound : 0 ≤ (localizedMajorArcBudget n U ζ * U ^ (n + 1)) ^ J.card :=
    (Nat.cast_nonneg D).trans hDb
  refine ⟨c * D, Nat.mul_pos hc hD, ?_, a, ?_⟩
  · rw [Nat.cast_mul, hcR]
    exact (mul_le_mul_of_nonneg_left hDb hcpos.le).trans
      (mul_le_mul_of_nonneg_right hcz.2 hbound)
  · intro S
    rw [Nat.cast_mul, hcR]
    have heq : (coefficient z : ℝ) * (ξ S - (a S : ℝ) / ((coefficient z : ℝ) * D)) =
        (coefficient z : ℝ) * ξ S - (a S : ℝ) / D := by
      field_simp [hcpos.ne', (Nat.cast_pos.mpr hD : (0 : ℝ) < D).ne']
    have hmul : (coefficient z : ℝ) * |ξ S - (a S : ℝ) / ((coefficient z : ℝ) * D)| ≤
        localizedMajorArcErrorBudget n U ζ / ∏ j, ((s j).length : ℝ) := by
      calc
        _ = |(coefficient z : ℝ) * (ξ S - (a S : ℝ) / ((coefficient z : ℝ) * D))| := by
          rw [abs_mul, abs_of_pos hcpos]
        _ = _ := congrArg abs heq
        _ ≤ _ := happ S
    calc
      _ ≤ (localizedMajorArcErrorBudget n U ζ / ∏ j, ((s j).length : ℝ)) / a₀ :=
        (le_div_iff₀ ha₀).mpr ((mul_comm _ _).trans_le
          ((mul_le_mul_of_nonneg_right hcz.1 (abs_nonneg _)).trans hmul))
      _ = _ := by ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical NNReal
open CircleFourier

theorem affine_weighted_positiveCoefficient_major_arc {Ω I : Type*} [Fintype Ω]
    [Fintype I] [DecidableEq I] {n : ℕ}
    (p : FiniteProbabilityWeights Ω) (coefficient : Ω → ℤ)
    (s : Fin (n + 1) → NormalizedScalarCubeSource I)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U ζ a₀ T : ℝ}
    (h : ∀ j, ScalarCubePrimitiveBudget (s j) A U)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (ha₀ : 0 < a₀)
    (hcoefficient : ∀ z, p.weight z ≠ 0 → a₀ ≤ (coefficient z : ℝ) ∧ (coefficient z : ℝ) ≤ T)
    (hlen : ∀ j, localizedMajorArcLengthBudget n U ζ ≤ (s j).length)
    (u : Fin (n + 1) → Option I → ℝ) (v : Fin (n + 1) → Option I → ℕ)
    (hv : ∀ j i, 0 < v j i) (hstride : ∀ j i, ((v j i * (s j).modulus i : ℕ) : ℝ) ≤ U)
    (ξ : Finset I → ℝ) (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    (hbias : ζ ≤ ‖p.complexMean (fun z =>
      (FiniteProbabilityWeights.pi (fun j => (s j).source)).complexMean
        (fun x => character (((coefficient z : ℝ) *
          booleanBlockPhase ξ (fun j => affineCubeCoordinates (u j) (v j) (fun i => (x j i : ℝ))) : ℝ) : CircleFourier.Circle)))‖) :
    ∃ D : ℕ, 0 < D ∧
      (D : ℝ) ≤ T * (localizedMajorArcBudget n U ζ * U ^ (n + 1)) ^ J.card ∧
      ∃ a : J → ℤ, ∀ S : J, |ξ S - (a S : ℝ) / D| ≤
        localizedMajorArcErrorBudget n U ζ / (a₀ * ∏ j, ((s j).length : ℝ)) := by
  obtain ⟨z, hz, hnorm⟩ := p.exists_positive_weight_norm_ge_mean (fun z =>
    (FiniteProbabilityWeights.pi (fun j => (s j).source)).complexMean
      (fun x => character (((coefficient z : ℝ) *
        booleanBlockPhase ξ (fun j => affineCubeCoordinates (u j) (v j) (fun i => (x j i : ℝ))) : ℝ) : CircleFourier.Circle)))
  have hcz := hcoefficient z hz.ne'
  have hcpos : 0 < (coefficient z : ℝ) := ha₀.trans_le hcz.1
  have hczpos : 0 < coefficient z := by exact_mod_cast hcpos
  let c : ℕ := (coefficient z).toNat
  have hcZ : (c : ℤ) = coefficient z := Int.toNat_of_nonneg hczpos.le
  have hcR : (c : ℝ) = (coefficient z : ℝ) := by exact_mod_cast hcZ
  have hc : 0 < c := Nat.cast_pos.mp (by rw [hcR]; exact hcpos)
  have hscaled : ζ ≤ ‖(FiniteProbabilityWeights.pi (fun j => (s j).source)).complexMean
      (fun x => character ((booleanBlockPhase (fun S => (coefficient z : ℝ) * ξ S)
        (fun j => affineCubeCoordinates (u j) (v j) (fun i => (x j i : ℝ))) : ℝ) : CircleFourier.Circle))‖ := by
    simpa only [booleanBlockPhase_frequency_mul] using hbias.trans hnorm
  obtain ⟨D, hD, hDb, a, happ⟩ := polynomial_affine_weightedCubeBlock_major_arc s A hA h hζ hζ1 hlen u v hv hstride
    (fun S => (coefficient z : ℝ) * ξ S) J hJ hscaled
  have hbound : 0 ≤ (localizedMajorArcBudget n U ζ * U ^ (n + 1)) ^ J.card :=
    (Nat.cast_nonneg D).trans hDb
  refine ⟨c * D, Nat.mul_pos hc hD, ?_, a, ?_⟩
  · rw [Nat.cast_mul, hcR]
    exact (mul_le_mul_of_nonneg_left hDb hcpos.le).trans
      (mul_le_mul_of_nonneg_right hcz.2 hbound)
  · intro S
    rw [Nat.cast_mul, hcR]
    have heq : (coefficient z : ℝ) * (ξ S - (a S : ℝ) / ((coefficient z : ℝ) * D)) =
        (coefficient z : ℝ) * ξ S - (a S : ℝ) / D := by
      field_simp [hcpos.ne', (Nat.cast_pos.mpr hD : (0 : ℝ) < D).ne']
    have hmul : (coefficient z : ℝ) * |ξ S - (a S : ℝ) / ((coefficient z : ℝ) * D)| ≤
        localizedMajorArcErrorBudget n U ζ / ∏ j, ((s j).length : ℝ) := by
      calc
        _ = |(coefficient z : ℝ) * (ξ S - (a S : ℝ) / ((coefficient z : ℝ) * D))| := by
          rw [abs_mul, abs_of_pos hcpos]
        _ = _ := congrArg abs heq
        _ ≤ _ := happ S
    calc
      _ ≤ (localizedMajorArcErrorBudget n U ζ / ∏ j, ((s j).length : ℝ)) / a₀ :=
        (le_div_iff₀ ha₀).mpr ((mul_comm _ _).trans_le
          ((mul_le_mul_of_nonneg_right hcz.1 (abs_nonneg _)).trans hmul))
      _ = _ := by ring

end Erdos3

end

end OAI
