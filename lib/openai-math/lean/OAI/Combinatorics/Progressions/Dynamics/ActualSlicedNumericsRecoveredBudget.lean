import OAI.Combinatorics.Progressions.Sampling.PreparedActualSlicedForecastSetup

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {A : Type} [Fintype A]
variable {Dmod : ℕ} {selected : A → Σ j : Fin m, Fin (n j)}
variable {τ δslice : ℝ}

variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)

omit [DecidableEq X] [Fintype A] in
theorem actualSlicedForecastDensityBudget_ge_one (v : ℝ) :
    1 ≤ actualSlicedForecastDensityBudget s v := by
  apply Real.one_le_exp_iff.mpr
  unfold forecastOriginalSmoothBudget
  positivity

namespace ActualFixedSpatialSlicedForecastNumerics

variable (qnum : ActualFixedSpatialSlicedForecastNumerics s)

omit [DecidableEq X] in

theorem joint_density_grid_cap_le_exp :
    s.κ * actualSlicedForecastDensityBudget s qnum.v * qnum.Ctail ^ Fintype.card A ≤
      Real.exp qnum.capLog := by
  have hbase : 0 ≤ s.κ * actualSlicedForecastDensityBudget s qnum.v *
      qnum.Ctail ^ Fintype.card A :=
    mul_nonneg (mul_nonneg s.hκ (Real.exp_nonneg _)) (pow_nonneg qnum.hCtail _)
  have hdecay : 0 ≤ actualSlicedForecastDecayBudget s := Real.exp_nonneg _
  apply le_trans _ qnum.hcap
  nlinarith

omit [DecidableEq X] in

theorem spatial_inverse_factor_le_exp : 8 / τ ≤ Real.exp qnum.Pnative := by
  have hD := actualSlicedForecastDensityBudget_ge_one s qnum.v
  have htail : 0 ≤ (Fintype.card A : ℝ) * (qnum.Lt : ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) qnum.Lt.coe_nonneg
  have hmax : 0 ≤ max (8 / τ) 1 := zero_le_one.trans (le_max_right _ _)
  calc
    _ ≤ max (8 / τ) 1 := le_max_left _ _
    _ ≤ (actualSlicedForecastDensityBudget s qnum.v +
        (Fintype.card A : ℝ) * (qnum.Lt : ℝ)) * max (8 / τ) 1 := by nlinarith
    _ ≤ _ := qnum.hfactor

end ActualFixedSpatialSlicedForecastNumerics
end Erdos3.VectorPolynomial

end

end OAI
