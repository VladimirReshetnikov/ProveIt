import OAI.Combinatorics.Progressions.Estimates.NativeFrozenMarkedLocalMark
import OAI.Combinatorics.Progressions.Geometry.GlobalChartNativeFactorization

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {σ τ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s)

noncomputable def polynomialOrbitRealChart
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i))
    (g : F.realification.PolynomialOrbit w) : F.realification.PolynomialOrbit v :=
  polynomialOrbitOfLog (realChartSubstitute β g.log)
    (F.adapted_realChartSubstitute_weightedSupport w v β hβ g.adapted)

attribute [local irreducible] realChartSubstitute

@[simp] theorem polynomialOrbitRealChart_log
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i))
    (g : F.realification.PolynomialOrbit w) :
    (F.polynomialOrbitRealChart w v β hβ g).log = realChartSubstitute β g.log := by
  unfold polynomialOrbitRealChart
  exact polynomialOrbitOfLog_log _ _

attribute [local irreducible] polynomialOrbitRealChart

theorem polynomialOrbitRealChart_realEval
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i))
    (g : F.realification.PolynomialOrbit w) (x : τ → ℝ) :
    F.realification.polynomialOrbitRealEval v x (F.polynomialOrbitRealChart w v β hβ g) =
      F.realification.polynomialOrbitRealEval w (fun i => MvPolynomial.eval x (β i)) g := by
  apply NilpotentLieBCHGroup.ext
  simp only [polynomialOrbitRealEval_coord, polynomialOrbitRealChart_log]
  exact eval₂_realChartSubstitute β x g.log

end Erdos3.NilpotentLieFiltration

namespace Erdos3.PolynomialPatch

variable {σ τ ξ : Type*} {s d : ℕ} (A : PolynomialPatch σ s d)

noncomputable def ofWeightedChartShearOrbit (w : ξ → ℕ)
    (β : ξ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE (fun _ : τ => 1) (w i))
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit w) :
    PolynomialPatch τ s d :=
  A.ofShearOrbit ((polynomialShearFiltration A.weight s A.weight_le).polynomialOrbitRealChart
    w (fun _ : τ => 1) β hβ g)

@[simp] theorem ofWeightedChartShearOrbit_weight (w : ξ → ℕ)
    (β : ξ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE (fun _ : τ => 1) (w i))
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit w) :
    (A.ofWeightedChartShearOrbit w β hβ g).weight = A.weight := rfl

@[simp] theorem ofWeightedChartShearOrbit_kernel (w : ξ → ℕ)
    (β : ξ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE (fun _ : τ => 1) (w i))
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit w) :
    (A.ofWeightedChartShearOrbit w β hβ g).kernel = A.kernel := rfl

theorem ofWeightedChartShearOrbit_value (w : ξ → ℕ)
    (β : ξ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE (fun _ : τ => 1) (w i))
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit w)
    (x : τ → ℝ) :
    (A.ofWeightedChartShearOrbit w β hβ g).value x =
      A.shearObservable (QuotientGroup.mk
        ((polynomialShearFiltration A.weight s A.weight_le).realification.polynomialOrbitRealEval
          w (fun i => MvPolynomial.eval x (β i)) g)) := by
  rw [ofWeightedChartShearOrbit, ofShearOrbit_value_real,
    NilpotentLieFiltration.polynomialOrbitRealChart_realEval]

theorem ofWeightedChartShearOrbit_shearGroupLift (w : ξ → ℕ)
    (β : ξ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE (fun _ : τ => 1) (w i))
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit w)
    (x : τ → ℝ) :
    (A.ofWeightedChartShearOrbit w β hβ g).form.shearGroupLift s A.weight_le x =
      (polynomialShearFiltration A.weight s A.weight_le).realification.polynomialOrbitRealEval
        w (fun i => MvPolynomial.eval x (β i)) g := by
  change (A.ofShearOrbit ((polynomialShearFiltration A.weight s A.weight_le).polynomialOrbitRealChart
    w (fun _ : τ => 1) β hβ g)).form.shearGroupLift s A.weight_le x = _
  rw [ofShearOrbit_shearGroupLift_real,
    NilpotentLieFiltration.polynomialOrbitRealChart_realEval]

end Erdos3.PolynomialPatch

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {σ τ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s)

attribute [local irreducible] realChartSubstitute polynomialOrbitRealChart
  weightedAdaptedRealChartHom polynomialOrbitCoordinates

theorem polynomialOrbitRealChart_polynomialCoordinates
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i))
    (g : F.realification.PolynomialOrbit w) :
    F.realification.polynomialOrbitCoordinates v
      (F.polynomialOrbitRealChart w v β hβ g) =
    F.weightedAdaptedRealChartHom w v β hβ
      (F.realification.polynomialOrbitCoordinates w g) := by
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  rw [F.realification.polynomialOrbitCoordinates_log, F.polynomialOrbitRealChart_log,
    F.weightedAdaptedRealChartHom_coord, F.realification.polynomialOrbitCoordinates_log]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.PolynomialPatch

open Module VectorPolynomial
open scoped TensorProduct

variable {σ τ ξ κ M : Type*} [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} (A : PolynomialPatch σ s d)
    (G : NilpotentLieFiltration M t)
    (φ : PolynomialShearLieAlgebra A.weight ℚ →ₗ⁅ℚ⁆ M)

local notation "F" => polynomialShearFiltration A.weight s A.weight_le

theorem exists_marked_chart_restoration
    (hφ : ∀ j, ∀ y ∈ (F).layer j, φ y ∈ G.layer j)
    (c : Basis κ ℚ M) (v : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {k | j ≤ v k}))
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ z ∈ (F).layer j, φ z = y)
    (w : ξ → ℕ) (β : ξ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE (fun _ : τ => 1) (w i))
    (g : (F).realification.PolynomialOrbit w)
    (q : G.realification.PolynomialOrbit w) :
    ∃ restored : (F).realification.PolynomialOrbit w,
      map ((realificationLieHom φ).toLinearMap.restrictScalars ℚ) restored.log = q.log ∧
      (∀ x : τ → ℝ, NilpotentLieBCHGroup.realificationMap
        (hnil := (F).lowerCentralSeries_eq_bot) (hM := G.lowerCentralSeries_eq_bot) φ
          ((A.ofWeightedChartShearOrbit w β hβ restored).form.shearGroupLift s A.weight_le x) =
            G.realification.polynomialOrbitRealEval w
              (fun i => MvPolynomial.eval x (β i)) q) ∧
      ∀ x : τ → ℝ, NilpotentLieBCHGroup.realificationMap
        (hnil := (F).lowerCentralSeries_eq_bot) (hM := G.lowerCentralSeries_eq_bot) φ
          ((F).realification.polynomialOrbitRealEval w
            (fun i => MvPolynomial.eval x (β i)) g) =
              G.realification.polynomialOrbitRealEval w
                (fun i => MvPolynomial.eval x (β i)) q →
        (A.ofWeightedChartShearOrbit w β hβ restored).value x =
          (A.ofWeightedChartShearOrbit w β hβ g).value x := by
  obtain ⟨restored, hmap, hmark, hkeep⟩ :=
    (F).exists_formal_marked_orbit_restoration G φ hφ c v hG hsurj w g q
  refine ⟨restored, hmap, ?_, ?_⟩
  · intro x
    rw [ofWeightedChartShearOrbit_shearGroupLift]
    exact hmark _
  · intro x hx
    rw [ofWeightedChartShearOrbit_value, ofWeightedChartShearOrbit_value]
    rw [hkeep _ hx]

end Erdos3.PolynomialPatch

end

end OAI
