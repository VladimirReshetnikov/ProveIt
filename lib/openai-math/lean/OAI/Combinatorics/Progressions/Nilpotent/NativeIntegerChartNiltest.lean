import OAI.Combinatorics.Progressions.Geometry.CommonRefilteredFactorsSymbolTransport

namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem integerSampledRealChart_freeze_support {σ τ : Type*}
    (w : σ → ℕ) (β : σ → MvPolynomial τ ℤ)
    (hβ : ∀ i, integerSampledRealChart β i ∈ weightedSupportLE (fun _ : τ => 1) (w i))
    (keep : τ → Prop) (fixed : {i // ¬keep i} → ℤ) :
    ∀ i, integerSampledRealChart (fun z => freezePolynomial keep fixed (β z)) i ∈
      weightedSupportLE (fun _ : {i // keep i} => 1) (w i) := by
  intro i
  change MvPolynomial.map (Int.castRingHom ℝ) (freezePolynomial keep fixed (β i)) ∈ _
  rw [freezePolynomial_map]
  exact freezePolynomial_support keep (fun j => (fixed j : ℝ)) (hβ i)

end Erdos3.VectorPolynomial

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open Module VectorPolynomial NilpotentLieFiltration
open scoped TensorProduct

attribute [local irreducible] realChartSubstitute polynomialOrbitRealChart
  weightedAdaptedRealChartHom realPolynomialSymbolHom

variable {L σ τ : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}
  (Q : D.Niltest w) (v : τ → ℕ) (β : σ → MvPolynomial τ ℤ)
  (hβ : ∀ i, integerSampledRealChart β i ∈ weightedSupportLE v (w i))

noncomputable def integerChartPullback : D.Niltest v :=
  Q.withOrbit (D.filtration.polynomialOrbitRealChart w v (integerSampledRealChart β) hβ Q.orbit)

@[simp] theorem integerChartPullback_orbit :
    (Q.integerChartPullback v β hβ).orbit =
      D.filtration.polynomialOrbitRealChart w v (integerSampledRealChart β) hβ Q.orbit := rfl

@[simp] theorem integerChartPullback_observable :
    (Q.integerChartPullback v β hβ).observable = Q.observable := rfl

@[simp] theorem integerChartPullback_normBound :
    (Q.integerChartPullback v β hβ).normBound = Q.normBound := rfl

@[simp] theorem integerChartPullback_lipBound :
    (Q.integerChartPullback v β hβ).lipBound = Q.lipBound := rfl

@[simp] theorem integerChartPullback_complexity (p : ℝ) :
    (Q.integerChartPullback v β hβ).ComplexityLE p ↔ Q.ComplexityLE p := Iff.rfl

theorem integerChartPullback_complexity_of {p : ℝ} (hQ : Q.ComplexityLE p) :
    (Q.integerChartPullback v β hβ).ComplexityLE p := hQ

@[simp] theorem integerChartPullback_unitIntervalValued :
    (Q.integerChartPullback v β hβ).UnitIntervalValued ↔ Q.UnitIntervalValued := Iff.rfl

@[simp] theorem integerChartPullback_eval (t : τ → ℤ) :
    (Q.integerChartPullback v β hβ).eval t =
      Q.eval (fun i => MvPolynomial.eval t (β i)) := by
  change Q.observable (QuotientGroup.mk
    (D.filtration.realification.polynomialOrbitEval v t
      (D.filtration.polynomialOrbitRealChart w v (integerSampledRealChart β) hβ Q.orbit))) = _
  rw [← D.filtration.realification.polynomialOrbitRealEval_integer,
    D.filtration.polynomialOrbitRealChart_realEval]
  simp only [integerSampledRealChart_eval]
  rw [D.filtration.realification.polynomialOrbitRealEval_integer]
  rfl

theorem integerChartPullback_vertical (η : L →ₗ[ℚ] ℚ)
    (hQ : ∀ z : D.RealGroup, z ∈ D.filtration.realification.subgroup s → ∀ x,
      Q.observable (z • x) =
        CircleFourier.character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) *
          Q.observable x) :
    ∀ z : D.RealGroup, z ∈ D.filtration.realification.subgroup s → ∀ x,
      (Q.integerChartPullback v β hβ).observable (z • x) =
        CircleFourier.character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) *
          (Q.integerChartPullback v β hβ).observable x := hQ

theorem integerChartPullback_polynomialCoordinates :
    D.filtration.realification.polynomialOrbitCoordinates v
      (Q.integerChartPullback v β hβ).orbit =
    D.filtration.weightedAdaptedRealChartHom w v (integerSampledRealChart β) hβ
      (D.filtration.realification.polynomialOrbitCoordinates w Q.orbit) := by
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  change (D.filtration.polynomialOrbitRealChart w v (integerSampledRealChart β) hβ Q.orbit).log =
    ((D.filtration.weightedAdaptedRealChartHom w v (integerSampledRealChart β) hβ
      (D.filtration.realification.polynomialOrbitCoordinates w Q.orbit)).coord :
        VectorPolynomial τ ℚ (ℝ ⊗[ℚ] L))
  rw [polynomialOrbitRealChart_log, weightedAdaptedRealChartHom_coord,
    polynomialOrbitCoordinates_log]

theorem integerChartPullback_orbit_eq_of_orbit_eq (R : D.Niltest w)
    (hQR : Q.orbit = R.orbit) :
    (Q.integerChartPullback v β hβ).orbit = (R.integerChartPullback v β hβ).orbit := by
  simp only [integerChartPullback_orbit, hQR]

theorem integerChartPullback_symbol {κ : Type*} (b : Basis κ ℚ L) (ω : κ → ℕ)
    (hF : ∀ k, D.filtration.layer k = Submodule.span ℚ (b '' {i | k ≤ ω i})) :
    (Q.integerChartPullback v β hβ).symbol b ω hF =
      D.filtration.realPolynomialSymbolHom b ω hF v
        (D.filtration.weightedAdaptedRealChartHom w v (integerSampledRealChart β) hβ
          (D.filtration.realification.polynomialOrbitCoordinates w Q.orbit)) := by
  change D.filtration.realPolynomialSymbolHom b ω hF v
    (D.filtration.realification.polynomialOrbitCoordinates v
      (Q.integerChartPullback v β hβ).orbit) = _
  rw [integerChartPullback_polynomialCoordinates]

theorem integerChartPullback_frozen_symbol_independent
    (hβ₁ : ∀ i, integerSampledRealChart β i ∈ weightedSupportLE (fun _ : τ => 1) (w i))
    (keep : τ → Prop) (fixed fixed' : {i // ¬keep i} → ℤ)
    (hfreeze : ∀ i, integerSampledRealChart (fun z => freezePolynomial keep fixed (β z)) i ∈
      weightedSupportLE (fun _ : {i // keep i} => 1) (w i))
    (hfreeze' : ∀ i, integerSampledRealChart (fun z => freezePolynomial keep fixed' (β z)) i ∈
      weightedSupportLE (fun _ : {i // keep i} => 1) (w i))
    {κ : Type*} (b : Basis κ ℚ L) (ω : κ → ℕ)
    (hF : ∀ k, D.filtration.layer k = Submodule.span ℚ (b '' {i | k ≤ ω i})) :
    (Q.integerChartPullback (fun _ : {i // keep i} => 1)
      (fun z => freezePolynomial keep fixed (β z)) hfreeze).symbol b ω hF =
    (Q.integerChartPullback (fun _ : {i // keep i} => 1)
      (fun z => freezePolynomial keep fixed' (β z)) hfreeze').symbol b ω hF := by
  rw [integerChartPullback_symbol, integerChartPullback_symbol]
  have hcast (a : {i // ¬keep i} → ℤ)
      (ha : ∀ i, integerSampledRealChart (fun z => freezePolynomial keep a (β z)) i ∈
        weightedSupportLE (fun _ : {i // keep i} => 1) (w i)) :
      D.filtration.weightedAdaptedRealChartHom w (fun _ : {i // keep i} => 1)
        (integerSampledRealChart (fun z => freezePolynomial keep a (β z))) ha
        (D.filtration.realification.polynomialOrbitCoordinates w Q.orbit) =
      D.filtration.weightedAdaptedRealChartHom w (fun _ : {i // keep i} => 1)
        (fun i => freezePolynomial keep (fun j => (a j : ℝ)) (integerSampledRealChart β i))
        (fun i => freezePolynomial_support keep (fun j => (a j : ℝ)) (hβ₁ i))
        (D.filtration.realification.polynomialOrbitCoordinates w Q.orbit) := by
    apply NilpotentLieBCHGroup.ext
    apply Subtype.ext
    simp only [weightedAdaptedRealChartHom_coord]
    apply congrArg (fun chart => realChartSubstitute chart Q.orbit.log)
    funext i
    exact freezePolynomial_map (Int.castRingHom ℝ) keep a (β i)
  rw [hcast fixed hfreeze, hcast fixed' hfreeze']
  exact D.filtration.realPolynomialSymbolHom_frozenChart_independent b ω hF w
    (integerSampledRealChart β) hβ₁ keep (fun i => (fixed i : ℝ))
    (fun i => (fixed' i : ℝ))
    (D.filtration.realification.polynomialOrbitCoordinates w Q.orbit)

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI
