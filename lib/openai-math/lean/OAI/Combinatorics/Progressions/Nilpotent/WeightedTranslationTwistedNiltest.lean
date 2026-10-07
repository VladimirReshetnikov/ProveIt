import OAI.Combinatorics.Progressions.Nilpotent.LocalMajorDenseSliceNiltest
import OAI.Combinatorics.Progressions.Polynomial.WeightedTranslationResiduePhase

namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial Module NilpotentLieBCHGroup
open scoped NNReal TensorProduct

variable {m : ℕ} (w : Fin m → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (hwd : ∀ i, w i ≤ d) [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)

noncomputable def weightedTranslationTwistedObservable (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ) :
    (weightedTranslationResidueNilmanifold w d hw hwd M hM).Space → ℂ :=
  twistedBufferedTranslationQuotientPhase M Ψ D₀ T ∘
    weightedTranslationResiduePhaseQuotientMap w d hw hwd M hM

@[simp] theorem weightedTranslationTwistedObservable_mk (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (g : (weightedFiltration w d hwd).realification.Group) :
    weightedTranslationTwistedObservable w d hw hwd M hM Ψ D₀ T (QuotientGroup.mk g) =
      twistedBufferedTranslationPhase M Ψ D₀ T (bchRealTranslationHom w d hwd g) := rfl

theorem weightedTranslationTwistedObservable_norm_le_one (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ) (hT : ∀ x r, ‖T x r‖ ≤ 1)
    (g : (weightedTranslationResidueNilmanifold w d hw hwd M hM).Space) :
    ‖weightedTranslationTwistedObservable w d hw hwd M hM Ψ D₀ T g‖ ≤ 1 :=
  twistedBufferedTranslationQuotientPhase_norm_le_one M Ψ D₀ T hT _

variable [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]

theorem weightedTranslationTwistedObservable_lipschitz
    (hd : 0 < d) (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ) (A K : ℝ≥0)
    (hdegree : D₀.totalDegree ≤ d) (hD : realPolynomialMass D₀ ≤ A)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (hT : ∀ x r, ‖T x r‖ ≤ 1) (hLip : ∀ r, LipschitzWith K (fun x => T x r)) :
    letI := (weightedTranslationResidueNilmanifold w d hw hwd M hM).metricSpace
    LipschitzWith (2 * twistedBufferedTranslationTermLip w d Ψ A K)
      (weightedTranslationTwistedObservable w d hw hwd M hM Ψ D₀ T) := by
  let e := (weightedOrderedBasis w d hw).baseChange ℝ
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d) := e.finiteDimensional_of_finite
  let := rightMetricSpace
    (hnil := (weightedFiltration w d hwd).realification.lowerCentralSeries_eq_bot) e
  let := rightMetricSpace_isIsometricSMul
    (hnil := (weightedFiltration w d hwd).realification.lowerCentralSeries_eq_bot) e
  exact rightCosetMetricSpace_lipschitz_lift
    (weightedTranslationResidueNilmanifold w d hw hwd M hM).realLattice
    (weightedTranslationResidueNilmanifold w d hw hwd M hM).realLattice_closed_discrete.1
    (weightedTranslationTwistedObservable w d hw hwd M hM Ψ D₀ T)
    (twistedBufferedTranslationPhase_lipschitz w d hw hd hwd M Ψ D₀ A K hdegree hD T hT hLip)

noncomputable def weightedTranslationTwistedNiltest {U : Type*} (ω : U → ℕ)
    (hd : 0 < d) (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ) (A K : ℝ≥0)
    (hdegree : D₀.totalDegree ≤ d) (hD : realPolynomialMass D₀ ≤ A)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (hT : ∀ x r, ‖T x r‖ ≤ 1) (hLip : ∀ r, LipschitzWith K (fun x => T x r))
    (q : (weightedFiltration w d hwd).realification.PolynomialOrbit ω) :
    (weightedTranslationResidueNilmanifold w d hw hwd M hM).Niltest ω where
  orbit := q
  observable := weightedTranslationTwistedObservable w d hw hwd M hM Ψ D₀ T
  normBound := 1
  lipBound := 2 * twistedBufferedTranslationTermLip w d Ψ A K
  norm_le := weightedTranslationTwistedObservable_norm_le_one w d hw hwd M hM Ψ D₀ T hT
  lipschitz := weightedTranslationTwistedObservable_lipschitz
    w d hw hwd M hM hd Ψ D₀ A K hdegree hD T hT hLip

@[simp] theorem weightedTranslationTwistedNiltest_eval {U : Type*} (ω : U → ℕ)
    (hd : 0 < d) (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ) (A K : ℝ≥0)
    (hdegree : D₀.totalDegree ≤ d) (hD : realPolynomialMass D₀ ≤ A)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (hT : ∀ x r, ‖T x r‖ ≤ 1) (hLip : ∀ r, LipschitzWith K (fun x => T x r))
    (q : (weightedFiltration w d hwd).realification.PolynomialOrbit ω) (t : U → ℤ) :
    (weightedTranslationTwistedNiltest w d hw hwd M hM ω hd Ψ D₀ A K hdegree hD T hT hLip q).eval t =
      twistedBufferedTranslationPhase M Ψ D₀ T (bchRealTranslationHom w d hwd
        ((weightedFiltration w d hwd).realification.polynomialOrbitEval ω t q)) := rfl

@[simp] theorem weightedTranslationTwistedNiltest_evalReal {U : Type*} (ω : U → ℕ)
    (hd : 0 < d) (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ) (A K : ℝ≥0)
    (hdegree : D₀.totalDegree ≤ d) (hD : realPolynomialMass D₀ ≤ A)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (hT : ∀ x r, ‖T x r‖ ≤ 1) (hLip : ∀ r, LipschitzWith K (fun x => T x r))
    (q : (weightedFiltration w d hwd).realification.PolynomialOrbit ω) (t : U → ℝ) :
    (weightedTranslationTwistedNiltest w d hw hwd M hM ω hd Ψ D₀ A K hdegree hD T hT hLip q).evalReal t =
      twistedBufferedTranslationPhase M Ψ D₀ T (bchRealTranslationHom w d hwd
        ((weightedFiltration w d hwd).realification.polynomialOrbitRealEval ω t q)) := rfl

theorem weightedTranslationTwistedNiltest_complexity {U : Type*} (ω : U → ℕ)
    (hd : 0 < d) (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ) (A K : ℝ≥0)
    (hdegree : D₀.totalDegree ≤ d) (hD : realPolynomialMass D₀ ≤ A)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (hT : ∀ x r, ‖T x r‖ ≤ 1) (hLip : ∀ r, LipschitzWith K (fun x => T x r))
    (q : (weightedFiltration w d hwd).realification.PolynomialOrbit ω) {p : ℝ}
    (hgeometry : (weightedTranslationResidueNilmanifold w d hw hwd M hM).GeometryComplexityLE p)
    (hbound : Real.log (3 + (2 * twistedBufferedTranslationTermLip w d Ψ A K : ℝ≥0)) ≤ p) :
    (weightedTranslationTwistedNiltest w d hw hwd M hM ω hd Ψ D₀ A K hdegree hD T hT hLip q).ComplexityLE p := by
  refine ⟨hgeometry, ?_⟩
  simpa only [weightedTranslationTwistedNiltest, NNReal.coe_one,
    show (2 : ℝ) + 1 = 3 by norm_num] using hbound

end Erdos3.PolynomialTranslationLie

end

end OAI
