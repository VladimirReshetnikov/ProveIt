/- Modified for ProveIt: Use IsModuleTopology.topologicalAddGroup on Lean 4.32; statements unchanged. -/
import OAI.Combinatorics.Progressions.Estimates.CoveredInducedCorrelationFamily
import OAI.Combinatorics.Progressions.Geometry.NativeCorrelationCoordinates

namespace OAI

section

namespace Erdos3.NativeVectorCorrelation

theorem exists_combined_factor_correlation {A I J K : Type*}
    {degree N : ℕ} [NeZero N] {p : ℝ}
    (f : A → ZMod N → ℂ) (g : K → ZMod N → ℂ)
    (a : I → ZMod N → ℂ) (b : J → ZMod N → ℂ)
    (c : I × J → ZMod N → ℂ) (j : J → K)
    (hc : ∀ ij x, c ij x = a ij.1 x * b ij.2 x)
    (W : NativeVectorCorrelation degree N p (fun z : A × (I × J) => fun x =>
      f z.1 x * star (g (j z.2.2) x) * star (a z.2.1 x) * star (b z.2.2 x))) :
    Nonempty (NativeVectorCorrelation degree N p (fun z : (A × K) × (I × J) => fun x =>
      f z.1.1 x * star (g z.1.2 x) * star (c z.2 x))) := by
  refine ⟨W.mapCoordinates _ (fun z => ((z.1, j z.2.2), z.2)) ?_⟩
  intro z x
  rw [hc, star_mul]
  ring

end Erdos3.NativeVectorCorrelation

namespace Erdos3.NativeRankRelation.CommonData

open Module NilpotentLieBCHGroup RationalFilteredNilmanifold
open scoped TensorProduct BigOperators NNReal

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {τ K I : Type} [Fintype I] {s r N n degree : ℕ} [NeZero N]
  {b p q P Z : ℝ} {W : NativeDegreeRankFamily s (r + 1) (ZMod N) b}
  {out : Fin W.outputDim} {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}
  (D : R.CommonData P) (t : ℕ)
  (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
  (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
  (u c : Fin t → ℝ) (h₀ : ZMod N) (h : τ → ZMod N)
  (f : τ → K → ZMod N → ℂ)

def HasUnitRankInducedCorrelationFamily (B C : ℝ) : Prop :=
  ∃ k : ℕ, 0 < k ∧ (k : ℝ) ≤ Real.exp B ∧
    ∃ F : NativeUnitRankFamily (fun _ : Unit => 1) s r τ
        ((I × I) × (I × Fin k)) C,
      ∃ (m : ℕ) (_hm : 0 < m), (m : ℝ) ≤ Real.exp B ∧
        ∃ d : ℕ, ∃ E : RationalFilteredNilmanifold
          (MarkedShiftQuotient D.coefficientFreeFiltration D.coefficientFreeGenerator
            D.coefficientWeight D.coefficientIsDependent t) (s + 1) d,
          ∃ M : E.MultidegreeStructure (mixedCorrelationDegree s),
            M.filtration = D.markedQuotientMultidegree t ∧ M.ComplexityLE B ∧
            (letI := moduleTopology ℝ (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
               D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t)
             letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
               D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t) :=
                  IsModuleTopology.topologicalAddGroup ℝ _
             letI := realification_moduleTopology_t2 E.basis
             letI := E.metricSpace
             ∃ G : Fin k → E.Space → ℂ,
               (∀ j z, ‖G j z‖ ≤ 2) ∧
               (∀ j, LipschitzWith ⟨Real.exp B, Real.exp_nonneg _⟩ (G j)) ∧
               ∀ z, Nonempty (NativeVectorCorrelation degree N B
                 (fun ij : (K × Fin k) × ((I × I) × (I × Fin k)) => fun a =>
                   f z ij.1.1 a * star (G ij.1.2 (QuotientGroup.mk
                     ((D.markedQuotientMultidegree t).realification.polynomialOrbitEval
                       (correlationInput ((h z).val : ℤ) (a.val : ℤ))
                       (D.localPhaseMarkedOrbit t x y u c h₀ m)))) *
                   star (F.eval z ij.2 (fun _ => (a.val : ℤ))))))

theorem HasCommonInducedCorrelationFamily.combineLower
    (A : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s n)
    {e k : ℕ} (Q : RationalFilteredNilmanifold D.DependentQuotient s e)
    [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
    [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
    [TopologicalSpace (ℝ ⊗[ℚ] D.DependentQuotient)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.DependentQuotient)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.DependentQuotient)]
    [T2Space (ℝ ⊗[ℚ] D.DependentQuotient)]
    {S : Subgroup A.RealGroup} {T : Subgroup Q.RealGroup}
    (V : A.UnitVerticalObservable S I Z) (U : Q.UnitVerticalObservable T (Fin k) Z)
    (hφ : A.lattice ≤ Q.lattice.comap (mapOfSteps
      (hL := A.filtration.lowerCentralSeries_eq_bot)
      (hM := Q.filtration.lowerCentralSeries_eq_bot) D.dependentQuotientMap))
    (a v : τ → A.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    {B C : ℝ} (hk : 0 < k) (hkB : (k : ℝ) ≤ Real.exp B)
    (F : NativeUnitRankFamily (fun _ : Unit => 1) s r τ ((I × I) × (I × Fin k)) C)
    (hF : ∀ z ij w, F.eval z ij w =
      (V.observable ij.1.1 (QuotientGroup.mk
        (A.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) w (v z))) *
        star (V.observable ij.1.2 (QuotientGroup.mk
          (A.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) w (a z))))) *
      mapDifferenceObservable V U D.dependentQuotientMap hφ ij.2 (QuotientGroup.mk
        (A.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) w (a z))))
    (hcommon : D.HasCommonInducedCorrelationFamily (degree := degree)
      t A Q V U hφ x y u c h₀ h a v f B) :
    D.HasUnitRankInducedCorrelationFamily (I := I) (degree := degree) t x y u c h₀ h f B C := by
  obtain ⟨m, hm, hmB, d₁, _, E₁, M, hMF, hM, hdata⟩ := hcommon
  refine ⟨k, hk, hkB, F, m, hm, hmB, d₁, E₁, M, hMF, hM, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
    D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
    D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t) :=
      IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 E₁.basis
  let := E₁.metricSpace
  obtain ⟨G, hGn, hGL, hcorr⟩ := hdata
  refine ⟨G, hGn, hGL, ?_⟩
  intro z
  exact NativeVectorCorrelation.exists_combined_factor_correlation (f z)
    (fun j w => G j (QuotientGroup.mk
      ((D.markedQuotientMultidegree t).realification.polynomialOrbitEval
        (correlationInput ((h z).val : ℤ) (w.val : ℤ))
        (D.localPhaseMarkedOrbit t x y u c h₀ m))))
    (fun (ij : I × I) w => V.observable ij.1 (QuotientGroup.mk
      (A.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
        (fun _ => (w.val : ℤ)) (v z))) *
      star (V.observable ij.2 (QuotientGroup.mk
        (A.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
          (fun _ => (w.val : ℤ)) (a z)))))
    (fun (ij : I × Fin k) w => mapDifferenceObservable V U D.dependentQuotientMap hφ ij
      (QuotientGroup.mk (A.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
        (fun _ => (w.val : ℤ)) (a z))))
    (fun ij w => F.eval z ij (fun _ => (w.val : ℤ))) Prod.snd
    (fun ij w => hF z ij (fun _ => (w.val : ℤ))) (Classical.choice (hcorr z))

variable (A : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s n)
  (T : A.DegreeRankStructure (r + 1))
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : A.UnitVerticalObservable (T.realSubgroup s (r + 1)) I Z)
  (a v : τ → A.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))

theorem HasCoveredInducedCorrelationFamily.combineLower
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hcovered : D.HasCoveredInducedCorrelationFamily (degree := degree)
      t A T V x y u c h₀ h a v f B)
    {L : Type} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
    (E : RationalFilteredNilmanifold L s d) (U : E.DegreeRankStructure (r + 1))
    (hfirst : E.HasLowerRankOrbitFamily U (fun _ : Unit => 1)
      (fun z (ij : I × I) w => V.observable ij.1 (QuotientGroup.mk
        (A.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) w (v z))) *
        star (V.observable ij.2 (QuotientGroup.mk
          (A.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) w (a z))))) C) :
    D.HasUnitRankInducedCorrelationFamily (I := I) (degree := degree)
      t x y u c h₀ h f B (productNiltestBudget (C + B + 2)) := by
  obtain ⟨Λ, _, l, hl, hin, hout, _, e, _, Q, S, _, _, hφ, V₀, _, hVobs, hcoeff⟩ := hcovered
  let A₀ := A.withLattice Λ l hl hin hout
  let T₀ := T.withLattice Λ l hl hin hout
  let := moduleTopology ℝ (ℝ ⊗[ℚ] D.DependentQuotient)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.DependentQuotient) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 Q.basis
  obtain ⟨k, hk, hkB, U₀, hcommon, hsecond⟩ := hcoeff
  obtain ⟨F, _, hF⟩ := exists_binary_lower_rank_unit_family (p := C + B + 2) E A₀ U T₀
    (fun _ : Unit => 1) _ _ (by linarith : 2 ≤ C + B + 2)
    (hfirst.mono (show C ≤ C + B + 2 by linarith))
    (hsecond.mono (show B ≤ C + B + 2 by linarith))
  apply HasCommonInducedCorrelationFamily.combineLower D t x y u c h₀ h f
    A₀ Q V₀ U₀ hφ a v hk hkB F ?_ hcommon
  intro z ij w
  rw [hF]
  have hvalue (i : I) (o : A.filtration.realification.PolynomialOrbit (fun _ : Unit => 1)) :
      V₀.observable i (QuotientGroup.mk
        (A₀.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) w o)) =
      V.observable i (QuotientGroup.mk
        (A.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) w o)) := hVobs i _
  simp only [hvalue]
  rfl

end Erdos3.NativeRankRelation.CommonData

end

end OAI
