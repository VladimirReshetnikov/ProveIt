/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Mathematical statements are unchanged from the pinned upstream source.
Use IsModuleTopology.topologicalAddGroup on Lean 4.32; statements unchanged. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.MixedPairStepDrop
import OAI.Combinatorics.Progressions.Lattices.CommonLocalAffineFamily
import OAI.Combinatorics.Progressions.Lattices.NativeCorrelatedAffineExistence
import OAI.Combinatorics.Progressions.Polynomial.MixedPairPolynomial

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

theorem HasLowerRankOrbitFamily.reindex {L I σ τ τ' : Type*}
    [LieRing L] [LieAlgebra ℚ L] [Fintype I] {s r d : ℕ}
    {D : RationalFilteredNilmanifold L s d} {R : D.DegreeRankStructure (r + 1)}
    {w : σ → ℕ} {f : τ → I → (σ → ℤ) → ℂ} {p : ℝ}
    (h : D.HasLowerRankOrbitFamily R w f p) (j : τ' → τ) :
    D.HasLowerRankOrbitFamily R w (fun t => f (j t)) p := by
  obtain ⟨n, hn, Q, U, hUc, hK⟩ := h
  refine ⟨n, hn, Q, U, hUc, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1)))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1))) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 Q.basis
  obtain ⟨K, hKn, hKc, hKu, a, ha0, ha⟩ := hK
  exact ⟨K, hKn, hKc, hKu, (fun t => a (j t)),
    (fun t => ha0 (j t)), fun t i x => ha (j t) i x⟩

end Erdos3.RationalFilteredNilmanifold

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped BigOperators TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s (r + 1) N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure (r + 1)) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s (r + 1)) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)
  {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

def CorrelatedLocalMarkedFamily (hs : 2 ≤ s) : Prop :=
    let Λ := (P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s
    let C := sharedFreeCorrelationBudget s hs P'
    let B := P' + Λ + C
    let Qc := C + sharedFreeComparisonBasisBudget Q P' + 2
    let S := D.comparisonCoefficientSpace E T hbQ hT V g hg D'
    ∃ J ⊆ H', J.Nonempty ∧ Real.exp (-((B + 4) ^ 7)) * N ≤ (J.card : ℝ) ∧
      ∃ t : ℕ, (t : ℝ) ≤ Λ ∧ ∃ (h₀ : ZMod N) (u c : Fin t → ℝ)
        (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
        (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ),
        (∀ i, u i ∈ Set.Ico (0 : ℝ) 1) ∧
        (∀ i, ∃ k : ℤ, (N : ℝ) * u i = (k : ℝ)) ∧
        (∀ i, |c i| ≤ properCyclicCoordinateBound t (Real.exp (-B)) + 1 / 16) ∧
        ∃ A K U : {h // h ∈ J} → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
          (∀ h : {h // h ∈ J},
            (∀ i, |affineCyclicTorusLocalLift u c h₀ h.val i| ≤ 1 / 16) ∧
            (A h).log = positiveUnivariate (fun j => (x j).val +
              ∑ i, affineCyclicTorusLocalLift u c h₀ h.val i • (y j i).val) ∧
            E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (A h) = 1 ∧
            E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (K h) = 1 ∧
            E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (U h) = 1 ∧
            (∀ j : Fin s,
              coefficients (K h).log (Finsupp.single () (j.val + 1)) ∈
                (T.filtration.layer (j.val + 1) 2).baseChange ℝ ∧
              coefficients (U h).log (Finsupp.single () (j.val + 1)) ∈
                (fourPetalSpace (D.dependentFreeSpan j)
                  (fourRefinedRelation (D.coefficientFreeSpan j) (D.dependentFreeSpan j)
                    (D'.coefficientFourSpace ⟨j.val + 1, by omega⟩))).baseChange ℝ) ∧
            ∀ n : ℤ,
              (markedShiftEval D.coefficientFreeFiltration D.coefficientFreeGenerator
                D.coefficientWeight D.coefficientIsDependent t
                  (fun i => (-affineCyclicTorusCarry u c h₀ h.val i : ℤ))).baseChange ℝ
                    (D.localAffineMarkedLift t x y u c h₀ h.val n) =
                      (E.filtration.realification.polynomialOrbitEval
                        (fun _ : Unit => 1) (fun _ => n) (A h)).coord) ∧
          ∃ Δ : Subgroup E.filtration.Group, Δ ≤ E.lattice ∧
            (Δ.subgroupOf E.lattice).Characteristic ∧ (Δ.subgroupOf E.lattice).Normal ∧
            (Δ.subgroupOf E.lattice).FiniteIndex ∧ (Δ.relIndex E.lattice : ℝ) ≤ Real.exp C ∧
            ∃ (l : ℕ) (hl : 0 < l)
              (hin : scaledIntegerGrid l ⊆ bchSubgroupCoordinates E.basis Δ)
              (hout : bchSubgroupCoordinates E.basis Δ ⊆ denominatorGrid l),
              (T.withLattice Δ l hl hin hout).ComplexityLE C ∧
              ∃ V₁ : (E.withLattice Δ l hl hin hout).UnitVerticalObservable
                  ((T.withLattice Δ l hl hin hout).realSubgroup s (r + 1)) (Fin W.family.outputDim) C,
                V₁.frequency = V.frequency ∧
                (∀ h : {h // h ∈ J}, Nonempty (NativeVectorCorrelation (s - 1) N C
                  (W.replacedRankResidual h.val (fun i z => V₁.observable i (QuotientGroup.mk
                    (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                      (fun _ => (z.val : ℤ)) (A h * K h * U h))))))) ∧
                ∃ M : RationalFilteredNilmanifold (SubspaceFreeLift.Algebra S (r + 1)) s
                    (finrank ℚ (SubspaceFreeLift.Algebra S (r + 1))),
                  ∃ Tm : M.DegreeRankStructure (r + 1),
                    Tm.filtration = SubspaceFreeLift.filtration S T.filtration.rank_le_degree ∧
                    Tm.ComplexityLE ((Qc + nativePairModelConstant s) ^ nativePairModelConstant s) ∧
                    M.HasLowerRankOrbitFamily Tm (fun _ : Unit => 1)
                      (fun h (i : Fin W.family.outputDim × Fin W.family.outputDim) z =>
                        V₁.observable i.1 (QuotientGroup.mk
                          (E.filtration.realification.polynomialOrbitEval
                            (fun _ : Unit => 1) z (A h * K h * U h))) *
                        star (V₁.observable i.2 (QuotientGroup.mk
                          (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) z (A h)))))
                      (nativeLowerPairModelBudget s Qc)

theorem CorrelatedAffineComparison.localMarkedFamily
    (hs : 2 ≤ s) (hP' : 0 ≤ P')
    (hdense : Real.exp (-P') * N ≤ (H'.card : ℝ))
    (h : D.CorrelatedAffineComparison E T hbQ hT V g hg D' hs) :
    D.CorrelatedLocalMarkedFamily E T hbQ hT V g hg D' hs := by
  classical
  let Λ := (P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s
  let C := sharedFreeCorrelationBudget s hs P'
  let B := P' + Λ + C
  obtain ⟨J, hJH, hJ, hJcard, t, radius, η, h₀, Γ, α, β,
    ht, hinj, hΓ0, hΓ, hα, hβ, v, A, K, U, hdata,
    Δ, hΔ, hchar, hnormal, hfinite, hindex, l, hl, hin, hout,
    hRank, V₁, hfreq, hcorr, M, Tm, hTm, hTmc, hfamily⟩ := h
  have hΛ : 0 ≤ Λ := pow_nonneg (add_nonneg hP' (Nat.cast_nonneg _)) _
  have hC : 0 ≤ C :=
    (show 0 ≤ sharedFreeCorrelationInput s P' by
      linarith only [(sharedFreeCorrelationInput_bounds s hP' le_rfl hP').1]).trans
        (sharedFreeCorrelationInput_le_budget s hs hP')
  have hB : 0 ≤ B := add_nonneg (add_nonneg hP' hΛ) hC
  have htB : (t : ℝ) ≤ B := ht.trans (by dsimp only [B]; linarith only [hP', hC])
  have hJB : Real.exp (-B) * N ≤ (J.card : ℝ) := by
    calc
      _ = Real.exp (-(Λ + C)) * (Real.exp (-P') * N) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        dsimp only [B]
        ring
      _ ≤ Real.exp (-(Λ + C)) * H'.card :=
        mul_le_mul_of_nonneg_left hdense (Real.exp_pos _).le
      _ ≤ _ := hJcard
  let v' (h : ZMod N) := if hh : h ∈ J then v ⟨h, hh⟩ else 0
  let A' (h : ZMod N) := if hh : h ∈ J then (A ⟨h, hh⟩).log else 0
  have hv' (h : ZMod N) (hh : h ∈ J) : ∀ i, |v' h i| ≤ (radius i : ℤ) := by
    simpa only [v', dite_eq_left hh] using (hdata ⟨h, hh⟩).1
  have hrep' (h : ZMod N) (hh : h ∈ J) : h = h₀ + η (v' h) := by
    simpa only [v', dite_eq_left hh] using (hdata ⟨h, hh⟩).2.1
  have hA' (h : ZMod N) (hh : h ∈ J) :
      A' h = Γ.log + positiveUnivariate (fun j => α j + ∑ i, (v' h i : ℝ) • β i j) := by
    simpa only [A', v', dite_eq_left hh] using (hdata ⟨h, hh⟩).2.2.1
  have hΓzero : coefficients Γ.log 0 = 0 := by
    have he := congrArg NilpotentLieBCHGroup.coord hΓ0
    simpa only [E.filtration.realification.polynomialOrbitEval_coord, Pi.zero_apply,
      Int.cast_zero, eval_zero_eq_coefficient, NilpotentLieBCHGroup.coord_one] using he
  have hΓmem (j : Fin s) : coefficients Γ.log (Finsupp.single () (j.val + 1)) ∈
      (D.coefficientFreeSpan j).baseChange ℝ :=
    Submodule.baseChange_mono ℝ
      (refined_firstProjection_le_common _ _ (D.dependentFreeSpan_le_coefficientFreeSpan j) _) (hΓ j)
  obtain ⟨J₁, hJ₁J, hJ₁, hcard, u, c, x, y, hu, hperiod, hc, hlocal⟩ :=
    D.exists_common_local_marked_family hB htB η radius hinj h₀ J hJ hJB v' hv' hrep'
      A' Γ.log Γ.degreeLE hΓzero hΓmem α β (fun j => (hα j).1) (fun i j => (hβ i j).1) hA'
  let lift (h : {h // h ∈ J₁}) : {h // h ∈ J} := ⟨h.val, hJ₁J h.property⟩
  refine ⟨J₁, (fun h hh => hJH (hJ₁J hh)), hJ₁, hcard, t, ht,
    h₀, u, c, x, y, hu, hperiod, hc, (fun h => A (lift h)), (fun h => K (lift h)),
    (fun h => U (lift h)), ?_, Δ, hΔ, hchar, hnormal, hfinite, hindex,
    l, hl, hin, hout, hRank, V₁, hfreq, (fun h => hcorr (lift h)), M, Tm, hTm, hTmc, ?_⟩
  · intro h
    obtain ⟨hsmall, hpoly, heval⟩ := hlocal h.val h.property
    have hAA : A' h.val = (A (lift h)).log := by simp only [A', dite_eq_left (hJ₁J h.property), lift]
    rw [hAA] at hpoly heval
    obtain ⟨_, _, _, hA0, hK0, hU0, hKU⟩ := hdata (lift h)
    refine ⟨hsmall, hpoly, hA0, hK0, hU0, hKU, ?_⟩
    intro n
    exact heval n
  · exact hfamily.reindex lift

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3

noncomputable def localCoveredInducedBudget (s : ℕ) (hs : 2 ≤ s) (q p : ℝ) : ℝ :=
  let Z := q + (p + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s +
    sharedFreeCorrelationBudget s hs p + 2
  let C := (NativeRankRelation.CommonData.exists_covered_induced_correlation_family s (by omega)).choose
  (Z + C) ^ C

end Erdos3

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped BigOperators TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s (r + 1) N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure (r + 1)) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s (r + 1)) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)
  {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

def CorrelatedLocalInducedFamily (hs : 2 ≤ s) (Bound : ℝ) : Prop :=
    let Λ := (P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s
    let C := sharedFreeCorrelationBudget s hs P'
    let B := P' + Λ + C
    let Qc := C + sharedFreeComparisonBasisBudget Q P' + 2
    let S := D.comparisonCoefficientSpace E T hbQ hT V g hg D'
    ∃ J ⊆ H', J.Nonempty ∧ Real.exp (-((B + 4) ^ 7)) * N ≤ (J.card : ℝ) ∧
      ∃ t : ℕ, (t : ℝ) ≤ Λ ∧ ∃ (h₀ : ZMod N) (u c : Fin t → ℝ)
        (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
        (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ),
        (∀ i, u i ∈ Set.Ico (0 : ℝ) 1) ∧
        (∀ i, ∃ k : ℤ, (N : ℝ) * u i = (k : ℝ)) ∧
        (∀ i, |c i| ≤ properCyclicCoordinateBound t (Real.exp (-B)) + 1 / 16) ∧
        ∃ A K U : {h // h ∈ J} → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
          (∀ h : {h // h ∈ J},
            (∀ i, |affineCyclicTorusLocalLift u c h₀ h.val i| ≤ 1 / 16) ∧
            (A h).log = positiveUnivariate (fun j => (x j).val +
              ∑ i, affineCyclicTorusLocalLift u c h₀ h.val i • (y j i).val) ∧
            E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (A h) = 1 ∧
            E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (K h) = 1 ∧
            E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (U h) = 1 ∧
            (∀ j : Fin s,
              coefficients (K h).log (Finsupp.single () (j.val + 1)) ∈
                (T.filtration.layer (j.val + 1) 2).baseChange ℝ ∧
              coefficients (U h).log (Finsupp.single () (j.val + 1)) ∈
                (fourPetalSpace (D.dependentFreeSpan j)
                  (fourRefinedRelation (D.coefficientFreeSpan j) (D.dependentFreeSpan j)
                    (D'.coefficientFourSpace ⟨j.val + 1, by omega⟩))).baseChange ℝ) ∧
            ∀ n : ℤ,
              (markedShiftEval D.coefficientFreeFiltration D.coefficientFreeGenerator
                D.coefficientWeight D.coefficientIsDependent t
                  (fun i => (-affineCyclicTorusCarry u c h₀ h.val i : ℤ))).baseChange ℝ
                    (D.localAffineMarkedLift t x y u c h₀ h.val n) =
                      (E.filtration.realification.polynomialOrbitEval
                        (fun _ : Unit => 1) (fun _ => n) (A h)).coord) ∧
          ∃ Δ : Subgroup E.filtration.Group, Δ ≤ E.lattice ∧
            (Δ.subgroupOf E.lattice).Characteristic ∧ (Δ.subgroupOf E.lattice).Normal ∧
            (Δ.subgroupOf E.lattice).FiniteIndex ∧ (Δ.relIndex E.lattice : ℝ) ≤ Real.exp C ∧
            ∃ (l : ℕ) (hl : 0 < l)
              (hin : scaledIntegerGrid l ⊆ bchSubgroupCoordinates E.basis Δ)
              (hout : bchSubgroupCoordinates E.basis Δ ⊆ denominatorGrid l),
              (T.withLattice Δ l hl hin hout).ComplexityLE C ∧
              ∃ V₁ : (E.withLattice Δ l hl hin hout).UnitVerticalObservable
                  ((T.withLattice Δ l hl hin hout).realSubgroup s (r + 1)) (Fin W.family.outputDim) C,
                V₁.frequency = V.frequency ∧
                (∀ h : {h // h ∈ J}, Nonempty (NativeVectorCorrelation (s - 1) N C
                  (W.replacedRankResidual h.val (fun i z => V₁.observable i (QuotientGroup.mk
                    (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                      (fun _ => (z.val : ℤ)) (A h * K h * U h))))))) ∧
                (∃ hCZ : C ≤ Q + Λ + C + 2,
                  D.HasCoveredInducedCorrelationFamily (degree := s - 1)
                    t (E.withLattice Δ l hl hin hout) (T.withLattice Δ l hl hin hout)
                    (V₁.mono hCZ) x y u c h₀ (fun h : {h // h ∈ J} => h.val)
                    A (fun h => A h * K h * U h)
                    (fun h i z => multiplicativeDerivative f h.val z *
                      star (W.mixed.evalCyclic N i (correlationInput h.val z))) Bound) ∧
                ∃ M : RationalFilteredNilmanifold (SubspaceFreeLift.Algebra S (r + 1)) s
                    (finrank ℚ (SubspaceFreeLift.Algebra S (r + 1))),
                  ∃ Tm : M.DegreeRankStructure (r + 1),
                    Tm.filtration = SubspaceFreeLift.filtration S T.filtration.rank_le_degree ∧
                    Tm.ComplexityLE ((Qc + nativePairModelConstant s) ^ nativePairModelConstant s) ∧
                    M.HasLowerRankOrbitFamily Tm (fun _ : Unit => 1)
                      (fun h (i : Fin W.family.outputDim × Fin W.family.outputDim) z =>
                        V₁.observable i.1 (QuotientGroup.mk
                          (E.filtration.realification.polynomialOrbitEval
                            (fun _ : Unit => 1) z (A h * K h * U h))) *
                        star (V₁.observable i.2 (QuotientGroup.mk
                          (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) z (A h)))))
                      (nativeLowerPairModelBudget s Qc)

theorem CorrelatedLocalMarkedFamily.induce
    (B₀ : D.CoefficientBases Q) (F : FreeCoordinateFrame E.basis Q)
    (hTfil : T.filtration = D.coefficientFreeFiltration)
    (hfreq : V.frequency = B₀.freeFrequency D)
    (hs : 2 ≤ s) (hP' : 0 ≤ P')
    (hlocal : D.CorrelatedLocalMarkedFamily E T hbQ hT V g hg D' hs) :
    let Z := Q + (P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s +
      sharedFreeCorrelationBudget s hs P' + 2
    let C := (exists_covered_induced_correlation_family s (by omega)).choose
    D.CorrelatedLocalInducedFamily E T hbQ hT V g hg D' hs ((Z + C) ^ C) := by
  intro Z Cout
  obtain ⟨J, hJH, hJ, hJcard, t, ht, h₀, u, c, x, y, hu, hperiod, hc,
    A, K, U, hdata, Δ, hΔ, hchar, hnormal, hfinite, hindex, l, hl, hin, hout,
    hRank, V₁, hVfreq, hcorr, M, Tm, hTm, hTmc, hfamily⟩ := hlocal
  let Λ := (P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s
  let Cc := sharedFreeCorrelationBudget s hs P'
  have hQ : 0 ≤ Q := (Nat.cast_nonneg W.family.dim).trans (W.family.complexity.1.1.trans hbQ)
  have hΛ : 0 ≤ Λ := by dsimp [Λ]; positivity
  have hCc : 0 ≤ Cc :=
    (show 0 ≤ sharedFreeCorrelationInput s P' by
      linarith only [(sharedFreeCorrelationInput_bounds s hP' le_rfl hP').1]).trans
        (sharedFreeCorrelationInput_le_budget s hs hP')
  have hCZ : Cc ≤ Z := by
    change Cc ≤ Q + Λ + Cc + 2
    linarith
  have hQZ : Q ≤ Z := by
    change Q ≤ Q + Λ + Cc + 2
    linarith
  have hΛZ : Λ ≤ Z := by
    change Λ ≤ Q + Λ + Cc + 2
    linarith
  have hZ : 0 ≤ Z := hCc.trans hCZ
  refine ⟨J, hJH, hJ, hJcard, t, ht, h₀, u, c, x, y, hu, hperiod, hc,
    A, K, U, hdata, Δ, hΔ, hchar, hnormal, hfinite, hindex, l, hl, hin, hout,
    hRank, V₁, hVfreq, hcorr, ?_, M, Tm, hTm, hTmc, hfamily⟩
  refine ⟨hCZ, ?_⟩
  apply (exists_covered_induced_correlation_family s (by omega)).choose_spec.2
    D B₀ t (E.withLattice Δ l hl hin hout) (T.withLattice Δ l hl hin hout) (V₁.mono hCZ)
    hTfil (hVfreq.trans hfreq) hZ (hRank.mono _ hCZ) (ht.trans hΛZ)
    (fun i j => (F.generator_height (by omega) i j).trans hQZ)
    (by
      simpa only [Fintype.card_fin] using
        W.family.output_bound.trans (Real.exp_le_exp.mpr (hbQ.trans hQZ)))
    x y u c h₀ (fun h : {h // h ∈ J} => h.val) A (fun h => A h * K h * U h)
    (fun h i => ((hdata h).1 i).trans (by norm_num))
    (fun h => (hdata h).2.1) (fun h => (hdata h).2.2.1)
  intro h
  exact (hcorr h).map (fun B => B.mono hCZ)

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

def NativeCorrelationStructure.HasLocalMarkedFamily
    {s r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
    (W : NativeCorrelationStructure s (r + 1) N p f) (hs : 2 ≤ s) (C : ℕ) : Prop :=
  let Z := (p + nativeSharedFreeRelationConstant s hs) ^ nativeSharedFreeRelationConstant s hs
  ∃ (A : ℝ) (hpA : p ≤ A), A ≤ Z ∧
  ∃ (out : Fin W.family.outputDim) (H : Finset (ZMod N)) (q P : ℝ),
    H ⊆ W.shifts ∧ H.Nonempty ∧ CyclicShortShiftSet H ∧ p ≤ q ∧ q ≤ P ∧ P ≤ A ∧
    ∃ (R : NativeRankRelation W.family out H q q) (D : R.CommonData P)
      (B : D.CoefficientBases A)
      (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
        (finrank ℚ D.CoefficientFreeLieAlgebra))
      (T : E.DegreeRankStructure (r + 1)) (hT : T.ComplexityLE A),
      T.filtration = D.coefficientFreeFiltration ∧ IsCentralLieBasis E.basis ∧
      Nonempty (FreeCoordinateFrame E.basis A) ∧
      (letI := moduleTopology ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
       letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra) :=
         IsModuleTopology.topologicalAddGroup ℝ _
       letI := realification_moduleTopology_t2 E.basis
       ∃ V : E.UnitVerticalObservable (T.realSubgroup s (r + 1)) (Fin W.family.outputDim) A,
         V.frequency = B.freeFrequency D ∧
         ∃ (ξ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
           (hξ : E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 ξ = 1),
           (∀ d : Fin s, coefficients ξ.log (Finsupp.single () (d.val + 1)) ∈
             (D.commonFreeSpan d).baseChange ℝ) ∧
           ∃ (v : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
             (hv : ∀ h, E.filtration.realification.polynomialOrbitEval
               (fun _ : Unit => 1) 0 (v h) = 1),
             (∀ h (d : Fin s), coefficients (v h).log (Finsupp.single () (d.val + 1)) ∈
               (D.dependentFreeSpan d).baseChange ℝ) ∧
             (let U := W.replacementFamily E T hpA hT V (fun h => ξ * v h)
                (fun h => by rw [map_mul, hξ, hv h, one_mul])
              ∃ (out' : Fin U.outputDim) (H' : Finset (ZMod N)) (q' : ℝ),
                H' ⊆ W.shifts ∧ H'.Nonempty ∧ CyclicShortShiftSet H' ∧
                Real.exp (-Z) * Fintype.card (ZMod N) ≤ (H'.card : ℝ) ∧
                A ≤ q' ∧ q' ≤ Z ∧
                ∃ (R' : NativeRankRelation U out' H' q' q') (D' : R'.CommonData Z),
                  D.CorrelatedLocalMarkedFamily E T hpA hT V (fun h => ξ * v h)
                    (fun h => by rw [map_mul, hξ, hv h, one_mul]) D' hs ∧
                  (Z + (Z + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s +
                    sharedFreeCorrelationBudget s hs Z + 4) ^ 7 ≤ (p + C) ^ C ∧
                  ((sharedFreeCorrelationBudget s hs Z + sharedFreeComparisonBasisBudget A Z + 2) +
                    nativePairModelConstant s) ^ nativePairModelConstant s ≤ (p + C) ^ C ∧
                  nativeLowerPairModelBudget s
                    (sharedFreeCorrelationBudget s hs Z + sharedFreeComparisonBasisBudget A Z + 2) ≤
                    (p + C) ^ C))

theorem exists_native_local_marked_family (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s (r + 1) N p f), (∀ x, ‖f x‖ ≤ 1) →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) → W.HasLocalMarkedFamily hs C := by
  obtain ⟨a, _, hsource⟩ := exists_native_correlated_affine_comparison s hs
  let A₀ : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget (A₀ + (A₀ + 4) ^ 7)
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W hf hN
  have hp : 0 ≤ p := (Nat.cast_nonneg _).trans W.family.complexity.1.1
  have hsum : (p + a) ^ a + ((p + a) ^ a + 4) ^ 7 ≤ (p + C) ^ C := by
    simpa [A₀, Polynomial.eval₂_pow] using hbound p hp
  have ha0 : 0 ≤ (p + a) ^ a := pow_nonneg (add_nonneg hp (Nat.cast_nonneg _)) _
  have haC : (p + a) ^ a ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (by positivity)).trans hsum
  have hchart : ((p + a) ^ a + 4) ^ 7 ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left ha0).trans hsum
  obtain ⟨A, hpA, hAZ, out, H, q, P, hHW, hH, hshort, hpq, hqP, hPA,
      R, D, B, E, T, hT, hTfil, hcentral, hframe, hdata⟩ :=
    hsource W hf ((Real.exp_le_exp.mpr haC).trans hN)
  let Z := (p + nativeSharedFreeRelationConstant s hs) ^ nativeSharedFreeRelationConstant s hs
  have hZ : 0 ≤ Z := pow_nonneg (add_nonneg hp (Nat.cast_nonneg _)) _
  let := moduleTopology ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 E.basis
  obtain ⟨V, hfreq, ξ, hξ, hcommon, v, hv, hdep, out', H', q',
      hsub, hH', hshort', hdense, hAq', hq'Z, R', D', hcomp, htotal, hpair, hlower⟩ := hdata
  have hdense' : Real.exp (-Z) * N ≤ (H'.card : ℝ) := by
    simpa only [ZMod.card] using hdense
  have hlocal := hcomp.localMarkedFamily D E T hpA hT V (fun h => ξ * v h)
    (fun h => by rw [map_mul, hξ, hv h, one_mul]) D' hs hZ hdense'
  have htotal0 : 0 ≤ Z + (Z + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s +
      sharedFreeCorrelationBudget s hs Z := by
    have hcorr0 : 0 ≤ sharedFreeCorrelationBudget s hs Z :=
      (show 0 ≤ sharedFreeCorrelationInput s Z by
        linarith only [(sharedFreeCorrelationInput_bounds s hZ le_rfl hZ).1]).trans
          (sharedFreeCorrelationInput_le_budget s hs hZ)
    exact add_nonneg (add_nonneg hZ (pow_nonneg (add_nonneg hZ (Nat.cast_nonneg _)) _)) hcorr0
  have htotalC : (Z + (Z + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s +
      sharedFreeCorrelationBudget s hs Z + 4) ^ 7 ≤ (p + C) ^ C :=
    (pow_le_pow_left₀ (add_nonneg htotal0 (by norm_num))
      (add_le_add htotal (le_rfl : (4 : ℝ) ≤ 4)) 7).trans hchart
  exact ⟨A, hpA, hAZ, out, H, q, P, hHW, hH, hshort, hpq, hqP, hPA,
    R, D, B, E, T, hT, hTfil, hcentral, hframe, V, hfreq, ξ, hξ, hcommon,
    v, hv, hdep, out', H', q', hsub, hH', hshort', hdense, hAq', hq'Z,
    R', D', hlocal, htotalC, hpair.trans haC, hlower.trans haC⟩

end Erdos3

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped BigOperators TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s (r + 1) N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure (r + 1)) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s (r + 1)) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)
  {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

theorem CorrelatedLocalInducedFamily.product (hs : 2 ≤ s) {Bound : ℝ}
    (hlocal : D.CorrelatedLocalInducedFamily E T hbQ hT V g hg D' hs Bound) :
    let Λ := (P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s
    let C := sharedFreeCorrelationBudget s hs P'
    let B := P' + Λ + C
    let Qc := C + sharedFreeComparisonBasisBudget Q P' + 2
    0 ≤ Bound ∧ 0 ≤ nativeLowerPairModelBudget s Qc ∧
    ∃ J : Finset (ZMod N), J ⊆ H' ∧ J.Nonempty ∧
      Real.exp (-((B + 4) ^ 7)) * N ≤ (J.card : ℝ) ∧
      HasBoundedProductCorrelation (I := Fin W.family.outputDim) (s := s) (r := r) (degree := s - 1)
        (fun h : {h // h ∈ J} => h.val) (fun h z => multiplicativeDerivative f h.val z)
        W.mixed.outputDim Bound
        (productNiltestBudget (nativeLowerPairModelBudget s Qc + Bound + 2))
        (productNiltestBudget (b + Bound + 2 + 4)) := by
  intro Λ C B Qc
  obtain ⟨J, hJH, hJ, hJcard, t, _, h₀, u, c, x, y, _, _, _,
    A, K, U, _, Δ, _, _, _, _, _, l, hl, hin, hout,
    _, V₁, _, _, hcovered, M, Tm, _, _, hfirst⟩ := hlocal
  obtain ⟨hCZ, hcovered⟩ := hcovered
  have hBound : 0 ≤ Bound := by
    obtain ⟨Δ₂, _, l₂, hl₂, hin₂, hout₂, hT₂, _⟩ := hcovered
    exact (Nat.cast_nonneg _).trans hT₂.1.1
  have hFirst : 0 ≤ nativeLowerPairModelBudget s Qc := by
    obtain ⟨n₀, _, Q₀, R₀, hR₀, _⟩ := hfirst
    exact (Nat.cast_nonneg n₀).trans hR₀.1.1
  have hunit := HasCoveredInducedCorrelationFamily.combineLower
    D t x y u c h₀ (fun h : {h // h ∈ J} => h.val)
    (fun h i z => multiplicativeDerivative f h.val z *
      star (W.mixed.evalCyclic N i (correlationInput h.val z)))
    (E.withLattice Δ l hl hin hout) (T.withLattice Δ l hl hin hout)
    (V₁.mono hCZ) A (fun h => A h * K h * U h)
    hBound hFirst hcovered M Tm hfirst
  refine ⟨hBound, hFirst, J, hJH, hJ, hJcard, ?_⟩
  exact HasUnitRankInducedCorrelationFamily.combineMixed D t x y u c h₀
    (fun h : {h // h ∈ J} => h.val) (fun h z => multiplicativeDerivative f h.val z)
    W.mixed hBound hunit

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_localCoveredInducedBudget_bound (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ q p : ℝ, 0 ≤ q → q ≤ p → 0 ≤ p →
      localCoveredInducedBudget s hs q p ≤ (p + C) ^ C := by
  obtain ⟨a, _, hsource⟩ := exists_sharedFreeCorrelationBudget_bound s hs
  let c := (NativeRankRelation.CommonData.exists_covered_induced_correlation_family s (by omega)).choose
  let P : Polynomial ℕ := (Polynomial.X + (Polynomial.X + Polynomial.C a) ^ a +
    2 + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro q p hq hqp hp
  obtain ⟨hsize, _, _⟩ := hsource q p hq hqp hp
  have hcorr : 0 ≤ sharedFreeCorrelationBudget s hs p :=
    (show 0 ≤ sharedFreeCorrelationInput s p by
      linarith only [(sharedFreeCorrelationInput_bounds s hp le_rfl hp).1]).trans
        (sharedFreeCorrelationInput_le_budget s hs hp)
  have hbase : 0 ≤ q + (p + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s +
      sharedFreeCorrelationBudget s hs p + 2 + c := by positivity
  have hle : q + (p + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s +
      sharedFreeCorrelationBudget s hs p + 2 + c ≤ p + (p + a) ^ a + 2 + c := by linarith
  have hb : (p + (p + a) ^ a + 2 + c) ^ c ≤ (p + C) ^ C := by
    simpa [P, Polynomial.eval₂_pow] using hbudget p hp
  exact (pow_le_pow_left₀ hbase hle c).trans hb

def NativeCorrelationStructure.HasLocalInducedFamily
    {s r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
    (W : NativeCorrelationStructure s (r + 1) N p f) (hs : 2 ≤ s) (C : ℕ) : Prop :=
  let Z := (p + nativeSharedFreeRelationConstant s hs) ^ nativeSharedFreeRelationConstant s hs
  ∃ (A : ℝ) (hpA : p ≤ A), A ≤ Z ∧
  ∃ (out : Fin W.family.outputDim) (H : Finset (ZMod N)) (q P : ℝ),
    H ⊆ W.shifts ∧ H.Nonempty ∧ CyclicShortShiftSet H ∧ p ≤ q ∧ q ≤ P ∧ P ≤ A ∧
    ∃ (R : NativeRankRelation W.family out H q q) (D : R.CommonData P)
      (B : D.CoefficientBases A)
      (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
        (finrank ℚ D.CoefficientFreeLieAlgebra))
      (T : E.DegreeRankStructure (r + 1)) (hT : T.ComplexityLE A),
      T.filtration = D.coefficientFreeFiltration ∧ IsCentralLieBasis E.basis ∧
      Nonempty (FreeCoordinateFrame E.basis A) ∧
      (letI := moduleTopology ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
       letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra) :=
         IsModuleTopology.topologicalAddGroup ℝ _
       letI := realification_moduleTopology_t2 E.basis
       ∃ V : E.UnitVerticalObservable (T.realSubgroup s (r + 1)) (Fin W.family.outputDim) A,
         V.frequency = B.freeFrequency D ∧
         ∃ (ξ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
           (hξ : E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 ξ = 1),
           (∀ d : Fin s, coefficients ξ.log (Finsupp.single () (d.val + 1)) ∈
             (D.commonFreeSpan d).baseChange ℝ) ∧
           ∃ (v : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
             (hv : ∀ h, E.filtration.realification.polynomialOrbitEval
               (fun _ : Unit => 1) 0 (v h) = 1),
             (∀ h (d : Fin s), coefficients (v h).log (Finsupp.single () (d.val + 1)) ∈
               (D.dependentFreeSpan d).baseChange ℝ) ∧
             (let U := W.replacementFamily E T hpA hT V (fun h => ξ * v h)
                (fun h => by rw [map_mul, hξ, hv h, one_mul])
              ∃ (out' : Fin U.outputDim) (H' : Finset (ZMod N)) (q' : ℝ),
                H' ⊆ W.shifts ∧ H'.Nonempty ∧ CyclicShortShiftSet H' ∧
                Real.exp (-Z) * Fintype.card (ZMod N) ≤ (H'.card : ℝ) ∧
                A ≤ q' ∧ q' ≤ Z ∧
                ∃ (R' : NativeRankRelation U out' H' q' q') (D' : R'.CommonData Z),
                  D.CorrelatedLocalInducedFamily E T hpA hT V (fun h => ξ * v h)
                    (fun h => by rw [map_mul, hξ, hv h, one_mul]) D' hs
                    (localCoveredInducedBudget s hs A Z) ∧
                  localCoveredInducedBudget s hs A Z ≤ (p + C) ^ C ∧
                  (Z + (Z + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s +
                    sharedFreeCorrelationBudget s hs Z + 4) ^ 7 ≤ (p + C) ^ C ∧
                  ((sharedFreeCorrelationBudget s hs Z + sharedFreeComparisonBasisBudget A Z + 2) +
                    nativePairModelConstant s) ^ nativePairModelConstant s ≤ (p + C) ^ C ∧
                  nativeLowerPairModelBudget s
                    (sharedFreeCorrelationBudget s hs Z + sharedFreeComparisonBasisBudget A Z + 2) ≤
                    (p + C) ^ C))

theorem exists_native_local_induced_family (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s (r + 1) N p f), (∀ x, ‖f x‖ ≤ 1) →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) → W.HasLocalInducedFamily hs C := by
  obtain ⟨a, _, hsource⟩ := exists_native_local_marked_family s hs
  obtain ⟨b, _, hlocalBudget⟩ := exists_localCoveredInducedBudget_bound s hs
  let A₀ : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  let Z₀ : Polynomial ℕ := (Polynomial.X + Polynomial.C (nativeSharedFreeRelationConstant s hs)) ^
    nativeSharedFreeRelationConstant s hs
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (A₀ + (Z₀ + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W hf hN
  have hp : 0 ≤ p := (Nat.cast_nonneg W.family.dim).trans W.family.complexity.1.1
  let Z := (p + nativeSharedFreeRelationConstant s hs) ^ nativeSharedFreeRelationConstant s hs
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have htotal : (p + a) ^ a + (Z + b) ^ b ≤ (p + C) ^ C := by
    simpa [A₀, Z₀, Z, Polynomial.eval₂_pow] using hbudget p hp
  have haC : (p + a) ^ a ≤ (p + C) ^ C := (le_add_of_nonneg_right (by positivity)).trans htotal
  have hbC : (Z + b) ^ b ≤ (p + C) ^ C := (le_add_of_nonneg_left (by positivity)).trans htotal
  obtain ⟨A, hpA, hAZ, out, H, q, P, hHW, hH, hshort, hpq, hqP, hPA,
    R, D, B, E, T, hT, hTfil, hcentral, hframe, hdata⟩ :=
    hsource W hf ((Real.exp_le_exp.mpr haC).trans hN)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 E.basis
  obtain ⟨V, hfreq, ξ, hξ, hcommon, v, hv, hdep, out', H', q', hsub, hH',
    hshort', hdense, hAq', hq'Z, R', D', hlocal, hchart, hpair, hlower⟩ := hdata
  obtain ⟨F⟩ := hframe
  have hinduced := hlocal.induce D E T hpA hT V (fun h => ξ * v h)
    (fun h => by rw [map_mul, hξ, hv h, one_mul]) D' B F hTfil hfreq hs hZ
  have hbound : localCoveredInducedBudget s hs A Z ≤ (p + C) ^ C :=
    (hlocalBudget A Z (hp.trans hpA) hAZ hZ).trans hbC
  refine ⟨A, hpA, hAZ, out, H, q, P, hHW, hH, hshort, hpq, hqP, hPA,
    R, D, B, E, T, hT, hTfil, hcentral, ⟨F⟩, V, hfreq, ξ, hξ, hcommon,
    v, hv, hdep, out', H', q', hsub, hH', hshort', hdense, hAq', hq'Z, R', D',
    hinduced, hbound, hchart.trans haC, hpair.trans haC, hlower.trans haC⟩

end Erdos3

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem productNiltestBudget_mono {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) :
    productNiltestBudget p ≤ productNiltestBudget q := by
  unfold productNiltestBudget productObservableLipBudget
  gcongr

theorem exists_native_product_correlation (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s (r + 1) N p f), (∀ x, ‖f x‖ ≤ 1) →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∃ J : Finset (ZMod N), J ⊆ W.shifts ∧ J.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * N ≤ (J.card : ℝ) ∧
        HasBoundedProductCorrelation (I := Fin W.family.outputDim) (s := s) (r := r) (degree := s - 1)
          (fun h : {h // h ∈ J} => h.val) (fun h z => multiplicativeDerivative f h.val z)
          W.mixed.outputDim ((p + C) ^ C) ((p + C) ^ C) ((p + C) ^ C) := by
  obtain ⟨a, _, hsource⟩ := exists_native_local_induced_family s hs
  let X : Polynomial ℕ := Polynomial.X
  let R₀ : Polynomial ℕ := (X + Polynomial.C a) ^ a
  let P₀ : Polynomial ℕ := X + 2 * R₀ + 6
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (R₀ + ((P₀ + 2) ^ 2 + P₀ + (P₀ + (P₀ ^ 2 + P₀ + 3) ^ 2) + P₀ ^ 2 + 4) + 1)
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W hf hN
  have hp : 0 ≤ p := (Nat.cast_nonneg W.family.dim).trans W.family.complexity.1.1
  let Rcap := (p + a) ^ a
  let Pcap := p + 2 * Rcap + 6
  have hRcap : 0 ≤ Rcap := by dsimp [Rcap]; positivity
  have hPcap : 0 ≤ Pcap := by dsimp [Pcap]; positivity
  have htotal : Rcap + productNiltestBudget Pcap + 1 ≤ (p + C) ^ C := by
    simpa [X, R₀, P₀, Rcap, Pcap, productNiltestBudget, productObservableLipBudget,
      Polynomial.eval₂_pow] using hbudget p hp
  have hprod0 : 0 ≤ productNiltestBudget Pcap :=
    (sq_nonneg (Pcap + 2)).trans (productNiltestBudget_geometry hPcap)
  have hRC : Rcap ≤ (p + C) ^ C := by linarith
  have hPC : productNiltestBudget Pcap ≤ (p + C) ^ C := by linarith
  obtain ⟨A, hpA, hAZ, out, H, q, P, hHW, hH, hshort, hpq, hqP, hPA,
    R, D, B, E, T, hT, hTfil, hcentral, hframe, hdata⟩ :=
    hsource W hf ((Real.exp_le_exp.mpr hRC).trans hN)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 E.basis
  obtain ⟨V, hfreq, ξ, hξ, hcommon, v, hv, hdep, out', H', q', hsub, hH',
    hshort', hdense, hAq', hq'Z, R', D', hlocal, hbound, hchart, hpair, hlower⟩ := hdata
  obtain ⟨hBound, hFirst, J, hJH, hJ, hJcard, hproduct⟩ :=
    hlocal.product D E T hpA hT V (fun h => ξ * v h)
      (fun h => by rw [map_mul, hξ, hv h, one_mul]) D' hs
  refine ⟨J, hJH.trans hsub, hJ, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (neg_le_neg (hchart.trans hRC))) (Nat.cast_nonneg N)).trans hJcard
  · apply hproduct.mono (hbound.trans hRC)
    · apply le_trans (productNiltestBudget_mono (by positivity) _) hPC
      change _ ≤ p + 2 * Rcap + 6
      change _ ≤ Rcap at hlower hbound
      linarith
    · apply le_trans (productNiltestBudget_mono (by positivity) _) hPC
      change _ ≤ p + 2 * Rcap + 6
      change _ ≤ Rcap at hbound
      linarith

end Erdos3

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_mixed_pair_orbit_factors (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r : ℝ}
      {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
        Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
      (_F : NativeMixedPairFactorization V r), 0 ≤ r →
      Real.exp ((p + q + r + C) ^ C) ≤ (N : ℝ) →
      Nonempty (NativePolynomialOrbitFactors (pi V.mixedPairModels)
        V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
        (fun _ : Fin (n + 2) => (N : ℝ)) ((p + q + r + C) ^ C)) := by
  obtain ⟨a, _, hconstruct⟩ := exists_native_polynomial_orbit_factors
    (∑ _ : MixedReplicatedIndex (n + 1), 1)
  let X : Polynomial ℕ := Polynomial.X
  let B := 4 * (X + 1) + (X + (X + 2) ^ 2 + 3) + 6
  let T := (B + 2) ^ 2 + B + (B + (B ^ 2 + B + 3) ^ 2) + B ^ 2 + 4 + X + Polynomial.C (n + 2)
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro p q r W N _ i j V F hr hN
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let u := p + q + r
  let b := 4 * (u + 1) + raisedNiltestBudget u + 6
  let t := productNiltestBudget b + u + ((n + 2 : ℕ) : ℝ)
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hpqu : p + q ≤ u := le_add_of_nonneg_right hr
  have hb : 0 ≤ b := by dsimp [b, raisedNiltestBudget]; positivity
  have hprod : 0 ≤ productNiltestBudget b := by
    unfold productNiltestBudget productObservableLipBudget
    positivity
  have hdim : (0 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hrt : r ≤ t := by dsimp [t, u]; linarith
  have hdimt : ((n + 2 : ℕ) : ℝ) ≤ t := by dsimp [t]; linarith
  have hBt : mixedPairBudget p q ≤ b := by
    dsimp [mixedPairBudget, b, raisedNiltestBudget]
    gcongr
  have hB0 : 0 ≤ mixedPairBudget p q :=
    (by norm_num : (0 : ℝ) ≤ 6).trans V.mixedPairBudget_six_le
  have hprodmono : productNiltestBudget (mixedPairBudget p q) ≤ productNiltestBudget b := by
    exact productNiltestBudget_mono hB0 hBt
  have htest : productNiltestBudget (mixedPairBudget p q) ≤ t :=
    hprodmono.trans (by dsimp [t]; linarith)
  have hcost : (t + a) ^ a ≤ (p + q + r + C) ^ C := by
    simpa [X, B, T, t, b, u, raisedNiltestBudget, productNiltestBudget,
      productObservableLipBudget, Polynomial.eval₂_pow] using hbudget u hu
  let := F.topology
  let := F.topologicalAdd
  let := F.continuousSMul
  let := F.hausdorff
  let D := pi V.mixedPairModels
  have hfactor : D.filtration.ControlledSymbolFactorization F.basis F.weight F.adapted
      (piFrequency V.mixedPairFrequencies) (fun _ : Fin (n + 2) => (N : ℝ))
      (D.filtration.realPolynomialSymbolHom F.basis F.weight F.adapted
        (fun _ => 1) V.mixedPairPolynomial) t := by
    have h := F.factorization
    rw [V.mixedPairNiltest_symbol] at h
    have H := NilpotentLieFiltration.ControlledSymbolFactorization.mono
      (pi V.mixedPairModels).filtration F.basis F.weight F.adapted h hrt
      (fun _ => by exact_mod_cast NeZero.pos N)
    dsimp only [D]
    exact H
  obtain ⟨R⟩ := hconstruct D F.basis F.weight F.adapted ht
    (V.mixedPairNiltest_complexity.1.mono D htest) (by simpa only [Fintype.card_fin] using hdimt)
    (fun a b => (F.height a b).trans hrt) V.mixedPairPolynomial
    (piFrequency V.mixedPairFrequencies) (fun _ : Fin (n + 2) => (N : ℝ))
    (fun _ => (Real.exp_le_exp.mpr hcost).trans hN) hfactor
  exact ⟨R.mono hcost (fun _ => by exact_mod_cast NeZero.pos N)⟩

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_mixed_pair_outer_control (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r : ℝ}
      {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
        Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
      (R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
        V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
        (fun _ : Fin (n + 2) => (N : ℝ)) r), 0 ≤ r →
      R.HasOuterValueControl ((p + q + r + C) ^ C) := by
  obtain ⟨a, _, hcontrol⟩ := exists_native_orbit_outer_control
    (∑ _ : MixedReplicatedIndex (n + 1), 1) (n + 2)
  let X : Polynomial ℕ := Polynomial.X
  let B := 4 * (X + 1) + (X + (X + 2) ^ 2 + 3) + 6
  let T := (B + 2) ^ 2 + B + (B + (B ^ 2 + B + 3) ^ 2) + B ^ 2 + 4 + X + 3
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro p q r W N _ i j V R hr
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let u := p + q + r
  let b := 4 * (u + 1) + raisedNiltestBudget u + 6
  let t := productNiltestBudget b + u + 3
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hpqu : p + q ≤ u := le_add_of_nonneg_right hr
  have hb : 0 ≤ b := by dsimp [b, raisedNiltestBudget]; positivity
  have hprod : 0 ≤ productNiltestBudget b := by
    unfold productNiltestBudget productObservableLipBudget
    positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hrt : r ≤ t := by dsimp [t, u]; linarith
  have hBt : mixedPairBudget p q ≤ b := by
    dsimp [mixedPairBudget, b, raisedNiltestBudget]
    gcongr
  have hB0 : 0 ≤ mixedPairBudget p q :=
    (by norm_num : (0 : ℝ) ≤ 6).trans V.mixedPairBudget_six_le
  have hprodmono : productNiltestBudget (mixedPairBudget p q) ≤ productNiltestBudget b :=
    productNiltestBudget_mono hB0 hBt
  have htest : productNiltestBudget (mixedPairBudget p q) ≤ t :=
    hprodmono.trans (by dsimp [t]; linarith)
  let D := pi V.mixedPairModels
  have hD : D.GeometryComplexityLE t := by
    apply (pi_geometry V.mixedPairModels hB0
      (by simpa using (show (3 : ℝ) ≤ mixedPairBudget p q from
        (by norm_num : (3 : ℝ) ≤ 6).trans V.mixedPairBudget_six_le))
      (fun k => (V.mixedPairTests_complexity k).1)).mono D
    exact (productNiltestBudget_geometry hB0).trans htest
  have hcost : (t + a) ^ a ≤ (p + q + r + C) ^ C := by
    simpa [X, B, T, t, b, u, raisedNiltestBudget, productNiltestBudget,
      productObservableLipBudget, Polynomial.eval₂_pow] using hbudget u hu
  have hN : ∀ _k : Fin (n + 2), (0 : ℝ) < N := fun _ => Nat.cast_pos.mpr (NeZero.pos N)
  have hout : R.HasOuterValueControl ((t + a) ^ a) :=
    hcontrol (R.mono hrt hN) ht hD hN (by simp)
  exact R.hasOuterValueControl_mono hout hcost

end Erdos3

end

section

namespace Erdos3.NativePolynomialOrbitFactors

open RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

variable {n : ℕ} {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p} {i j : Fin W.outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
  (R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
    V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
    (fun _ : Fin (n + 2) => (N : ℝ)) r)

theorem mixed_pair_top_agreement (x : ℝ ⊗[ℚ] V.MixedPairAlgebra)
    (hx : x ∈ (pi V.mixedPairModels).filtration.realGradedRefiltrationLayer
      R.subalgebra (∑ _ : MixedReplicatedIndex (n + 1), 1)) :
    realifyFunctional W.vertical.frequency (realificationLieHom (V.mixedPairProjection 0) x) =
      realifyFunctional W.vertical.frequency (realificationLieHom (V.mixedPairProjection 1) x) := by
  have h := R.kills_top x hx
  rw [V.mixedPairFrequency_real] at h
  linarith

theorem mixed_pair_middle_top_agreement (α : (Fin (n + 2)) →₀ ℕ)
    (hα : Finsupp.weight (fun _ => 1) α = ∑ _ : MixedReplicatedIndex (n + 1), 1) :
    realifyFunctional W.vertical.frequency (realificationLieHom (V.mixedPairProjection 0)
      (coefficients (R.middle.coord : VectorPolynomial (Fin (n + 2)) ℚ
        (ℝ ⊗[ℚ] V.MixedPairAlgebra)) α)) =
    realifyFunctional W.vertical.frequency (realificationLieHom (V.mixedPairProjection 1)
      (coefficients (R.middle.coord : VectorPolynomial (Fin (n + 2)) ℚ
        (ℝ ⊗[ℚ] V.MixedPairAlgebra)) α)) := by
  apply R.mixed_pair_top_agreement
  simpa only [hα] using R.middle_coefficients α

theorem mixed_pair_middle_bracket_agreement (α β : (Fin (n + 2)) →₀ ℕ)
    (hαβ : Finsupp.weight (fun _ => 1) α + Finsupp.weight (fun _ => 1) β =
      ∑ _ : MixedReplicatedIndex (n + 1), 1) :
    realifyFunctional W.vertical.frequency
      ⁅realificationLieHom (V.mixedPairProjection 0)
          (coefficients (R.middle.coord : VectorPolynomial (Fin (n + 2)) ℚ
            (ℝ ⊗[ℚ] V.MixedPairAlgebra)) α),
        realificationLieHom (V.mixedPairProjection 0)
          (coefficients (R.middle.coord : VectorPolynomial (Fin (n + 2)) ℚ
            (ℝ ⊗[ℚ] V.MixedPairAlgebra)) β)⁆ =
    realifyFunctional W.vertical.frequency
      ⁅realificationLieHom (V.mixedPairProjection 1)
          (coefficients (R.middle.coord : VectorPolynomial (Fin (n + 2)) ℚ
            (ℝ ⊗[ℚ] V.MixedPairAlgebra)) α),
        realificationLieHom (V.mixedPairProjection 1)
          (coefficients (R.middle.coord : VectorPolynomial (Fin (n + 2)) ℚ
            (ℝ ⊗[ℚ] V.MixedPairAlgebra)) β)⁆ := by
  have h := R.middle_bracket_frequency α β hαβ
  rw [V.mixedPairFrequency_real] at h
  simp only [LieHom.map_lie] at h
  linarith

variable [TopologicalSpace (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.MixedPairAlgebra)]

theorem mixed_pair_eval_factors (x : Fin (n + 2) → ℤ) :
    W.mixedAntisymmetric i j x * star (V.test.eval x) =
      V.mixedPairNiltest.observable (QuotientGroup.mk
        ((pi V.mixedPairModels).filtration.adaptedPolynomialRealValueHom
            (fun _ : Fin (n + 2) => 1) (fun k => (x k : ℝ)) R.slow *
          (pi V.mixedPairModels).filtration.adaptedPolynomialRealValueHom
            (fun _ : Fin (n + 2) => 1) (fun k => (x k : ℝ)) R.middle *
          (pi V.mixedPairModels).filtration.adaptedPolynomialRealValueHom
            (fun _ : Fin (n + 2) => 1) (fun k => (x k : ℝ)) R.rational)) := by
  rw [← V.mixedPairNiltest_eval x]
  exact R.eval_niltest V.mixedPairNiltest V.mixedPairPolynomial_eq_test x

theorem mixed_pair_top_layer_invariant (z : (pi V.mixedPairModels).RealGroup)
    (hz : z.coord ∈ (pi V.mixedPairModels).filtration.realGradedRefiltrationLayer
      R.subalgebra (∑ _ : MixedReplicatedIndex (n + 1), 1)) (x : (pi V.mixedPairModels).Space) :
    V.mixedPairNiltest.observable (z • x) = V.mixedPairNiltest.observable x := by
  have htop : z ∈ (pi V.mixedPairModels).filtration.realification.subgroup
      (∑ _ : MixedReplicatedIndex (n + 1), 1) :=
    (pi V.mixedPairModels).filtration.realGradedRefiltrationLayer_le R.subalgebra _ hz
  rw [V.mixedPairNiltest_vertical z htop, R.kills_top z.coord hz]
  simp only [AddCircle.coe_zero, CircleFourier.character_zero, one_mul]

end Erdos3.NativePolynomialOrbitFactors

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

namespace NativeSampleCorrelation

variable {n : ℕ} {p q : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p} {i j : Fin W.outputDim}
  (V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.mixedAntisymmetric i j (fun k => ((z k).val : ℤ))))

include V in
theorem mixedPairComparison_component_cost : p + 4 ≤ mixedPairBudget p q := by
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  have hr : 0 ≤ raisedNiltestBudget (p + q) :=
    (add_nonneg hp hq).trans (le_raisedNiltestBudget _)
  unfold mixedPairBudget
  linarith

noncomputable def mixedPairComparisonTests (a b : Fin W.outputDim) :
    ∀ k, (V.mixedPairModels k).Niltest (fun _ : Fin (n + 2) => 1)
  | none => (V.test.raiseStep (by rw [mixedReplicated_totalDegree]; omega :
      n + 1 ≤ ∑ _ : MixedReplicatedIndex (n + 1), 1)).oneOnOrbit
  | some k => ![W.mixedPairComponent a id, (W.mixedPairComponent b (mixedExchangeCoordinate n)).conjugate] k

theorem mixedPairComparisonTests_complexity (a b : Fin W.outputDim) (k : Option (Fin 2)) :
    (V.mixedPairComparisonTests a b k).ComplexityLE (mixedPairBudget p q) := by
  cases k with
  | none =>
    exact Niltest.oneOnOrbit_complexity _
      ((by norm_num : (2 : ℝ) ≤ 6).trans V.mixedPairBudget_six_le)
      (V.mixedPairTests_complexity none).1
  | some k =>
    fin_cases k
    · exact (W.mixedPairComponent_complexity a id).mono V.mixedPairComparison_component_cost
    · exact (W.mixedPairComponent_complexity b (mixedExchangeCoordinate n)).mono V.mixedPairComparison_component_cost

theorem mixedPairComparisonTests_vertical (a b : Fin W.outputDim) (k : Option (Fin 2))
    (z : (V.mixedPairModels k).RealGroup)
    (hz : z ∈ (V.mixedPairModels k).filtration.realification.subgroup
      (∑ _ : MixedReplicatedIndex (n + 1), 1)) (x : (V.mixedPairModels k).Space) :
    (V.mixedPairComparisonTests a b k).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (V.mixedPairFrequencies k) z.coord : ℝ) :
          CircleFourier.Circle) * (V.mixedPairComparisonTests a b k).observable x := by
  cases k with
  | none => exact Niltest.oneOnOrbit_vertical _ z x
  | some k =>
    fin_cases k
    · exact W.mixedPairComponent_vertical a id z hz x
    · exact Niltest.conjugate_vertical _ _ (W.mixedPairComponent_vertical b (mixedExchangeCoordinate n)) z hz x

variable [TopologicalSpace (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.MixedPairAlgebra)]

noncomputable def mixedPairComparisonNiltest (a b : Fin W.outputDim) :
    (pi V.mixedPairModels).Niltest (fun _ : Fin (n + 2) => 1) :=
  piNiltest V.mixedPairModels (V.mixedPairComparisonTests a b)
    ((by norm_num : (0 : ℝ) ≤ 6).trans V.mixedPairBudget_six_le)
    (by simpa using (show (3 : ℝ) ≤ mixedPairBudget p q from
      (by norm_num : (3 : ℝ) ≤ 6).trans V.mixedPairBudget_six_le))
    (V.mixedPairComparisonTests_complexity a b)

theorem mixedPairComparisonNiltest_complexity (a b : Fin W.outputDim) :
    (V.mixedPairComparisonNiltest a b).ComplexityLE
      (productNiltestBudget (mixedPairBudget p q)) :=
  piNiltest_complexity V.mixedPairModels (V.mixedPairComparisonTests a b) _ _ _

theorem mixedPairComparisonNiltest_orbit (a b : Fin W.outputDim) :
    (V.mixedPairComparisonNiltest a b).orbit = V.mixedPairNiltest.orbit := by
  change NilpotentLieFiltration.piRealOrbit _ _ = NilpotentLieFiltration.piRealOrbit _ _
  apply congrArg (NilpotentLieFiltration.piRealOrbit
    (fun k => (V.mixedPairModels k).filtration))
  funext k
  cases k with
  | none => rfl
  | some k => fin_cases k <;> rfl

theorem mixedPairComparisonNiltest_observable (a b : Fin W.outputDim)
    (x : (pi V.mixedPairModels).Space) :
    (V.mixedPairComparisonNiltest a b).observable x =
      W.vertical.observable a (productProjection V.mixedPairModels (some 0) x) *
        star (W.vertical.observable b (productProjection V.mixedPairModels (some 1) x)) := by
  change (∏ k, (V.mixedPairComparisonTests a b k).observable
    (productProjection V.mixedPairModels k x)) = _
  rw [Fintype.prod_option, Fin.prod_univ_two]
  change 1 * (W.vertical.observable a
    (productProjection V.mixedPairModels (some 0) x) *
      star (W.vertical.observable b (productProjection V.mixedPairModels (some 1) x))) = _
  exact one_mul _

theorem mixedPairComparisonNiltest_vertical (a b : Fin W.outputDim)
    (z : (pi V.mixedPairModels).RealGroup)
    (hz : z ∈ (pi V.mixedPairModels).filtration.realification.subgroup
      (∑ _ : MixedReplicatedIndex (n + 1), 1)) (x : (pi V.mixedPairModels).Space) :
    (V.mixedPairComparisonNiltest a b).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (piFrequency V.mixedPairFrequencies) z.coord : ℝ) :
          CircleFourier.Circle) * (V.mixedPairComparisonNiltest a b).observable x :=
  piNiltest_vertical V.mixedPairModels (V.mixedPairComparisonTests a b)
    V.mixedPairFrequencies _ _ _ (V.mixedPairComparisonTests_vertical a b) z hz x

end NativeSampleCorrelation

namespace NativePolynomialOrbitFactors

variable {n : ℕ} {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p} {i j : Fin W.outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
  (R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
    V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
    (fun _ : Fin (n + 2) => (N : ℝ)) r)
  [TopologicalSpace (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.MixedPairAlgebra)]

theorem mixed_pair_comparison_invariant (a b : Fin W.outputDim)
    (z : (pi V.mixedPairModels).RealGroup)
    (hz : z.coord ∈ (pi V.mixedPairModels).filtration.realGradedRefiltrationLayer
      R.subalgebra (∑ _ : MixedReplicatedIndex (n + 1), 1)) (x : (pi V.mixedPairModels).Space) :
    (V.mixedPairComparisonNiltest a b).observable (z • x) =
      (V.mixedPairComparisonNiltest a b).observable x := by
  have htop : z ∈ (pi V.mixedPairModels).filtration.realification.subgroup
      (∑ _ : MixedReplicatedIndex (n + 1), 1) :=
    (pi V.mixedPairModels).filtration.realGradedRefiltrationLayer_le R.subalgebra _ hz
  rw [V.mixedPairComparisonNiltest_vertical a b z htop, R.kills_top z.coord hz]
  simp only [AddCircle.coe_zero, CircleFourier.character_zero, one_mul]

end NativePolynomialOrbitFactors

end Erdos3

end

end OAI
