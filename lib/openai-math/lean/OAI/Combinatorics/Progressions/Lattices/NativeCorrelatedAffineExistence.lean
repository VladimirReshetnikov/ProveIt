import OAI.Combinatorics.Progressions.Estimates.SharedFreeCorrelatedFactorization

namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s (r + 1) N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (B₀ : D.CoefficientBases Q)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure (r + 1)) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  (F : FreeCoordinateFrame E.basis Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s (r + 1)) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

def CorrelatedAffineComparison (hs : 2 ≤ s) : Prop :=
    let Λ := (P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s
    let C := sharedFreeCorrelationBudget s hs P'
    let Qc := C + sharedFreeComparisonBasisBudget Q P' + 2
    let Lv := sharedFreePetalLiftBudget s Q P'
    let S := D.comparisonCoefficientSpace E T hbQ hT V g hg D'
    ∃ J ⊆ H', J.Nonempty ∧ Real.exp (-(Λ + C)) * H'.card ≤ (J.card : ℝ) ∧
      ∃ (r₀ : ℕ) (R₀ : Fin r₀ → ℕ) (η : (Fin r₀ → ℤ) →+ ZMod N) (h₀ : ZMod N)
        (Γ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
        (α : Fin s → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
        (β : Fin r₀ → Fin s → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra),
        (r₀ : ℝ) ≤ Λ ∧ Set.InjOn η {x | ∀ j, |x j| ≤ (R₀ j : ℤ)} ∧ E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 Γ = 1 ∧
        (∀ d : Fin s, coefficients Γ.log (Finsupp.single () (d.val + 1)) ∈
          ((fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
            (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)).map (LinearMap.proj 0)).baseChange ℝ) ∧
        (∀ d, α d ∈ (D.dependentFreeSpan d).baseChange ℝ ∧
          ‖(E.basis.baseChange ℝ).equivFun (α d)‖ ≤ Real.exp Lv) ∧
        (∀ j d, β j d ∈ (D.dependentFreeSpan d).baseChange ℝ ∧
          ‖(E.basis.baseChange ℝ).equivFun (β j d)‖ ≤ Real.exp Lv) ∧
        ∃ (x : {h // h ∈ J} → Fin r₀ → ℤ)
          (A K U : {h // h ∈ J} → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1)),
          (∀ h : {h // h ∈ J},
            (∀ j, |x h j| ≤ (R₀ j : ℤ)) ∧ h.val = h₀ + η (x h) ∧
            (A h).log = Γ.log + positiveUnivariate (fun d => α d + ∑ j, (x h j : ℝ) • β j d) ∧
            E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (A h) = 1 ∧
            E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (K h) = 1 ∧
            E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (U h) = 1 ∧
            ∀ d : Fin s,
              coefficients (K h).log (Finsupp.single () (d.val + 1)) ∈
                (T.filtration.layer (d.val + 1) 2).baseChange ℝ ∧
              coefficients (U h).log (Finsupp.single () (d.val + 1)) ∈
                (fourPetalSpace (D.dependentFreeSpan d)
                  (fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
                    (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩))).baseChange ℝ) ∧
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

include F

theorem CoefficientBases.has_correlated_affine_comparison
    (hTfil : T.filtration = D.coefficientFreeFiltration)
    (hfreq : V.frequency = B₀.freeFrequency D)
    (hs : 2 ≤ s) (hp' : 0 ≤ p') (hP' : 0 ≤ P') (hQP' : Q ≤ P') (hpp' : p' ≤ P')
    (hf : ∀ x, ‖f x‖ ≤ 1)
    (Hsource : Finset (ZMod N)) (hsource : Hsource.Nonempty)
    (hsourceDense : Real.exp (-Q) * Fintype.card (ZMod N) ≤ (Hsource.card : ℝ))
    (hHsource : H' ⊆ Hsource)
    (hcorr : ∀ h ∈ Hsource, Nonempty (NativeVectorCorrelation (s - 1) N Q
      (W.replacedRankResidual h (fun i x => V.observable i (QuotientGroup.mk
        (E.filtration.realification.polynomialOrbitEval
          (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) (g h)))))))
    (ξ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (v : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hsplit : ∀ h, g h = ξ * v h)
    (hξ : ∀ d : Fin s, coefficients ξ.log (Finsupp.single () (d.val + 1)) ∈
      (D.commonFreeSpan d).baseChange ℝ)
    (hv : ∀ h (d : Fin s), coefficients (v h).log (Finsupp.single () (d.val + 1)) ∈
      (D.dependentFreeSpan d).baseChange ℝ)
    (hN : Real.exp (sharedFreeCorrelationBudget s hs P') ≤ (N : ℝ)) :
    D.CorrelatedAffineComparison E T hbQ hT V g hg D' hs := by
  exact B₀.exists_correlated_lower_factorization D E T hbQ hT F V g hg D'
    hTfil hfreq hs hp' hP' hQP' hpp' hf Hsource hsource hsourceDense hHsource hcorr
    ξ v hsplit hξ hv hN

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

noncomputable def nativeSharedFreeRelationConstant (s : ℕ) (hs : 2 ≤ s) : ℕ :=
  (exists_native_shared_free_rank_relation s hs).choose

theorem exists_native_correlated_comparison_budget (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      let Z := (p + nativeSharedFreeRelationConstant s hs) ^ nativeSharedFreeRelationConstant s hs
      Z ≤ (p + C) ^ C ∧ ∀ A : ℝ, 0 ≤ A → A ≤ Z →
        sharedFreeCorrelationBudget s hs Z ≤ (p + C) ^ C ∧
        Z + (Z + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s +
          sharedFreeCorrelationBudget s hs Z ≤ (p + C) ^ C ∧
        ((sharedFreeCorrelationBudget s hs Z + sharedFreeComparisonBasisBudget A Z + 2) +
          nativePairModelConstant s) ^ nativePairModelConstant s ≤ (p + C) ^ C ∧
        nativeLowerPairModelBudget s
          (sharedFreeCorrelationBudget s hs Z + sharedFreeComparisonBasisBudget A Z + 2) ≤
          (p + C) ^ C := by
  let a := nativeSharedFreeRelationConstant s hs
  obtain ⟨b, _, hbound⟩ := exists_sharedFreeCorrelationBudget_bound s hs
  let Z₀ : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Z₀ + (Z₀ + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro p hp Z
  have hZ : 0 ≤ Z := pow_nonneg (add_nonneg hp (Nat.cast_nonneg _)) _
  have hsum : Z + (Z + b) ^ b ≤ (p + C) ^ C := by
    change (p + a) ^ a + ((p + a) ^ a + b) ^ b ≤ (p + C) ^ C
    simpa [Z₀, Polynomial.eval₂_pow] using hbudget p hp
  have hZC : Z ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (pow_nonneg (add_nonneg hZ (Nat.cast_nonneg b)) b)).trans hsum
  have hbC : (Z + b) ^ b ≤ (p + C) ^ C := (le_add_of_nonneg_left hZ).trans hsum
  refine ⟨hZC, ?_⟩
  intro A hA hAZ
  obtain ⟨hmain, hpair, hlower⟩ := hbound A Z hA hAZ hZ
  have hΛ : 0 ≤ (Z + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s :=
    pow_nonneg (add_nonneg hZ (Nat.cast_nonneg _)) _
  have hcorrCost : sharedFreeCorrelationBudget s hs Z ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left hΛ).trans (hmain.trans hbC)
  have htotal : Z + (Z + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s +
      sharedFreeCorrelationBudget s hs Z ≤ (p + C) ^ C := by
    linarith only [hmain, hsum]
  exact ⟨hcorrCost, htotal, hpair.trans hbC, hlower.trans hbC⟩

def NativeCorrelationStructure.HasCorrelatedAffineComparison
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
         IsModuleTopology.isTopologicalAddGroup ℝ _
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
                  D.CorrelatedAffineComparison E T hpA hT V (fun h => ξ * v h)
                    (fun h => by rw [map_mul, hξ, hv h, one_mul]) D' hs ∧
                  Z + (Z + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s +
                    sharedFreeCorrelationBudget s hs Z ≤ (p + C) ^ C ∧
                  ((sharedFreeCorrelationBudget s hs Z + sharedFreeComparisonBasisBudget A Z + 2) +
                    nativePairModelConstant s) ^ nativePairModelConstant s ≤ (p + C) ^ C ∧
                  nativeLowerPairModelBudget s
                    (sharedFreeCorrelationBudget s hs Z + sharedFreeComparisonBasisBudget A Z + 2) ≤
                    (p + C) ^ C))

theorem exists_native_correlated_affine_comparison (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s (r + 1) N p f), (∀ x, ‖f x‖ ≤ 1) →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) → W.HasCorrelatedAffineComparison hs C := by
  obtain ⟨C, hC, hbudget⟩ := exists_native_correlated_comparison_budget s hs
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W hf hN
  unfold NativeCorrelationStructure.HasCorrelatedAffineComparison
  intro Z
  have hp : 0 ≤ p := (Nat.cast_nonneg _).trans W.family.complexity.1.1
  obtain ⟨hZC, hcost⟩ := hbudget p hp
  have hZ : 0 ≤ Z := pow_nonneg (add_nonneg hp (Nat.cast_nonneg _)) _
  obtain ⟨A, hpA, hAZ, out, H, q, P, hHW, hH, hshort, hpq, hqP, hPA,
      R, D, B, E, T, hT, hTfil, hcentral, hframe, hdata⟩ :=
    (exists_native_shared_free_rank_relation s hs).choose_spec.2 W hf
      ((Real.exp_le_exp.mpr hZC).trans hN)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra) :=
    IsModuleTopology.isTopologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 E.basis
  obtain ⟨V, hfreq, ξ, hξ, hcommon, Hsource, _, hsourceW, hsource, _, hsourceDense,
      v, hv, hdep, hcorr, hnext⟩ := hdata
  obtain ⟨out', H', q', hsub, hH', hshort', hdense, hAq', hq'Z, R', ⟨D'⟩⟩ := hnext
  obtain ⟨F⟩ := hframe
  have hA : 0 ≤ A := hp.trans hpA
  obtain ⟨hcorrCost, htotal, hpair, hlower⟩ := hcost A hA hAZ
  have hmodel := B.has_correlated_affine_comparison D E T hpA hT F V (fun h => ξ * v h)
    (fun h => by rw [map_mul, hξ, hv h, one_mul]) D'
    hTfil hfreq hs (hA.trans hAq') hZ hAZ hq'Z hf
    Hsource hsource hsourceDense hsub hcorr ξ v (fun _ => rfl) hcommon hdep
    ((Real.exp_le_exp.mpr hcorrCost).trans hN)
  refine ⟨A, hpA, hAZ, out, H, q, P, hHW, hH, hshort, hpq, hqP, hPA,
    R, D, B, E, T, hT, hTfil, hcentral, ⟨F⟩, V, hfreq, ξ, hξ, hcommon,
    v, hv, hdep, out', H', q', (fun h hh => hsourceW (hsub hh)), hH', hshort',
    hdense, hAq', hq'Z, R', D', hmodel, htotal, hpair, hlower⟩

end Erdos3

end

end OAI
