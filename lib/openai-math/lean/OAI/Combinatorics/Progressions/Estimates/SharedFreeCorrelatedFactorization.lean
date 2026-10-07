/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Dynamics.SharedFreeCorrelationBudget

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

include F

theorem CoefficientBases.exists_correlated_lower_factorization
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
                      (nativeLowerPairModelBudget s Qc) := by
  intro Λ C Qc Lv S
  classical
  let P₀ := sharedFreeCorrelationInput s P'
  have hQ0 : 0 ≤ Q := (Nat.cast_nonneg _).trans hT.1.1
  obtain ⟨hP₀, hQP₀, hΛP₀, hdenP₀, hslowP₀, hperiodP₀⟩ :=
    sharedFreeCorrelationInput_bounds s hQ0 hQP' hP'
  have hP₀C : P₀ ≤ C := sharedFreeCorrelationInput_le_budget s hs hP'
  have hC0 : 0 ≤ C := (show 0 ≤ P₀ by linarith).trans hP₀C
  obtain ⟨D₁, _, _, J, hJH, hJ, hcard, r₀, R₀, η, h₀, m, Γ, α, β,
      hrank, hproper, hm, hmb, hΓ0, hΓ, hα, hβ, x, ε, A, K, U, ρ, hdata, hperiod, _⟩ :=
    B₀.exists_shared_free_lower_factorization D E T hbQ hT F V g hg D'
      hTfil hfreq hs hp' hP' hQP' hpp' ξ v hsplit hξ hv
      ((Real.exp_le_exp.mpr (hΛP₀.trans hP₀C)).trans hN)
  obtain ⟨M₀, hM₀, hM₀b, hperiod, _⟩ := hperiod
  let X := W.replaceRank E T hbQ hT V g hg Hsource hsource hsourceDense hcorr
  let ε' (h : ZMod N) := if hh : h ∈ J then ε ⟨h, hh⟩ else 1
  let a' (h : ZMod N) := if hh : h ∈ J then A ⟨h, hh⟩ * K ⟨h, hh⟩ * U ⟨h, hh⟩ else 1
  let ρ' (h : ZMod N) := if hh : h ∈ J then ρ ⟨h, hh⟩ else 1
  have hprod' (h : ZMod N) (hh : h ∈ J) : ε' h * a' h * ρ' h = X.family.orbit h := by
    rcases hdata ⟨h, hh⟩ with ⟨_, _, _, _, _, _, _, _, _, _, hprod, _⟩
    change ε' h * a' h * ρ' h = g h
    simp only [ε', a', ρ', dite_eq_left hh]
    simpa only [mul_assoc] using hprod
  have hε' (h : ZMod N) (hh : h ∈ J) :
      CoefficientBound (E.basis.baseChange ℝ) (fun _ : Unit => (N : ℝ))
        (Real.exp ((P₀ + 2) ^ 1)) (ε' h).log := by
    rcases hdata ⟨h, hh⟩ with ⟨_, _, _, _, _, _, _, _, hε, _, _, _⟩
    simp only [ε', dite_eq_left hh]
    exact CoefficientBound.mono _ _ (fun _ => Nat.cast_pos.mpr (NeZero.pos N)) hε hslowP₀
  have hρ' (h : ZMod N) (hh : h ∈ J) : CoefficientGrid (E.basis.baseChange ℝ) m (ρ' h).log := by
    rcases hdata ⟨h, hh⟩ with ⟨_, _, _, _, _, _, _, _, _, hρ, _, _⟩
    simpa only [ρ', dite_eq_left hh] using hρ
  have hperiod' (h : ZMod N) (hh : h ∈ J) (z z' : Unit → ℤ)
      (hres : ∀ j, (M₀ : ℤ) ∣ z j - z' j) :
      (QuotientGroup.mk (E.filtration.realification.polynomialOrbitEval
        (fun _ : Unit => 1) z (ρ' h)) : E.Space) =
      QuotientGroup.mk (E.filtration.realification.polynomialOrbitEval
        (fun _ : Unit => 1) z' (ρ' h)) := by
    simpa only [ρ', dite_eq_left hh] using (hperiod ⟨h, hh⟩ z z' hres).1
  obtain ⟨Δ, hΔ, hchar, hnormal, hfinite, hindex, l, hl, hin, hout,
      hRank, J₂, hsub, hJ₂, hdense, V₁, hfreq₁, hcorr₁⟩ :=
    (exists_shared_factor_correlations s hs).choose_spec.2 X hf hP₀ hQP₀ m M₀ hm
      (hmb.trans (Real.exp_le_exp.mpr hdenP₀)) hM₀
      (hM₀b.trans (Real.exp_le_exp.mpr hperiodP₀)) J
      (fun h hh => hHsource (hJH hh)) hJ ε' a' ρ' hprod' hε' hρ' hperiod' hN
  let lift (h : {h // h ∈ J₂}) : {h // h ∈ J} := ⟨h.val, hsub h.property⟩
  refine ⟨J₂, (fun h hh => hJH (hsub hh)), hJ₂, ?_, r₀, R₀, η, h₀, Γ, α, β,
    hrank, hproper, hΓ0, hΓ, hα, hβ, (fun h => x (lift h)), (fun h => A (lift h)),
    (fun h => K (lift h)), (fun h => U (lift h)), ?_, Δ, hΔ, hchar, hnormal, hfinite,
    hindex, l, hl, hin, hout, hRank, V₁, hfreq₁, ?_, ?_⟩
  · calc
      _ = Real.exp (-C) * (Real.exp (-Λ) * H'.card) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-C) * J.card := mul_le_mul_of_nonneg_left hcard (Real.exp_pos _).le
      _ ≤ _ := hdense
  · intro h
    rcases hdata (lift h) with ⟨hx, hs, hA, _, hA0, hK0, hU0, _, _, _, _, hKU⟩
    exact ⟨hx, hs, hA, hA0, hK0, hU0, hKU⟩
  · intro h
    have hc := hcorr₁ h.val h.property
    change Nonempty (NativeVectorCorrelation (s - 1) N C
      (W.replacedRankResidual h.val (fun i z => V₁.observable i (QuotientGroup.mk
        (E.filtration.realification.polynomialOrbitEval
          (fun _ : Unit => 1) (fun _ => (z.val : ℤ)) (a' h.val)))))) at hc
    have ha : a' h.val = A (lift h) * K (lift h) * U (lift h) := by
      simp only [a', dite_eq_left (hsub h.property), lift]
    rw [ha] at hc
    exact hc
  · apply B₀.exists_covered_factored_family D E T hbQ hT F V g hg D'
      hTfil hfreq hs hP' hQP' Δ l hl hin hout hC0 hRank V₁ hfreq₁
      (fun h => A (lift h)) (fun h => K (lift h)) (fun h => U (lift h))
    · intro h
      rcases hdata (lift h) with ⟨_, _, _, _, hA0, _, _, _, _, _, _, _⟩
      exact hA0
    · intro h
      rcases hdata (lift h) with ⟨_, _, _, _, _, hK0, _, _, _, _, _, _⟩
      exact hK0
    · intro h
      rcases hdata (lift h) with ⟨_, _, _, _, _, _, hU0, _, _, _, _, _⟩
      exact hU0
    · intro h d
      rcases hdata (lift h) with ⟨_, _, hA, _, _, _, _, _, _, _, _, _⟩
      rw [hA]
      exact affine_refined_coefficient_mem D.coefficientFreeSpan D.dependentFreeSpan
        (fun d : Fin s => D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)
        Γ.log α β (fun j => (x (lift h) j : ℝ)) hΓ (fun d => (hα d).1) (fun j d => (hβ j d).1) d
    · intro h d
      rcases hdata (lift h) with ⟨_, _, _, _, _, _, _, _, _, _, _, hKU⟩
      exact (hKU d).1
    · intro h d
      rcases hdata (lift h) with ⟨_, _, _, _, _, _, _, _, _, _, _, hKU⟩
      exact (hKU d).2

end Erdos3.NativeRankRelation.CommonData

end

end OAI
