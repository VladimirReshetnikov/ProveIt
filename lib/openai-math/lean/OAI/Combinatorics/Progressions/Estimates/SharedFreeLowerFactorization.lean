/- Modified for ProveIt: Use IsModuleTopology.topologicalAddGroup on Lean 4.32; statements unchanged. -/
import OAI.Combinatorics.Progressions.Dynamics.SharedFreeFullOrbitBudget
import OAI.Combinatorics.Progressions.Dynamics.SharedFreeLowerComparisonBudget
import OAI.Combinatorics.Progressions.Lattices.AffineRefinedCoefficients
import OAI.Combinatorics.Progressions.Polynomial.PolynomialOrbitLogSum
import OAI.Combinatorics.Progressions.Polynomial.SharedFreeCommonPolynomialCorrections

namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial CyclicCrootSisask
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure r) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  (F : FreeCoordinateFrame E.basis Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s r) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

include F

theorem exists_shared_free_full_orbit_factorization
    (hTfil : T.filtration = D.coefficientFreeFiltration)
    (hs : 2 ≤ s) (hp' : 0 ≤ p') (hP' : 0 ≤ P') (hQP' : Q ≤ P') (hpp' : p' ≤ P')
    (ξ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (v : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hsplit : ∀ h, g h = ξ * v h)
    (hξ : ∀ d : Fin s, coefficients ξ.log (Finsupp.single () (d.val + 1)) ∈
      (D.commonFreeSpan d).baseChange ℝ)
    (hv : ∀ h (d : Fin s), coefficients (v h).log (Finsupp.single () (d.val + 1)) ∈
      (D.dependentFreeSpan d).baseChange ℝ)
    (hN : Real.exp ((P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s) ≤ (N : ℝ)) :
    let B := (P' + 2) ^ 3 + 2 * P'
    let Λ := (P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s
    let Lc := sharedFreeCommonCorrectionBudget s Q P'
    let Lv := sharedFreePetalLiftBudget s Q P'
    ∃ D₁ : R'.CommonData B, D₁.quadruples ⊆ D'.quadruples ∧ D₁.spaces = D'.spaces ∧
      ∃ J ⊆ H', J.Nonempty ∧ Real.exp (-Λ) * H'.card ≤ (J.card : ℝ) ∧
        ∃ (r₀ : ℕ) (R₀ : Fin r₀ → ℕ) (η : (Fin r₀ → ℤ) →+ ZMod N) (h₀ : ZMod N)
          (m : ℕ) (Γ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
          (α : Fin s → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
          (β : Fin r₀ → Fin s → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra),
          (r₀ : ℝ) ≤ Λ ∧ Set.InjOn η {x | ∀ j, |x j| ≤ (R₀ j : ℤ)} ∧ 0 < m ∧ (m : ℝ) ≤ Real.exp ((s : ℝ) * (Lc + Lv)) ∧
          E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 Γ = 1 ∧
          (∀ d : Fin s, coefficients Γ.log (Finsupp.single () (d.val + 1)) ∈
            ((fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
              (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)).map (LinearMap.proj 0)).baseChange ℝ) ∧
          (∀ d, α d ∈ (D.dependentFreeSpan d).baseChange ℝ ∧
            ‖(E.basis.baseChange ℝ).equivFun (α d)‖ ≤ Real.exp Lv) ∧
          (∀ j d, β j d ∈ (D.dependentFreeSpan d).baseChange ℝ ∧
            ‖(E.basis.baseChange ℝ).equivFun (β j d)‖ ≤ Real.exp Lv) ∧
          ∀ h ∈ J, ∃ x : Fin r₀ → ℤ,
            (∀ j, |x j| ≤ (R₀ j : ℤ)) ∧ h = h₀ + η x ∧
            ∃ ε A K U ρ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
              A.log = Γ.log + positiveUnivariate (fun d => α d + ∑ j, (x j : ℝ) • β j d) ∧
              E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 ε = 1 ∧
              E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 A = 1 ∧
              E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 K = 1 ∧
              E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 U = 1 ∧
              E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 ρ = 1 ∧
              CoefficientBound (E.basis.baseChange ℝ) (fun _ : Unit => (N : ℝ))
                (Real.exp Lc + Real.exp Lv) ε.log ∧
              CoefficientGrid (E.basis.baseChange ℝ) m ρ.log ∧
              ε * A * K * U * ρ = g h ∧
              ∀ d : Fin s,
                coefficients K.log (Finsupp.single () (d.val + 1)) ∈
                  (T.filtration.layer (d.val + 1) 2).baseChange ℝ ∧
                coefficients U.log (Finsupp.single () (d.val + 1)) ∈
                  (fourPetalSpace (D.dependentFreeSpan d)
                    (fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
                      (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩))).baseChange ℝ := by
  intro B Λ Lc Lv
  classical
  obtain ⟨mc, Γ, εc, ρc, hmc, hmcb, hΓ0, hεc0, hρc0, hεc, hρc, hcommon⟩ :=
    D.exists_shared_free_common_polynomial_corrections E T hbQ hT F V g hg D'
      hTfil hs hp' hP' hQP' hpp' ξ v hsplit hξ hv hN
  obtain ⟨D₁, hsub, hspaces, J, hJH, hJ, hcard, r₀, R₀, η, h₀, mv, α, β,
      hrank, hproper, hmv, hmvb, hα, hβ, hfamily⟩ :=
    D.exists_shared_free_affine_orbit_family E T hbQ hT F V g hg D'
      hTfil hs hp' hP' hQP' hpp' ξ v hsplit hξ hv hN
  let m := mc * mv
  have hm : 0 < m := Nat.mul_pos hmc hmv
  have hmcdiv : mc ∣ m := ⟨mv, rfl⟩
  have hmvdiv : mv ∣ m := ⟨mc, Nat.mul_comm _ _⟩
  have hmb : (m : ℝ) ≤ Real.exp ((s : ℝ) * (Lc + Lv)) := by
    change ((mc * mv : ℕ) : ℝ) ≤ _
    rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp ((s : ℝ) * Lc) * Real.exp ((s : ℝ) * Lv) :=
        mul_le_mul hmcb hmvb (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hρcM : CoefficientGrid (E.basis.baseChange ℝ) m ρc.log :=
    fun a => realDenominatorGrid_subset_of_dvd hmc hmcdiv (hρc a)
  refine ⟨D₁, hsub, hspaces, J, hJH, hJ, hcard, r₀, R₀, η, h₀, m, Γ, α, β,
    hrank, hproper, hm, hmb, hΓ0, (fun d => (hcommon d).1), hα, hβ, ?_⟩
  intro h hh
  obtain ⟨x, hx, hspace, Av, εv, ρv, U, hAv, hAv0, hεv0, hρv0, hU0,
      hεv, hρv, hdependent⟩ := hfamily h hh
  let ε := εc.logSum εv
  let ρ := ρc.logSum ρv
  let A := Γ.logSum Av
  have hε0 := εc.logSum_normalized εv hεc0 hεv0
  have hρ0 := ρc.logSum_normalized ρv hρc0 hρv0
  have hA0 := Γ.logSum_normalized Av hΓ0 hAv0
  have hρvM : CoefficientGrid (E.basis.baseChange ℝ) m ρv.log :=
    fun a => realDenominatorGrid_subset_of_dvd hmv hmvdiv (hρv a)
  have hcoeff (d : Fin s) : coefficients (g h).log (Finsupp.single () (d.val + 1)) -
      (coefficients ε.log (Finsupp.single () (d.val + 1)) +
        coefficients A.log (Finsupp.single () (d.val + 1)) +
        coefficients U.log (Finsupp.single () (d.val + 1)) +
        coefficients ρ.log (Finsupp.single () (d.val + 1))) ∈
      (T.filtration.layer (Finsupp.weight (fun _ : Unit => 1)
        (Finsupp.single () (d.val + 1))) 2).baseChange ℝ := by
    have hp := T.polynomialOrbit_mul_coefficient_sub_mem_rank_two (by omega)
      (fun _ : Unit => 1) (Finsupp.single () (d.val + 1)) ξ (v h)
    rw [← hsplit h, (hcommon d).2, (hdependent d).2] at hp
    convert hp using 1
    simp only [ε, ρ, A, NilpotentLieFiltration.PolynomialOrbit.logSum_log,
      map_add, Finsupp.add_apply]
    abel
  obtain ⟨K, hK0, hprod, hK⟩ := T.exists_polynomialOrbit_factorization_rank_two (by omega)
    (fun _ : Unit => 1) (fun d : Fin s => Finsupp.single () (d.val + 1))
    (g h) ε A U ρ (hg h) hε0 hA0 hU0 hρ0 hcoeff
  refine ⟨x, hx, hspace, ε, A, K, U, ρ, ?_, hε0, hA0, hK0, hU0, hρ0,
    CoefficientBound.add _ _ hεc hεv, CoefficientGrid.add _ _ hρcM hρvM, hprod, ?_⟩
  · exact congrArg (fun z => Γ.log + z) hAv
  · intro d
    exact ⟨by simpa only [Finsupp.weight_single, smul_eq_mul, mul_one] using hK d,
      (hdependent d).1⟩

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.RationalFilteredNilmanifold

open VectorPolynomial
open scoped TensorProduct NNReal

theorem exists_sharedFreeFactorFreezing (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) {q p : ℝ},
      0 ≤ q → q ≤ p → 0 ≤ p → D.GeometryComplexityLE q →
      ∀ m : ℕ, 0 < m →
      (m : ℝ) ≤ Real.exp ((s : ℝ) *
        (sharedFreeCommonCorrectionBudget s q p + sharedFreePetalLiftBudget s q p)) →
      ∃ M : ℕ, 0 < M ∧ (M : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        (∀ ρ : D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
          CoefficientGrid (D.basis.baseChange ℝ) m ρ.log →
          ∀ x y : Unit → ℤ, (∀ j, (M : ℤ) ∣ x j - y j) →
            ((QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval
              (fun _ : Unit => 1) x ρ) : D.Space) =
              QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval
                (fun _ : Unit => 1) y ρ)) ∧
            ((QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval
              (fun _ : Unit => 1) x ρ)⁻¹ : D.Space) =
              QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval
                (fun _ : Unit => 1) y ρ)⁻¹)) ∧
        ∀ (Φ : D.Space → ℂ) (K : ℝ≥0), (∀ z, ‖Φ z‖ ≤ 1) →
          (letI := D.metricSpace; LipschitzWith K Φ) → (K : ℝ) ≤ Real.exp q →
          ∀ ε a ρ g : D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
            ε * a * ρ = g → ∀ T : ℝ, 0 < T →
            CoefficientBound (D.basis.baseChange ℝ) (fun _ : Unit => T)
              (Real.exp (sharedFreeCommonCorrectionBudget s q p) +
                Real.exp (sharedFreePetalLiftBudget s q p)) ε.log →
            CoefficientGrid (D.basis.baseChange ℝ) m ρ.log →
            ∀ (x y : Unit → ℤ) (δ : ℝ), 0 ≤ δ →
              (∀ j, |(x j : ℝ)| ≤ T) → (∀ j, |(y j : ℝ)| ≤ T) →
              (∀ j, |(x j : ℝ) - y j| ≤ T * δ) →
              (∀ j, (M : ℤ) ∣ x j - y j) →
              ‖Φ (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval
                  (fun _ : Unit => 1) x g)) -
                Φ (QuotientGroup.mk
                  (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) y ε *
                   D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x a *
                   D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) y ρ))‖ ≤
                Real.exp ((p + C) ^ C) * δ := by
  obtain ⟨a, _, hfull⟩ := exists_sharedFreeFullOrbitBudget_bound s
  obtain ⟨b, _, hperiod⟩ := exists_native_orbit_rational_period s
  obtain ⟨c, _, hfreeze⟩ := exists_orbit_factor_freezing s 1
  let B : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a + Polynomial.X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((B + Polynomial.C b) ^ b + (B + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D q p hq hqp hp hD m hm hmb
  let t := (p + a) ^ a + p + 2
  have hpow : 0 ≤ (p + a) ^ a := by positivity
  have ht : 0 ≤ t := by dsimp only [t]; positivity
  have hqt : q ≤ t := by dsimp only [t]; linarith
  have hbt : (p + a) ^ a ≤ t := by dsimp only [t]; linarith
  have ht1 : (1 : ℝ) ≤ t := by dsimp only [t]; linarith
  have hsum : (t + b) ^ b + (t + c) ^ c ≤ (p + C) ^ C := by
    simpa [B, t, Polynomial.eval₂_pow] using hbudget p hp
  have hbC : (t + b) ^ b ≤ (p + C) ^ C := by
    linarith [show 0 ≤ (t + c) ^ c by positivity]
  have hcC : (t + c) ^ c ≤ (p + C) ^ C := by
    linarith [show 0 ≤ (t + b) ^ b by positivity]
  obtain ⟨_, _, _, hden, hslow⟩ := hfull q p hq hqp hp
  obtain ⟨M, hM, hMb, hsolve⟩ := hperiod D (fun _ : Unit => 1)
    (fun _ => Nat.zero_lt_one) t ht (hD.mono D hqt)
    (by simpa only [Fintype.card_unit, Nat.cast_one] using ht1) m hm
    (hmb.trans (Real.exp_le_exp.mpr (hden.trans hbt)))
  refine ⟨M, hM, hMb.trans (Real.exp_le_exp.mpr hbC), hsolve, ?_⟩
  intro Φ K hΦ hLip hK ε a₀ ρ g hprod T hT hε hρ x y δ hδ hx hy hxy hres
  have hε' : CoefficientBound (D.basis.baseChange ℝ) (fun _ : Unit => T)
      (Real.exp ((t + 2) ^ 1)) ε.log :=
    CoefficientBound.mono _ _ (fun _ => hT) hε
      (hslow.trans (Real.exp_le_exp.mpr (by simpa only [pow_one] using
        (hbt.trans (show t ≤ t + 2 by linarith)))))
  exact (hfreeze D (fun _ : Unit => 1) (fun _ => Nat.zero_lt_one) t ht
    (hD.mono D hqt) (by simpa only [Fintype.card_unit, Nat.cast_one] using ht1)
    Φ K hΦ hLip (hK.trans (Real.exp_le_exp.mpr hqt)) ε a₀ ρ g hprod
    (fun _ : Unit => T) (fun _ => hT) hε' x y δ hδ hx hy hxy
    (hsolve ρ hρ x y hres).1).trans
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hcC) hδ)

end Erdos3.RationalFilteredNilmanifold

namespace Erdos3

noncomputable def sharedFreeFactorFreezingConstant (s : ℕ) : ℕ :=
  (RationalFilteredNilmanifold.exists_sharedFreeFactorFreezing.{0} s).choose

end Erdos3

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module NilpotentLieBCHGroup RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (B₀ : D.CoefficientBases Q)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure r) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  (F : FreeCoordinateFrame E.basis Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s r) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

include F

theorem CoefficientBases.exists_invariant_native_comparison_model
    (hTfil : T.filtration = D.coefficientFreeFiltration)
    (hfreq : V.frequency = B₀.freeFrequency D)
    (hs : 2 ≤ s) (hP' : 0 ≤ P') (hQP' : Q ≤ P') :
    let S := D.comparisonCoefficientSpace E T hbQ hT V g hg D'
    let hS := D.comparisonCoefficientSpace_le_layer E T hbQ hT V g hg D' hTfil
    ∃ B : ∀ j, Basis (Fin (finrank ℚ (S j))) ℚ (S j),
      (∀ j a i, rationalLogHeight ((Pi.basis (fun _ : Fin 2 => E.basis)).repr
        (B j a : Fin 2 → D.CoefficientFreeLieAlgebra) i) ≤ sharedFreeComparisonBasisBudget Q P') ∧
      let φ := SubspaceFreeLift.evaluation S B (piRank (fun _ : Fin 2 => E) (fun _ => T)).filtration hS
      ∃ M : RationalFilteredNilmanifold (SubspaceFreeLift.Algebra S r) s
          (finrank ℚ (SubspaceFreeLift.Algebra S r)),
        ∃ U : M.DegreeRankStructure r,
          U.filtration = SubspaceFreeLift.filtration S T.filtration.rank_le_degree ∧
          U.ComplexityLE (sharedFreeComparisonModelBudget s Q P') ∧ IsCentralLieBasis M.basis ∧
          Nonempty (FreeCoordinateFrame M.basis (sharedFreeComparisonModelBudget s Q P')) ∧
          (∀ i j, rationalLogHeight ((pi (fun _ : Fin 2 => E)).basis.repr
            (φ (M.basis j)) i) ≤ sharedFreeComparisonModelBudget s Q P') ∧
          M.lattice ≤ (pi (fun _ : Fin 2 => E)).lattice.comap (mapOfSteps
            (hL := M.filtration.lowerCentralSeries_eq_bot)
            (hM := (pi (fun _ : Fin 2 => E)).filtration.lowerCentralSeries_eq_bot) φ) ∧
          (letI := moduleTopology ℝ (ℝ ⊗[ℚ] SubspaceFreeLift.Algebra S r)
           letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] SubspaceFreeLift.Algebra S r) :=
             IsModuleTopology.topologicalAddGroup ℝ _
           letI := realification_moduleTopology_t2 M.basis
           ∃ Z : M.UnitVerticalObservable (U.realSubgroup s r)
               (Fin W.family.outputDim × Fin W.family.outputDim) (sharedFreeComparisonModelBudget s Q P'),
             Z.frequency = (pairDifferenceFunctional V.frequency).comp φ.toLinearMap ∧
             (∀ x ∈ U.filtration.layer s r, Z.frequency x = 0) ∧
             (∀ i z, z ∈ U.realSubgroup s r → ∀ x, Z.observable i (z • x) = Z.observable i x) ∧
             ∀ i x, Z.observable i (QuotientGroup.mk x) =
               V.pairedObservable T i (QuotientGroup.mk (realificationMap
                 (hnil := M.filtration.lowerCentralSeries_eq_bot)
                 (hM := (pi (fun _ : Fin 2 => E)).filtration.lowerCentralSeries_eq_bot) φ x))) := by
  intro S hS
  obtain ⟨J, hJ, M, U, hU, hUc, hcentral, hframe, hmatrix, hlattice, hZ⟩ :=
    D.exists_native_comparison_model E T hbQ hT F V g hg D' hTfil hs hP' hQP'
  refine ⟨J, hJ, M, U, hU, hUc, hcentral, hframe, hmatrix, hlattice, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] SubspaceFreeLift.Algebra S r)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] SubspaceFreeLift.Algebra S r) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 M.basis
  obtain ⟨Z, hfreqZ, hobs⟩ := hZ
  have hzero := B₀.native_comparison_frequency_zero D E T hbQ hT V g hg D'
    hTfil hfreq J M U hU Z.frequency hfreqZ
  exact ⟨Z, hfreqZ, hzero,
    (fun i z hz x => Z.rank_invariant_of_frequency_zero U hzero z hz i x), hobs⟩

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module NilpotentLieBCHGroup RationalFilteredNilmanifold
open scoped TensorProduct

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

theorem CoefficientBases.exists_uniform_lower_comparison_model
    (hTfil : T.filtration = D.coefficientFreeFiltration)
    (hfreq : V.frequency = B₀.freeFrequency D)
    (hs : 2 ≤ s) (hP' : 0 ≤ P') (hQP' : Q ≤ P') :
    let S := D.comparisonCoefficientSpace E T hbQ hT V g hg D'
    let hS := D.comparisonCoefficientSpace_le_layer E T hbQ hT V g hg D' hTfil
    ∃ B : ∀ j, Basis (Fin (finrank ℚ (S j))) ℚ (S j),
      (∀ j a i, rationalLogHeight ((Pi.basis (fun _ : Fin 2 => E.basis)).repr
        (B j a : Fin 2 → D.CoefficientFreeLieAlgebra) i) ≤ sharedFreeComparisonBasisBudget Q P') ∧
      let φ := SubspaceFreeLift.evaluation S B (piRank (fun _ : Fin 2 => E) (fun _ => T)).filtration hS
      ∃ M : RationalFilteredNilmanifold (SubspaceFreeLift.Algebra S (r + 1)) s
          (finrank ℚ (SubspaceFreeLift.Algebra S (r + 1))),
        ∃ U : M.DegreeRankStructure (r + 1),
          U.filtration = SubspaceFreeLift.filtration S T.filtration.rank_le_degree ∧
          U.ComplexityLE (sharedFreeComparisonModelBudget s Q P') ∧
          (letI := moduleTopology ℝ (ℝ ⊗[ℚ] SubspaceFreeLift.Algebra S (r + 1))
           letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] SubspaceFreeLift.Algebra S (r + 1)) :=
             IsModuleTopology.topologicalAddGroup ℝ _
           letI := realification_moduleTopology_t2 M.basis
           ∃ Z : M.UnitVerticalObservable (U.realSubgroup s (r + 1))
               (Fin W.family.outputDim × Fin W.family.outputDim) (sharedFreeComparisonModelBudget s Q P'),
             (∀ i x, Z.observable i (QuotientGroup.mk x) =
               V.pairedObservable T i (QuotientGroup.mk (realificationMap
                 (hnil := M.filtration.lowerCentralSeries_eq_bot)
                 (hM := (pi (fun _ : Fin 2 => E)).filtration.lowerCentralSeries_eq_bot) φ x))) ∧
             M.HasUniformLowerRankUnitFamily U Z.observable (fun _ : Unit => 1)
               (sharedFreeLowerComparisonBudget s Q P')) := by
  intro S hS
  obtain ⟨J, hJ, M, U, hU, hUc, _, _, _, _, hZ⟩ :=
    B₀.exists_invariant_native_comparison_model D E T hbQ hT F V g hg D'
      hTfil hfreq hs hP' hQP'
  refine ⟨J, hJ, M, U, hU, hUc, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] SubspaceFreeLift.Algebra S (r + 1))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] SubspaceFreeLift.Algebra S (r + 1)) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 M.basis
  obtain ⟨Z, _, hzero, _, hobs⟩ := hZ
  refine ⟨Z, hobs, ?_⟩
  have hpM : 0 ≤ sharedFreeComparisonModelBudget s Q P' :=
    (Nat.cast_nonneg _).trans hUc.1.1
  exact UnitVerticalObservable.hasUniformLowerRankUnitFamily M U Z
    (fun _ : Unit => 1) hpM hUc hzero

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct

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

theorem CoefficientBases.exists_lower_factored_family {τ : Type*}
    (hTfil : T.filtration = D.coefficientFreeFiltration)
    (hfreq : V.frequency = B₀.freeFrequency D)
    (hs : 2 ≤ s) (hP' : 0 ≤ P') (hQP' : Q ≤ P')
    (A K U : τ → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hA0 : ∀ t, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (A t) = 1)
    (hK0 : ∀ t, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (K t) = 1)
    (hU0 : ∀ t, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (U t) = 1)
    (hA : ∀ t (d : Fin s), coefficients (A t).log (Finsupp.single () (d.val + 1)) ∈
      ((fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
        (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)).map (LinearMap.proj 0)).baseChange ℝ)
    (hK : ∀ t (d : Fin s), coefficients (K t).log (Finsupp.single () (d.val + 1)) ∈
      (T.filtration.layer (d.val + 1) 2).baseChange ℝ)
    (hU : ∀ t (d : Fin s), coefficients (U t).log (Finsupp.single () (d.val + 1)) ∈
      (fourPetalSpace (D.dependentFreeSpan d)
        (fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
          (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩))).baseChange ℝ) :
    let S := D.comparisonCoefficientSpace E T hbQ hT V g hg D'
    ∃ M : RationalFilteredNilmanifold (SubspaceFreeLift.Algebra S (r + 1)) s
        (finrank ℚ (SubspaceFreeLift.Algebra S (r + 1))),
      ∃ Tm : M.DegreeRankStructure (r + 1),
        Tm.filtration = SubspaceFreeLift.filtration S T.filtration.rank_le_degree ∧
        Tm.ComplexityLE (sharedFreeComparisonModelBudget s Q P') ∧
        M.HasLowerRankOrbitFamily Tm (fun _ : Unit => 1)
          (fun t (i : Fin W.family.outputDim × Fin W.family.outputDim) x =>
            V.observable i.1 (QuotientGroup.mk
              (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x (A t * K t * U t))) *
            star (V.observable i.2 (QuotientGroup.mk
              (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x (A t)))))
          (sharedFreeLowerComparisonBudget s Q P') := by
  intro S
  obtain ⟨J, _, M, Tm, hTm, hTmc, hZ⟩ :=
    B₀.exists_uniform_lower_comparison_model D E T hbQ hT F V g hg D'
      hTfil hfreq hs hP' hQP'
  refine ⟨M, Tm, hTm, hTmc, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] SubspaceFreeLift.Algebra S (r + 1))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] SubspaceFreeLift.Algebra S (r + 1)) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 M.basis
  obtain ⟨Z, hobs, huniform⟩ := hZ
  apply huniform.realizeFamily
  intro t
  obtain ⟨u, hu0, _, hu⟩ := D.exists_native_factored_comparison_orbit E T hbQ hT V g hg D'
    hTfil (by omega) (A t) (K t) (U t) (hA0 t) (hK0 t) (hU0 t) (hA t) (hK t) (hU t)
    J M Tm hTm
  refine ⟨u, hu0, ?_⟩
  intro i x
  exact SubspaceFreeLift.native_pair_observable_eval E T S J
    (D.comparisonCoefficientSpace_le_layer E T hbQ hT V g hg D' hTfil)
    M Tm V Z hobs ![A t * K t * U t, A t] u hu i x

end Erdos3.NativeRankRelation.CommonData

end

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

theorem CoefficientBases.exists_shared_free_lower_factorization
    (hTfil : T.filtration = D.coefficientFreeFiltration)
    (hfreq : V.frequency = B₀.freeFrequency D)
    (hs : 2 ≤ s) (hp' : 0 ≤ p') (hP' : 0 ≤ P') (hQP' : Q ≤ P') (hpp' : p' ≤ P')
    (ξ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (v : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hsplit : ∀ h, g h = ξ * v h)
    (hξ : ∀ d : Fin s, coefficients ξ.log (Finsupp.single () (d.val + 1)) ∈
      (D.commonFreeSpan d).baseChange ℝ)
    (hv : ∀ h (d : Fin s), coefficients (v h).log (Finsupp.single () (d.val + 1)) ∈
      (D.dependentFreeSpan d).baseChange ℝ)
    (hN : Real.exp ((P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s) ≤ (N : ℝ)) :
    let B := (P' + 2) ^ 3 + 2 * P'
    let Λ := (P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s
    let Lc := sharedFreeCommonCorrectionBudget s Q P'
    let Lv := sharedFreePetalLiftBudget s Q P'
    ∃ D₁ : R'.CommonData B, D₁.quadruples ⊆ D'.quadruples ∧ D₁.spaces = D'.spaces ∧
      ∃ J ⊆ H', J.Nonempty ∧ Real.exp (-Λ) * H'.card ≤ (J.card : ℝ) ∧
        ∃ (r₀ : ℕ) (R₀ : Fin r₀ → ℕ) (η : (Fin r₀ → ℤ) →+ ZMod N) (h₀ : ZMod N)
          (m : ℕ) (Γ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
          (α : Fin s → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
          (β : Fin r₀ → Fin s → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra),
          (r₀ : ℝ) ≤ Λ ∧ Set.InjOn η {x | ∀ j, |x j| ≤ (R₀ j : ℤ)} ∧ 0 < m ∧ (m : ℝ) ≤ Real.exp ((s : ℝ) * (Lc + Lv)) ∧
          E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 Γ = 1 ∧
          (∀ d : Fin s, coefficients Γ.log (Finsupp.single () (d.val + 1)) ∈
            ((fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
              (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)).map (LinearMap.proj 0)).baseChange ℝ) ∧
          (∀ d, α d ∈ (D.dependentFreeSpan d).baseChange ℝ ∧
            ‖(E.basis.baseChange ℝ).equivFun (α d)‖ ≤ Real.exp Lv) ∧
          (∀ j d, β j d ∈ (D.dependentFreeSpan d).baseChange ℝ ∧
            ‖(E.basis.baseChange ℝ).equivFun (β j d)‖ ≤ Real.exp Lv) ∧
          ∃ (x : {h // h ∈ J} → Fin r₀ → ℤ)
            (ε A K U ρ : {h // h ∈ J} →
              E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1)),
            (∀ h : {h // h ∈ J},
              (∀ j, |x h j| ≤ (R₀ j : ℤ)) ∧ h.val = h₀ + η (x h) ∧
              (A h).log = Γ.log + positiveUnivariate
                (fun d => α d + ∑ j, (x h j : ℝ) • β j d) ∧
              E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (ε h) = 1 ∧
              E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (A h) = 1 ∧
              E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (K h) = 1 ∧
              E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (U h) = 1 ∧
              E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (ρ h) = 1 ∧
              CoefficientBound (E.basis.baseChange ℝ) (fun _ : Unit => (N : ℝ))
                (Real.exp Lc + Real.exp Lv) (ε h).log ∧
              CoefficientGrid (E.basis.baseChange ℝ) m (ρ h).log ∧
              ε h * A h * K h * U h * ρ h = g h.val ∧
              ∀ d : Fin s,
                coefficients (K h).log (Finsupp.single () (d.val + 1)) ∈
                  (T.filtration.layer (d.val + 1) 2).baseChange ℝ ∧
                coefficients (U h).log (Finsupp.single () (d.val + 1)) ∈
                  (fourPetalSpace (D.dependentFreeSpan d)
                    (fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
                      (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩))).baseChange ℝ) ∧
            (∃ M₀ : ℕ, 0 < M₀ ∧
              (M₀ : ℝ) ≤ Real.exp ((P' + sharedFreeFactorFreezingConstant s) ^
                sharedFreeFactorFreezingConstant s) ∧
              (∀ (h : {h // h ∈ J}) (y z : Unit → ℤ),
                (∀ j, (M₀ : ℤ) ∣ y j - z j) →
                ((QuotientGroup.mk (E.filtration.realification.polynomialOrbitEval
                  (fun _ : Unit => 1) y (ρ h)) : E.Space) =
                  QuotientGroup.mk (E.filtration.realification.polynomialOrbitEval
                    (fun _ : Unit => 1) z (ρ h))) ∧
                ((QuotientGroup.mk (E.filtration.realification.polynomialOrbitEval
                  (fun _ : Unit => 1) y (ρ h))⁻¹ : E.Space) =
                  QuotientGroup.mk (E.filtration.realification.polynomialOrbitEval
                    (fun _ : Unit => 1) z (ρ h))⁻¹)) ∧
              ∀ (h : {h // h ∈ J}) i (y z : Unit → ℤ) (δ : ℝ), 0 ≤ δ →
                (∀ j, |(y j : ℝ)| ≤ N) → (∀ j, |(z j : ℝ)| ≤ N) →
                (∀ j, |(y j : ℝ) - z j| ≤ (N : ℝ) * δ) →
                (∀ j, (M₀ : ℤ) ∣ y j - z j) →
                ‖V.observable i (QuotientGroup.mk
                    (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) y (g h.val))) -
                  V.observable i (QuotientGroup.mk
                    (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) z (ε h) *
                     E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) y
                       (A h * K h * U h) *
                     E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) z (ρ h)))‖ ≤
                  Real.exp ((P' + sharedFreeFactorFreezingConstant s) ^
                    sharedFreeFactorFreezingConstant s) * δ) ∧
            let S := D.comparisonCoefficientSpace E T hbQ hT V g hg D'
            ∃ M : RationalFilteredNilmanifold (SubspaceFreeLift.Algebra S (r + 1)) s
                (finrank ℚ (SubspaceFreeLift.Algebra S (r + 1))),
              ∃ Tm : M.DegreeRankStructure (r + 1),
                Tm.filtration = SubspaceFreeLift.filtration S T.filtration.rank_le_degree ∧
                Tm.ComplexityLE (sharedFreeComparisonModelBudget s Q P') ∧
                M.HasLowerRankOrbitFamily Tm (fun _ : Unit => 1)
                  (fun h (i : Fin W.family.outputDim × Fin W.family.outputDim) y =>
                    V.observable i.1 (QuotientGroup.mk
                      (E.filtration.realification.polynomialOrbitEval
                        (fun _ : Unit => 1) y (A h * K h * U h))) *
                    star (V.observable i.2 (QuotientGroup.mk
                      (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) y (A h)))))
                  (sharedFreeLowerComparisonBudget s Q P') := by
  intro B Λ Lc Lv
  classical
  obtain ⟨D₁, hsub, hspaces, J, hJH, hJ, hcard, r₀, R₀, η, h₀, m, Γ, α, β,
      hrank, hproper, hm, hmb, hΓ0, hΓ, hα, hβ, hfamily⟩ :=
    D.exists_shared_free_full_orbit_factorization E T hbQ hT F V g hg D'
      hTfil hs hp' hP' hQP' hpp' ξ v hsplit hξ hv hN
  choose x hx hspace ε A K U ρ hAl hε0 hA0 hK0 hU0 hρ0 hε hρ hprod hKU using
    (fun h : {h // h ∈ J} => hfamily h.val h.property)
  have hAc : ∀ (h : {h // h ∈ J}) (d : Fin s),
      coefficients (A h).log (Finsupp.single () (d.val + 1)) ∈
        ((fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
          (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)).map (LinearMap.proj 0)).baseChange ℝ := by
    intro h d
    rw [hAl h]
    exact affine_refined_coefficient_mem D.coefficientFreeSpan D.dependentFreeSpan
      (fun d : Fin s => D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)
      Γ.log α β (fun j => (x h j : ℝ)) hΓ (fun d => (hα d).1) (fun j d => (hβ j d).1) d
  refine ⟨D₁, hsub, hspaces, J, hJH, hJ, hcard, r₀, R₀, η, h₀, m, Γ, α, β,
    hrank, hproper, hm, hmb, hΓ0, hΓ, hα, hβ, x, ε, A, K, U, ρ, ?_, ?_, ?_⟩
  · intro h
    exact ⟨hx h, hspace h, hAl h, hε0 h, hA0 h, hK0 h, hU0 h, hρ0 h,
      hε h, hρ h, hprod h, hKU h⟩
  · have hQ : 0 ≤ Q := (Nat.cast_nonneg _).trans hT.1.1
    obtain ⟨M₀, hM₀, hM₀b, hperiod, hfreeze⟩ :=
      (RationalFilteredNilmanifold.exists_sharedFreeFactorFreezing.{0} s).choose_spec.2
        E hQ hQP' hP' hT.1 m hm hmb
    refine ⟨M₀, hM₀, hM₀b, (fun h y z hres => hperiod (ρ h) (hρ h) y z hres), ?_⟩
    intro h i y z δ hδ hy hz hyz hres
    exact hfreeze (V.observable i) V.lipBound (V.norm i) (V.lipschitz i) V.lip_bound
      (ε h) (A h * K h * U h) (ρ h) (g h.val)
      (by simpa only [mul_assoc] using hprod h) (N : ℝ)
      (by exact_mod_cast NeZero.pos N) (hε h) (hρ h) y z δ hδ hy hz hyz hres
  · exact B₀.exists_lower_factored_family D E T hbQ hT F V g hg D'
      hTfil hfreq hs hP' hQP' A K U hA0 hK0 hU0 hAc
      (fun h d => (hKU h d).1) (fun h d => (hKU h d).2)

end Erdos3.NativeRankRelation.CommonData

end

end OAI
