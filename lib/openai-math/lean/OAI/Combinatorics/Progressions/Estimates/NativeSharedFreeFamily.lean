/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.NativeCoveredCommonFactorization
import OAI.Combinatorics.Progressions.Linear.CommonCoefficientBasisBudget
import OAI.Combinatorics.Progressions.Polynomial.NativeFreePolynomialLifts

namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem exists_coefficient_bases (hP : 0 ≤ P) (hbP : b ≤ P) :
    Nonempty (D.CoefficientBases (coefficientSpaceBasisBudget P)) := by
  classical
  choose c hc e he using fun d : Fin s =>
    D.exists_coefficient_space_bases hP hbP
      ⟨d.val + 1, Nat.succ_lt_succ d.isLt⟩ (Nat.succ_pos d.val)
  exact ⟨⟨c, e, hc, he⟩⟩

theorem exists_controlled_coefficient_bases :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {s r N : ℕ} [NeZero N] {b p q P : ℝ}
      {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
      {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}
      (D : R.CommonData P), 0 ≤ P → b ≤ P → Nonempty (D.CoefficientBases ((P + C) ^ C)) := by
  obtain ⟨C, hC, hbound⟩ := coefficientSpaceBasisBudget_bound
  refine ⟨C, hC, ?_⟩
  intro s r N _ b p q P W out H R D hP hbP
  obtain ⟨B⟩ := D.exists_coefficient_bases hP hbP
  exact ⟨B.mono D (hbound P hP)⟩

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module NilpotentLieBCHGroup
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_native_common_free_model (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {b p q P M : ℝ}
      {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
      {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}
      (D : R.CommonData P) (B : D.CoefficientBases M)
      (E : RationalFilteredNilmanifold W.L s W.dim) (S : E.DegreeRankStructure r),
      S.filtration = W.rank.filtration → E.basis = W.model.basis →
      0 ≤ M → S.ComplexityLE M → ∀ (I : Type*) [Fintype I]
      (U : E.UnitVerticalObservable (S.realSubgroup s r) I M),
      ∃ F : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
          (finrank ℚ D.CoefficientFreeLieAlgebra),
        ∃ T : F.DegreeRankStructure r,
          T.filtration = D.coefficientFreeFiltration ∧
          T.ComplexityLE ((M + C) ^ C) ∧ IsCentralLieBasis F.basis ∧
          Nonempty (FreeCoordinateFrame F.basis ((M + C) ^ C)) ∧
          (∀ i j, rationalLogHeight (E.basis.repr (B.freeEvaluation D (F.basis j)) i) ≤ (M + C) ^ C) ∧
          F.lattice ≤ E.lattice.comap (mapOfSteps
            (hL := F.filtration.lowerCentralSeries_eq_bot)
            (hM := E.filtration.lowerCentralSeries_eq_bot) (B.freeEvaluation D)) ∧
          (letI := moduleTopology ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
           letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra) :=
             IsModuleTopology.isTopologicalAddGroup ℝ _
           letI := realification_moduleTopology_t2 F.basis
           ∃ V : F.UnitVerticalObservable (T.realSubgroup s r) I ((M + C) ^ C),
             V.frequency = U.frequency.comp (B.freeEvaluation D).toLinearMap ∧
             ∀ i x, V.observable i (QuotientGroup.mk x) =
               U.observable i (QuotientGroup.mk (realificationMap
                 (hnil := F.filtration.lowerCentralSeries_eq_bot)
                 (hM := E.filtration.lowerCentralSeries_eq_bot) (B.freeEvaluation D) x))) := by
  obtain ⟨a, _, hfree⟩ := exists_native_free_unit_observable s
  let K₀ : Polynomial ℕ := Polynomial.C (2 * s + 1) * Polynomial.X + 1
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((K₀ + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro r N _ b p q P M W out H R D B E S hS hE hM hcomplex I _ U
  let K := ((2 * s + 1 : ℕ) : ℝ) * M + 1
  have hcoef : (1 : ℝ) ≤ (2 * s + 1 : ℕ) := by exact_mod_cast (show 1 ≤ 2 * s + 1 by omega)
  have hMK : M ≤ K := by dsimp only [K]; nlinarith
  have hK : 0 ≤ K := hM.trans hMK
  have hdim : (W.dim : ℝ) ≤ M := hcomplex.1.1
  have hcard : (Fintype.card D.CoefficientAlphabet : ℝ) ≤ K := by
    calc
      _ ≤ (2 : ℝ) * s * W.dim := by exact_mod_cast D.coefficientAlphabet_card
      _ ≤ (2 : ℝ) * s * M := mul_le_mul_of_nonneg_left hdim (by positivity)
      _ ≤ K := by dsimp only [K]; push_cast; nlinarith
  have hbound : (K + a) ^ a ≤ (M + C) ^ C := by
    simpa [K₀, K, Polynomial.eval₂_pow] using hbudget M hM
  have hgen (x : D.CoefficientAlphabet) :
      B.generator D x ∈ S.filtration.layer (D.coefficientWeight x) 0 := by
    rw [hS]
    exact B.generator_mem_layer D x
  have hheight (x : D.CoefficientAlphabet) (i : Fin W.dim) :
      rationalLogHeight (E.basis.repr (B.generator D x) i) ≤ K := by
    rw [hE]
    exact (B.generator_height D x i).trans hMK
  obtain ⟨F, T, hT, hTc, hcentral, ⟨frame⟩, hmatrix, hlattice, hV⟩ :=
    hfree D.CoefficientAlphabet W.L I r W.dim W.rank.filtration.rank_le_degree E S
      D.coefficientWeight D.coefficientWeight_pos (B.generator D) hgen K hK hcard
      (hcomplex.mono S hMK) hheight (U.mono hMK)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra) :=
    IsModuleTopology.isTopologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 F.basis
  obtain ⟨V, hfreq, hobs⟩ := hV
  have heval : FreeDegreeRankLieAlgebra.lift S.filtration D.coefficientWeight
      D.coefficientWeight_pos (B.generator D) hgen = B.freeEvaluation D := by
    apply FreeDegreeRankLieAlgebra.hom_ext
    intro x
    exact (FreeDegreeRankLieAlgebra.lift_of _ _ _ _ _ x).trans
      (B.freeEvaluation_generator D x).symm
  rw [heval] at hmatrix hlattice hfreq hobs
  refine ⟨F, T, hT, hTc.mono T hbound, hcentral,
    ⟨frame.mono hbound⟩, (fun i j => (hmatrix i j).trans hbound), hlattice, ?_⟩
  exact ⟨V.mono hbound, hfreq, hobs⟩

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_native_shared_common_factorization (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {κ : Type*} {r N : ℕ} [NeZero N] {p : ℝ} {F : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p F), (∀ x, ‖F x‖ ≤ 1) →
      ∀ (c : Basis κ ℚ W.family.L) (τ : κ → ℕ)
        (hG : ∀ j, W.family.rank.filtration.associatedDegree.layer j =
          Submodule.span ℚ (c '' {i | j ≤ τ i})),
        Real.exp ((p + C) ^ C) ≤ N →
        let α : Fin s → Unit →₀ ℕ := fun d => Finsupp.single () (d.val + 1)
        ∃ (out : Fin W.family.outputDim) (H : Finset (ZMod N)) (q P : ℝ),
          H ⊆ W.shifts ∧ H.Nonempty ∧ CyclicShortShiftSet H ∧
          p ≤ q ∧ q ≤ P ∧ P ≤ (p + C) ^ C ∧
          ∃ (R : NativeRankRelation W.family out H q q) (D : R.CommonData P)
            (A : D.SparseAnchors), A.shifts ⊆ W.shifts ∧
            Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (A.shifts.card : ℝ) ∧
            ∃ n M : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
              0 < M ∧ (M : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
              (∀ t (ht : t ∈ D.quadruples), (D.witness t ht).projectedDenominator ∣ n) ∧
              ∃ ξ : W.family.model.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
                W.family.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 ξ = 1 ∧
                (∀ d (hd : Finsupp.weight (fun _ : Unit => 1) (α d) ≤ s),
                  Multiplicative.toAdd (W.family.rank.filtration.nativeHorizontalCoefficientHom
                    (by omega) c τ hG (fun _ : Unit => 1) (α d)
                    (W.family.rank.orbitEquiv (fun _ : Unit => 1) ξ)) ∈
                    (fourFirstProjection (D.horizontal
                      ⟨Finsupp.weight (fun _ : Unit => 1) (α d), Nat.lt_succ_of_le hd⟩)).baseChange ℝ) ∧
              ∃ H' : Finset (ZMod N), H' ⊆ A.shifts ∧ H'.Nonempty ∧
                Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (H'.card : ℝ) ∧
              ∃ Λ : Subgroup W.family.model.filtration.Group, Λ ≤ W.family.model.lattice ∧
                (Λ.subgroupOf W.family.model.lattice).Characteristic ∧
                (Λ.subgroupOf W.family.model.lattice).Normal ∧
                (Λ.subgroupOf W.family.model.lattice).FiniteIndex ∧
                (Λ.relIndex W.family.model.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
                ∃ (K : ℕ) (hK : 0 < K)
                  (hin : scaledIntegerGrid K ⊆ bchSubgroupCoordinates W.family.model.basis Λ)
                  (hout : bchSubgroupCoordinates W.family.model.basis Λ ⊆ denominatorGrid K),
                  (W.family.rank.withLattice Λ K hK hin hout).ComplexityLE ((p + C) ^ C) ∧
              ∃ U : (W.family.model.withLattice Λ K hK hin hout).UnitVerticalObservable
                  ((W.family.rank.withLattice Λ K hK hin hout).realSubgroup s r)
                  (Fin W.family.outputDim) ((p + C) ^ C),
                U.frequency = W.family.vertical.frequency ∧
              ∀ h ∈ H', ∃ ε γ v : W.family.model.filtration.realification.PolynomialOrbit
                  (fun _ : Unit => 1),
                W.family.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 ε = 1 ∧
                W.family.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 γ = 1 ∧
                W.family.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 v = 1 ∧
                CoefficientBound (W.family.model.basis.baseChange ℝ) (fun _ : Unit => (N : ℝ))
                  (Real.exp ((p + C) ^ C)) ε.log ∧
                CoefficientGrid (W.family.model.basis.baseChange ℝ) n γ.log ∧
                ε * ξ * v * γ = W.family.orbit h ∧
                (∀ d (hd : Finsupp.weight (fun _ : Unit => 1) (α d) ≤ s),
                  Multiplicative.toAdd (W.family.rank.filtration.nativeHorizontalCoefficientHom
                    (by omega) c τ hG (fun _ : Unit => 1) (α d)
                    (W.family.rank.orbitEquiv (fun _ : Unit => 1) v)) ∈
                    (fourDependentProjection (D.horizontal
                      ⟨Finsupp.weight (fun _ : Unit => 1) (α d), Nat.lt_succ_of_le hd⟩)).baseChange ℝ) ∧
                Nonempty (NativeVectorCorrelation (s - 1) N ((p + C) ^ C)
                  (W.replacedRankResidual h (fun i x => U.observable i (QuotientGroup.mk
                    (W.family.model.filtration.realification.polynomialOrbitEval
                      (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) (ξ * v)))))) ∧
                ∀ x y : Unit → ℤ, (∀ j, (M : ℤ) ∣ x j - y j) →
                  ((QuotientGroup.mk (W.family.model.filtration.realification.polynomialOrbitEval
                    (fun _ : Unit => 1) x γ) : W.family.model.Space) =
                    QuotientGroup.mk (W.family.model.filtration.realification.polynomialOrbitEval
                      (fun _ : Unit => 1) y γ)) ∧
                  ((QuotientGroup.mk (W.family.model.filtration.realification.polynomialOrbitEval
                    (fun _ : Unit => 1) x γ)⁻¹ : W.family.model.Space) =
                    QuotientGroup.mk (W.family.model.filtration.realification.polynomialOrbitEval
                      (fun _ : Unit => 1) y γ)⁻¹) := by
  obtain ⟨a, _, hfactor⟩ := exists_native_frozen_common_factorization s hs
  obtain ⟨b, _, hshared⟩ := exists_native_shared_frozen_orbit_correlations s 1
  let B₀ : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (B₀ + (B₀ + 2 + Polynomial.C b) ^ b + 2)
  refine ⟨C, hC, ?_⟩
  intro κ r N _ p F W hF c τ hG hN α
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.family.dim).trans W.family.complexity.1.1
  let B := (p + a) ^ a
  let T := (B + 2 + b) ^ b
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  have hcost : B + T + 2 ≤ (p + C) ^ C := by
    simpa [B₀, B, T, Polynomial.eval₂_pow] using hbudget p hp
  have hBC : B ≤ (p + C) ^ C := by linarith
  have hTC : T ≤ (p + C) ^ C := by linarith
  obtain ⟨out, H, q, P, hHW, hH, hshort, hpq, hqP, hPB, R, D, A,
      hAW, hdensity, n, M, hn, hnB, hM, hMB, hproj, ξ, hξ₀, hfirst, hsplit⟩ :=
    hfactor W hF c τ hG ((Real.exp_le_exp.mpr hBC).trans hN)
  have hpB : p ≤ B + 2 := (hpq.trans (hqP.trans hPB)).trans (by linarith)
  have hA : A.shifts.Nonempty := by
    have hcard : (0 : ℝ) < Fintype.card (ZMod N) := by exact_mod_cast Fintype.card_pos
    have hpos := (mul_pos (Real.exp_pos (-B)) hcard).trans_le hdensity
    exact Finset.card_pos.mp (by exact_mod_cast hpos)
  have hdata (h : {h // h ∈ A.shifts}) := hsplit h h.property
  choose ε γ v hε₀ hγ₀ hv₀ hε hγ heq hdep hy hperiod using hdata
  choose y _hunit V using hy
  let ε' (h : ZMod N) := if hh : h ∈ A.shifts then ε ⟨h, hh⟩ else 1
  let γ' (h : ZMod N) := if hh : h ∈ A.shifts then γ ⟨h, hh⟩ else 1
  let v' (h : ZMod N) := if hh : h ∈ A.shifts then v ⟨h, hh⟩ else 1
  let y' (h : ZMod N) := if hh : h ∈ A.shifts then y ⟨h, hh⟩ else 0
  have hε' (h : ZMod N) (hh : h ∈ A.shifts) :
      CoefficientBound (W.family.model.basis.baseChange ℝ) (fun _ : Unit => (N : ℝ))
        (Real.exp (((B + 2) + 2) ^ 1)) (ε' h).log := by
    simp only [ε', dite_eq_left hh]
    exact CoefficientBound.mono _ _ (fun _ => by exact_mod_cast NeZero.pos N) (hε ⟨h, hh⟩)
      (Real.exp_le_exp.mpr (by simp only [pow_one]; linarith))
  have hγ' (h : ZMod N) (hh : h ∈ A.shifts) :
      CoefficientGrid (W.family.model.basis.baseChange ℝ) n (γ' h).log := by
    simpa only [γ', dite_eq_left hh] using hγ ⟨h, hh⟩
  have hcorr (h : ZMod N) (hh : h ∈ A.shifts) :
      Nonempty (NativeVectorCorrelation (s - 1) N (B + 2)
        (W.replacedRankResidual h (fun i x => W.family.model.frozenCyclicOrbitValue
          (W.family.vertical.observable i) (ε' h) (ξ * v' h) (γ' h) (y' h) x))) := by
    simpa only [ε', γ', v', y', dite_eq_left hh] using
      (show Nonempty _ from ⟨(Classical.choice (V ⟨h, hh⟩)).mono (show B ≤ B + 2 by linarith)⟩)
  obtain ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, K, hK, hin, hout,
      hRank, H', hsub, hnonempty, hdense, U, hfreq, hU⟩ :=
    hshared W hF (show 0 ≤ B + 2 by linarith) hpB n hn
      (hnB.trans (Real.exp_le_exp.mpr (by linarith)))
      A.shifts ε' γ' (fun h => ξ * v' h) y' hA hε' hγ' hcorr
  have hdense' : Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (H'.card : ℝ) := by
    calc
      _ ≤ Real.exp (-(B + T)) * Fintype.card (ZMod N) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (Nat.cast_nonneg _)
      _ = Real.exp (-T) * (Real.exp (-B) * Fintype.card (ZMod N)) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-T) * A.shifts.card := mul_le_mul_of_nonneg_left hdensity (Real.exp_pos _).le
      _ ≤ _ := hdense
  refine ⟨out, H, q, P, hHW, hH, hshort, hpq, hqP, hPB.trans hBC, R, D, A,
    hAW, ?_, n, M, hn, hnB.trans (Real.exp_le_exp.mpr hBC), hM,
    hMB.trans (Real.exp_le_exp.mpr hBC), hproj, ξ, hξ₀, hfirst,
    H', hsub, hnonempty, hdense', Λ, hΛ, hchar, hnormal, hfinite,
    hindex.trans (Real.exp_le_exp.mpr hTC), K, hK, hin, hout, hRank.mono _ hTC,
    U.mono hTC, hfreq, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hBC))
      (Nat.cast_nonneg _)).trans hdensity
  · intro h hh
    let h' : {h // h ∈ A.shifts} := ⟨h, hsub hh⟩
    refine ⟨ε h', γ h', v h', hε₀ h', hγ₀ h', hv₀ h', ?_, hγ h', heq h', hdep h', ?_, hperiod h'⟩
    · exact CoefficientBound.mono _ _ (fun _ => by exact_mod_cast NeZero.pos N) (hε h')
        (Real.exp_le_exp.mpr hBC)
    · simpa only [v', dite_eq_left (hsub hh), h', UnitVerticalObservable.mono] using
        (show Nonempty _ from ⟨(Classical.choice (hU h hh)).mono hTC⟩)

end Erdos3

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_native_shared_free_family (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p f), (∀ x, ‖f x‖ ≤ 1) →
        Real.exp ((p + C) ^ C) ≤ N →
        ∃ (out : Fin W.family.outputDim) (H : Finset (ZMod N)) (q P : ℝ),
          H ⊆ W.shifts ∧ H.Nonempty ∧ CyclicShortShiftSet H ∧
          p ≤ q ∧ q ≤ P ∧ P ≤ (p + C) ^ C ∧
          ∃ (R : NativeRankRelation W.family out H q q) (D : R.CommonData P)
            (B : D.CoefficientBases ((p + C) ^ C))
            (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
              (finrank ℚ D.CoefficientFreeLieAlgebra))
            (T : E.DegreeRankStructure r),
            T.filtration = D.coefficientFreeFiltration ∧
            T.ComplexityLE ((p + C) ^ C) ∧ IsCentralLieBasis E.basis ∧
            Nonempty (FreeCoordinateFrame E.basis ((p + C) ^ C)) ∧
            (letI := moduleTopology ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
             letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra) :=
               IsModuleTopology.isTopologicalAddGroup ℝ _
             letI := realification_moduleTopology_t2 E.basis
             ∃ V : E.UnitVerticalObservable (T.realSubgroup s r)
                 (Fin W.family.outputDim) ((p + C) ^ C),
               V.frequency = B.freeFrequency D ∧
               ∃ ξ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
                 E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 ξ = 1 ∧
                 (∀ d : Fin s, coefficients ξ.log (Finsupp.single () (d.val + 1)) ∈
                   (D.commonFreeSpan d).baseChange ℝ) ∧
                 ∃ H' : Finset (ZMod N), H' ⊆ H ∧ H' ⊆ W.shifts ∧ H'.Nonempty ∧
                   CyclicShortShiftSet H' ∧
                   Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (H'.card : ℝ) ∧
                   ∀ h ∈ H', ∃ v : E.filtration.realification.PolynomialOrbit
                       (fun _ : Unit => 1),
                     E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 v = 1 ∧
                     (∀ d : Fin s, coefficients v.log (Finsupp.single () (d.val + 1)) ∈
                       (D.dependentFreeSpan d).baseChange ℝ) ∧
                     Nonempty (NativeVectorCorrelation (s - 1) N ((p + C) ^ C)
                       (W.replacedRankResidual h (fun i x => V.observable i (QuotientGroup.mk
                         (E.filtration.realification.polynomialOrbitEval
                           (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) (ξ * v))))))) := by
  obtain ⟨a, _, hshared⟩ := exists_native_shared_common_factorization s hs
  obtain ⟨b, _, hbases⟩ := NativeRankRelation.CommonData.exists_controlled_coefficient_bases
  obtain ⟨e, _, hfree⟩ := NativeRankRelation.CommonData.exists_native_common_free_model s
  let A₀ : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  let M₀ : Polynomial ℕ := A₀ + (A₀ + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (M₀ + (M₀ + Polynomial.C e) ^ e)
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W hf hN
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.family.dim).trans W.family.complexity.1.1
  obtain ⟨c, τ, _, _, _, hLayers, _⟩ :=
    W.family.model.exists_controlled_adapted_basis hp W.family.complexity.1
  have hG (j : ℕ) : W.family.rank.filtration.associatedDegree.layer j =
      Submodule.span ℚ (c '' {i | j ≤ τ i}) := by
    rw [W.family.rank.associated]
    exact hLayers j
  let A := (p + a) ^ a
  let M := A + (A + b) ^ b
  let Q := (M + e) ^ e
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hAB : 0 ≤ (A + b) ^ b := by positivity
  have hM : 0 ≤ M := add_nonneg hA hAB
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hAM : A ≤ M := le_add_of_nonneg_right hAB
  have hMC : M ≤ (p + C) ^ C := by
    have h : M + Q ≤ (p + C) ^ C := by
      simpa [A₀, M₀, A, M, Q, Polynomial.eval₂_pow] using hbudget p hp
    exact (le_add_of_nonneg_right hQ).trans h
  have hQC : Q ≤ (p + C) ^ C := by
    have h : M + Q ≤ (p + C) ^ C := by
      simpa [A₀, M₀, A, M, Q, Polynomial.eval₂_pow] using hbudget p hp
    exact (le_add_of_nonneg_left hM).trans h
  have hAC := hAM.trans hMC
  obtain ⟨out, H, q, P, hHW, hH, hshort, hpq, hqP, hPA, R, D, anchors,
      hanchors, _hdensity, n, m, _hn, _hnA, _hm, _hmA, _hproj, ξ, hξ0, hcommon,
      H', hsub, hnonempty, hdense, Λ, _hΛ, _hchar, _hnormal, _hfinite, _hindex,
      k, hk, hin, hout, hRank, U, hfreq, hfactor⟩ :=
    hshared W hf c τ hG ((Real.exp_le_exp.mpr hAC).trans hN)
  have hP : 0 ≤ P := hp.trans (hpq.trans hqP)
  obtain ⟨B₀⟩ := hbases D hP (hpq.trans hqP)
  have hBM : (P + b) ^ b ≤ M := by
    calc
      (P + b) ^ b ≤ (A + b) ^ b :=
        pow_le_pow_left₀ (by positivity) (by change P + (b : ℝ) ≤ A + b; linarith) b
      _ ≤ M := le_add_of_nonneg_left hA
  let B := B₀.mono D hBM
  obtain ⟨E, T, hT, hTc, hcentral, ⟨frame⟩, _hmatrix, _hlattice, hV⟩ :=
    hfree D B (W.family.model.withLattice Λ k hk hin hout)
      (W.family.rank.withLattice Λ k hk hin hout) rfl rfl hM
      (hRank.mono _ hAM) (Fin W.family.outputDim) (U.mono hAM)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra) :=
    IsModuleTopology.isTopologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 E.basis
  obtain ⟨V, hVfreq, hVobs⟩ := hV
  have hdegree (d : Fin s) :
      Finsupp.weight (fun _ : Unit => 1) (Finsupp.single () (d.val + 1)) ≤ s := by
    simpa only [Finsupp.weight_single, smul_eq_mul, mul_one] using Nat.succ_le_of_lt d.isLt
  have hξcoeff (d : Fin s) : coefficients ξ.log (Finsupp.single () (d.val + 1)) ∈
      (D.commonCoefficientSpace ⟨d.val + 1, by omega⟩).baseChange ℝ := by
    have h := (D.native_coefficient_mem_common (by omega) c τ hG (fun _ : Unit => 1)
      (Finsupp.single () (d.val + 1)) (hdegree d) ξ).mpr (hcommon d (hdegree d))
    simpa only [Finsupp.weight_single, smul_eq_mul, mul_one] using h
  obtain ⟨ξ', hξ'0, hξ'coeff, _hξ'log, hξ'eval⟩ :=
    B.exists_native_commonFreePolynomialOrbit D E T hT ξ hξ0 hξcoeff
  have hH'H : H' ⊆ H := hsub.trans anchors.shifts_subset
  refine ⟨out, H, q, P, hHW, hH, hshort, hpq, hqP, hPA.trans hAC, R, D,
    B.mono D hMC, E, T, hT, hTc.mono T hQC, hcentral, ⟨frame.mono hQC⟩, V.mono hQC, ?_, ξ', hξ'0,
    hξ'coeff, H', hH'H, hsub.trans hanchors, hnonempty,
    (fun x hx y hy => hshort x (hH'H hx) y (hH'H hy)), ?_, ?_⟩
  · change V.frequency = W.family.vertical.frequency.comp (B.freeEvaluation D).toLinearMap
    change V.frequency = U.frequency.comp (B.freeEvaluation D).toLinearMap at hVfreq
    rw [hfreq] at hVfreq
    exact hVfreq
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hAC))
      (Nat.cast_nonneg _)).trans hdense
  · intro h hh
    obtain ⟨ε, γ, v, _hε0, _hγ0, hv0, _hε, _hγ, _heq, hdep, hcorr, _hperiod⟩ := hfactor h hh
    have hvcoeff (d : Fin s) : coefficients v.log (Finsupp.single () (d.val + 1)) ∈
        (D.dependentCoefficientSpace ⟨d.val + 1, by omega⟩).baseChange ℝ := by
      have h := (D.native_coefficient_mem_dependent (by omega) c τ hG (fun _ : Unit => 1)
        (Finsupp.single () (d.val + 1)) (hdegree d) v).mpr (hdep d (hdegree d))
      simpa only [Finsupp.weight_single, smul_eq_mul, mul_one] using h
    obtain ⟨v', hv'0, hv'coeff, _hv'log, hv'eval⟩ :=
      B.exists_native_dependentFreePolynomialOrbit D E T hT v hv0 hvcoeff
    refine ⟨v', hv'0, hv'coeff, ?_⟩
    have hvalue (i : Fin W.family.outputDim) (x : ZMod N) :
        (V.mono hQC).observable i (QuotientGroup.mk
          (E.filtration.realification.polynomialOrbitEval
            (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) (ξ' * v'))) =
        U.observable i (QuotientGroup.mk
          (W.family.model.filtration.realification.polynomialOrbitEval
            (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) (ξ * v))) := by
      change V.observable i _ = _
      rw [hVobs]
      change U.observable i _ = U.observable i _
      congr 2
      rw [map_mul, map_mul, hξ'eval, hv'eval, map_mul]
    have heq : (fun (i : Fin W.family.outputDim) (x : ZMod N) =>
        (V.mono hQC).observable i (QuotientGroup.mk
        (E.filtration.realification.polynomialOrbitEval
          (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) (ξ' * v')))) =
        (fun (i : Fin W.family.outputDim) (x : ZMod N) => U.observable i (QuotientGroup.mk
          (W.family.model.filtration.realification.polynomialOrbitEval
            (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) (ξ * v)))) :=
      funext fun i => funext (hvalue i)
    rw [heq]
    exact ⟨(Classical.choice hcorr).mono hAC⟩

end Erdos3

end

end OAI
