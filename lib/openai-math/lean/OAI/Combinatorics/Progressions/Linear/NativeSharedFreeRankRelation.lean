/- Modified for ProveIt: Use IsModuleTopology.topologicalAddGroup on Lean 4.32; statements unchanged. -/
import OAI.Combinatorics.Progressions.Estimates.NativeSharedFreeFamily

namespace OAI

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

theorem exists_native_shared_free_rank_relation (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p f), (∀ x, ‖f x‖ ≤ 1) →
      Real.exp ((p + C) ^ C) ≤ N →
      ∃ (A : ℝ) (hpA : p ≤ A), A ≤ (p + C) ^ C ∧
      ∃ (out : Fin W.family.outputDim) (H : Finset (ZMod N)) (q P : ℝ),
        H ⊆ W.shifts ∧ H.Nonempty ∧ CyclicShortShiftSet H ∧
        p ≤ q ∧ q ≤ P ∧ P ≤ A ∧
        ∃ (R : NativeRankRelation W.family out H q q) (D : R.CommonData P)
          (B : D.CoefficientBases A)
          (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
            (finrank ℚ D.CoefficientFreeLieAlgebra))
          (T : E.DegreeRankStructure r) (hT : T.ComplexityLE A),
          T.filtration = D.coefficientFreeFiltration ∧ IsCentralLieBasis E.basis ∧
          Nonempty (FreeCoordinateFrame E.basis A) ∧
          (letI := moduleTopology ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
           letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra) :=
             IsModuleTopology.topologicalAddGroup ℝ _
           letI := realification_moduleTopology_t2 E.basis
           ∃ V : E.UnitVerticalObservable (T.realSubgroup s r) (Fin W.family.outputDim) A,
             V.frequency = B.freeFrequency D ∧
             ∃ (ξ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
               (hξ : E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 ξ = 1),
               (∀ d : Fin s, coefficients ξ.log (Finsupp.single () (d.val + 1)) ∈
                 (D.commonFreeSpan d).baseChange ℝ) ∧
               ∃ H' : Finset (ZMod N), H' ⊆ H ∧ H' ⊆ W.shifts ∧ H'.Nonempty ∧
                 CyclicShortShiftSet H' ∧
                 Real.exp (-A) * Fintype.card (ZMod N) ≤ (H'.card : ℝ) ∧
                 ∃ (v : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
                   (hv : ∀ h, E.filtration.realification.polynomialOrbitEval
                     (fun _ : Unit => 1) 0 (v h) = 1),
                   (∀ h (d : Fin s), coefficients (v h).log (Finsupp.single () (d.val + 1)) ∈
                     (D.dependentFreeSpan d).baseChange ℝ) ∧
                   (∀ h ∈ H', Nonempty (NativeVectorCorrelation (s - 1) N A
                     (W.replacedRankResidual h (fun i x => V.observable i (QuotientGroup.mk
                       (E.filtration.realification.polynomialOrbitEval
                         (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) (ξ * v h))))))) ∧
                   (let U := W.replacementFamily E T hpA hT V (fun h => ξ * v h)
                     (fun h => by rw [map_mul, hξ, hv h, one_mul])
                    ∃ (out' : Fin U.outputDim) (H'' : Finset (ZMod N)) (q' : ℝ),
                      H'' ⊆ H' ∧ H''.Nonempty ∧ CyclicShortShiftSet H'' ∧
                      Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (H''.card : ℝ) ∧
                      A ≤ q' ∧ q' ≤ (p + C) ^ C ∧
                      ∃ R' : NativeRankRelation U out' H'' q' q',
                        Nonempty (R'.CommonData ((p + C) ^ C)))) := by
  obtain ⟨a, _, hfree⟩ := exists_native_shared_free_family s hs
  obtain ⟨c, _, hrelation⟩ := exists_native_common_rank_relation s (by omega)
  let A₀ : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ :=
    exists_natPolynomial_eval_budget (A₀ + (A₀ + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W hf hN
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.family.dim).trans W.family.complexity.1.1
  let A := (p + a) ^ a
  let Z := (A + c) ^ c
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hZ : 0 ≤ Z := by dsimp only [Z]; positivity
  have hAZ : A + Z ≤ (p + C) ^ C := by
    simpa [A₀, A, Z, Polynomial.eval₂_pow] using hbudget p hp
  have hAC : A ≤ (p + C) ^ C := (le_add_of_nonneg_right hZ).trans hAZ
  have hZC : Z ≤ (p + C) ^ C := (le_add_of_nonneg_left hA).trans hAZ
  obtain ⟨out, H, q, P, hHW, hH, hshort, hpq, hqP, hPA, R, D, B, E, T,
    hfiltration, hT, hcentral, hframe, hdata⟩ :=
    hfree W hf ((Real.exp_le_exp.mpr hAC).trans hN)
  have hpA : p ≤ A := hpq.trans (hqP.trans hPA)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 E.basis
  obtain ⟨V, hfreq, ξ, hξ, hcommon, H', hH'H, hH'W, hH', hshort', hdense, hfactor⟩ := hdata
  have hall (h : ZMod N) :
      ∃ v : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
        E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 v = 1 ∧
        (∀ d : Fin s, coefficients v.log (Finsupp.single () (d.val + 1)) ∈
          (D.dependentFreeSpan d).baseChange ℝ) ∧
        (h ∈ H' → Nonempty (NativeVectorCorrelation (s - 1) N A
          (W.replacedRankResidual h (fun i x => V.observable i (QuotientGroup.mk
            (E.filtration.realification.polynomialOrbitEval
              (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) (ξ * v))))))) := by
    by_cases hh : h ∈ H'
    · obtain ⟨v, hv, hcoeff, hc⟩ := hfactor h hh
      exact ⟨v, hv, hcoeff, fun _ => hc⟩
    · refine ⟨1, map_one _, ?_, fun hh' => (hh hh').elim⟩
      intro d
      change (0 : ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra) ∈ _
      exact Submodule.zero_mem _
  choose v hv hcoeff hcorr using hall
  let X := W.replaceRank E T hpA hT V (fun h => ξ * v h)
    (fun h => by rw [map_mul, hξ, hv h, one_mul]) H' hH' hdense hcorr
  obtain ⟨out', H'', q', hsub, hnonempty, hshort'', hdense'', hAq, hqZ, R', ⟨D'⟩⟩ :=
    hrelation X hf ((Real.exp_le_exp.mpr hZC).trans hN)
  refine ⟨A, hpA, hAC, out, H, q, P, hHW, hH, hshort, hpq, hqP, hPA,
    R, D, B, E, T, hT, hfiltration, hcentral, hframe, V, hfreq, ξ, hξ, hcommon,
    H', hH'H, hH'W, hH', hshort', hdense, v, hv, hcoeff, hcorr,
    out', H'', q', hsub, hnonempty, hshort'', ?_, hAq, hqZ.trans hZC, R', ⟨D'.mono hZC⟩⟩
  exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hZC))
    (Nat.cast_nonneg _)).trans hdense''

end Erdos3

end

end OAI
