/- Modified for ProveIt: Use IsModuleTopology.topologicalAddGroup on Lean 4.32; statements unchanged. -/
import OAI.Combinatorics.Progressions.Estimates.NativeTwoVariableSplitFreezing
import OAI.Combinatorics.Progressions.Nilpotent.PreparedDilationNiltest

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module
open scoped TensorProduct BigOperators NNReal

theorem exists_controlled_dilation_family (s : ℕ) (q : ℤ) :
    ∃ Z : ℕ, 2 ≤ Z ∧ ∀ {σ I : Type*} {L : Type}
      [Fintype σ] [DecidableEq σ] [Fintype I] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {t d : ℕ} {bound : σ → ℕ} (D : RationalFilteredNilmanifold L t d)
      (M : D.MultidegreeStructure bound) (_hs : ∑ j, bound j = t) (_ht : t = s + 1)
      {p : ℝ}, M.ComplexityLE p →
      ∀ (V : D.UnitVerticalObservable (M.realSubgroup bound) I p)
        (g : M.filtration.realification.PolynomialOrbit),
      ∃ R : NativeIntegerModelFamily (fun _ : σ => 1) s ((p + Z) ^ Z)
        (dilationTensorCrossProduct
          (fun j y => V.observable j
            (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval y g))) q t),
        R.dim ≤ 2 * d := by
  obtain ⟨C, _, hnormal⟩ := exists_controlled_group_normalization (s + 1)
  obtain ⟨Z, hZ, hbudget⟩ := DilationBudget.exists_full_bound (s + 1) q C
    (MultilinearityBudget.reconstructionExponent s)
  refine ⟨Z, hZ, ?_⟩
  intro σ I L _ _ _ _ _ _ _ _ _ t d bound D M hs ht p hM V g
  subst ht
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hM.1.1
  have hshift := DilationBudget.shift_bounds q hp
  have hA := DilationBudget.ambient_bounds (s + 1) q hp
  have hQbound := DilationBudget.quotient_bounds (s + 1) q hp
  have hB := DilationBudget.common_bounds (s + 1) q C hp
  obtain ⟨E, hEF, hEL, hE, hdim, he⟩ := M.exists_dilationPair_model (q : ℚ)
    (hM.mono M hshift.2.1) hshift.2.2
  have hE' := hE.mono E hA.2.2.1
  obtain ⟨n, hn, Q, hQF, hQL, hQ, hq, _⟩ := E.exists_controlled_top_quotient hA.1 hE'
  obtain ⟨ε, γ, A, hγ, hfactor, _, hAnorm, hε⟩ := hnormal D p hp hM.1
    (M.filtration.realification.polynomialOrbitEval 0 g)
  let K := M.filtration.ordinary.dilationPairSubalgebra (q : ℚ)
  let J := K ⧸ E.filtration.layerIdeal (s + 1)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] K)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] K) := IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] K) := realification_moduleTopology_t2 E.basis
  let := moduleTopology ℝ (ℝ ⊗[ℚ] J)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] J) := IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] J) := realification_moduleTopology_t2 Q.basis
  have he' (j : Fin 2) (a) (k) : rationalLogHeight
      (D.basis.repr (M.filtration.ordinary.dilationPairProjection (q : ℚ) j (E.basis a)) k) ≤
        DilationBudget.common (s + 1) q C p := by
    fin_cases j
    · exact (he a k).1.trans (hA.2.2.2.trans hB.2.2.1)
    · exact (he a k).2.trans (hA.2.2.2.trans hB.2.2.1)
  have hall (a : I × (Fin (q ^ (s + 1)).natAbs → I)) := M.exists_prepared_dilation_niltest
    q hs E hEF hEL Q hQF hQL hB.1 (hM.1.mono D hB.2.1) (hE'.mono E hB.2.2.1) he'
    (hQ.mono Q hB.2.2.2.1)
    (fun j k => (hq k j).trans (hQbound.2.2.trans hB.2.2.2.1))
    (V.mono hB.2.1) g ε γ hγ hfactor A (hAnorm.trans (Real.exp_le_exp.mpr hB.2.2.2.2)) hε a.1 a.2
  choose T hnorm hcomplex hzero heval using hall
  refine ⟨{
    L := J
    dim := n
    model := Q
    test := T
    norm := fun a => (hnorm a).le
    complexity := fun a => (hcomplex a).mono (hbudget p hp).1
    normalized := hzero
    eval := heval }, hn.trans hdim⟩

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open RationalFilteredNilmanifold.MultidegreeStructure
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem exists_dilation_family {σ : Type*} [Fintype σ] [DecidableEq σ]
    (bound : σ → ℕ) (hpos : 1 ≤ ∑ j, bound j) (q : ℤ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter bound p),
      ∃ R : NativeIntegerModelFamily (fun _ : σ => 1) ((∑ j, bound j) - 1)
        ((p + C) ^ C) (dilationTensorCrossProduct W.eval q (∑ j, bound j)),
        R.dim ≤ 2 * W.dim := by
  obtain ⟨C, hC, hcontrol⟩ := exists_controlled_dilation_family ((∑ j, bound j) - 1) q
  exact ⟨C, hC, fun W => hcontrol W.model W.multi rfl (Nat.sub_add_cancel hpos).symm
    W.complexity W.vertical W.orbit⟩

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
