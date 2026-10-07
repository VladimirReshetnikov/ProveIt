/- Modified for ProveIt: Use IsModuleTopology.topologicalAddGroup on Lean 4.32; statements unchanged. -/
import OAI.Combinatorics.Progressions.Estimates.NativeNilcharacterTranslationEquivalence

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

open scoped TensorProduct BigOperators

theorem exists_integer_translation_equivalence_budget (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} {I σ : Type*}
      [LieRing L] [LieAlgebra ℚ L] [Fintype I]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d) {p : ℝ}
      (V : D.UnitVerticalObservable (D.filtration.realification.subgroup (s + 1)) I p)
      (g : D.filtration.realification.PolynomialOrbit (fun _ : σ => 1)),
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card I : ℝ) ≤ Real.exp p →
      ∀ a b : σ → ℤ,
      NativeIntegerVectorEquivalence s ((p + C) ^ C)
        (fun i x => V.observable i (QuotientGroup.mk
          (D.filtration.realification.polynomialOrbitEval (fun _ : σ => 1) (x + a) g)))
        (fun i x => V.observable i (QuotientGroup.mk
          (D.filtration.realification.polynomialOrbitEval (fun _ : σ => 1) (x + b) g))) := by
  obtain ⟨A, _, hexpand⟩ := exists_shifted_product_expansion s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C A) ^ A + X + 4)
  refine ⟨C, hC, ?_⟩
  intro L I σ _ _ _ _ _ _ _ d D p V g hp hD hI a b
  let r := (p + A) ^ A
  let q := r + p + 4
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hrq : r ≤ q := by dsimp [q]; linarith
  have hq : 0 ≤ q := hp.trans hpq
  have hbound : q ≤ (p + C) ^ C := by
    simpa [q, r, X, Polynomial.eval₂_pow] using hbudget p hp
  have hd := hI.trans (Real.exp_le_exp.mpr (hpq.trans hbound))
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra) :=
    realification_moduleTopology_t2 (Module.finBasis ℚ D.filtration.squareLieSubalgebra)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1))) := IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1))) :=
    realification_moduleTopology_t2 (Module.finBasis ℚ (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1)))
  refine ⟨hd, hd, ?_⟩
  intro i j
  obtain ⟨n, Q, S, _, hSc, hSe⟩ := hexpand D V g hp hD (fun _ => Nat.zero_lt_one) i j a b
  have hcard : (Fintype.card (Fin 4) : ℝ) ≤ Real.exp q := by
    simp only [Fintype.card_fin, Nat.cast_ofNat]
    have h4 : 4 ≤ q := by dsimp [q]; linarith
    linarith [Real.add_one_le_exp q]
  have hcost : (∑ k, ‖polarizationWeight k‖) ≤ Real.exp q := by
    rw [polarizationWeight_cost]
    exact Real.one_le_exp hq
  exact ⟨(NativeIntegerExpansion.ofFamily Q S polarizationWeight hcard
    (fun k => (hSc k).mono hrq) hcost hSe).mono hbound⟩

end Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem exists_multidegree_integer_translation (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ : Type*} [Fintype σ] (bound : σ → ℕ),
      (∑ i, bound i) = s + 1 → ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter bound p)
      (a b : σ → ℤ), NativeIntegerVectorEquivalence s ((p + C) ^ C)
        (fun i x => W.eval i (x + a)) (fun i x => W.eval i (x + b)) := by
  obtain ⟨C, hC, htranslate⟩ := UnitVerticalObservable.exists_integer_translation_equivalence_budget s
  refine ⟨C, hC, ?_⟩
  intro σ _ bound hdegree p W a b
  rw [← hdegree] at htranslate
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let U : W.model.UnitVerticalObservable
      (W.model.filtration.realification.subgroup (∑ i, bound i)) (Fin W.outputDim) p :=
    { W.vertical with
      vertical := fun i z hz x => W.vertical.vertical i z (W.multi.realSubgroup_top.symm ▸ hz) x
      integral := fun z hz hL => W.vertical.integral z (W.multi.realSubgroup_top.symm ▸ hz) hL }
  have hI : (Fintype.card (Fin W.outputDim) : ℝ) ≤ Real.exp p := by
    simpa only [Fintype.card_fin] using W.output_bound
  have E := htranslate W.model U (W.multi.orbitToOrdinary W.orbit) hp W.complexity.1 hI a b
  have heval (i : Fin W.outputDim) (x : σ → ℤ) :
      U.observable i (QuotientGroup.mk
        (W.model.filtration.realification.polynomialOrbitEval (fun _ => 1) x
          (W.multi.orbitToOrdinary W.orbit))) = W.eval i x := by
    rw [W.multi.orbitToOrdinary_eval]
    rfl
  simpa only [heval] using E

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
