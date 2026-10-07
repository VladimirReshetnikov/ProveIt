import OAI.Combinatorics.Progressions.Estimates.MixedPrimitiveGowers

namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeCyclicModel.lie NativeCyclicModel.algebra NativeCyclicModel.topology
  NativeCyclicModel.topologicalAdd NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

theorem exists_mixed_diagonal_niltest {d : ℕ} {p : ℝ}
    (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) p) (i : Fin W.outputDim) :
    ∃ T : W.model.Niltest (fun _ : Unit => 1), T.normBound = 1 ∧ T.ComplexityLE (p + 4) ∧
      ∀ n : ℤ, T.eval (fun _ => n) = W.eval i (fun _ => n) := by
  obtain ⟨T, hT, hcomplexity, heval⟩ := W.exists_linear_niltest i
    (fun _ => { toFun := fun x : Unit → ℤ => x (), map_zero' := rfl, map_add' := fun _ _ => rfl })
  exact ⟨T, hT, hcomplexity, fun n => heval (fun _ => n)⟩

theorem exists_mixed_primitive_niltest_budget (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) p,
      ∀ i : Fin W.outputDim, ∀ g ∈ nativeCyclicFunctions (d + 2) N p,
      (fun n : ZMod N => star (W.eval i (fun _ => (n.val : ℤ))) * g n) ∈
        nativeCyclicFunctions (d + 3) N ((p + C) ^ C) := by
  obtain ⟨A, _, hproduct⟩ := exists_productNiltestBudget_bound
  let X : Polynomial ℕ := Polynomial.X
  let R := 2 * X + (X + 2) ^ 2 + 7
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((R + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp W i g ⟨G⟩
  have hdegree : (∑ _ : MixedReplicatedIndex (d + 2), (1 : ℕ)) = d + 3 := mixedReplicated_totalDegree (d + 1)
  have hraise : d + 2 ≤ ∑ _ : MixedReplicatedIndex (d + 2), (1 : ℕ) := by omega
  obtain ⟨T, hTnorm, hT, hTeval⟩ := W.exists_mixed_diagonal_niltest i
  let r := 2 * p + (p + 2) ^ 2 + 7
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hpr : p + 4 ≤ r := by dsimp [r]; nlinarith [sq_nonneg (p + 2)]
  have hGr : raisedNiltestBudget p ≤ r := by dsimp [raisedNiltestBudget, r]; linarith
  let K : Bool → Type := BoolLieFamily W.L G.L
  let dims : Bool → ℕ := fun b => Bool.rec G.dim W.dim b
  let models : ∀ b, RationalFilteredNilmanifold (K b) (∑ _ : MixedReplicatedIndex (d + 2), 1) (dims b) := fun b => by
    cases b
    · exact G.model.raiseStep hraise
    · exact W.model
  let tests : ∀ b, (models b).Niltest (fun _ : Unit => 1) := fun b => by
    cases b
    · exact G.test.raiseStep hraise
    · exact T.conjugate
  have htests : ∀ b, (tests b).ComplexityLE r := by
    intro b
    cases b
    · exact (G.test.raiseStep_complexity hraise hp G.complexity).mono hGr
    · exact hT.mono hpr
  have hcap : ∀ b, (tests b).normBound ≤ 1 := by
    intro b
    cases b
    · exact G.norm
    · exact hTnorm.le
  have hcard : (Fintype.card Bool : ℝ) ≤ r := by
    simp only [Fintype.card_bool, Nat.cast_ofNat]
    linarith
  let : FiniteDimensional ℚ (∀ b, K b) :=
    (RationalFilteredNilmanifold.productFinBasis models).finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ b, K b))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ b, K b)) :=
    IsModuleTopology.isTopologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] (∀ b, K b)) :=
    realification_moduleTopology_t2 (RationalFilteredNilmanifold.productFinBasis models)
  let S := RationalFilteredNilmanifold.unitBoundedPiNiltest models tests hr hcard htests hcap
  have hcost : productNiltestBudget r ≤ (p + C) ^ C := by
    apply (hproduct r hr).trans
    simpa [X, R, r, Polynomial.eval₂_pow] using hbudget p hp
  have H : Nonempty (NativeCyclicModel (∑ _ : MixedReplicatedIndex (d + 2), 1) N ((p + C) ^ C)
      (fun n : ZMod N => star (W.eval i (fun _ => (n.val : ℤ))) * g n)) := by
    refine ⟨{
      L := ∀ b, K b
      dim := _
      model := RationalFilteredNilmanifold.pi models
      test := S
      norm := le_rfl
      complexity := (RationalFilteredNilmanifold.unitBoundedPiNiltest_complexity
        models tests hr hcard htests hcap).mono hcost
      eval := ?_ }⟩
    intro n
    change _ = S.eval (fun _ => (n.val : ℤ))
    rw [RationalFilteredNilmanifold.unitBoundedPiNiltest_eval, Fintype.prod_bool]
    change _ = star (T.eval (fun _ => (n.val : ℤ))) *
      (G.test.raiseStep hraise).eval (fun _ => (n.val : ℤ))
    rw [hTeval, RationalFilteredNilmanifold.Niltest.raiseStep_eval, G.eval n]
    rfl
  change Nonempty (NativeCyclicModel (d + 3) N ((p + C) ^ C) _)
  simpa only [hdegree] using H

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
