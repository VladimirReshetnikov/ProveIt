import OAI.Combinatorics.Progressions.Estimates.QuadraticCyclicIntegration

namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem exists_quadratic_primitive_niltest_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p,
      ∀ i : Fin W.outputDim, ∀ χ : AddChar (ZMod N) ℂ,
      (fun n : ZMod N => star (W.eval i (fun _ => (n.val : ℤ))) * χ n) ∈
        nativeCyclicFunctions 2 N ((p + C) ^ C) := by
  obtain ⟨A, _, hproduct⟩ := exists_productNiltestBudget_bound
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((Polynomial.X + 216 + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp W i χ
  obtain ⟨T, hTnorm, hT, hTeval⟩ := W.exists_quadratic_diagonal_niltest i
  obtain ⟨U, hUnorm, hU, hUeval⟩ := exists_cyclic_character_niltest χ
  let hdegree : 1 ≤ 2 := by omega
  let r := p + 216
  have hr : 0 ≤ r := by dsimp [r]; linarith
  let K : Bool → Type := BoolLieFamily W.L (RationalTorus.Algebra 1)
  let dims : Bool → ℕ := fun b => Bool.rec 1 W.dim b
  let models : ∀ b, RationalFilteredNilmanifold (K b) 2 (dims b) := fun b => by
    cases b
    · exact (RationalTorus.nilmanifold 1).raiseStep hdegree
    · exact W.model
  let tests : ∀ b, (models b).Niltest (fun _ : Unit => 1) := fun b => by
    cases b
    · exact U.raiseStep hdegree
    · exact T.conjugate
  have htests : ∀ b, (tests b).ComplexityLE r := by
    intro b
    cases b
    · apply (U.raiseStep_complexity hdegree (by norm_num) hU).mono
      dsimp [raisedNiltestBudget, r]
      linarith
    · exact hT.mono (by dsimp [r]; linarith)
  have hcap : ∀ b, (tests b).normBound ≤ 1 := by
    intro b
    cases b
    · exact hUnorm
    · exact hTnorm.le
  have hcard : (Fintype.card Bool : ℝ) ≤ r := by
    simp only [Fintype.card_bool, Nat.cast_ofNat]
    dsimp [r]
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
    simpa [r, Polynomial.eval₂_pow] using hbudget p hp
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
    (U.raiseStep hdegree).eval (fun _ => (n.val : ℤ))
  rw [hTeval, RationalFilteredNilmanifold.Niltest.raiseStep_eval]
  change _ = star (W.eval i (fun _ => (n.val : ℤ))) * U.evalCyclic N (fun _ => n)
  rw [hUeval]

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
