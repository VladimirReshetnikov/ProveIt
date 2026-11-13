module
public import M6PA.Theory
public import M6PA.Calibration.ActualCertificateConstructorsLocality
@[expose] public section

/-! Positive-result fuel stability for the exact V1 verifier. Rejection zero
is not preserved; every nonzero result, including successful formula zero,
is preserved. Induction invariants are explicit first-order PA formulas. -/
namespace M6.PA.ActualCertificateConstructors
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open SourceCantorInternal ActualCheckExpression ActualRuleExpression
open ActualCheckerBlueprint
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Only successful child values need to be preserved. -/
theorem rule_preserves (x y tag payload : V)
    (h : ∀ i ≤ payload, nth x i ≠ 0 → nth y i = nth x i)
    (hx : ruleValue x tag payload ≠ 0) :
    ruleValue y tag payload = ruleValue x tag payload := by
  have hb : decodeLeft (decodeRight payload) ≤ payload :=
    le_trans (decodeValue_bounds _).1 (decodeValue_bounds _).2
  have hc : decodeLeft (decodeRight (decodeRight payload)) ≤ payload :=
    le_trans (decodeValue_bounds _).1
      (le_trans (decodeValue_bounds _).2 (decodeValue_bounds _).2)
  by_cases hm : nth x (decodeLeft (decodeRight payload)) = 0
  · by_cases ht : tag=0 ∨ tag=1
    · rcases ht with ht | ht
      all_goals
        unfold ruleValue rule mp gen at hx
        expose_actual_rule_helpers
        simp only [ActualCheckExpression.eval,Nat.cast_zero,Nat.cast_one,ht] at hx
        simp [hm] at hx
    · have ht0 : tag≠0 := fun he => ht (Or.inl he)
      have ht1 : tag≠1 := fun he => ht (Or.inr he)
      unfold ruleValue rule
      simp only [ActualCheckExpression.eval,Nat.cast_zero,Nat.cast_one,ht0,ht1,ite_false]
      unfold leaf1 leaf2 leaf3 leaf4 leaf5 leaf6 leaf7 leaf8 rawBundle
      expose_actual_rule_helpers
      rfl
  · have eb := h _ hb hm
    by_cases hj : nth x (decodeLeft (decodeRight (decodeRight payload))) = 0
    · by_cases ht : tag=0
      · unfold ruleValue rule mp at hx
        expose_actual_rule_helpers
        simp only [ActualCheckExpression.eval,Nat.cast_zero,Nat.cast_one,ht,ite_true] at hx
        simp [hm,hj] at hx
      · unfold ruleValue rule mp gen leaf1 leaf2 leaf3 leaf4 leaf5 leaf6 leaf7 leaf8 rawBundle
        expose_actual_rule_helpers
        simp only [ActualCheckExpression.eval,Nat.cast_zero,Nat.cast_one,ht,ite_false,eb]
    · have ec := h _ hc hj
      unfold ruleValue rule mp gen leaf1 leaf2 leaf3 leaf4 leaf5 leaf6 leaf7 leaf8 rawBundle
      expose_actual_rule_helpers
      simp only [ActualCheckExpression.eval,eb,ec]
      rfl

noncomputable def fuelStepFormula : ArithmeticSemisentence 1 :=
  “fuel. ∀ b i, ∃ x y u v,
    !tableGraph x fuel b ∧ !tableGraph y (fuel+1) b ∧
    !nthDef u x i ∧ !nthDef v y i ∧ (u ≠ 0 → v=u)”

theorem fuelStep_formula (fuel : V) :
    fuelStepFormula.Evalb ![fuel] ↔ ∀ b i : V,
      nth (tableValue fuel b) i ≠ 0 →
      nth (tableValue (fuel+1) b) i = nth (tableValue fuel b) i := by
  simp [fuelStepFormula,table_graph]

section Peano
variable [V↓[ℒₒᵣ] ⊧* theory]

theorem table_fuel_step (fuel bound i : V)
    (h : nth (tableValue fuel bound) i ≠ 0) :
    nth (tableValue (fuel+1) bound) i = nth (tableValue fuel bound) i := by
  let : InductionScheme ℒₒᵣ Set.univ ⪯ theory :=
    Entailment.WeakerThan.ofSubset Set.subset_union_right
  have : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
    models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have hall : ∀ f : V, ∀ b i : V, nth (tableValue f b) i ≠ 0 →
      nth (tableValue (f+1) b) i = nth (tableValue f b) i := by
    refine InductionScheme.succ_induction (C := Set.univ)
      (P := fun f : V => ∀ b i : V, nth (tableValue f b) i ≠ 0 →
        nth (tableValue (f+1) b) i = nth (tableValue f b) i) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb fuelStepFormula,by trivial,?_⟩
      intro n
      simpa using (fuelStep_formula (V := V) n).symm
    · intro b i hi
      exact False.elim (hi (table_zero_entry b i))
    · intro n ih b i hi
      have hib : i < b+1 := by
        by_contra hn
        exact hi (table_outside _ b i (le_of_not_gt hn))
      rw [table_succ,ActualCheckerRows.rows_nth _ _ _ hib] at hi
      rw [table_succ,ActualCheckerRows.rows_nth _ _ _ hib,
        table_succ,ActualCheckerRows.rows_nth _ _ _ hib]
      exact rule_preserves _ _ _ _ (fun j _ hj => by simpa only [table_succ] using ih b j hj) hi
  exact hall fuel bound i h
end Peano

#print axioms rule_preserves
#print axioms fuelStep_formula
#print axioms table_fuel_step
end M6.PA.ActualCertificateConstructors
