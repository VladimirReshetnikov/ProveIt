module
public import M6PA.Theory
public import M6PA.Scheduler.ActualCheckerBlueprint
public import M6PA.Scheduler.ActualCompilerLeafSoundness
public import M6PA.Scheduler.SourceCantorInjectiveInternal
@[expose] public section

/-! All-model locality of the exact V1 verifier. This is not yet a constructor
closure theorem: fuel extension and numeric parent construction are separate. -/
namespace M6.PA.ActualCertificateConstructors
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open SourceCantorInternal ActualCheckExpression ActualRuleExpression
open ActualCheckerBlueprint

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- V1 rules consult only child indices bounded by their payload. -/
theorem rule_locality (x y tag payload : V)
    (h : ∀ i ≤ payload, nth x i = nth y i) :
    ruleValue x tag payload = ruleValue y tag payload := by
  have hb : decodeLeft (decodeRight payload) ≤ payload :=
    le_trans (decodeValue_bounds _).1 (decodeValue_bounds _).2
  have hc : decodeLeft (decodeRight (decodeRight payload)) ≤ payload :=
    le_trans (decodeValue_bounds _).1
      (le_trans (decodeValue_bounds _).2 (decodeValue_bounds _).2)
  have eb := h _ hb
  have ec := h _ hc
  unfold ruleValue rule mp gen leaf1 leaf2 leaf3 leaf4 leaf5 leaf6 leaf7 leaf8 rawBundle
  expose_actual_rule_helpers
  simp only [ActualCheckExpression.eval, eb, ec]
  rfl

/-- Fuel zero rejects at every index, including outside its stored vector. -/
theorem table_zero_entry (bound i : V) : nth (tableValue 0 bound) i = 0 := by
  rw [table_zero]
  by_cases hi : i < bound+1
  · exact nth_repeatVec 0 _ hi
  · apply nth_lt_len
    simpa using le_of_not_gt hi

/-- Out-of-range indices are rejection, not a successful formula-zero result. -/
theorem table_outside (fuel bound i : V) (hi : bound+1 ≤ i) :
    nth (tableValue fuel bound) i = 0 := by
  by_cases hf : fuel=0
  · subst fuel
    exact table_zero_entry bound i
  · have he : fuel=(fuel-1)+1 :=
      (sub_add_self_of_le (one_le_of_zero_lt fuel (pos_of_ne_zero hf))).symm
    rw [he,table_succ]
    apply nth_lt_len
    simpa [ActualCheckerRows.rows_length] using hi

/-- Explicit arithmetic invariant for table-bound independence. -/
noncomputable def localityFormula : ArithmeticSemisentence 1 :=
  “fuel. ∀ b c i, i ≤ b ∧ i ≤ c →
    ∃ x y u v, !tableGraph x fuel b ∧ !tableGraph y fuel c ∧
      !nthDef u x i ∧ !nthDef v y i ∧ u = v”

theorem locality_formula (fuel : V) :
    localityFormula.Evalb ![fuel] ↔
      ∀ b c i : V, i ≤ b ∧ i ≤ c →
        nth (tableValue fuel b) i = nth (tableValue fuel c) i := by
  simp [localityFormula,table_graph]

section Peano
variable [V↓[ℒₒᵣ] ⊧* theory]

/-- Equality is uniform in nonstandard fuel, bounds, and tree indices. -/
theorem table_locality (fuel b c i : V) (hib : i ≤ b) (hic : i ≤ c) :
    nth (tableValue fuel b) i = nth (tableValue fuel c) i := by
  let : InductionScheme ℒₒᵣ Set.univ ⪯ theory :=
    Entailment.WeakerThan.ofSubset Set.subset_union_right
  have : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
    models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have hall : ∀ f : V, ∀ b c i : V, i ≤ b ∧ i ≤ c →
      nth (tableValue f b) i = nth (tableValue f c) i := by
    refine InductionScheme.succ_induction (C := Set.univ)
      (P := fun f : V => ∀ b c i : V, i ≤ b ∧ i ≤ c →
        nth (tableValue f b) i = nth (tableValue f c) i) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb localityFormula,by trivial,?_⟩
      intro n
      simpa using (locality_formula (V := V) n).symm
    · intro b c i hi
      simp only [table_zero]
      rw [nth_repeatVec 0 (b+1) ((le_iff_lt_succ).mp hi.1),
        nth_repeatVec 0 (c+1) ((le_iff_lt_succ).mp hi.2)]
    · intro n ih b c i hi
      rw [table_succ,table_succ,
        ActualCheckerRows.rows_nth _ _ _ ((le_iff_lt_succ).mp hi.1),
        ActualCheckerRows.rows_nth _ _ _ ((le_iff_lt_succ).mp hi.2)]
      apply rule_locality
      intro j hj
      have hji : j ≤ i := le_trans hj (decodeValue_bounds i).2
      exact ih b c j ⟨le_trans hji hi.1,le_trans hji hi.2⟩
  exact hall fuel b c i ⟨hib,hic⟩
end Peano

#print axioms table_zero_entry
#print axioms table_outside
#print axioms rule_locality
#print axioms locality_formula
#print axioms table_locality
end M6.PA.ActualCertificateConstructors
