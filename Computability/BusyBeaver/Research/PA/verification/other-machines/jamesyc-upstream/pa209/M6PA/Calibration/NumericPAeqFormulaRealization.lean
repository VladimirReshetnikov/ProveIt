module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaRealizationAtoms
public import M6PA.Calibration.NumericPAeqFormulaRealizationNegativeAtom
public import M6PA.Calibration.NumericPAeqFormulaRealizationConstants
public import M6PA.Calibration.NumericPAeqFormulaRealizationQuantifiers
public import M6PA.Calibration.NumericPAeqFormulaRealizationInvariant
@[expose] public section

/-! Full-PA original-formula rank induction. The entire finite domain and actual
substitution-value guard remains the antecedent of the supplied certificate. -/
namespace M6.PA.NumericPAeqFormulaRealization
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCheckerBlueprint
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
private theorem formula_step (p:V) (ih:∀q<p,FormulaSupply (V:=V) q):FormulaSupply (V:=V) p := by
  intro s r b f a w h native lo z hc
  rcases IsSemiformula.case_iff.mp h.2.2.2.1 with
    ⟨k,fn,ts,hfn,ht,rfl⟩|⟨k,fn,ts,hfn,ht,rfl⟩|rfl|rfl|
    ⟨p,q,hp,hq,rfl⟩|⟨p,q,hp,hq,rfl⟩|⟨p,hp,rfl⟩|⟨p,hp,rfl⟩
  · exact formula_rel_supply k fn ts s r b f a w h native lo z hc
  · exact formula_nrel_of_rel (formula_rel_supply k fn ts) s r b f a w h native lo z hc
  · exact formula_verum_supply s r b f a w h native lo z hc
  · exact formula_falsum_supply s r b f a w h native lo z hc
  · exact formula_and_step (ih p (lt_K!_left p q)) (ih q (lt_K!_right p q)) s r b f a w h native lo z hc
  · exact formula_or_step (ih p (lt_or_left p q)) (ih q (lt_or_right p q)) s r b f a w h native lo z hc
  · exact formula_all_step (ih p (lt_forall p)) s r b f a w h native lo z hc
  · exact formula_exs_step (ih p (lt_exists p)) s r b f a w h native lo z hc
attribute [local irreducible] formulaInvariant
theorem open_source_formula (p:V):FormulaSupply (V:=V) p := by
  let : InductionScheme ℒₒᵣ Set.univ ⪯ theory := Entailment.WeakerThan.ofSubset Set.subset_union_right
  have : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
    models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have hall : ∀k:V,∀p<k,FormulaSupply (V:=V) p := by
    refine InductionScheme.succ_induction (C:=Set.univ)
      (P:=fun k:V => ∀p<k,FormulaSupply (V:=V) p) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb formulaInvariant,by trivial,?_⟩
      intro k; simpa using (formula_invariant (V:=V) k).symm
    · intro p hp; exact False.elim (by simpa using hp)
    · intro k ih p hp
      rcases eq_or_lt_of_le (lt_succ_iff_le.mp hp) with he|hlt
      · subst p; exact formula_step k ih
      · exact ih p hlt
  exact hall (p+1) p (lt_add_one p)
theorem open_source_formula_realization_certificate {s r b f a w p:V}
    (h:FormulaEnvironment s r b f a w p) (native lo z:V)
    (hc:RelationalSource.Numeric.FormulaCovered 0 native lo z (formulaCode s r b f a w p)):
    ∃code,verifyValue code=RelationalSource.Numeric.translate (RelationalSource.Numeric.parameters 0 native lo z)
      (formulaCode s r b f a w p)+1 :=
  open_source_formula p s r b f a w h native lo z hc
#print axioms formula_step
#print axioms open_source_formula
#print axioms open_source_formula_realization_certificate
end M6.PA.NumericPAeqFormulaRealization

