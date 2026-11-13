module
public import M6PA.Theory
public import M6PA.Calibration.ActualCertificateConstructorsMonotone
@[expose] public section

/-! Arbitrary model-length extension of successful V1 checker fuel, with an
explicit arithmetic induction invariant and exact table-bound transport. -/
namespace M6.PA.ActualCertificateConstructors
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open SourceCantorInternal ActualCheckerBlueprint

noncomputable def fuelExtensionFormula : ArithmeticSemisentence 1 :=
  “delta. ∀ f b i, ∃ x y u v,
    !tableGraph x f b ∧ !tableGraph y (f+delta) b ∧
    !nthDef u x i ∧ !nthDef v y i ∧ (u ≠ 0 → v=u)”

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem fuelExtension_formula (delta : V) :
    fuelExtensionFormula.Evalb ![delta] ↔ ∀ f b i : V,
      nth (tableValue f b) i ≠ 0 →
      nth (tableValue (f+delta) b) i = nth (tableValue f b) i := by
  simp [fuelExtensionFormula,table_graph]

section Peano
variable [V↓[ℒₒᵣ] ⊧* theory]

theorem table_fuel_add (fuel delta bound i : V)
    (h : nth (tableValue fuel bound) i ≠ 0) :
    nth (tableValue (fuel+delta) bound) i = nth (tableValue fuel bound) i := by
  let : InductionScheme ℒₒᵣ Set.univ ⪯ theory :=
    Entailment.WeakerThan.ofSubset Set.subset_union_right
  have : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
    models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have hall : ∀ delta : V, ∀ f b i : V, nth (tableValue f b) i ≠ 0 →
      nth (tableValue (f+delta) b) i = nth (tableValue f b) i := by
    refine InductionScheme.succ_induction (C := Set.univ)
      (P := fun delta : V => ∀ f b i : V, nth (tableValue f b) i ≠ 0 →
        nth (tableValue (f+delta) b) i = nth (tableValue f b) i) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb fuelExtensionFormula,by trivial,?_⟩
      intro n
      simpa using (fuelExtension_formula (V := V) n).symm
    · intro f b i _
      simp
    · intro d ih f b i hi
      have he := ih f b i hi
      rw [← add_assoc,table_fuel_step _ _ _ (by rw [he]; exact hi),he]
  exact hall delta fuel bound i h

/-- Accepted outputs persist when both fuel and table bound are enlarged.
The output remains `a+1`; in particular `a=0` is preserved, not rejected. -/
theorem table_transport (fuel delta oldBound newBound i a : V)
    (hiOld : i ≤ oldBound) (hiNew : i ≤ newBound)
    (h : nth (tableValue fuel oldBound) i = a+1) :
    nth (tableValue (fuel+delta) newBound) i = a+1 := by
  have hn : nth (tableValue fuel oldBound) i ≠ 0 := by
    rw [h]
    exact ne_of_gt (lt_of_le_of_lt (by simp : (0:V) ≤ a) (lt_add_one a))
  rw [table_locality (fuel+delta) newBound oldBound i hiNew hiOld,
    table_fuel_add fuel delta oldBound i hn,h]
end Peano

#print axioms fuelExtension_formula
#print axioms table_fuel_add
#print axioms table_transport
end M6.PA.ActualCertificateConstructors
