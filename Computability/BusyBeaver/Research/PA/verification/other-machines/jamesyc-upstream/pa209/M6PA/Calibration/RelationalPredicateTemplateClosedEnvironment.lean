module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateFormula
@[expose] public section

/-! A fixed template with no source free variables does not inspect its source
free environment. The unary hole may still contain arbitrary target free
parameters: it is kept unchanged on both sides, including beneath binders.
No representation of model-valued vectors by host functions is assumed. -/
namespace M6.PA.RelationalPredicateTemplate
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem closed_term_free_environment {s : Nat} (t : Term s)
    (hc : ∀i,¬t.FVar? i) (b f g : V) :
    termValue t b f=termValue t b g := by
  cases t with
  | bvar i => rfl
  | fvar i => exact (hc i (by simp)).elim
  | func fn _ => nomatch fn

theorem closed_atom_free_environment {s k : Nat} (r : Relation k)
    (ts : Fin k → Term s) (hc : ∀j i,¬(ts j).FVar? i) (P b f g : V) :
    atomValue r ts P b f=atomValue r ts P b g := by
  cases r <;> simp only [atomValue,closed_term_free_environment _ (hc _) b f g]

theorem closed_formula_free_environment {s : Nat} (p : Formula s)
    (hc : ∀i,¬p.FVar? i) (P b f g : V) :
    formulaValue p P b f=formulaValue p P b g := by
  induction p generalizing b f g with
  | verum => rfl
  | falsum => rfl
  | rel r ts =>
    exact closed_atom_free_environment r ts
      (fun j i hi => hc i (by simpa using Exists.intro j hi)) P b f g
  | nrel r ts =>
    simp only [formulaValue,closed_atom_free_environment r ts
      (fun j i hi => hc i (by simpa using Exists.intro j hi)) P b f g]
  | and p q ihp ihq =>
    simp only [formulaValue,ihp (fun i hi => hc i
      ((FFL.FirstOrder.Semiformula.fvar?_and i p q).mpr (Or.inl hi))) b f g,
      ihq (fun i hi => hc i
      ((FFL.FirstOrder.Semiformula.fvar?_and i p q).mpr (Or.inr hi))) b f g]
  | or p q ihp ihq =>
    simp only [formulaValue,ihp (fun i hi => hc i
      ((FFL.FirstOrder.Semiformula.fvar?_or i p q).mpr (Or.inl hi))) b f g,
      ihq (fun i hi => hc i
      ((FFL.FirstOrder.Semiformula.fvar?_or i p q).mpr (Or.inr hi))) b f g]
  | all p ih =>
    simp only [formulaValue,ih (fun i hi => hc i hi) (bindBound b) (bindFree f) (bindFree g)]
  | exs p ih =>
    simp only [formulaValue,ih (fun i hi => hc i hi) (bindBound b) (bindFree f) (bindFree g)]

theorem formulaValue_closed_environment {s : Nat} (p : Formula s)
    (hc : p.freeVariables=∅) (P b f g : V) :
    formulaValue p P b f=formulaValue p P b g :=
  closed_formula_free_environment p (by intro i hi; simp [Semiformula.FVar?,hc] at hi) P b f g

#print axioms closed_term_free_environment
#print axioms closed_atom_free_environment
#print axioms closed_formula_free_environment
#print axioms formulaValue_closed_environment
end M6.PA.RelationalPredicateTemplate
