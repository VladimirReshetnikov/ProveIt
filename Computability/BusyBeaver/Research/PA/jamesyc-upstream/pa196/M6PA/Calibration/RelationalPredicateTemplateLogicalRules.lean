module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateSequent
@[expose] public section
namespace M6.PA.RelationalPredicateTemplate
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language
variable {T : Theory L} [T.Δ₁]
@[simp] theorem sequentValue_append_one (Γ : LK.Sequent sourceLanguage) (p : Formula 0) (P f : V) :
    sequentValue (Γ+⦃p⦄) P f=insert (formulaValue p P 0 f) (sequentValue Γ P f) := by
  apply mem_ext; intro x; simp [mem_sequentValue,or_comm,or_left_comm,or_assoc]
@[simp] theorem sequentValue_append_two (Γ : LK.Sequent sourceLanguage) (p q : Formula 0) (P f : V) :
    sequentValue (Γ+⦃p,q⦄) P f=insert (formulaValue p P 0 f) (insert (formulaValue q P 0 f) (sequentValue Γ P f)) := by
  apply mem_ext; intro x; simp [mem_sequentValue,or_comm,or_left_comm,or_assoc]

theorem template_and {Γ : LK.Sequent sourceLanguage} {p q : Formula 0} {P f : V}
    (hp : Derivable T (sequentValue (Γ+⦃p⦄) P f))
    (hq : Derivable T (sequentValue (Γ+⦃q⦄) P f)) :
    Derivable T (sequentValue (Γ+⦃p⋏q⦄) P f) := by
  simpa only [sequentValue_append_one,formulaValue] using
    Derivable.and (by simpa only [sequentValue_append_one] using hp)
      (by simpa only [sequentValue_append_one] using hq)

theorem template_or {Γ : LK.Sequent sourceLanguage} {p q : Formula 0} {P f : V}
    (hpq : Derivable T (sequentValue (Γ+⦃p,q⦄) P f)) :
    Derivable T (sequentValue (Γ+⦃p⋎q⦄) P f) := by
  simpa only [sequentValue_append_one,formulaValue] using
    Derivable.or (by simpa only [sequentValue_append_two] using hpq)

theorem template_contraction {Γ : LK.Sequent sourceLanguage} {p : Formula 0} {P f : V}
    (hp : Derivable T (sequentValue (Γ+⦃p,p⦄) P f)) :
    Derivable T (sequentValue (Γ+⦃p⦄) P f) := by
  apply Derivable.ofSetEq (s':=sequentValue (Γ+⦃p,p⦄) P f) ?_ hp
  intro x; simp [mem_sequentValue,or_comm,or_left_comm,or_assoc]

theorem template_weakening {Γ : LK.Sequent sourceLanguage} {p : Formula 0} {P f : V}
    (hp : IsFormula L (formulaValue p P 0 f))
    (hd : Derivable T (sequentValue Γ P f)) :
    Derivable T (sequentValue (Γ+⦃p⦄) P f) := by
  rw [sequentValue_append_one]
  exact Derivable.wk (by simp [hp,hd.isFormulaSet]) (by intro x hx; simp [hx]) hd

#print axioms template_and
#print axioms template_or
#print axioms template_contraction
#print axioms template_weakening
end M6.PA.RelationalPredicateTemplate
