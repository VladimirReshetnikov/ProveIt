module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateClosedAgreement
@[expose] public section
namespace M6.PA.RelationalPredicateTemplate
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language
set_option backward.isDefEq.respectTransparency false

theorem closed_atomValue_lift {s k : Nat} (r : RelationalSource.Relation k)
    (ts : Fin k → Semiterm L Nat s) {P b f : V}
    (hb : IdentityBound s b) (hc : ∀j i,¬(ts j).FVar? i) :
    atomValue (injection.rel r) (fun i => liftTerm (ts i)) P b f=
      (⌜FFL.FirstOrder.Semiformula.rel r ts⌝ : V) := by
  cases r <;>
    simp [atomValue,closed_termValue_lift _ hb (hc _),injection,
      FFL.FirstOrder.Semiformula.quote_rel,quote_rel_def,SemitermVec.val,
      FFL.FirstOrder.Semiterm.quote_def,Matrix.vecHead,Matrix.vecTail]
  · change (0:V)=(0:Nat)
    simp
  · change (1:V)=(1:Nat)
    simp

theorem closed_formulaValue_lift {s : Nat} (p : Semiformula L Nat s) {P b f : V}
    (h : EnvironmentsValid (s:V) (s:V) b f) (hb : IdentityBound s b)
    (hc : ∀i,¬p.FVar? i) :
    formulaValue (liftFormula p) P b f=(⌜p⌝ : V) := by
  induction p generalizing b f with
  | verum => rfl
  | falsum => rfl
  | rel r ts =>
    exact closed_atomValue_lift r ts hb (fun j i hi => hc i (by simpa using Exists.intro j hi))
  | nrel r ts =>
    change neg L (atomValue (injection.rel r) (fun i => liftTerm (ts i)) P b f)=_
    rw [closed_atomValue_lift r ts hb (fun j i hi => hc i (by simpa using Exists.intro j hi))]
    simp [FFL.FirstOrder.Semiformula.quote_def]
  | and p q ihp ihq =>
    change qqAnd (formulaValue (liftFormula p) P b f) (formulaValue (liftFormula q) P b f)=_
    rw [ihp h hb (fun i hi => hc i ((FFL.FirstOrder.Semiformula.fvar?_and i p q).mpr (Or.inl hi))),
      ihq h hb (fun i hi => hc i ((FFL.FirstOrder.Semiformula.fvar?_and i p q).mpr (Or.inr hi)))]
    rfl
  | or p q ihp ihq =>
    change qqOr (formulaValue (liftFormula p) P b f) (formulaValue (liftFormula q) P b f)=_
    rw [ihp h hb (fun i hi => hc i ((FFL.FirstOrder.Semiformula.fvar?_or i p q).mpr (Or.inl hi))),
      ihq h hb (fun i hi => hc i ((FFL.FirstOrder.Semiformula.fvar?_or i p q).mpr (Or.inr hi)))]
    rfl
  | all p ih =>
    change qqAll (formulaValue (liftFormula p) P (bindBound b) (bindFree f))=_
    rw [ih (by simpa only [Nat.cast_add,Nat.cast_one] using bindEnvironments_valid h)
      (identityBound_bind h.1 hb) (fun i hi => hc i hi)]
    rfl
  | exs p ih =>
    change qqExs (formulaValue (liftFormula p) P (bindBound b) (bindFree f))=_
    rw [ih (by simpa only [Nat.cast_add,Nat.cast_one] using bindEnvironments_valid h)
      (identityBound_bind h.1 hb) (fun i hi => hc i hi)]
    rfl

theorem formulaValue_closed (p : RelationalSource.ND.Form) (hc : p.freeVariables=∅)
    (P : V) {f : V} (hf : IsSemitermVec L (len f) 0 f) :
    formulaValue (liftFormula p) P 0 f=(⌜p⌝ : V) :=
  closed_formulaValue_lift p ⟨by simp,hf⟩ (fun i => Fin.elim0 i)
    (by intro i hi; simp [Semiformula.FVar?,hc] at hi)

#print axioms closed_atomValue_lift
#print axioms closed_formulaValue_lift
#print axioms formulaValue_closed
end M6.PA.RelationalPredicateTemplate
