module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaCoverage
@[expose] public section

/-! Finite quoted-environment agreement used by later standard calibration.
The numeric binder operations are justified independently for arbitrary models;
these lemmas merely identify their action on explicitly agreeing host terms. -/
namespace M6.PA.NumericPAeqFormula
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
open RelationalSource.Ordinal (Term Formula)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def BoundAgreement {s m : Nat} (param : V) (b : Fin s → Term m) : Prop :=
  ∀i : Fin s,nth (nth param 0) (i:Nat)=⌜b i⌝
def FreeAgreement {m : Nat} (param : V) (f : Nat → Term m) (limit : Nat) : Prop :=
  ∀i,i<limit→(i:V)<len (nth param 1) ∧ nth (nth param 1) (i:V)=⌜f i⌝

theorem quote_bShift_value {m : Nat} (t : Term m) :
    (⌜Rew.bShift t⌝ : V)=termBShift language ⌜t⌝ := by
  simp [FFL.FirstOrder.Semiterm.quote_def]

theorem binder_bound_agreement {s m : Nat} {param : V} (b : Fin s → Term m)
    (h : ParametersValid (s:V) (m:V) param) (hb : BoundAgreement param b) :
    BoundAgreement (binderParameters param) (ForwardRelational.bindEnv b) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [ForwardRelational.bindEnv,binderParameters_bound_zero]
  · have hi : (j:V)<(s:V) := by simpa using j.isLt
    simpa only [Fin.val_succ,Nat.cast_add,Nat.cast_one,ForwardRelational.bindEnv,
      Fin.cases_succ,ForwardRelational.shiftEnv,←quote_bShift_value,hb j]
      using binderParameters_bound_succ h hi

theorem binder_free_agreement {s m limit : Nat} {param : V} (f : Nat → Term m)
    (h : ParametersValid (s:V) (m:V) param) (hf : FreeAgreement param f limit) :
    FreeAgreement (binderParameters param) (ForwardRelational.shiftEnv f) limit := by
  intro i hi
  obtain ⟨hir,he⟩ := hf i hi
  refine ⟨?_,?_⟩
  · simpa [binderParameters,NumericPAeqTerm.shiftTerms_length h.2] using hir
  · simpa only [ForwardRelational.shiftEnv,he,←quote_bShift_value]
      using binderParameters_free_nth h hir

theorem equality_bound_agreement {s m : Nat} {param index : V} (b : Fin s → Term m)
    (h : ParametersValid (s:V) (m:V) param) (hb : BoundAgreement param b) :
    BoundAgreement (equalityTermParameters param index)
      (ForwardRelational.shiftEnv (ForwardRelational.shiftEnv b)) := by
  intro i
  have hi : (i:V)<(s:V) := by simpa using i.isLt
  simpa only [ForwardRelational.shiftEnv,hb i,←quote_bShift_value]
    using equalityTermParameters_bound_nth (index := index) h hi

theorem equality_free_agreement {s m limit : Nat} {param index : V} (f : Nat → Term m)
    (h : ParametersValid (s:V) (m:V) param) (hf : FreeAgreement param f limit) :
    FreeAgreement (equalityTermParameters param index)
      (ForwardRelational.shiftEnv (ForwardRelational.shiftEnv f)) limit := by
  intro i hi
  obtain ⟨hir,he⟩ := hf i hi
  refine ⟨?_,?_⟩
  · simpa [equalityTermParameters,NumericPAeqTerm.shiftTerms_length h.2,
      NumericPAeqTerm.shiftTerms_length (NumericPAeqTerm.shiftTerms_isSemitermVec h.2)] using hir
  · simpa only [ForwardRelational.shiftEnv,he,←quote_bShift_value]
      using equalityTermParameters_free_nth (index := index) h hir

#print axioms equality_bound_agreement
#print axioms equality_free_agreement
#print axioms quote_bShift_value
#print axioms binder_bound_agreement
#print axioms binder_free_agreement
end M6.PA.NumericPAeqFormula
