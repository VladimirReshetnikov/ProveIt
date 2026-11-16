module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqTermValidity
public import M6PA.Calibration.NumericPAeqFormulaAgreement
@[expose] public section

/-! Explicit finite support agreement for quotation calibration. No infinite
host function is asserted to have a finite numeric representation. -/
namespace M6.PA.NumericPAeqTerm
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
open RelationalSource.Ordinal (Term Formula)
open NumericPAeqFormula (BoundAgreement quote_bShift_value)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def TermFreeAgreement {s m : Nat} (param : V) (t : ForwardRelational.SourceTerm s) (f : Nat → Term m) : Prop :=
  ∀i,t.FVar? i→(i:V)<len (nth param 1) ∧ nth (nth param 1) (i:V)=⌜f i⌝

theorem child_bound_agreement {s m : Nat} {param : V} (b : Fin s → Term m)
    (h : ParametersValid (s:V) (m:V) param) (hb : BoundAgreement param b) :
    BoundAgreement (childParameters param) (ForwardRelational.shiftEnv b) := by
  intro i
  have hi : (i:V)<(s:V) := by simpa using i.isLt
  simpa only [ForwardRelational.shiftEnv,hb i,←quote_bShift_value]
    using childParameters_bound_nth h hi

theorem child_free_agreement {s m : Nat} {param : V} (t : ForwardRelational.SourceTerm s) (f : Nat → Term m)
    (h : ParametersValid (s:V) (m:V) param) (hf : TermFreeAgreement param t f) :
    TermFreeAgreement (childParameters param) t (ForwardRelational.shiftEnv f) := by
  intro i hi
  obtain ⟨hir,he⟩ := hf i hi
  refine ⟨?_,?_⟩
  · simpa [childParameters,shiftTerms_length h.2.1] using hir
  · simpa only [ForwardRelational.shiftEnv,he,←quote_bShift_value]
      using childParameters_free_nth h hir

theorem binary_bound_agreement {s m : Nat} {param index : V} (b : Fin s → Term m)
    (h : ParametersValid (s:V) (m:V) param) (hb : BoundAgreement param b) :
    BoundAgreement (binaryParameters param index) (ForwardRelational.shiftEnv (ForwardRelational.shiftEnv b)) := by
  intro i
  have hi : (i:V)<(s:V) := by simpa using i.isLt
  simpa only [ForwardRelational.shiftEnv,hb i,←quote_bShift_value]
    using binaryParameters_bound_nth (i:=index) h hi

theorem binary_free_agreement {s m : Nat} {param index : V}
    (t : ForwardRelational.SourceTerm s) (f : Nat → Term m)
    (h : ParametersValid (s:V) (m:V) param) (hf : TermFreeAgreement param t f) :
    TermFreeAgreement (binaryParameters param index) t (ForwardRelational.shiftEnv (ForwardRelational.shiftEnv f)) := by
  intro i hi
  obtain ⟨hir,he⟩ := hf i hi
  refine ⟨?_,?_⟩
  · simpa [binaryParameters,shiftTerms_length (shiftTerms_isSemitermVec h.2.1)] using hir
  · simp only [binaryParameters,parameters_free]
    rw [shiftTerms_nth (shiftTerms_isSemitermVec h.2.1) hir,shiftTerms_nth h.2.1 hir,he]
    simp [ForwardRelational.shiftEnv,quote_bShift_value]

theorem termFreeAgreement_child {s m k : Nat} {param : V} (fn : Presentation.Func k)
    (ts : Fin k → ForwardRelational.SourceTerm s) (f : Nat → Term m)
    (hf : TermFreeAgreement param (.func fn ts) f) (j : Fin k) : TermFreeAgreement param (ts j) f := by
  intro i hi
  exact hf i (by simpa only [Semiterm.fvar?_func] using ⟨j,hi⟩)

#print axioms child_bound_agreement
#print axioms child_free_agreement
#print axioms binary_bound_agreement
#print axioms binary_free_agreement
#print axioms termFreeAgreement_child
end M6.PA.NumericPAeqTerm
