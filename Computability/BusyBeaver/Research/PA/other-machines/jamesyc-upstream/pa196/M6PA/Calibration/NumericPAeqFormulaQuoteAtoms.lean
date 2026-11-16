module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaAgreement
public import M6PA.Calibration.NumericPAeqFormulaRecursion
public import M6PA.Calibration.NumericPAeqTermCalibration
@[expose] public section
namespace M6.PA.NumericPAeqFormula
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource.Ordinal (Term Formula)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

def FormulaFreeAgreement {s m : Nat} (param : V) (p : ForwardRelational.SourceFormula s)
    (f : Nat → Term m) : Prop :=
  ∀i,p.FVar? i→(i:V)<len (nth param 1) ∧ nth (nth param 1) (i:V)=⌜f i⌝

theorem formulaFreeAgreement_binder {s m k : Nat} {param : V}
    (p : ForwardRelational.SourceFormula k) (f : Nat → Term m)
    (h : ParametersValid (s:V) (m:V) param) (hf : FormulaFreeAgreement param p f) :
    FormulaFreeAgreement (binderParameters param) p (ForwardRelational.shiftEnv f) := by
  intro i hi
  obtain ⟨hir,he⟩ := hf i hi
  refine ⟨?_,?_⟩
  · simpa [binderParameters,NumericPAeqTerm.shiftTerms_length h.2] using hir
  · simpa only [ForwardRelational.shiftEnv,he,←quote_bShift_value]
      using binderParameters_free_nth h hir

theorem equality_termFreeAgreement {s m : Nat} {param index : V}
    (t : ForwardRelational.SourceTerm s) (f : Nat → Term m)
    (h : ParametersValid (s:V) (m:V) param) (hf : NumericPAeqTerm.TermFreeAgreement param t f) :
    NumericPAeqTerm.TermFreeAgreement (equalityTermParameters param index) t
      (ForwardRelational.shiftEnv (ForwardRelational.shiftEnv f)) := by
  intro i hi
  obtain ⟨hir,he⟩ := hf i hi
  refine ⟨?_,?_⟩
  · simpa [equalityTermParameters,NumericPAeqTerm.shiftTerms_length h.2,
      NumericPAeqTerm.shiftTerms_length (NumericPAeqTerm.shiftTerms_isSemitermVec h.2)] using hir
  · simpa only [ForwardRelational.shiftEnv,he,←quote_bShift_value]
      using equalityTermParameters_free_nth (index := index) h hir

noncomputable def quoteTerms {s k : Nat} (ts : Fin k → ForwardRelational.SourceTerm s) : V :=
  SemitermVec.val (fun i => (⌜ts i⌝ : Bootstrapping.Semiterm V Presentation.language s))
theorem quoteTerms_nth {s k : Nat} (ts : Fin k → ForwardRelational.SourceTerm s) (i : Fin k) :
    nth (quoteTerms (V:=V) ts) (i:Nat)=(⌜ts i⌝ : V) := by
  simpa [quoteTerms,FFL.FirstOrder.Semiterm.quote_def] using!
    (SemitermVec.val_nth_eq (fun j => (⌜ts j⌝ : Bootstrapping.Semiterm V Presentation.language s)) i)

theorem atomCode_quote {s m : Nat} (ts : Fin 2 → ForwardRelational.SourceTerm s)
    (param : V) (b : Fin s → Term m) (f : Nat → Term m)
    (h : ParametersValid (s:V) (m:V) param) (hb : BoundAgreement param b)
    (hf : ∀j,NumericPAeqTerm.TermFreeAgreement param (ts j) f) :
    atomCode param 2 0 (quoteTerms ts)=⌜ForwardRelational.equal (ts 0) (ts 1) b f⌝ := by
  have h0 := quoteTerms_nth (V:=V) ts (0:Fin 2)
  have h1 := quoteTerms_nth (V:=V) ts (1:Fin 2)
  simp only [Fin.val_zero,Fin.val_one,Nat.cast_zero,Nat.cast_one] at h0 h1
  unfold atomCode
  rw [h0,h1]
  have hl := NumericPAeqTerm.valueSyntax_quote (ts 0) (equalityTermParameters param 1)
    (ForwardRelational.shiftEnv (ForwardRelational.shiftEnv b))
    (ForwardRelational.shiftEnv (ForwardRelational.shiftEnv f)) (.bvar 1)
    (by simpa [Nat.cast_add,Arithmetic.add_assoc,one_add_one_eq_two] using equalityTermParameters_valid h (show (1:V)<2 by simp))
    (equality_bound_agreement b h hb)
    (equality_termFreeAgreement _ f h (hf 0)) (by simp)
  have hr := NumericPAeqTerm.valueSyntax_quote (ts 1) (equalityTermParameters param 0)
    (ForwardRelational.shiftEnv (ForwardRelational.shiftEnv b))
    (ForwardRelational.shiftEnv (ForwardRelational.shiftEnv f)) (.bvar 0)
    (by simpa [Nat.cast_add,Arithmetic.add_assoc,one_add_one_eq_two] using equalityTermParameters_valid h (show (0:V)<2 by simp))
    (equality_bound_agreement b h hb)
    (equality_termFreeAgreement _ f h (hf 1)) (by simp)
  rw [hl,hr,equalityCode_quote]
  rfl

#print axioms formulaFreeAgreement_binder
#print axioms equality_termFreeAgreement
#print axioms quoteTerms_nth
#print axioms atomCode_quote
end M6.PA.NumericPAeqFormula
