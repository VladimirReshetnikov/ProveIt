module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqTermAgreement
@[expose] public section

/-! Standard-syntax calibration of the independently total all-model numeric
term interpreter. Only explicitly agreeing finite environment entries are used. -/
namespace M6.PA.NumericPAeqTerm
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
open RelationalSource.Ordinal (Term Formula)
open NumericPAeqFormula (BoundAgreement)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

theorem quote_source_add {s : Nat} (u v : ForwardRelational.SourceTerm s) :
    (⌜Presentation.add u v⌝ : V)=qqFunc 2 2 (⌜u⌝∷(⌜v⌝∷0)) := by
  simp [Presentation.add,SemitermVec.val,quote_func_def]
  exact ⟨by rfl,rfl,rfl⟩
theorem quote_source_mul {s : Nat} (u v : ForwardRelational.SourceTerm s) :
    (⌜Presentation.mul u v⌝ : V)=qqFunc 2 3 (⌜u⌝∷(⌜v⌝∷0)) := by
  simp [Presentation.mul,SemitermVec.val,quote_func_def]
  exact ⟨by rfl,rfl,rfl⟩

theorem valueSyntax_quote {s : Nat} (t : ForwardRelational.SourceTerm s) :
    ∀{m : Nat} (param : V) (b : Fin s → Term m) (f : Nat → Term m) (z : Term m),
    ParametersValid (s:V) (m:V) param → BoundAgreement param b → TermFreeAgreement param t f →
    nth param 2=⌜z⌝ → valueSyntax param (⌜t⌝ : V)=⌜ForwardRelational.value t b f z⌝ := by
  induction t with
  | bvar i =>
    intro m param b f z hv hb hf hz
    rw [FFL.FirstOrder.Semiterm.quote_bvar,valueSyntax_bvar,hz,hb i]
    exact variableValue_bound_forward i b f z
  | fvar i =>
    intro m param b f z hv hb hf hz
    obtain ⟨_,he⟩ := hf i (by simp)
    rw [FFL.FirstOrder.Semiterm.quote_fvar,valueSyntax_fvar,hz,he]
    exact variableValue_free_forward i b f z
  | func fn ts ih =>
    intro m param b f z hv hb hf hz
    cases fn with
    | zero =>
      have hts : ts=Fin.elim0 := by funext i; exact Fin.elim0 i
      subst ts
      change valueSyntax param (⌜(Presentation.zero : ForwardRelational.SourceTerm s)⌝ : V)=_
      rw [Presentation.quote_zero,valueSyntax_zero,hz]
      exact zeroValue_forward b f z
    | succ =>
      have hts : ts=![ts 0] := by ext i; fin_cases i <;> rfl
      have hsrc : (FFL.FirstOrder.Semiterm.func Presentation.Func.succ ts) = Presentation.succ (ts 0) := by
        rw [hts]; rfl
      rw [hsrc,Presentation.quote_successor,valueSyntax_successor _ _ (by simp [FFL.FirstOrder.Semiterm.quote_def]),hz]
      have hi := ih 0 (childParameters param) (ForwardRelational.shiftEnv b)
        (ForwardRelational.shiftEnv f) (.bvar 0)
        (by simpa using childParameters_valid hv)
        (child_bound_agreement b hv hb)
        (child_free_agreement (ts 0) f hv (termFreeAgreement_child .succ ts f hf 0))
        (by simp [childParameters])
      rw [hi]
      exact successorValue_forward (ts 0) b f z
    | add =>
      have hts : ts=![ts 0,ts 1] := by ext i; fin_cases i <;> rfl
      have hsrc : (FFL.FirstOrder.Semiterm.func Presentation.Func.add ts) = Presentation.add (ts 0) (ts 1) := by
        rw [hts]; rfl
      rw [hsrc,quote_source_add,valueSyntax_addition _ _ _ (by simp [FFL.FirstOrder.Semiterm.quote_def]) (by simp [FFL.FirstOrder.Semiterm.quote_def]),hz]
      have hl := ih 0 (binaryParameters param 1) (ForwardRelational.shiftEnv (ForwardRelational.shiftEnv b))
        (ForwardRelational.shiftEnv (ForwardRelational.shiftEnv f)) (.bvar 1)
        (by simpa [Nat.cast_add,Arithmetic.add_assoc,one_add_one_eq_two] using binaryParameters_valid hv (show (1:V)<2 by simp))
        (binary_bound_agreement b hv hb)
        (binary_free_agreement (ts 0) f hv (termFreeAgreement_child .add ts f hf 0))
        (by simp [binaryParameters])
      have hr := ih 1 (binaryParameters param 0) (ForwardRelational.shiftEnv (ForwardRelational.shiftEnv b))
        (ForwardRelational.shiftEnv (ForwardRelational.shiftEnv f)) (.bvar 0)
        (by simpa [Nat.cast_add,Arithmetic.add_assoc,one_add_one_eq_two] using binaryParameters_valid hv (show (0:V)<2 by simp))
        (binary_bound_agreement b hv hb)
        (binary_free_agreement (ts 1) f hv (termFreeAgreement_child .add ts f hf 1))
        (by simp [binaryParameters])
      rw [hl,hr]
      exact additionValue_forward (ts 0) (ts 1) b f z
    | mul =>
      have hts : ts=![ts 0,ts 1] := by ext i; fin_cases i <;> rfl
      have hsrc : (FFL.FirstOrder.Semiterm.func Presentation.Func.mul ts) = Presentation.mul (ts 0) (ts 1) := by
        rw [hts]; rfl
      rw [hsrc,quote_source_mul,valueSyntax_multiplication _ _ _ (by simp [FFL.FirstOrder.Semiterm.quote_def]) (by simp [FFL.FirstOrder.Semiterm.quote_def]),hz]
      have hl := ih 0 (binaryParameters param 1) (ForwardRelational.shiftEnv (ForwardRelational.shiftEnv b))
        (ForwardRelational.shiftEnv (ForwardRelational.shiftEnv f)) (.bvar 1)
        (by simpa [Nat.cast_add,Arithmetic.add_assoc,one_add_one_eq_two] using binaryParameters_valid hv (show (1:V)<2 by simp))
        (binary_bound_agreement b hv hb)
        (binary_free_agreement (ts 0) f hv (termFreeAgreement_child .mul ts f hf 0))
        (by simp [binaryParameters])
      have hr := ih 1 (binaryParameters param 0) (ForwardRelational.shiftEnv (ForwardRelational.shiftEnv b))
        (ForwardRelational.shiftEnv (ForwardRelational.shiftEnv f)) (.bvar 0)
        (by simpa [Nat.cast_add,Arithmetic.add_assoc,one_add_one_eq_two] using binaryParameters_valid hv (show (0:V)<2 by simp))
        (binary_bound_agreement b hv hb)
        (binary_free_agreement (ts 1) f hv (termFreeAgreement_child .mul ts f hf 1))
        (by simp [binaryParameters])
      rw [hl,hr]
      exact multiplicationValue_forward (ts 0) (ts 1) b f z

#print axioms quote_source_add
#print axioms quote_source_mul
#print axioms valueSyntax_quote
end M6.PA.NumericPAeqTerm
