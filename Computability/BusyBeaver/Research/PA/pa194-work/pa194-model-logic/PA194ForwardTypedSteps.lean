import PA194ForwardAligned
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194ForwardTyped
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher
open M6.PA.RelationalSource
open Ordinal (Term Formula)
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem quote_add {n : Nat} (a b : SourceTerm n) :
    (⌜PA194PAeq.add a b⌝ : V) = ^func (2 : V) 2 (?[⌜a⌝,⌜b⌝] : V) := by
  simp [PA194PAeq.add,SemitermVec.val,Semiterm.quote_def]
  constructor
  · change ((2 : Nat) : V) = 2; simp
  · constructor <;> rfl
theorem quote_mul {n : Nat} (a b : SourceTerm n) :
    (⌜PA194PAeq.mul a b⌝ : V) = ^func (2 : V) 3 (?[⌜a⌝,⌜b⌝] : V) := by
  simp [PA194PAeq.mul,SemitermVec.val,Semiterm.quote_def]
  constructor
  · change ((3 : Nat) : V) = 3; simp
  · constructor <;> rfl

theorem bound_value_quote {n m : Nat} (i : Fin n) (b : Fin n → Term m) (f : Nat → Term m) (z : Term m)
    (param : V) (h : Aligned param b f z) :
    translate param (⌜(.bvar i : SourceTerm n)⌝ : V) = ⌜value (.bvar i) b f z⌝ := by
  have hi : (⌜(.bvar i : SourceTerm n)⌝ : V) = ^#(i.val : V) := by simp [Semiterm.quote_def]
  rw [hi,translate_bound,h.2.2.2,h.2.1 i]
  exact variableValue_quote z (b i)

theorem free_value_quote {n m : Nat} (i : Nat) (b : Fin n → Term m) (f : Nat → Term m) (z : Term m)
    (param : V) (h : Aligned param b f z) (hi : (i : V) < len (nth param 1)) :
    translate param (⌜(.fvar i : SourceTerm n)⌝ : V) = ⌜value (.fvar i) b f z⌝ := by
  have he : (⌜(.fvar i : SourceTerm n)⌝ : V) = ^&(i : V) := by simp [Semiterm.quote_def]
  rw [he,translate_free,h.2.2.2,h.2.2.1 i hi]
  exact variableValue_quote z (f i)

theorem zero_value_quote {n m : Nat} (b : Fin n → Term m) (f : Nat → Term m) (z : Term m)
    (param : V) (h : Aligned param b f z) :
    translate param (⌜(PA194PAeq.zero : SourceTerm n)⌝ : V) = ⌜value PA194PAeq.zero b f z⌝ := by
  rw [PA194PAeq.quote_zero,translate_zero,h.2.2.2]
  exact zeroValue_quote z

theorem quote_term_valid {n : Nat} (a : SourceTerm n) : IsUTerm PA194PAeq.language (⌜a⌝ : V) := by
  simpa [Semiterm.quote_def] using (⌜a⌝ : Bootstrapping.Semiterm V PA194PAeq.language n).isSemiterm.isUTerm

theorem succ_value_quote {n m : Nat} (a : SourceTerm n) (b : Fin n → Term m) (f : Nat → Term m) (z : Term m)
    (param : V) (h : Aligned param b f z)
    (hc : translate (childParameters param) (⌜a⌝ : V) = ⌜value a (shiftEnv b) (shiftEnv f) (.bvar 0)⌝) :
    translate param (⌜PA194PAeq.succ a⌝ : V) = ⌜value (PA194PAeq.succ a) b f z⌝ := by
  rw [PA194PAeq.quote_successor,translate_succ param _ (quote_term_valid a),hc,h.2.2.2,successorValue_quote]
  rfl

theorem addition_value_quote {n m : Nat} (a c : SourceTerm n) (b : Fin n → Term m) (f : Nat → Term m) (z : Term m)
    (param : V) (h : Aligned param b f z)
    (hl : translate (binaryParameters param 1) (⌜a⌝ : V) = ⌜value a (shiftEnv (shiftEnv b)) (shiftEnv (shiftEnv f)) (.bvar 1)⌝)
    (hr : translate (binaryParameters param 0) (⌜c⌝ : V) = ⌜value c (shiftEnv (shiftEnv b)) (shiftEnv (shiftEnv f)) (.bvar 0)⌝) :
    translate param (⌜PA194PAeq.add a c⌝ : V) = ⌜value (PA194PAeq.add a c) b f z⌝ := by
  rw [quote_add,translate_add param _ _ (quote_term_valid a) (quote_term_valid c),hl,hr,h.2.2.2,additionValue_quote]
  rfl

theorem multiplication_value_quote {n m : Nat} (a c : SourceTerm n) (b : Fin n → Term m) (f : Nat → Term m) (z : Term m)
    (param : V) (h : Aligned param b f z)
    (hl : translate (binaryParameters param 1) (⌜a⌝ : V) = ⌜value a (shiftEnv (shiftEnv b)) (shiftEnv (shiftEnv f)) (.bvar 1)⌝)
    (hr : translate (binaryParameters param 0) (⌜c⌝ : V) = ⌜value c (shiftEnv (shiftEnv b)) (shiftEnv (shiftEnv f)) (.bvar 0)⌝) :
    translate param (⌜PA194PAeq.mul a c⌝ : V) = ⌜value (PA194PAeq.mul a c) b f z⌝ := by
  rw [quote_mul,translate_mul param _ _ (quote_term_valid a) (quote_term_valid c),hl,hr,h.2.2.2,multiplicationValue_quote]
  rfl
#print axioms succ_value_quote
#print axioms addition_value_quote
#print axioms multiplication_value_quote
#print axioms quote_add
#print axioms quote_mul
#print axioms bound_value_quote
#print axioms free_value_quote
#print axioms zero_value_quote
end generic
end PA194ForwardTyped
