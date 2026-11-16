import PA194PAeqClosureClosed
import PA194ForwardTermCorrect
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeqBind
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ForwardTyped
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
@[simp] theorem bindTermVec_nil (k : V) : bindTermVec k 0 0 = 0 := by
  simp [bindTermVec,termConstruction]
theorem bindTermVec_cons {k ar t v : V} (ht : IsUTerm PA194PAeq.language t)
    (hv : IsUTermVec PA194PAeq.language ar v) :
    bindTermVec k (ar+1) (t ∷ v) = bindTerm k t ∷ bindTermVec k ar v := by
  simpa [bindTermVec,bindTerm] using termConstruction.resultVec_cons PA194PAeq.language ![k] hv ht

theorem bindTerm_quote_fix {n : Nat} (t : SourceTerm n) :
    bindTerm (n : V) (⌜t⌝ : V) = (⌜(Rew.fix t : SourceTerm (n+1))⌝ : V) := by
  induction t with
  | bvar i => simp [Rew.fix_bvar]
  | fvar i =>
    cases i with
    | zero => simp [Rew.fix_fvar_zero,bindFree]
    | succ i => simp [Rew.fix_fvar_succ,bindFree]
  | func f ts ih =>
    cases f with
    | zero =>
      have he : (.func .zero ts : SourceTerm n) = PA194PAeq.zero := by congr 1; funext i; exact Fin.elim0 i
      rw [he,PA194PAeq.quote_zero]
      have hf : PA194PAeq.language.IsFunc (0 : V) 0 := by simp
      have hv : IsUTermVec PA194PAeq.language (0 : V) 0 := by simp
      rw [bindTerm_func hf hv,bindTermVec_nil]
      rfl
    | succ =>
      have he : (.func .succ ts : SourceTerm n) = PA194PAeq.succ (ts 0) := by congr 1; funext i; fin_cases i; rfl
      rw [he,PA194PAeq.quote_successor]
      have ht := quote_term_valid (V := V) (ts 0)
      have hf : PA194PAeq.language.IsFunc (1 : V) 1 := by simp
      have hv : IsUTermVec PA194PAeq.language (1 : V) (?[⌜ts 0⌝] : V) := by simp [ht]
      rw [bindTerm_func hf hv]
      have hvec : bindTermVec (n : V) 1 (?[⌜ts 0⌝] : V) = ?[bindTerm (n : V) ⌜ts 0⌝] := by
        simpa using (bindTermVec_cons (k := (n : V)) ht (show IsUTermVec PA194PAeq.language (0 : V) 0 by simp))
      rw [hvec,ih 0]
      simp [PA194PAeq.succ,Rew.func,PA194PAeq.quote_successor]
      constructor
      · change (1 : V) = ((1 : Nat) : V); simp
      · rfl
    | add =>
      have he : (.func .add ts : SourceTerm n) = PA194PAeq.add (ts 0) (ts 1) := by congr 1; funext i; fin_cases i <;> rfl
      rw [he,quote_add]
      have h0 := quote_term_valid (V := V) (ts 0)
      have h1 := quote_term_valid (V := V) (ts 1)
      have hf : PA194PAeq.language.IsFunc (2 : V) 2 := by simp
      have hv : IsUTermVec PA194PAeq.language (2 : V) (?[⌜ts 0⌝,⌜ts 1⌝] : V) := by simp [h0,h1]
      rw [bindTerm_func hf hv]
      have hvec : bindTermVec (n : V) 2 (?[⌜ts 0⌝,⌜ts 1⌝] : V) = ?[bindTerm (n : V) ⌜ts 0⌝,bindTerm (n : V) ⌜ts 1⌝] := by
        have hv1 : IsUTermVec PA194PAeq.language (1 : V) (?[⌜ts 1⌝] : V) := by simp [h1]
        have hh := bindTermVec_cons (k := (n : V)) h0 hv1
        have hh' := bindTermVec_cons (k := (n : V)) h1 (show IsUTermVec PA194PAeq.language (0 : V) 0 by simp)
        have htail : bindTermVec (n : V) 1 (?[⌜ts 1⌝] : V) = ?[bindTerm (n : V) ⌜ts 1⌝] := by simpa using hh'
        simpa [htail,one_add_one_eq_two] using hh
      rw [hvec,ih 0,ih 1]
      simp [PA194PAeq.add,Rew.func,quote_add]
      constructor
      · change (2 : V) = ((2 : Nat) : V); simp
      · constructor <;> rfl
    | mul =>
      have he : (.func .mul ts : SourceTerm n) = PA194PAeq.mul (ts 0) (ts 1) := by congr 1; funext i; fin_cases i <;> rfl
      rw [he,quote_mul]
      have h0 := quote_term_valid (V := V) (ts 0)
      have h1 := quote_term_valid (V := V) (ts 1)
      have hf : PA194PAeq.language.IsFunc (2 : V) 3 := by simp
      have hv : IsUTermVec PA194PAeq.language (2 : V) (?[⌜ts 0⌝,⌜ts 1⌝] : V) := by simp [h0,h1]
      rw [bindTerm_func hf hv]
      have hvec : bindTermVec (n : V) 2 (?[⌜ts 0⌝,⌜ts 1⌝] : V) = ?[bindTerm (n : V) ⌜ts 0⌝,bindTerm (n : V) ⌜ts 1⌝] := by
        have hv1 : IsUTermVec PA194PAeq.language (1 : V) (?[⌜ts 1⌝] : V) := by simp [h1]
        have hh := bindTermVec_cons (k := (n : V)) h0 hv1
        have hh' := bindTermVec_cons (k := (n : V)) h1 (show IsUTermVec PA194PAeq.language (0 : V) 0 by simp)
        have htail : bindTermVec (n : V) 1 (?[⌜ts 1⌝] : V) = ?[bindTerm (n : V) ⌜ts 1⌝] := by simpa using hh'
        simpa [htail,one_add_one_eq_two] using hh
      rw [hvec,ih 0,ih 1]
      simp [PA194PAeq.mul,Rew.func,quote_mul]
      constructor
      · change (3 : V) = ((3 : Nat) : V); simp
      · constructor <;> rfl
#print axioms bindTerm_quote_fix
end generic
end PA194PAeqBind
