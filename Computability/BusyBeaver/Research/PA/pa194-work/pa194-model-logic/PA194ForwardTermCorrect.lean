import PA194ForwardTypedSteps
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

theorem quote_succ_child_lt {n : Nat} (a : SourceTerm n) :
    (⌜a⌝ : V) < ⌜PA194PAeq.succ a⌝ := by
  rw [PA194PAeq.quote_successor]
  simpa using (nth_lt_qqFunc_of_lt (k := (1 : V)) (f := (1 : V))
    (v := (?[⌜a⌝] : V)) (i := (0 : V)) (by simp))
theorem quote_add_children_lt {n : Nat} (a b : SourceTerm n) :
    (⌜a⌝ : V) < ⌜PA194PAeq.add a b⌝ ∧ (⌜b⌝ : V) < ⌜PA194PAeq.add a b⌝ := by
  rw [quote_add]
  constructor
  · simpa using (nth_lt_qqFunc_of_lt (k := (2 : V)) (f := (2 : V))
      (v := (?[⌜a⌝,⌜b⌝] : V)) (i := (0 : V)) (by simp))
  · simpa using (nth_lt_qqFunc_of_lt (k := (2 : V)) (f := (2 : V))
      (v := (?[⌜a⌝,⌜b⌝] : V)) (i := (1 : V)) (by simp))
theorem quote_mul_children_lt {n : Nat} (a b : SourceTerm n) :
    (⌜a⌝ : V) < ⌜PA194PAeq.mul a b⌝ ∧ (⌜b⌝ : V) < ⌜PA194PAeq.mul a b⌝ := by
  rw [quote_mul]
  constructor
  · simpa using (nth_lt_qqFunc_of_lt (k := (2 : V)) (f := (3 : V))
      (v := (?[⌜a⌝,⌜b⌝] : V)) (i := (0 : V)) (by simp))
  · simpa using (nth_lt_qqFunc_of_lt (k := (2 : V)) (f := (3 : V))
      (v := (?[⌜a⌝,⌜b⌝] : V)) (i := (1 : V)) (by simp))

theorem value_quote {n : Nat} (t : SourceTerm n) : ∀ {m : Nat} (b : Fin n → Term m)
    (f : Nat → Term m) (z : Term m) (param : V), Aligned param b f z →
    (⌜t⌝ : V) < len (nth param 1) → translate param (⌜t⌝ : V) = ⌜value t b f z⌝ := by
  induction t with
  | bvar i =>
    intro m b f z param h hlen
    exact bound_value_quote i b f z param h
  | fvar i =>
    intro m b f z param h hlen
    apply free_value_quote i b f z param h
    have hi : (i : V) < (⌜(.fvar i : SourceTerm n)⌝ : V) := by
      simp only [Semiterm.quote_fvar,qqFvar]
      exact lt_of_le_of_lt (le_pair_right (1 : V) (i : V)) (lt_add_one _)
    exact lt_trans hi hlen
  | func sym ts ih =>
    cases sym with
    | zero =>
      intro m b f z param h hlen
      have he : (.func .zero ts : SourceTerm n) = PA194PAeq.zero := by
        congr 1; funext i; exact Fin.elim0 i
      rw [he]
      exact zero_value_quote b f z param h
    | succ =>
      intro m b f z param h hlen
      have he : (.func .succ ts : SourceTerm n) = PA194PAeq.succ (ts 0) := by
        congr 1; funext i; fin_cases i; rfl
      rw [he] at hlen ⊢
      apply succ_value_quote (ts 0) b f z param h
      apply ih 0 (shiftEnv b) (shiftEnv f) (.bvar 0) (childParameters param) (aligned_child h)
      have hc := lt_trans (quote_succ_child_lt (V := V) (ts 0)) hlen
      simpa [childParameters,shiftTerms_length h.1.2.1] using hc
    | add =>
      intro m b f z param h hlen
      have he : (.func .add ts : SourceTerm n) = PA194PAeq.add (ts 0) (ts 1) := by
        congr 1; funext i; fin_cases i <;> rfl
      rw [he] at hlen ⊢
      apply addition_value_quote (ts 0) (ts 1) b f z param h
      · apply ih 0 (shiftEnv (shiftEnv b)) (shiftEnv (shiftEnv f)) (.bvar 1) (binaryParameters param 1)
        · have he : (Fin.castLE (show 2 ≤ (m+1)+1 by omega) (1 : Fin 2) : Fin ((m+1)+1)) = 1 := by
            apply Fin.ext
            rfl
          simpa [he] using aligned_binary h (1 : Fin 2)
        · have hc := lt_trans (quote_add_children_lt (V := V) (ts 0) (ts 1)).1 hlen
          have hf1 := shiftTerms_valid h.1.2.1
          simpa [binaryParameters,shiftTerms_length h.1.2.1,shiftTerms_length hf1] using hc
      · apply ih 1 (shiftEnv (shiftEnv b)) (shiftEnv (shiftEnv f)) (.bvar 0) (binaryParameters param 0)
        · simpa using aligned_binary h (0 : Fin 2)
        · have hc := lt_trans (quote_add_children_lt (V := V) (ts 0) (ts 1)).2 hlen
          have hf1 := shiftTerms_valid h.1.2.1
          simpa [binaryParameters,shiftTerms_length h.1.2.1,shiftTerms_length hf1] using hc
    | mul =>
      intro m b f z param h hlen
      have he : (.func .mul ts : SourceTerm n) = PA194PAeq.mul (ts 0) (ts 1) := by
        congr 1; funext i; fin_cases i <;> rfl
      rw [he] at hlen ⊢
      apply multiplication_value_quote (ts 0) (ts 1) b f z param h
      · apply ih 0 (shiftEnv (shiftEnv b)) (shiftEnv (shiftEnv f)) (.bvar 1) (binaryParameters param 1)
        · have he : (Fin.castLE (show 2 ≤ (m+1)+1 by omega) (1 : Fin 2) : Fin ((m+1)+1)) = 1 := by
            apply Fin.ext
            rfl
          simpa [he] using aligned_binary h (1 : Fin 2)
        · have hc := lt_trans (quote_mul_children_lt (V := V) (ts 0) (ts 1)).1 hlen
          have hf1 := shiftTerms_valid h.1.2.1
          simpa [binaryParameters,shiftTerms_length h.1.2.1,shiftTerms_length hf1] using hc
      · apply ih 1 (shiftEnv (shiftEnv b)) (shiftEnv (shiftEnv f)) (.bvar 0) (binaryParameters param 0)
        · simpa using aligned_binary h (0 : Fin 2)
        · have hc := lt_trans (quote_mul_children_lt (V := V) (ts 0) (ts 1)).2 hlen
          have hf1 := shiftTerms_valid h.1.2.1
          simpa [binaryParameters,shiftTerms_length h.1.2.1,shiftTerms_length hf1] using hc
#print axioms value_quote
end generic
end PA194ForwardTyped
