import PA194PAeqTypedClosure
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeqBind
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ForwardTyped
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
def finFreeBound (s : Finset Nat) : Nat := (s.max).recBotCoe 0 Nat.succ
@[simp] theorem finFreeBound_empty : finFreeBound ∅ = 0 := by simp [finFreeBound]
@[simp] theorem finFreeBound_singleton (x : Nat) : finFreeBound {x} = x+1 := by simp [finFreeBound]
theorem finFreeBound_union (s t : Finset Nat) : finFreeBound (s ∪ t) = max (finFreeBound s) (finFreeBound t) := by
  unfold finFreeBound
  rw [Finset.max_union]
  generalize hs : s.max = a
  generalize ht : t.max = b
  cases a using WithBot.recBotCoe with
  | bot => simp
  | coe a =>
    cases b using WithBot.recBotCoe with
    | bot => simp
    | coe b =>
      rw [← WithBot.coe_max]
      simp only [WithBot.recBotCoe_coe, Nat.succ_max_succ]
theorem natCast_max (a b : Nat) : ((max a b : Nat) : V) = max (a : V) (b : V) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h,max_eq_right (by exact_mod_cast h)]
  · rw [max_eq_left h,max_eq_left (by exact_mod_cast h)]
@[simp] theorem termFreeBoundVec_nil : termFreeBoundVec (0 : V) 0 = 0 := by simp [termFreeBoundVec,termFreeConstruction]
theorem termFreeBoundVec_cons {ar t v : V} (ht : IsUTerm PA194PAeq.language t)
    (hv : IsUTermVec PA194PAeq.language ar v) :
    termFreeBoundVec (ar+1) (t ∷ v) = termFreeBound t ∷ termFreeBoundVec ar v := by
  simpa [termFreeBoundVec,termFreeBound] using termFreeConstruction.resultVec_cons PA194PAeq.language ![] hv ht

theorem termFreeBound_quote {n : Nat} (t : SourceTerm n) :
    termFreeBound (⌜t⌝ : V) = (finFreeBound t.freeVariables : V) := by
  induction t with
  | bvar x => simp [Semiterm.freeVariables_bvar]
  | fvar x => simp [Semiterm.freeVariables_fvar]
  | func f ts ih =>
    cases f with
    | zero =>
      have he : (.func .zero ts : SourceTerm n) = PA194PAeq.zero := by congr 1; funext i; exact Fin.elim0 i
      rw [he,PA194PAeq.quote_zero]
      have hf : PA194PAeq.language.IsFunc (0 : V) 0 := by simp
      have hv : IsUTermVec PA194PAeq.language (0 : V) 0 := by simp
      rw [termFreeBound_func hf hv,termFreeBoundVec_nil]
      simp [PA194PAeq.zero,Semiterm.freeVariables_func]
    | succ =>
      have he : (.func .succ ts : SourceTerm n) = PA194PAeq.succ (ts 0) := by congr 1; funext i; fin_cases i; rfl
      rw [he,PA194PAeq.quote_successor]
      have ht := quote_term_valid (V := V) (ts 0)
      have hf : PA194PAeq.language.IsFunc (1 : V) 1 := by simp
      have hv : IsUTermVec PA194PAeq.language (1 : V) (?[⌜ts 0⌝] : V) := by simp [ht]
      rw [termFreeBound_func hf hv]
      have hv' := termFreeBoundVec_cons ht (show IsUTermVec PA194PAeq.language (0 : V) 0 by simp)
      simp only [zero_add,termFreeBoundVec_nil] at hv'
      rw [hv',ih 0]
      have hfree : (PA194PAeq.succ (ts 0)).freeVariables = (ts 0).freeVariables := by
        ext x; simp [PA194PAeq.succ,Semiterm.freeVariables_func,Fin.exists_fin_one]
      rw [hfree]
      simp
    | add =>
      have he : (.func .add ts : SourceTerm n) = PA194PAeq.add (ts 0) (ts 1) := by congr 1; funext i; fin_cases i <;> rfl
      rw [he,quote_add]
      have h0 := quote_term_valid (V := V) (ts 0)
      have h1 := quote_term_valid (V := V) (ts 1)
      have hf : PA194PAeq.language.IsFunc (2 : V) 2 := by simp
      have hv : IsUTermVec PA194PAeq.language (2 : V) (?[⌜ts 0⌝,⌜ts 1⌝] : V) := by simp [h0,h1]
      rw [termFreeBound_func hf hv]
      have hv1 : IsUTermVec PA194PAeq.language (1 : V) (?[⌜ts 1⌝] : V) := by simp [h1]
      have hh := termFreeBoundVec_cons h0 hv1
      have hh' := termFreeBoundVec_cons h1 (show IsUTermVec PA194PAeq.language (0 : V) 0 by simp)
      have htail : termFreeBoundVec 1 (?[⌜ts 1⌝] : V) = ?[termFreeBound (⌜ts 1⌝ : V)] := by simpa using hh'
      have hpair : termFreeBoundVec 2 (?[⌜ts 0⌝,⌜ts 1⌝] : V) = ?[termFreeBound (⌜ts 0⌝ : V),termFreeBound (⌜ts 1⌝ : V)] := by simpa [htail,one_add_one_eq_two] using hh
      rw [hpair,ih 0,ih 1]
      have hfree : (PA194PAeq.add (ts 0) (ts 1)).freeVariables = (ts 0).freeVariables ∪ (ts 1).freeVariables := by
        ext x; simp [PA194PAeq.add,Semiterm.freeVariables_func,Fin.exists_fin_two]
      rw [hfree,finFreeBound_union,natCast_max]
      simp
    | mul =>
      have he : (.func .mul ts : SourceTerm n) = PA194PAeq.mul (ts 0) (ts 1) := by congr 1; funext i; fin_cases i <;> rfl
      rw [he,quote_mul]
      have h0 := quote_term_valid (V := V) (ts 0)
      have h1 := quote_term_valid (V := V) (ts 1)
      have hf : PA194PAeq.language.IsFunc (2 : V) 3 := by simp
      have hv : IsUTermVec PA194PAeq.language (2 : V) (?[⌜ts 0⌝,⌜ts 1⌝] : V) := by simp [h0,h1]
      rw [termFreeBound_func hf hv]
      have hv1 : IsUTermVec PA194PAeq.language (1 : V) (?[⌜ts 1⌝] : V) := by simp [h1]
      have hh := termFreeBoundVec_cons h0 hv1
      have hh' := termFreeBoundVec_cons h1 (show IsUTermVec PA194PAeq.language (0 : V) 0 by simp)
      have htail : termFreeBoundVec 1 (?[⌜ts 1⌝] : V) = ?[termFreeBound (⌜ts 1⌝ : V)] := by simpa using hh'
      have hpair : termFreeBoundVec 2 (?[⌜ts 0⌝,⌜ts 1⌝] : V) = ?[termFreeBound (⌜ts 0⌝ : V),termFreeBound (⌜ts 1⌝ : V)] := by simpa [htail,one_add_one_eq_two] using hh
      rw [hpair,ih 0,ih 1]
      have hfree : (PA194PAeq.mul (ts 0) (ts 1)).freeVariables = (ts 0).freeVariables ∪ (ts 1).freeVariables := by
        ext x; simp [PA194PAeq.mul,Semiterm.freeVariables_func,Fin.exists_fin_two]
      rw [hfree,finFreeBound_union,natCast_max]
      simp
#print axioms termFreeBound_quote
end generic
end PA194PAeqBind
