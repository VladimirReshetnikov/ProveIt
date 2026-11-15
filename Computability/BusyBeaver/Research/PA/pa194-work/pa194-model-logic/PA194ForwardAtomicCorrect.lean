import PA194ForwardFormulaAligned
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194ForwardTyped
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher PA194FormulaDispatcher
open M6.PA.RelationalSource
open Ordinal (Term Formula)
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem orderIsoCode_quote {m : Nat} (x y : Term m) :
    orderIsoCode (⌜x⌝ : V) ⌜y⌝ = ⌜PairGraph.orderIso x y⌝ := by
  rw [orderIsoCode,templateTwo_quote]
  congr 1
  simpa [orderIsoTemplate,Rewriting.subst,app_eq_rewAux] using
    PairGraph.orderIso_rew (Rew.subst ![x,y]) (.bvar 0) (.bvar 1)

theorem atomicEquality_quote {n m : Nat} (a c : SourceTerm n) (b : Fin n → Term m)
    (f : Nat → Term m) (z : Term m) (param : V) (h : Aligned param b f z)
    (ha : (⌜a⌝ : V) < len (nth param 1)) (hc : (⌜c⌝ : V) < len (nth param 1)) :
    atomicEquality param (⌜a⌝ : V) ⌜c⌝ = ⌜equal a c b f⌝ := by
  have hal1 : Aligned (binaryParameters param 1) (shiftEnv (shiftEnv b)) (shiftEnv (shiftEnv f)) (.bvar 1) := by
    have he : (Fin.castLE (show 2 ≤ (m+1)+1 by omega) (1 : Fin 2) : Fin ((m+1)+1)) = 1 := by
      apply Fin.ext
      rfl
    simpa [he] using aligned_binary h (1 : Fin 2)
  have hal0 : Aligned (binaryParameters param 0) (shiftEnv (shiftEnv b)) (shiftEnv (shiftEnv f)) (.bvar 0) := by
    simpa using aligned_binary h (0 : Fin 2)
  have hf1 := shiftTerms_valid h.1.2.1
  have hla : (⌜a⌝ : V) < len (nth (binaryParameters param 1) 1) := by
    simpa [binaryParameters,shiftTerms_length h.1.2.1,shiftTerms_length hf1] using ha
  have hlc : (⌜c⌝ : V) < len (nth (binaryParameters param 0) 1) := by
    simpa [binaryParameters,shiftTerms_length h.1.2.1,shiftTerms_length hf1] using hc
  have hleft := value_quote a (shiftEnv (shiftEnv b)) (shiftEnv (shiftEnv f)) (.bvar 1) (binaryParameters param 1) hal1 hla
  have hright := value_quote c (shiftEnv (shiftEnv b)) (shiftEnv (shiftEnv f)) (.bvar 0) (binaryParameters param 0) hal0 hlc
  have h0 : (^#(0 : V)) = (⌜(.bvar 0 : Term (m+2))⌝ : V) := by simp
  have h1 : (^#(1 : V)) = (⌜(.bvar 1 : Term (m+2))⌝ : V) := by simp
  rw [atomicEquality,hleft,hright,h1,h0,orderIsoCode_quote]
  rfl
#print axioms orderIsoCode_quote
#print axioms atomicEquality_quote
end generic
end PA194ForwardTyped
