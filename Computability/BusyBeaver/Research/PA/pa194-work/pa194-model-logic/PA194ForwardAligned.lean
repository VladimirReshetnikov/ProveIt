import PA194ForwardTyped
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

def Aligned {n m : Nat} (param : V) (b : Fin n → Term m) (f : Nat → Term m) (z : Term m) : Prop :=
  ParametersValid (n : V) (m : V) param ∧
  (∀ i : Fin n, nth (nth param 0) (i.val : V) = (⌜b i⌝ : V)) ∧
  (∀ i : Nat, (i : V) < len (nth param 1) → nth (nth param 1) (i : V) = (⌜f i⌝ : V)) ∧
  nth param 2 = (⌜z⌝ : V)

theorem cast_fin_lt {n : Nat} (i : Fin n) : (i.val : V) < (n : V) := by exact_mod_cast i.isLt

theorem aligned_shift {n m : Nat} {param : V} {b : Fin n → Term m} {f : Nat → Term m} {z : Term m}
    (h : Aligned param b f z) (j : Fin (m+1)) :
    Aligned (shiftParameters param (j.val : V)) (shiftEnv b) (shiftEnv f) (.bvar j) := by
  refine ⟨by simpa using shiftParameters_valid h.1 (by simpa using cast_fin_lt (V := V) j),?_,?_,?_⟩
  · intro i
    have hi : (i.val : V) < (n : V) := cast_fin_lt i
    simp only [shiftParameters,parameters_bound]
    rw [shiftTerms_nth h.1.1 hi,h.2.1 i]
    simp [shiftEnv,Semiterm.quote_def]
  · intro i hi
    have hl : len (nth (shiftParameters param (j.val : V)) 1) = len (nth param 1) := by
      simpa [shiftParameters] using shiftTerms_length h.1.2.1
    have hi' : (i : V) < len (nth param 1) := by simpa [hl] using hi
    simp only [shiftParameters,parameters_free]
    rw [shiftTerms_nth h.1.2.1 hi',h.2.2.1 i hi']
    simp [shiftEnv,Semiterm.quote_def]
  · simp [shiftParameters]

theorem aligned_child {n m : Nat} {param : V} {b : Fin n → Term m} {f : Nat → Term m} {z : Term m}
    (h : Aligned param b f z) :
    Aligned (childParameters param) (shiftEnv b) (shiftEnv f) (.bvar 0) := by
  refine ⟨by simpa using childParameters_valid h.1,?_,?_,?_⟩
  · intro i
    rw [childParameters_bound_nth h.1 (cast_fin_lt i),h.2.1 i]
    simp [shiftEnv,Semiterm.quote_def]
  · intro i hi
    have hl : len (nth (childParameters param) 1) = len (nth param 1) := by
      simpa [childParameters] using shiftTerms_length h.1.2.1
    have hi' : (i : V) < len (nth param 1) := by simpa [hl] using hi
    rw [childParameters_free_nth h.1 hi',h.2.2.1 i hi']
    simp [shiftEnv,Semiterm.quote_def]
  · simp [childParameters]

theorem aligned_binary {n m : Nat} {param : V} {b : Fin n → Term m} {f : Nat → Term m} {z : Term m}
    (h : Aligned param b f z) (j : Fin 2) :
    Aligned (binaryParameters param (j.val : V)) (shiftEnv (shiftEnv b)) (shiftEnv (shiftEnv f)) (.bvar (Fin.castLE (by omega) j)) := by
  have h1 := aligned_child h
  have h2 := aligned_shift h1 (Fin.castLE (show 2 ≤ (m+1)+1 by omega) j)
  simpa [shiftParameters_child] using h2
#print axioms aligned_shift
#print axioms aligned_binary
#print axioms aligned_child
end generic
end PA194ForwardTyped
