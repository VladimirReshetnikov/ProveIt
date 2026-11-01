import DiophantineConsistency.AdaptiveFoldSquares
import DiophantineConsistency.AdaptiveNamedValues47Context
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveNamedValues47Zeros
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveSquareWitnessDirect14 AdaptiveDirectOrdinateSquareSums AdaptiveNamedValues47Context AdaptiveFoldSquares
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def tailIndex (i : Fin 32) : Fin 35 := if h : i.val < 7 then ⟨i.val + 1, by omega⟩ else ⟨i.val + 3, by omega⟩

theorem square_zero {σ : Type*} (e : Expr σ) (v : σ → V) :
    InternalZero (e*e) v ↔ InternalZero e v := by
  rw [rep_zero_iff (rawSquare_rep e v), mul_self_eq_zero, magnitude_zero_iff]
  rfl

theorem old_zero {σ : Type*} (p : Fin 4 → ℤ) (f : Fin 2 ⊕ Fin 47 → Expr σ) (v : σ → V) :
    InternalZero ((oldSum p).subst f) v ↔
      InternalZero ((residuals p 0).subst f) v ∧
      ∀ i : Fin 34, InternalZero ((residuals p i.succ).subst f) v := by
  let r0 := (residuals p 0).subst f
  let es : List (Expr σ) := List.ofFn (fun i : Fin 34 => (residuals p i.succ).subst f)
  have hf := foldSquares_zero_iff v es (r0*r0) _ (rawSquare_rep r0 v)
  change InternalZero ((oldSum p).subst f) v ↔ InternalZero (r0*r0) v ∧
    ∀ e ∈ es, InternalZero e v at hf
  rw [square_zero] at hf
  constructor
  · intro hz
    obtain ⟨h0,ht⟩ := hf.mp hz
    refine ⟨h0, ?_⟩
    intro i
    exact ht _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
  · rintro ⟨h0,ht⟩
    apply hf.mpr
    refine ⟨h0, ?_⟩
    intro e he
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
    exact ht i

theorem new_zero {σ : Type*} (p : Fin 4 → ℤ) (f : Fin 2 ⊕ Fin 47 → Expr σ) (v : σ → V) :
    InternalZero ((newSum p).subst f) v ↔
      InternalZero ((residuals p 0).subst f) v ∧
      ∀ i : Fin 32, InternalZero ((residuals p (tailIndex i)).subst f) v := by
  let r0 := (residuals p 0).subst f
  let es : List (Expr σ) := List.ofFn (fun i : Fin 32 => (residuals p (tailIndex i)).subst f)
  have hf := foldSquares_zero_iff v es (r0*r0) _ (rawSquare_rep r0 v)
  change InternalZero ((newSum p).subst f) v ↔ InternalZero (r0*r0) v ∧
    ∀ e ∈ es, InternalZero e v at hf
  rw [square_zero] at hf
  constructor
  · intro hz
    obtain ⟨h0,ht⟩ := hf.mp hz
    refine ⟨h0, ?_⟩
    intro i
    exact ht _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
  · rintro ⟨h0,ht⟩
    apply hf.mpr
    refine ⟨h0, ?_⟩
    intro e he
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
    exact ht i
theorem old_all {σ : Type*} (p : Fin 4 → ℤ) (f : Fin 2 ⊕ Fin 47 → Expr σ) (v : σ → V) :
  InternalZero ((oldSum p).subst f) v ↔ ∀ i : Fin 35, InternalZero ((residuals p i).subst f) v := by
  rw [old_zero]
  constructor
  · rintro ⟨h0, hs⟩ i
    by_cases hi : i.val = 0
    · have : i = 0 := Fin.ext hi
      simpa [this] using h0
    · have hi1 : 0 < i.val := by omega
      let j : Fin 34 := ⟨i.val - 1, by omega⟩
      have hj : j.succ = i := Fin.ext (by simp [j]; omega)
      simpa [hj] using hs j
  · intro h
    exact ⟨h 0, fun i => h i.succ⟩
theorem new_all {σ : Type*} (p : Fin 4 → ℤ) (f : Fin 2 ⊕ Fin 47 → Expr σ) (v : σ → V) :
  InternalZero ((newSum p).subst f) v ↔ ∀ i : Fin 35, i ≠ 8 → i ≠ 9 → InternalZero ((residuals p i).subst f) v := by
  rw [new_zero]
  constructor
  · rintro ⟨h0, hs⟩ i hi hj
    by_cases hz : i.val = 0
    · have : i = 0 := Fin.ext hz
      simpa [this] using h0
    · have h8 : i.val ≠ 8 := by intro h; apply hi; exact Fin.ext h
      have h9 : i.val ≠ 9 := by intro h; apply hj; exact Fin.ext h
      by_cases hlt : i.val < 8
      · let j : Fin 32 := ⟨i.val - 1, by omega⟩
        have hj' : tailIndex j = i := Fin.ext (by simp only [tailIndex, j, Fin.val_mk, dif_pos (show i.val - 1 < 7 by omega)]; omega)
        simpa [hj'] using hs j
      · let j : Fin 32 := ⟨i.val - 3, by omega⟩
        have hj' : tailIndex j = i := Fin.ext (by simp only [tailIndex, j, Fin.val_mk, dif_neg (show ¬ i.val - 3 < 7 by omega)]; omega)
        simpa [hj'] using hs j
  · intro h
    refine ⟨h 0 (by decide) (by decide), ?_⟩
    intro i
    apply h (tailIndex i)
    · intro he; have : (tailIndex i).val = 8 := congrArg Fin.val he
      unfold tailIndex at this
      split at this <;> simp_all <;> omega
    · intro he; have : (tailIndex i).val = 9 := congrArg Fin.val he
      unfold tailIndex at this
      split at this <;> simp_all <;> omega
#print axioms old_all
#print axioms new_all
end DiophantineConsistency.AdaptiveNamedValues47Zeros
