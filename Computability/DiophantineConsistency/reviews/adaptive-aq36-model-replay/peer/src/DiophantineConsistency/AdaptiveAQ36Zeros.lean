import DiophantineConsistency.AdaptiveAQ36Context
import DiophantineConsistency.AdaptiveFoldSquares
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveAQ36Zeros
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveSquareWitnessDirect14 AdaptiveDirectOrdinateSquareSums AdaptiveAQ36Context AdaptiveFoldSquares
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def tailIndex : Fin 22 → Fin 27 := ![1,2,3,4,5,6,7,8,9,10,13,14,15,16,17,18,19,20,22,23,24,26]

theorem square_zero {σ : Type*} (e : Expr σ) (v : σ → V) :
    InternalZero (e*e) v ↔ InternalZero e v := by
  rw [rep_zero_iff (rawSquare_rep e v), mul_self_eq_zero, magnitude_zero_iff]
  rfl

theorem old_zero {σ : Type*} (p : Fin 4 → ℤ) (f : Fin 4 ⊕ Fin 36 → Expr σ) (v : σ → V) :
    InternalZero ((oldSum p).subst f) v ↔
      InternalZero ((residuals p 0).subst f) v ∧
      ∀ i : Fin 26, InternalZero ((residuals p i.succ).subst f) v := by
  let r0 := (residuals p 0).subst f
  let es : List (Expr σ) := List.ofFn (fun i : Fin 26 => (residuals p i.succ).subst f)
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

theorem new_zero {σ : Type*} (p : Fin 4 → ℤ) (f : Fin 4 ⊕ Fin 36 → Expr σ) (v : σ → V) :
    InternalZero ((newSum p).subst f) v ↔
      InternalZero ((residuals p 0).subst f) v ∧
      ∀ i : Fin 22, InternalZero ((residuals p (tailIndex i)).subst f) v := by
  let r0 := (residuals p 0).subst f
  let es : List (Expr σ) := List.ofFn (fun i : Fin 22 => (residuals p (tailIndex i)).subst f)
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

theorem tail_covers (i : Fin 27) (h0 : i ≠ 0) (h11 : i ≠ 11) (h12 : i ≠ 12) (h21 : i ≠ 21) (h25 : i ≠ 25) : ∃ j : Fin 22, tailIndex j = i := by
  fin_cases i
  · exact False.elim (h0 rfl)
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨4, rfl⟩
  · exact ⟨5, rfl⟩
  · exact ⟨6, rfl⟩
  · exact ⟨7, rfl⟩
  · exact ⟨8, rfl⟩
  · exact ⟨9, rfl⟩
  · exact False.elim (h11 rfl)
  · exact False.elim (h12 rfl)
  · exact ⟨10, rfl⟩
  · exact ⟨11, rfl⟩
  · exact ⟨12, rfl⟩
  · exact ⟨13, rfl⟩
  · exact ⟨14, rfl⟩
  · exact ⟨15, rfl⟩
  · exact ⟨16, rfl⟩
  · exact ⟨17, rfl⟩
  · exact False.elim (h21 rfl)
  · exact ⟨18, rfl⟩
  · exact ⟨19, rfl⟩
  · exact ⟨20, rfl⟩
  · exact False.elim (h25 rfl)
  · exact ⟨21, rfl⟩
#print axioms old_zero
#print axioms new_zero
end DiophantineConsistency.AdaptiveAQ36Zeros
