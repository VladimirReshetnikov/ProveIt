import DiophantineConsistency.AdaptiveFoldSquares
import DiophantineConsistency.AdaptiveAQ40Context
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveAQ40Zeros
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveSquareWitnessDirect14 AdaptiveDirectOrdinateSquareSums AdaptiveAQ40Context AdaptiveFoldSquares
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def tailIndex (i : Fin 26) : Fin 28 := if h : i.val < 8 then ⟨i.val + 1, by omega⟩ else ⟨i.val + 2, by omega⟩

theorem square_zero {σ : Type*} (e : Expr σ) (v : σ → V) :
    InternalZero (e*e) v ↔ InternalZero e v := by
  rw [rep_zero_iff (rawSquare_rep e v), mul_self_eq_zero, magnitude_zero_iff]
  rfl

theorem old_zero {σ : Type*} (p : Fin 4 → ℤ) (f : Fin 2 ⊕ Fin 39 → Expr σ) (v : σ → V) :
    InternalZero ((oldSum p).subst f) v ↔
      InternalZero ((residuals p 0).subst f) v ∧
      ∀ i : Fin 27, InternalZero ((residuals p i.succ).subst f) v := by
  let r0 := (residuals p 0).subst f
  let es : List (Expr σ) := List.ofFn (fun i : Fin 27 => (residuals p i.succ).subst f)
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

theorem new_zero {σ : Type*} (p : Fin 4 → ℤ) (f : Fin 2 ⊕ Fin 39 → Expr σ) (v : σ → V) :
    InternalZero ((newSum p).subst f) v ↔
      InternalZero ((residuals p 0).subst f) v ∧
      ∀ i : Fin 26, InternalZero ((residuals p (tailIndex i)).subst f) v := by
  let r0 := (residuals p 0).subst f
  let es : List (Expr σ) := List.ofFn (fun i : Fin 26 => (residuals p (tailIndex i)).subst f)
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
#print axioms old_zero
#print axioms new_zero
end DiophantineConsistency.AdaptiveAQ40Zeros
