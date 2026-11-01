import DiophantineConsistency.AdaptiveFoldSquares
import DiophantineConsistency.AdaptiveAQ34Context
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveAQ34Zeros
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveSquareWitnessDirect14 AdaptiveDirectOrdinateSquareSums AdaptiveFoldSquares AdaptiveAQ34Context
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem square_zero {σ : Type*} (e : Expr σ) (v : σ → V) :
    InternalZero (e*e) v ↔ InternalZero e v := by
  rw [rep_zero_iff (rawSquare_rep e v), mul_self_eq_zero, magnitude_zero_iff]
  rfl

theorem sum_zero {σ : Type*} (p : Fin 4 → ℤ) (f : Fin 2 ⊕ Fin 32 → Expr σ) (v : σ → V) :
    InternalZero ((sum p).subst f) v ↔ ∀ i : Fin 22, InternalZero ((residuals p i).subst f) v := by
  let r0 := (residuals p 0).subst f
  let es : List (Expr σ) := List.ofFn (fun i : Fin 21 => (residuals p i.succ).subst f)
  have hf := foldSquares_zero_iff v es (r0*r0) _ (rawSquare_rep r0 v)
  change InternalZero ((sum p).subst f) v ↔ InternalZero (r0*r0) v ∧
    ∀ e ∈ es, InternalZero e v at hf
  rw [square_zero] at hf
  constructor
  · intro hz i
    obtain ⟨h0,ht⟩ := hf.mp hz
    by_cases hi : i.val = 0
    · have : i = 0 := Fin.ext hi
      simpa [this] using h0
    · have hi1 : 0 < i.val := by omega
      let j : Fin 21 := ⟨i.val - 1, by omega⟩
      have hj : j.succ = i := Fin.ext (by simp [j]; omega)
      simpa [hj] using ht _ (List.mem_ofFn.mpr ⟨j, rfl⟩)
  · intro h
    apply hf.mpr
    refine ⟨h 0, ?_⟩
    intro e he
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
    exact h i.succ
#print axioms sum_zero
end DiophantineConsistency.AdaptiveAQ34Zeros
