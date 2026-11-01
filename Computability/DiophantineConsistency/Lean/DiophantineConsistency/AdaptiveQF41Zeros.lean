import DiophantineConsistency.AdaptiveQF41Context
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveQF41Zeros
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveSquareWitnessDirect14 AdaptiveDirectOrdinateSquareSums AdaptiveFoldSquares AdaptiveQF41Context
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem square_zero {σ : Type*} (e : Expr σ) (v : σ → V) :
    InternalZero (e*e) v ↔ InternalZero e v := by
  rw [rep_zero_iff (rawSquare_rep e v), mul_self_eq_zero, magnitude_zero_iff]
  rfl

theorem old_all (p : Fin 4 → ℤ) (v : Fin 42 → V) :
    InternalZero (AdaptiveQV42Context.literal p) v ↔ ∀ i : Fin 33,
      InternalZero ((AdaptiveQV42Context.residuals p i).subst AdaptiveQV42Context.newFill) v := by
  rw [← AdaptiveQV42Context.new_literal]
  let r0 := (AdaptiveQV42Context.residuals p 0).subst AdaptiveQV42Context.newFill
  let es : List (Expr (Fin 42)) := List.ofFn (fun i : Fin 32 =>
    (AdaptiveQV42Context.residuals p i.succ).subst AdaptiveQV42Context.newFill)
  have hf := foldSquares_zero_iff v es (r0*r0) _ (rawSquare_rep r0 v)
  change InternalZero ((AdaptiveQV42Context.sum p).subst AdaptiveQV42Context.newFill) v ↔
    InternalZero (r0*r0) v ∧ ∀ e ∈ es, InternalZero e v at hf
  rw [square_zero] at hf
  constructor
  · intro hz i
    obtain ⟨h0,ht⟩ := hf.mp hz
    by_cases hi : i.val = 0
    · have : i = 0 := Fin.ext hi
      simpa [this] using h0
    · have hi1 : 0 < i.val := by omega
      let j : Fin 32 := ⟨i.val - 1, by omega⟩
      have hj : j.succ = i := Fin.ext (by simp [j]; omega)
      simpa [hj] using ht _ (List.mem_ofFn.mpr ⟨j, rfl⟩)
  · intro h
    apply hf.mpr
    refine ⟨h 0, ?_⟩
    intro e he
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
    exact h i.succ

theorem new_all (p : Fin 4 → ℤ) (v : Fin 41 → V) :
    InternalZero (AdaptiveQF41Context.literal p) v ↔ ∀ i : Fin 32, InternalZero (residuals p i) v := by
  rw [← literal_eq]
  let r0 := residuals p 0
  let es : List (Expr (Fin 41)) := List.ofFn (fun i : Fin 31 => residuals p i.succ)
  have hf := foldSquares_zero_iff v es (r0*r0) _ (rawSquare_rep r0 v)
  change InternalZero (sum p) v ↔ InternalZero (r0*r0) v ∧ ∀ e ∈ es, InternalZero e v at hf
  rw [square_zero] at hf
  constructor
  · intro hz i
    obtain ⟨h0,ht⟩ := hf.mp hz
    by_cases hi : i.val = 0
    · have : i = 0 := Fin.ext hi
      simpa [this] using h0
    · have hi1 : 0 < i.val := by omega
      let j : Fin 31 := ⟨i.val - 1, by omega⟩
      have hj : j.succ = i := Fin.ext (by simp [j]; omega)
      simpa [hj] using ht _ (List.mem_ofFn.mpr ⟨j, rfl⟩)
  · intro h
    apply hf.mpr
    refine ⟨h 0, ?_⟩
    intro e he
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
    exact h i.succ
#print axioms old_all
#print axioms new_all
end DiophantineConsistency.AdaptiveQF41Zeros
