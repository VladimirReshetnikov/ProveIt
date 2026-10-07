import OAI.Combinatorics.Progressions.Polynomial.AdaptedPolynomialSubstitution

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def shiftedAdaptedSubmodule (w : σ → ℕ) (k : ℕ) :
    Submodule ℚ (VectorPolynomial σ ℚ L) where
  carrier := {p | ∀ α, coefficients p α ∈ F.layer (Finsupp.weight w α + k)}
  zero_mem' := by intro α; simp
  add_mem' hp hq := by
    intro α
    simpa only [map_add, Finsupp.add_apply] using (F.layer _).add_mem (hp α) (hq α)
  smul_mem' r p hp := by
    intro α
    simpa only [map_smul, Finsupp.smul_apply] using (F.layer _).smul_mem r (hp α)

theorem monomial_mem_shiftedAdaptedSubmodule (w : σ → ℕ) (k : ℕ)
    (α : σ →₀ ℕ) {a : L} (ha : a ∈ F.layer (Finsupp.weight w α + k)) :
    monomial (R := ℚ) α a ∈ F.shiftedAdaptedSubmodule w k := by
  classical
  intro β
  by_cases h : α = β
  · subst β
    simpa using ha
  · simp [h]

theorem lie_mem_shiftedAdaptedSubmodule (w : σ → ℕ) {i j : ℕ}
    {p q : VectorPolynomial σ ℚ L}
    (hp : p ∈ F.shiftedAdaptedSubmodule w i) (hq : q ∈ F.shiftedAdaptedSubmodule w j) :
    ⁅p, q⁆ ∈ F.shiftedAdaptedSubmodule w (i + j) := by
  classical
  rw [← sum_monomial_coefficients p, ← sum_monomial_coefficients q]
  simp only [Finsupp.sum]
  rw [sum_lie_sum]
  apply Submodule.sum_mem
  intro α _
  apply Submodule.sum_mem
  intro β _
  rw [lie_monomial]
  apply F.monomial_mem_shiftedAdaptedSubmodule
  simpa only [map_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using F.lie_mem (hp α) (hq β)

noncomputable def shiftedAdaptedIdeal (w : σ → ℕ) : LieIdeal ℚ (F.adaptedLieSubalgebra w) :=
  { (F.shiftedAdaptedSubmodule w 1).comap (F.adaptedLieSubalgebra w).incl.toLinearMap with
    lie_mem := by
      intro p q hq
      have hp : (p : VectorPolynomial σ ℚ L) ∈ F.shiftedAdaptedSubmodule w 0 := by
        intro α
        simpa only [Nat.add_zero] using p.property α
      exact F.lie_mem_shiftedAdaptedSubmodule w hp hq }

theorem adapted_constant (w : σ → ℕ) (a : L) : F.Adapted w (monomial 0 a) := by
  apply (F.mem_adaptedSubmodule w _).mp
  apply F.monomial_mem_adaptedSubmodule
  rw [map_zero]
  apply F.antitone (Nat.zero_le 1)
  rw [F.one_eq_top]
  trivial

noncomputable def adaptedConstant (w : σ → ℕ) (a : L) : F.adaptedLieSubalgebra w :=
  ⟨monomial 0 a, (F.mem_adaptedSubmodule w _).mpr (F.adapted_constant w a)⟩

theorem adaptedConstant_mem_shiftedIdeal (w : σ → ℕ) (a : L) :
    F.adaptedConstant w a ∈ F.shiftedAdaptedIdeal w := by
  apply F.monomial_mem_shiftedAdaptedSubmodule
  simp only [map_zero, Nat.zero_add, F.one_eq_top, Submodule.mem_top]

end Erdos3.NilpotentLieFiltration

end

end OAI
