import OAI.Combinatorics.Progressions.Estimates.ShiftedAdaptedIdeal

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

theorem shiftedAdaptedSubmodule_antitone : Antitone (F.shiftedAdaptedSubmodule w) := by
  intro i j hij p hp α
  exact F.antitone (Nat.add_le_add_left hij _) (hp α)

noncomputable def shiftedPolynomialIdeal (k : ℕ) : LieIdeal ℚ (F.adaptedLieSubalgebra w) :=
  { (F.shiftedAdaptedSubmodule w k).comap (F.adaptedLieSubalgebra w).incl.toLinearMap with
    lie_mem := by
      intro p q hq
      have hp : p.val ∈ F.shiftedAdaptedSubmodule w 0 := by
        intro α
        simpa only [Nat.add_zero] using p.property α
      change ⁅p.val, q.val⁆ ∈ F.shiftedAdaptedSubmodule w k
      have hq' : q.val ∈ F.shiftedAdaptedSubmodule w k := hq
      simpa only [Nat.zero_add] using F.lie_mem_shiftedAdaptedSubmodule w hp hq' }

@[simp] theorem mem_shiftedPolynomialIdeal (k : ℕ) (p : F.adaptedLieSubalgebra w) :
    p ∈ F.shiftedPolynomialIdeal w k ↔
      ∀ α, coefficients p.val α ∈ F.layer (Finsupp.weight w α + k) := Iff.rfl

theorem shiftedPolynomialIdeal_antitone : Antitone (F.shiftedPolynomialIdeal w) := by
  intro i j hij p hp
  exact F.shiftedAdaptedSubmodule_antitone w hij hp

@[simp] theorem shiftedPolynomialIdeal_one : F.shiftedPolynomialIdeal w 1 = F.shiftedAdaptedIdeal w := by
  rfl

theorem shiftedPolynomialIdeal_lie_mem {i j : ℕ} {p q : F.adaptedLieSubalgebra w}
    (hp : p ∈ F.shiftedPolynomialIdeal w i) (hq : q ∈ F.shiftedPolynomialIdeal w j) :
    ⁅p, q⁆ ∈ F.shiftedPolynomialIdeal w (i + j) :=
  F.lie_mem_shiftedAdaptedSubmodule w hp hq

theorem adaptedConstant_mem_shiftedPolynomialIdeal (k : ℕ) {x : L} (hx : x ∈ F.layer k) :
    F.adaptedConstant w x ∈ F.shiftedPolynomialIdeal w k := by
  apply F.monomial_mem_shiftedAdaptedSubmodule
  simpa only [map_zero, Nat.zero_add] using hx

end Erdos3.NilpotentLieFiltration

end

end OAI
