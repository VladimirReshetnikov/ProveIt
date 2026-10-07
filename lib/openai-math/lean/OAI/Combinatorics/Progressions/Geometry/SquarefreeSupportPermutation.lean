import OAI.Combinatorics.Progressions.Polynomial.SquarefreePolynomialPermutation

namespace OAI

section

namespace Erdos3

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

noncomputable def squarefreeSupportModule (P : SquarefreeIndex ι → Prop) :
    Submodule ℚ (SquarefreePolynomial ι L) where
  carrier := {x | ∀ a, ¬P a → squarefreePolynomialEquiv x a = 0}
  zero_mem' := by
    intro a _
    exact congrFun (map_zero squarefreePolynomialEquiv) a
  add_mem' := by
    intro x y hx hy a ha
    rw [map_add, Pi.add_apply, hx a ha, hy a ha, add_zero]
  smul_mem' := by
    intro r x hx a ha
    rw [map_smul, Pi.smul_apply, hx a ha, smul_zero]

theorem mem_squarefreeSupportModule (P : SquarefreeIndex ι → Prop)
    (x : SquarefreePolynomial ι L) :
    x ∈ squarefreeSupportModule P ↔ ∀ a, ¬P a → squarefreePolynomialEquiv x a = 0 := Iff.rfl

theorem squarefreeSupportModule_mono {P Q : SquarefreeIndex ι → Prop}
    (h : ∀ a, P a → Q a) :
    squarefreeSupportModule (L := L) P ≤ squarefreeSupportModule Q := by
  intro x hx a ha
  exact hx a (fun hp => ha (h a hp))

theorem squarefreeSupportModule_eq_top {P : SquarefreeIndex ι → Prop}
    (h : ∀ a, P a) : squarefreeSupportModule (L := L) P = ⊤ := by
  apply top_unique
  intro x _ a ha
  exact False.elim (ha (h a))

theorem squarefreeSupportModule_eq_bot {P : SquarefreeIndex ι → Prop}
    (h : ∀ a, ¬P a) : squarefreeSupportModule (L := L) P = ⊥ := by
  apply bot_unique
  intro x hx
  change x = 0
  apply squarefreePolynomialEquiv.injective
  ext a
  exact hx a (h a)

theorem squarefreeMonomial_mem_support {P : SquarefreeIndex ι → Prop}
    (a : SquarefreeIndex ι) (ha : P a) (v : L) :
    squarefreeMonomial a v ∈ squarefreeSupportModule P := by
  intro b hb
  exact squarefreePolynomialEquiv_monomial_ne a b
    (fun he => hb (he ▸ ha)) v

end Erdos3

end

section

namespace Erdos3

variable {ι κ L : Type*} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]

theorem squarefreePermute_mem_support_iff (e : ι ≃ κ)
    (P : SquarefreeIndex ι → Prop) (Q : SquarefreeIndex κ → Prop)
    (hPQ : ∀ a, Q (SquarefreeIndex.permute e a) ↔ P a) (x : SquarefreePolynomial ι L) :
    squarefreePermute e x ∈ squarefreeSupportModule Q ↔ x ∈ squarefreeSupportModule P := by
  constructor
  · intro hx a ha
    have hq : ¬Q (SquarefreeIndex.permute e a) := fun h => ha ((hPQ a).mp h)
    have hz := hx (SquarefreeIndex.permute e a) hq
    simpa only [squarefreePermute_coefficient, Equiv.symm_apply_apply] using hz
  · intro hx b hb
    rw [squarefreePermute_coefficient]
    apply hx
    intro hp
    apply hb
    have hq := (hPQ ((SquarefreeIndex.permute e).symm b)).mpr hp
    simpa only [Equiv.apply_symm_apply] using hq

omit [Fintype ι] [Fintype κ] in
theorem SquarefreeIndex.permutedBound_le_iff (e : ι ≃ κ) (c : ι → ℕ) (a : SquarefreeIndex ι) :
    (fun j => c (e.symm j)) ≤ (fun j => (permute e a).val j) ↔
      c ≤ (fun i => a.val i) := by
  constructor
  · intro h i
    simpa only [permute_apply, Equiv.symm_apply_apply] using h (e i)
  · intro h j
    exact h (e.symm j)

end Erdos3

end

end OAI
