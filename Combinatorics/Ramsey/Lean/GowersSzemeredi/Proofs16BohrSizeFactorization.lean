import GowersSzemeredi.Proofs16BohrSizeRelations

/-! The relation weight factorizes when relations split: the algebraic core
of [49] Claim 34, in `ℤ/N`.

Claim 34 compares the Bohr set of `Γ ∪ {L₁(y), …, L_r(y)}` with that of `Γ`.
For a good `y`, every bounded relation `Σ ν_γ γ + Σ λⱼ Lⱼ(y) = 0` has
`ν ∈ M` (a relation of `Γ` alone) and `λ ∈ Λ` (a relation the maps satisfy
identically), and conversely. Under this splitting the relation weight of
the concatenated tuple is the product of the weight of `Γ` and
`W_Λ = Σ_{λ ∈ Λ} Π c_{λⱼ}` (`relationWeight_sumElim_of_split`).

With Proposition 23 (`bohr_card_approx_relations`) on both Bohr sets,
`|B(Γ ∪ L(y))|` is within `2εN + ‖W_Λ‖·2εN` of `W_Λ·|B(Γ)|`
(`bohr_card_factor_of_split`). [49] states this with a real `δᵢ` and
error `2η/5`, implicitly using `|δᵢ| ≤ 1`. Here the factor `‖W_Λ‖` stays
explicit.

Claim 34's pair version (ii) is the same statement with `κ` replaced by
`κ ⊕ κ` and `ℓ` by the concatenation of `L(y)` and `L(y′)`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Classical

/-- The weight of the coefficient vectors in `Λ`. -/
def latticeWeight {N : Nat} [NeZero N] {κ : Type*} [Fintype κ] (a c R : Nat)
    (Λ : Set (κ → centeredBall N R)) : Complex :=
  ∑ v : κ → centeredBall N R, (∏ j, trapezoidRelationCoeff a c (v j : ZMod N)) *
    (if v ∈ Λ then 1 else 0)

/-- **The relation weight factorizes when relations split.** -/
theorem relationWeight_sumElim_of_split {N : Nat} [NeZero N] {ι κ : Type*} [Fintype ι]
    [Fintype κ] (γ : ι → ZMod N) (ℓ : κ → ZMod N) (a c R : Nat)
    (Λ : Set (κ → centeredBall N R))
    (hsplit : ∀ (ν : ι → centeredBall N R) (μ : κ → centeredBall N R),
      (∑ i, (ν i : ZMod N) * γ i) + (∑ j, (μ j : ZMod N) * ℓ j) = 0 ↔
        (∑ i, (ν i : ZMod N) * γ i = 0 ∧ μ ∈ Λ)) :
    relationWeight (Sum.elim γ ℓ) a c R = relationWeight γ a c R * latticeWeight a c R Λ := by
  unfold relationWeight latticeWeight
  rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  refine Finset.sum_nbij' (fun v => (fun i => v (Sum.inl i), fun j => v (Sum.inr j)))
    (fun p => Sum.elim p.1 p.2) (by simp) (by simp)
    (fun v _ => by funext q; cases q <;> rfl) (fun p _ => rfl) (fun v _ => ?_)
  simp only [Fintype.prod_sum_type, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  rw [if_congr (hsplit (fun i => v (Sum.inl i)) (fun j => v (Sum.inr j))) rfl rfl]
  by_cases h1 : ∑ i, (v (Sum.inl i) : ZMod N) * γ i = 0 <;>
    by_cases h2 : (fun j => v (Sum.inr j)) ∈ Λ <;> simp [h1, h2] <;> ring

/-- **[49] Claim 34 (i) in `ℤ/N`.** -/
theorem bohr_card_factor_of_split {N : Nat} [NeZero N] {ι κ : Type*} [Fintype ι] [Fintype κ]
    (γ : ι → ZMod N) (ℓ : κ → ZMod N) {a c R : Nat} (hca : c ≤ a) (ha : 2 * a < N)
    (hc : 2 * c < N) (Λ : Set (κ → centeredBall N R))
    (hsplit : ∀ (ν : ι → centeredBall N R) (μ : κ → centeredBall N R),
      (∑ i, (ν i : ZMod N) * γ i) + (∑ j, (μ j : ZMod N) * ℓ j) = 0 ↔
        (∑ i, (ν i : ZMod N) * γ i = 0 ∧ μ ∈ Λ))
    {ε : Real}
    (hband : ((bohr (Finset.univ.image γ) (((a + c : Nat) : Real) / N)).card : Real) ≤
      (bohr (Finset.univ.image γ) (((a - c : Nat) : Real) / N)).card + ε * N)
    (hband' : ((bohr (Finset.univ.image (Sum.elim γ ℓ)) (((a + c : Nat) : Real) / N)).card :
        Real) ≤
      (bohr (Finset.univ.image (Sum.elim γ ℓ)) (((a - c : Nat) : Real) / N)).card + ε * N)
    (htrunc : (1 + N / ((centeredBall N c).card * (R + 1 : Real))) ^ Fintype.card ι - 1 ≤ ε)
    (htrunc' : (1 + N / ((centeredBall N c).card * (R + 1 : Real))) ^
      Fintype.card (ι ⊕ κ) - 1 ≤ ε) :
    ‖(((bohr (Finset.univ.image (Sum.elim γ ℓ)) (((a - c : Nat) : Real) / N)).card : Real) :
        Complex) -
      latticeWeight a c R Λ *
        (((bohr (Finset.univ.image γ) (((a - c : Nat) : Real) / N)).card : Real) : Complex)‖ ≤
      2 * ε * N + ‖latticeWeight a c R Λ‖ * (2 * ε * N) := by
  have h1 := bohr_card_approx_relations γ hca ha hc hband htrunc
  have h2 := bohr_card_approx_relations (Sum.elim γ ℓ) hca ha hc hband' htrunc'
  rw [relationWeight_sumElim_of_split γ ℓ a c R Λ hsplit] at h2
  set Bγ := (((bohr (Finset.univ.image γ) (((a - c : Nat) : Real) / N)).card : Real) : Complex)
  set Bγℓ := (((bohr (Finset.univ.image (Sum.elim γ ℓ)) (((a - c : Nat) : Real) / N)).card :
    Real) : Complex)
  set W := latticeWeight a c R Λ
  set V := relationWeight γ a c R
  calc ‖Bγℓ - W * Bγ‖ = ‖(Bγℓ - N * (V * W)) + W * (N * V - Bγ)‖ := by ring_nf
    _ ≤ ‖Bγℓ - N * (V * W)‖ + ‖W * (N * V - Bγ)‖ := norm_add_le _ _
    _ = ‖Bγℓ - N * (V * W)‖ + ‖W‖ * ‖Bγ - N * V‖ := by
        rw [norm_mul, ← norm_neg (N * V - Bγ), neg_sub]
    _ ≤ 2 * ε * N + ‖W‖ * (2 * ε * N) :=
        add_le_add h2 (mul_le_mul_of_nonneg_left h1 (norm_nonneg _))

end LeanProofs.GowersSzemeredi
