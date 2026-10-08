import GowersSzemeredi.Proofs16MilicevicStructure

/-! The readout: Freiman bihomomorphisms are bi-affine on product progressions.

Research notes J.2 reduce the readout (R) to two inputs:
* Milićević's passage from E-bilinear maps to Freiman-bilinear maps on a
  bilinear Bohr variety `V`;
* product boxes inside `V`, which is item (D).

This module proves the remaining link. If `Φ` is a Freiman bihomomorphism
on `V` (an `IsEBihomomorphism V Φ {0}`), and `P × Q ⊆ V` for progressions
`P = {a + i d}` and `Q = {b + j e}`, then `Φ` is bi-affine there:

`Φ(a + i d, b + j e) = c₀ + i c₁ + j c₂ + i j c₃`.

Each one-variable restriction has vanishing second differences, from the
quadruple `(i+1) + (i-1) = i + i`, so it is affine; affine in both indices
separately is bi-affine. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- A sequence with vanishing second differences on `[0, L)` is affine there. -/
theorem affine_of_second_difference {G : Type*} [AddCommGroup G] (f : Nat → G) (L : Nat)
    (h : ∀ i, i + 2 < L → f (i + 2) - f (i + 1) = f (i + 1) - f i) :
    ∀ i, i < L → f i = f 0 + i • (f 1 - f 0) := by
  intro i hi
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    match i, hi with
    | 0, _ => simp
    | 1, _ => simp
    | (k + 2), hk =>
      have h1 := ih (k + 1) (by omega) (by omega)
      have h0 := ih k (by omega) (by omega)
      have hd := h k hk
      have : f (k + 2) = f (k + 1) + (f (k + 1) - f k) := by rw [← hd]; abel
      rw [this, h1, h0]
      simp only [add_smul, one_smul, succ_nsmul]
      abel

/-- Affine in each index separately (on the grid) implies bi-affine. -/
theorem biaffine_of_affine_rows_cols {G : Type*} [AddCommGroup G] (f : Nat → Nat → G)
    (L₁ L₂ : Nat)
    (hrow : ∀ j, j < L₂ → ∀ i, i < L₁ → f i j = f 0 j + i • (f 1 j - f 0 j))
    (hcol : ∀ i, i < L₁ → ∀ j, j < L₂ → f i j = f i 0 + j • (f i 1 - f i 0))
    (hL₁ : 2 ≤ L₁) (hL₂ : 2 ≤ L₂) :
    ∀ i j, i < L₁ → j < L₂ →
      f i j = f 0 0 + i • (f 1 0 - f 0 0) + j • (f 0 1 - f 0 0) +
        (i * j) • (f 1 1 - f 1 0 - f 0 1 + f 0 0) := by
  intro i j hi hj
  have h0 := hcol 0 (by omega) j hj
  have h1 := hcol 1 (by omega) j hj
  rw [hrow j hj i hi, h0, h1, mul_nsmul']
  simp only [smul_sub, smul_add, mul_comm i j, mul_nsmul]
  abel

/-- **Readout.** A Freiman bihomomorphism on `V` is bi-affine on every
product of progressions contained in `V`. -/
theorem freiman_bihom_biaffine_on_product {N : Nat} {V : Finset (ZMod N × ZMod N)}
    {Φ : ZMod N × ZMod N → ZMod N} (hΦ : IsEBihomomorphism V Φ {0})
    (a d b e : ZMod N) (L₁ L₂ : Nat) (hL₁ : 2 ≤ L₁) (hL₂ : 2 ≤ L₂)
    (hsub : ∀ i j, i < L₁ → j < L₂ → (a + (i : ZMod N) * d, b + (j : ZMod N) * e) ∈ V) :
    let f : Nat → Nat → ZMod N := fun i j => Φ (a + (i : ZMod N) * d, b + (j : ZMod N) * e)
    ∀ i j, i < L₁ → j < L₂ →
      f i j = f 0 0 + i • (f 1 0 - f 0 0) + j • (f 0 1 - f 0 0) +
        (i * j) • (f 1 1 - f 1 0 - f 0 1 + f 0 0) := by
  intro f
  apply biaffine_of_affine_rows_cols f L₁ L₂ _ _ hL₁ hL₂
  · intro j hj
    apply affine_of_second_difference (fun i => f i j) L₁
    intro i hi
    have hq := hΦ.1 (a + ((i + 2 : Nat) : ZMod N) * d) (a + (i : ZMod N) * d)
      (a + ((i + 1 : Nat) : ZMod N) * d) (a + ((i + 1 : Nat) : ZMod N) * d)
      (b + (j : ZMod N) * e) (by push_cast; ring)
      (hsub _ _ hi hj) (hsub _ _ (by omega) hj) (hsub _ _ (by omega) hj) (hsub _ _ (by omega) hj)
    have hq0 : f (i + 2) j + f i j - f (i + 1) j - f (i + 1) j = 0 := hq
    show f (i + 2) j - f (i + 1) j = f (i + 1) j - f i j
    linear_combination hq0
  · intro i hi
    apply affine_of_second_difference (fun j => f i j) L₂
    intro j hj
    have hq := hΦ.2 (a + (i : ZMod N) * d) (b + ((j + 2 : Nat) : ZMod N) * e) (b + (j : ZMod N) * e)
      (b + ((j + 1 : Nat) : ZMod N) * e) (b + ((j + 1 : Nat) : ZMod N) * e)
      (by push_cast; ring)
      (hsub _ _ hi hj) (hsub _ _ hi (by omega)) (hsub _ _ hi (by omega)) (hsub _ _ hi (by omega))
    have hq0 : f i (j + 2) + f i j - f i (j + 1) - f i (j + 1) = 0 := hq
    show f i (j + 2) - f i (j + 1) = f i (j + 1) - f i j
    linear_combination hq0

end LeanProofs.GowersSzemeredi
