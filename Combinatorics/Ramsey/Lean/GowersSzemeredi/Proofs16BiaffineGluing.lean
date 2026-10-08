import GowersSzemeredi.Proofs16FreimanBilinearReadout

/-! Gluing bi-affine pieces along a shared square.

A bi-affine function `A + B i + C j + D i j` on an index grid is determined
by its values on any `2 × 2` square `{i₀, i₀+1} × {j₀, j₀+1}`. The four
values give, by unimodular elimination, `D`, then `B` and `C`, then `A`.
So two bi-affine descriptions that agree on one shared square agree
everywhere.

Consequence for the readout (R), research notes J.2: if a Freiman
bihomomorphism is bi-affine on two overlapping product boxes inside its
domain, and the overlap contains a `2 × 2` square, one bi-affine (hence
multilinear) function describes it on the union. Connected chains of
overlapping boxes inside `V` are therefore covered by a single multilinear
function, which is the linking option for partial cells. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The bi-affine function with coefficients `(A, B, C, D)`. -/
def biaffineAt {R : Type*} [CommRing R] (A B C D : R) (i j : Nat) : R :=
  A + (i : R) * B + (j : R) * C + ((i : R) * j) * D

/-- **Bi-affine functions are determined by a square.** -/
theorem biaffine_coeffs_eq_of_square {R : Type*} [CommRing R] {A B C D A' B' C' D' : R}
    (i₀ j₀ : Nat)
    (h00 : biaffineAt A B C D i₀ j₀ = biaffineAt A' B' C' D' i₀ j₀)
    (h10 : biaffineAt A B C D (i₀ + 1) j₀ = biaffineAt A' B' C' D' (i₀ + 1) j₀)
    (h01 : biaffineAt A B C D i₀ (j₀ + 1) = biaffineAt A' B' C' D' i₀ (j₀ + 1))
    (h11 : biaffineAt A B C D (i₀ + 1) (j₀ + 1) = biaffineAt A' B' C' D' (i₀ + 1) (j₀ + 1)) :
    A = A' ∧ B = B' ∧ C = C' ∧ D = D' := by
  unfold biaffineAt at h00 h10 h01 h11
  push_cast at h00 h10 h01 h11
  have hD : D = D' := by linear_combination h11 - h10 - h01 + h00
  have hB : B = B' := by
    linear_combination h10 - h00 - (j₀ : R) * (h11 - h10 - h01 + h00)
  have hC : C = C' := by
    linear_combination h01 - h00 - (i₀ : R) * (h11 - h10 - h01 + h00)
  have hA : A = A' := by
    linear_combination h00 - (i₀ : R) * (h10 - h00 - (j₀ : R) * (h11 - h10 - h01 + h00)) -
      (j₀ : R) * (h01 - h00 - (i₀ : R) * (h11 - h10 - h01 + h00)) -
      ((i₀ : R) * j₀) * (h11 - h10 - h01 + h00)
  exact ⟨hA, hB, hC, hD⟩

/-- **Gluing.** If `f` agrees with one bi-affine function on a set `S₁`,
with another on `S₂`, and both sets contain a common square, then the two
functions coincide; so one bi-affine function describes `f` on
`S₁ ∪ S₂`. -/
theorem biaffine_glue {R : Type*} [CommRing R] (f : Nat → Nat → R)
    {S₁ S₂ : Set (Nat × Nat)} {A B C D A' B' C' D' : R}
    (h₁ : ∀ p ∈ S₁, f p.1 p.2 = biaffineAt A B C D p.1 p.2)
    (h₂ : ∀ p ∈ S₂, f p.1 p.2 = biaffineAt A' B' C' D' p.1 p.2)
    (i₀ j₀ : Nat)
    (hsq : ∀ a b : Nat, a ≤ 1 → b ≤ 1 → (i₀ + a, j₀ + b) ∈ S₁ ∧ (i₀ + a, j₀ + b) ∈ S₂) :
    ∀ p ∈ S₁ ∪ S₂, f p.1 p.2 = biaffineAt A B C D p.1 p.2 := by
  have hpt : ∀ a b : Nat, a ≤ 1 → b ≤ 1 →
      biaffineAt A B C D (i₀ + a) (j₀ + b) = biaffineAt A' B' C' D' (i₀ + a) (j₀ + b) := by
    intro a b ha hb
    obtain ⟨m1, m2⟩ := hsq a b ha hb
    rw [← h₁ _ m1, ← h₂ _ m2]
  obtain ⟨hA, hB, hC, hD⟩ := biaffine_coeffs_eq_of_square i₀ j₀
    (by simpa using hpt 0 0 (by omega) (by omega)) (hpt 1 0 le_rfl (by omega))
    (by simpa using hpt 0 1 (by omega) le_rfl) (hpt 1 1 le_rfl le_rfl)
  intro p hp
  rcases hp with hp | hp
  · exact h₁ p hp
  · rw [h₂ p hp, hA, hB, hC, hD]

/-- The readout of `freiman_bihom_biaffine_on_product`, in `biaffineAt` form. -/
theorem freiman_bihom_biaffineAt_on_product {N : Nat} {V : Finset (ZMod N × ZMod N)}
    {Φ : ZMod N × ZMod N → ZMod N} (hΦ : IsEBihomomorphism V Φ {0})
    (a d b e : ZMod N) (L₁ L₂ : Nat) (hL₁ : 2 ≤ L₁) (hL₂ : 2 ≤ L₂)
    (hsub : ∀ i j, i < L₁ → j < L₂ → (a + (i : ZMod N) * d, b + (j : ZMod N) * e) ∈ V) :
    let f : Nat → Nat → ZMod N := fun i j => Φ (a + (i : ZMod N) * d, b + (j : ZMod N) * e)
    ∀ i j, i < L₁ → j < L₂ →
      f i j = biaffineAt (f 0 0) (f 1 0 - f 0 0) (f 0 1 - f 0 0) (f 1 1 - f 1 0 - f 0 1 + f 0 0) i j := by
  intro f i j hi hj
  have h : f i j = f 0 0 + i • (f 1 0 - f 0 0) + j • (f 0 1 - f 0 0) +
      (i * j) • (f 1 1 - f 1 0 - f 0 1 + f 0 0) :=
    freiman_bihom_biaffine_on_product hΦ a d b e L₁ L₂ hL₁ hL₂ hsub i j hi hj
  rw [h]
  unfold biaffineAt
  simp only [nsmul_eq_mul]
  push_cast
  ring

end LeanProofs.GowersSzemeredi
