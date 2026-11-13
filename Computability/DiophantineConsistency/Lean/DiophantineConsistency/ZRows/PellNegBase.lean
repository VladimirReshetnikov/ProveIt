import DiophantineConsistency.P138.P138FirstIndex

/-! # Two exact Lucas congruences

In every model `V` of `𝗜𝚺₁`, with the Pell coordinates `χ_b(t) = xcoord t b`,
`ψ_b(t) = ycoord t b` of the base `β = b + 2`:

* **The odd alternating residue** (`alt_odd`). If `m ∣ b + 3` (so `β ≡ −1`), then
  `ψ_b(2j + 1) ≡ 2j + 1 (mod m)` exactly. `P138FirstIndex.alt_sign` gives only `±`;
  here the two steps `stepA`, `stepB` are chained along even times (`alt_even`).
* **The negated base** (`nb_even`, `nb_odd`). If `F ∣ (b₁ + 2) + (b₂ + 2)` (so
  `β₁ ≡ −β₂` and `Δ₁ ≡ Δ₂`), then at even times `χ₁ ≡ χ₂`, `ψ₁ ≡ −ψ₂`, and at odd times
  `ψ₁ ≡ ψ₂ (mod F)`. The two one-step laws are ring identities (`step_from_even`,
  `step_from_odd`, quotients computed offline); the induction carries natural
  quotients on both sides (`two_sided`).

Both are used by the ten-integer interpolation of package 106, where the second
Pell base `G` satisfies `G ≡ −1 (mod Ω ξ)` and `G ≡ −A/2 (mod F)`.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ZRowsPellNegBase

/-! ## The one-step laws (any commutative ring) -/

section Ring
variable {𝔸 : Type*} [CommRing 𝔸]

/-- From the even state `χ₁ ≡ χ₂`, `ψ₁ ≡ −ψ₂` to the odd state `χ₁ ≡ −χ₂`, `ψ₁ ≡ ψ₂`. -/
theorem step_from_even (F k b1 b2 X1 X2 Y1 Y2 e1 e2 : 𝔸) (hb : b1 = F * k - b2 - 4)
    (hx : X1 = X2 + F * e1) (hy : Y1 = F * e2 - Y2) :
    F ∣ ((b1 + 2) * X1 + (b1 + 1) * (b1 + 3) * Y1) +
        ((b2 + 2) * X2 + (b2 + 1) * (b2 + 3) * Y2) ∧
      F ∣ (X1 + (b1 + 2) * Y1) - (X2 + (b2 + 2) * Y2) := by
  subst hb hx hy
  refine ⟨⟨F ^ 2 * e2 * k ^ 2 - F * Y2 * k ^ 2 - 2 * F * b2 * e2 * k + F * e1 * k -
      4 * F * e2 * k + X2 * k + 2 * Y2 * b2 * k + 4 * Y2 * k + b2 ^ 2 * e2 - b2 * e1 +
      4 * b2 * e2 - 2 * e1 + 3 * e2, by ring⟩,
    ⟨F * e2 * k - Y2 * k - b2 * e2 + e1 - 2 * e2, by ring⟩⟩

/-- From the odd state `χ₁ ≡ −χ₂`, `ψ₁ ≡ ψ₂` to the even state `χ₁ ≡ χ₂`, `ψ₁ ≡ −ψ₂`. -/
theorem step_from_odd (F k b1 b2 X1 X2 Y1 Y2 e1 e2 : 𝔸) (hb : b1 = F * k - b2 - 4)
    (hx : X1 = F * e1 - X2) (hy : Y1 = Y2 + F * e2) :
    F ∣ ((b1 + 2) * X1 + (b1 + 1) * (b1 + 3) * Y1) -
        ((b2 + 2) * X2 + (b2 + 1) * (b2 + 3) * Y2) ∧
      F ∣ (X1 + (b1 + 2) * Y1) + (X2 + (b2 + 2) * Y2) := by
  subst hb hx hy
  refine ⟨⟨F ^ 2 * e2 * k ^ 2 + F * Y2 * k ^ 2 - 2 * F * b2 * e2 * k + F * e1 * k -
      4 * F * e2 * k - X2 * k - 2 * Y2 * b2 * k - 4 * Y2 * k + b2 ^ 2 * e2 - b2 * e1 +
      4 * b2 * e2 - 2 * e1 + 3 * e2, by ring⟩,
    ⟨F * e2 * k + Y2 * k - b2 * e2 + e1 - 2 * e2, by ring⟩⟩

end Ring

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing ArithmeticPellRecurrence

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## The recurrences in the ring of differences -/

theorem ιx_succ (t b : V) : (ι (xcoord (t + 1) b) : DiffRing V) =
    (ι b + 2) * ι (xcoord t b) + (ι b + 1) * (ι b + 3) * ι (ycoord t b) := by
  rw [x_succ]; unfold delta; simp only [map_add, map_mul, map_ofNat, map_one]

theorem ιy_succ (t b : V) : (ι (ycoord (t + 1) b) : DiffRing V) =
    ι (xcoord t b) + (ι b + 2) * ι (ycoord t b) := by
  rw [y_succ]; simp only [map_add, map_mul, map_ofNat]

/-- A signed difference with a natural modulus has natural quotients on both sides. -/
theorem two_sided {x y m : V} {q : DiffRing V} (h : ι x - ι y = ι m * q) :
    ∃ p p' : V, x + m * p = y + m * p' := by
  rcases nonneg_or_nonpos q with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · refine ⟨0, c, ?_⟩
    apply ι_injective
    simp only [map_add, map_mul, mul_zero, add_zero]
    linear_combination h
  · refine ⟨c, 0, ?_⟩
    apply ι_injective
    simp only [map_add, map_mul, mul_zero, add_zero]
    linear_combination h

/-! ## The odd alternating residue -/

/-- At even times, `χ ≡ 1` and `ψ ≡ −t (mod m)` for `m ∣ b + 3`. -/
theorem alt_even (b m : V) (hm : 0 < m) (hd : m ∣ b + 3) (j : V) :
    ∃ r1 r2 : V, xcoord (2 * j) b = 1 + m * r1 ∧ ycoord (2 * j) b + 2 * j = m * r2 := by
  induction j using ISigma1.sigma1_succ_induction
  · definability
  case zero => exact ⟨0, 0, by simp, by simp⟩
  case succ j ih =>
    obtain ⟨w, hw⟩ := hd
    obtain ⟨r1, r2, h1, h2⟩ := ih
    obtain ⟨r3, r4, h3, h4⟩ := P138FirstIndex.stepA b m w (2 * j) r1 r2 hm hw h1 h2
    obtain ⟨r5, r6, h5, h6⟩ := P138FirstIndex.stepB b m w (2 * j + 1) r3 r4 hm hw h3 h4
    refine ⟨r5, r6, ?_, ?_⟩
    · rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring]; exact h5
    · rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring]; exact h6

/-- **The odd alternating residue**: `ψ_b(2j + 1) ≡ 2j + 1 (mod m)` for `m ∣ b + 3`. -/
theorem alt_odd (b m : V) (hm : 0 < m) (hd : m ∣ b + 3) (j : V) :
    (ι m : DiffRing V) ∣ ι (ycoord (2 * j + 1) b) - ι (2 * j + 1) := by
  obtain ⟨r1, r2, h1, h2⟩ := alt_even b m hm hd j
  obtain ⟨w, hw⟩ := hd
  obtain ⟨-, r4, -, h4⟩ := P138FirstIndex.stepA b m w (2 * j) r1 r2 hm hw h1 h2
  refine ⟨ι r4, ?_⟩
  rw [h4]
  simp only [map_add, map_mul, map_one, map_ofNat]
  ring

/-! ## The negated base -/

/-- The negated base at even times. -/
theorem nb_even (b1 b2 F : V) (hF : 0 < F) (hk : F ∣ (b1 + 2) + (b2 + 2)) (j : V) :
    (∃ p p' : V, xcoord (2 * j) b1 + F * p = xcoord (2 * j) b2 + F * p') ∧
      ∃ r : V, ycoord (2 * j) b1 + ycoord (2 * j) b2 = F * r := by
  induction j using ISigma1.sigma1_succ_induction
  · definability
  case zero => exact ⟨⟨0, 0, by simp⟩, ⟨0, by simp⟩⟩
  case succ j ih =>
    obtain ⟨k, hkk⟩ := hk
    have hb : (ι b1 : DiffRing V) = ι F * ι k - ι b2 - 4 := by
      have := congrArg (ι (V := V)) hkk
      simp only [map_add, map_mul, map_ofNat] at this
      linear_combination this
    obtain ⟨⟨p, p', hp⟩, ⟨r, hr⟩⟩ := ih
    have hx : (ι (xcoord (2 * j) b1) : DiffRing V) =
        ι (xcoord (2 * j) b2) + ι F * (ι p' - ι p) := by
      have := congrArg (ι (V := V)) hp
      simp only [map_add, map_mul] at this
      linear_combination this
    have hy : (ι (ycoord (2 * j) b1) : DiffRing V) = ι F * ι r - ι (ycoord (2 * j) b2) := by
      have := congrArg (ι (V := V)) hr
      simp only [map_add, map_mul] at this
      linear_combination this
    obtain ⟨o1, o2⟩ := step_from_even _ _ _ _ _ _ _ _ _ _ hb hx hy
    rw [← ιx_succ, ← ιx_succ] at o1
    rw [← ιy_succ, ← ιy_succ] at o2
    obtain ⟨c1, hc1⟩ := o1
    obtain ⟨c2, hc2⟩ := o2
    have hx' : (ι (xcoord (2 * j + 1) b1) : DiffRing V) =
        ι F * c1 - ι (xcoord (2 * j + 1) b2) := by linear_combination hc1
    have hy' : (ι (ycoord (2 * j + 1) b1) : DiffRing V) =
        ι (ycoord (2 * j + 1) b2) + ι F * c2 := by linear_combination hc2
    obtain ⟨o3, o4⟩ := step_from_odd _ _ _ _ _ _ _ _ _ _ hb hx' hy'
    rw [← ιx_succ, ← ιx_succ] at o3
    rw [← ιy_succ, ← ιy_succ] at o4
    obtain ⟨c3, hc3⟩ := o3
    obtain ⟨c4, hc4⟩ := o4
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring]
    refine ⟨two_sided hc3, ?_⟩
    obtain ⟨r', hr'⟩ := P138FirstIndex.nat_quot hF (by
      have := ι_nonneg (ycoord (2 * j + 1 + 1) b1)
      have := ι_nonneg (ycoord (2 * j + 1 + 1) b2)
      linarith) hc4
    refine ⟨r', ?_⟩
    apply ι_injective
    simp only [map_add, map_mul]
    rw [← hr']
    exact hc4

/-- **The negated base at odd times**: `ψ_{b₁}(2j + 1) ≡ ψ_{b₂}(2j + 1) (mod F)` when
`F ∣ (b₁ + 2) + (b₂ + 2)`. -/
theorem nb_odd (b1 b2 F : V) (hF : 0 < F) (hk : F ∣ (b1 + 2) + (b2 + 2)) (j : V) :
    (ι F : DiffRing V) ∣ ι (ycoord (2 * j + 1) b1) - ι (ycoord (2 * j + 1) b2) := by
  obtain ⟨⟨p, p', hp⟩, ⟨r, hr⟩⟩ := nb_even b1 b2 F hF hk j
  obtain ⟨k, hkk⟩ := hk
  have hb : (ι b1 : DiffRing V) = ι F * ι k - ι b2 - 4 := by
    have := congrArg (ι (V := V)) hkk
    simp only [map_add, map_mul, map_ofNat] at this
    linear_combination this
  have hx : (ι (xcoord (2 * j) b1) : DiffRing V) =
      ι (xcoord (2 * j) b2) + ι F * (ι p' - ι p) := by
    have := congrArg (ι (V := V)) hp
    simp only [map_add, map_mul] at this
    linear_combination this
  have hy : (ι (ycoord (2 * j) b1) : DiffRing V) = ι F * ι r - ι (ycoord (2 * j) b2) := by
    have := congrArg (ι (V := V)) hr
    simp only [map_add, map_mul] at this
    linear_combination this
  have o2 := (step_from_even _ _ _ _ _ _ _ _ _ _ hb hx hy).2
  rw [← ιy_succ, ← ιy_succ] at o2
  exact o2

#print axioms alt_odd
#print axioms nb_even
#print axioms nb_odd

end DiophantineConsistency.ZRowsPellNegBase
