import DiophantineConsistency.P138.P138FirstIndex
import DiophantineConsistency.ModelProductPell
import DiophantineConsistency.ArithmeticPellCommonUnit
import DiophantineConsistency.ArithmeticPellResidueClasses

/-! # Small Lucas-sequence facts for the ten-integer certificate

Natural-number facts about `χ_b(n) = xcoord n b`, `ψ_b(n) = ycoord n b` in a model `V` of
`IΣ₁`, used by the signed square certificate of the ten-integer forms (`Z10Cert`).

* `x_two`, `x_two_add_one`: `χ_b(2) = (b+2)² + δ(b)` and `χ_b(2) + 1 = 2 (b+2)²`.
* `double_x_of_sq`: if the squares of the bases `b + 2` and `g + 2` agree modulo `m`, then
  `χ_b(2t) ≡ χ_g(2t) (mod m)`. This covers a base and its negative: Sun's `G ≡ −A/2 (mod F)`
  is used only through `G² ≡ (A/2)² (mod F)`. The proof composes the sequences with the unit
  of index two (`ArithmeticPellCommonUnit.composition`) and transfers the new base
  (`ModelProductPell.pp_base_transfer`).
* `y_add_two`: for `3 ∣ b + 2`, `ψ_b(t+2) + ψ_b(t) ≡ 0 (mod 3)`.
* `three_dvd_y`: for `3 ∣ b + 2`, `ψ_b(4j+3) ≡ −1 (mod 3)`; this fixes the sign of `C`.
* `even_of_sq`: a natural square `d² = 4k` has `d = 2s` with `s² = k`.
* `pm_trans`, `pm_symm`: composition of congruences up to sign in a commutative ring. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.Z10Lucas

section Ring
variable {R : Type*} [CommRing R]

/-- Congruences up to sign compose. -/
theorem pm_trans {m x y z : R} (h1 : m ∣ x - y ∨ m ∣ x + y) (h2 : m ∣ y - z ∨ m ∣ y + z) :
    m ∣ x - z ∨ m ∣ x + z := by
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · left; have := dvd_add h1 h2; rwa [show x - y + (y - z) = x - z by ring] at this
  · right; have := dvd_add h1 h2; rwa [show x - y + (y + z) = x + z by ring] at this
  · right; have := dvd_sub h1 h2; rwa [show x + y - (y - z) = x + z by ring] at this
  · left; have := dvd_sub h1 h2; rwa [show x + y - (y + z) = x - z by ring] at this

/-- Congruences up to sign are symmetric. -/
theorem pm_symm {m x y : R} (h : m ∣ x - y ∨ m ∣ x + y) : m ∣ y - x ∨ m ∣ y + x := by
  rcases h with h | h
  · left; have := dvd_neg.mpr h; rwa [show -(x - y) = y - x by ring] at this
  · right; rwa [add_comm] at h

end Ring

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing ZRowsCoprimeSquares ModelProductPell
open ArithmeticPellRecurrence

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem x_one (b : V) : xcoord 1 b = b + 2 := by simpa using x_succ (0 : V) b

theorem y_one (b : V) : ycoord 1 b = 1 := by simpa using y_succ (0 : V) b

theorem y_two (b : V) : ycoord 2 b = 2 * (b + 2) := by
  have h := y_succ (1 : V) b
  rw [one_add_one_eq_two, x_one, y_one] at h
  rw [h]; ring

theorem x_two (b : V) : xcoord 2 b = (b + 2) * (b + 2) + delta b := by
  have h := x_succ (1 : V) b
  rw [one_add_one_eq_two, x_one, y_one, mul_one] at h
  exact h

theorem x_two_add_one (b : V) : xcoord 2 b + 1 = 2 * ((b + 2) * (b + 2)) := by
  rw [x_two]; unfold delta; ring

/-- Bases with congruent squares have congruent abscissae at even indices. -/
theorem double_x_of_sq (b g m : V) (hm : 0 < m)
    (h : ((b + 2) * (b + 2)) % m = ((g + 2) * (g + 2)) % m) (t : V) :
    xcoord (2 * t) b % m = xcoord (2 * t) g % m := by
  have h2 : xcoord 2 b % m = xcoord 2 g % m := by
    apply ArithmeticPellResidueClasses.mod_add_cancel _ _ 1 _ hm
    rw [x_two_add_one, x_two_add_one]
    exact pp_mod_mul hm rfl h
  have hB : (b * b + 4 * b + 2 + delta b) + 2 = xcoord 2 b := by rw [x_two]; ring
  have hG : (g * g + 4 * g + 2 + delta g) + 2 = xcoord 2 g := by rw [x_two]; ring
  have hbase : ((b * b + 4 * b + 2 + delta b) + 2) % m =
      ((g * g + 4 * g + 2 + delta g) + 2) % m := by rw [hB, hG]; exact h2
  have ht := (pp_base_transfer _ _ m hm hbase t).1
  rw [(ArithmeticPellCommonUnit.composition _ b 2 hB t).1,
    (ArithmeticPellCommonUnit.composition _ g 2 hG t).1] at ht
  exact ht

/-- For `3 ∣ b + 2`: `ψ(t+2) + ψ(t) ≡ 0 (mod 3)`. -/
theorem y_add_two (b w t : V) (hw : b + 2 = 3 * w) :
    ∃ k : V, ycoord (t + 2) b + ycoord t b = 3 * k := by
  have hδ : delta b * ycoord t b + ycoord t b = (b + 2) * (b + 2) * ycoord t b := by
    unfold delta; ring
  refine ⟨w * (xcoord t b + ycoord (t + 1) b) + 3 * w * w * ycoord t b, ?_⟩
  calc ycoord (t + 2) b + ycoord t b
      = (b + 2) * (xcoord t b + ycoord (t + 1) b) +
          (delta b * ycoord t b + ycoord t b) := by
        rw [show t + 2 = (t + 1) + 1 by ring, y_succ (t + 1) b, x_succ t b]; ring
    _ = 3 * (w * (xcoord t b + ycoord (t + 1) b) + 3 * w * w * ycoord t b) := by
        rw [hδ, hw]; ring

/-- For `3 ∣ b + 2`: `ψ(4j+3) ≡ −1 (mod 3)`. -/
theorem three_dvd_y (b w : V) (hw : b + 2 = 3 * w) (j : V) :
    ∃ r : V, ycoord (4 * j + 3) b + 1 = 3 * r := by
  induction j using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    obtain ⟨k, hk⟩ := y_add_two b w 1 hw
    rw [y_one] at hk
    exact ⟨k, by rw [show (4 : V) * 0 + 3 = 1 + 2 by ring]; exact hk⟩
  case succ j ih =>
    obtain ⟨r, hr⟩ := ih
    obtain ⟨k1, h1⟩ := y_add_two b w (4 * j + 3 + 2) hw
    obtain ⟨k2, h2⟩ := y_add_two b w (4 * j + 3) hw
    rw [show 4 * (j + 1) + 3 = 4 * j + 3 + 2 + 2 by ring]
    have hd : (ι (3 : V) : DiffRing V) ∣ ι (ycoord (4 * j + 3 + 2 + 2) b + 1) := by
      refine ⟨ι k1 + ι r - ι k2, ?_⟩
      have e1 := congrArg (ι (V := V)) h1
      have e2 := congrArg (ι (V := V)) h2
      have e3 := congrArg (ι (V := V)) hr
      simp only [map_add, map_mul, map_one, map_ofNat] at e1 e2 e3 ⊢
      linear_combination e1 - e2 + e3
    obtain ⟨r', hr'⟩ := ι_dvd_iff.mp hd
    exact ⟨r', hr'⟩

/-- A natural square `d² = 4k` has an even root. -/
theorem even_of_sq (d k : V) (h : d * d = 4 * k) : ∃ s : V, d = 2 * s ∧ s * s = k := by
  obtain ⟨t, ht | ht⟩ := even_or_odd d
  · refine ⟨t, ht, ?_⟩
    apply ι_injective (V := V)
    have e := congrArg (ι (V := V)) h
    rw [ht] at e
    simp only [map_mul, map_ofNat] at e ⊢
    linarith
  · exfalso
    have hd : (ι (4 : V) : DiffRing V) ∣ 1 := by
      refine ⟨ι k - ι t * ι t - ι t, ?_⟩
      have e := congrArg (ι (V := V)) h
      rw [ht] at e
      simp only [map_add, map_mul, map_one, map_ofNat] at e ⊢
      linear_combination e
    have h0 := P138FirstIndex.eq_zero_of_dvd_small hd (by rw [abs_one, map_ofNat]; norm_num)
    exact one_ne_zero h0

#print axioms pm_trans
#print axioms double_x_of_sq
#print axioms three_dvd_y
#print axioms even_of_sq

end DiophantineConsistency.Z10Lucas
