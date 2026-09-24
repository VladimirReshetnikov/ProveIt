import Diophantine.Paper1982.Digits

/-!
# The canonical combined code (Section 4 of the affine-radix proofs)

For a power-of-two radix `B ≥ 4` and `S₂ = l + e q < B^(2L)`, the middle
mask `(l + e q) & θλ = 0`, where `θ = B − 4` and `λ = Σ_{i<2L} Bⁱ`, says
that all base-`B` digits of `S₂` are at most three. The mask has digit
`B − 4` in each of its low `2L` positions. The base-four congruence
`S₂ = V + t θ` then identifies those digits with the base-four digits of the
fixed index component `V`, provided `B − 4` exceeds both `S₂`'s and `V`'s
base-four value (`B ≥ 2·4^(2L+1)`).  This is Lemma 2.9 of the 1982 article
with radix `B = 2^m` and digit bound `4 = 2²`, applied to the digit list of
`V`; it does not depend on the rest of the system, so it serves every
version of the certificate whose coding equation `E45` and middle mask are
unchanged (the 95- to 91-operation systems).

`split_code` then recovers `l` and `e` separately from `S₂ = ofDigits B ys`
when `ys` is the concatenation of the two digit lists and `l < B^L`.
-/

namespace Jones1980

open Jones1982 (τ mask29)
open Nat

/-- `Σ_{i<k} Bⁱ`, as `ofDigits B (replicate k 1)`. -/
def geom (B k : ℕ) : ℕ := ofDigits B (List.replicate k 1)

theorem geom_zero (B : ℕ) : geom B 0 = 0 := by unfold geom; simp

theorem geom_succ (B k : ℕ) : geom B (k + 1) = 1 + geom B k * B := by
  unfold geom; rw [List.replicate_succ, ofDigits_cons, mul_comm]

/-- `geom B k · (B − 1) + 1 = B^k`. -/
theorem geom_mul_sub_one (B : ℕ) (hB : 1 ≤ B) : ∀ k, geom B k * (B - 1) + 1 = B ^ k
  | 0 => by simp [geom_zero]
  | k + 1 => by
    have ih := geom_mul_sub_one B hB k
    have e : geom B (k + 1) * (B - 1) = (B - 1) + B * (geom B k * (B - 1)) := by
      rw [geom_succ]; ring
    have h2 : B * (geom B k * (B - 1)) + B = B ^ k * B := by rw [← ih]; ring
    rw [e, pow_succ]; omega

/-- `mask29 B 4 k = (B − 4) · geom B k`. -/
theorem mask29_eq_geom (B : ℕ) : ∀ k, mask29 B 4 k = (B - 4) * geom B k
  | 0 => by simp [Jones1982.mask29_zero, geom_zero]
  | k + 1 => by rw [Jones1982.mask29_succ, geom_succ, mask29_eq_geom B k]; ring

/-- `θλ = mask29 B 4 (2L)` for `θ = B − 4` and `λ (B − 1) = B^(2L) − 1`. -/
theorem theta_lam_eq_mask {B θ lam L : ℕ} (hB : 5 ≤ B) (hθ : θ + 4 = B)
    (hlam : lam * (B - 1) = B ^ (2 * L) - 1) : θ * lam = mask29 B 4 (2 * L) := by
  have hg := geom_mul_sub_one B (by omega) (2 * L)
  have : lam = geom B (2 * L) := by
    have h : lam * (B - 1) = geom B (2 * L) * (B - 1) := by omega
    exact Nat.eq_of_mul_eq_mul_right (by omega) h
  rw [this, mask29_eq_geom]
  congr 1; omega

/-- The canonical combined code: the middle mask and the base-four congruence identify
`S₂` with the radix-`B` value of the base-four digit list of `V`. -/
theorem S2_eq_ofDigits {B m L S2 V θ lam t : ℕ} (hBm : B = 2 ^ m) (ys : List ℕ)
    (hys : ∀ y ∈ ys, y < 4) (hlen : ys.length ≤ 2 * L) (hV : V = ofDigits 4 ys)
    (hθ : θ + 4 = B) (hlam : lam * (B - 1) = B ^ (2 * L) - 1)
    (hH : 2 * 4 ^ (2 * L + 1) ≤ B)
    (hS2 : S2 < B ^ (2 * L)) (hmask : τ 2 S2 (θ * lam) = 0) (hE45 : S2 = V + t * θ) :
    S2 = ofDigits B ys := by
  have hB5 : 5 ≤ B := by
    have : 2 * 4 ^ 1 ≤ 2 * 4 ^ (2 * L + 1) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
    omega
  have hm2 : 2 ≤ m := by
    by_contra h; push Not at h
    interval_cases m <;> simp_all
  have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
  have key := Jones1982.lemma_2_9 (s := 2) (t := m) (n := 2 * L) (m := 2 * L) (k := 2 * L)
    (by norm_num) hm2 le_rfl le_rfl (by rw [← hBm]; simpa [h4] using hH)
    (ys := ys) (by simpa [h4] using hys) (by omega) S2
  rw [← hBm] at key
  apply key.2
  refine ⟨?_, ?_, ?_⟩
  · -- `S2 ≡ ofDigits 4 ys [MOD B − 4]`
    rw [← h4, ← hV, hE45]
    show (V + t * θ) % (B - 4) = V % (B - 4)
    have : θ = B - 4 := by omega
    rw [this, Nat.add_mul_mod_self_right]
  · calc S2 < B ^ (2 * L) := hS2
      _ ≤ 2 ^ 2 * B ^ (2 * L) := Nat.le_mul_of_pos_left _ (by norm_num)
  · rw [← h4, ← theta_lam_eq_mask hB5 hθ hlam]; exact hmask

/-- Splitting the concatenated code: `l + e B^L = l' + e' B^L` with `l, l' < B^L`
forces `l = l'` and `e = e'`. -/
theorem split_code {q l l' e e' : ℕ} (hq : 0 < q) (hl : l < q) (hl' : l' < q)
    (h : l + e * q = l' + e' * q) : l = l' ∧ e = e' := by
  have h1 : (l + e * q) % q = l := by rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hl]
  have h2 : (l' + e' * q) % q = l' := by rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hl']
  have hl_eq : l = l' := by rw [← h1, h, h2]
  refine ⟨hl_eq, ?_⟩
  subst hl_eq
  have := Nat.add_left_cancel h
  exact Nat.eq_of_mul_eq_mul_right hq this

/-- The value of a concatenated digit list. -/
theorem ofDigits_append_eq (B : ℕ) (l0 e0 : List ℕ) :
    ofDigits B (l0 ++ e0) = ofDigits B l0 + ofDigits B e0 * B ^ l0.length := by
  rw [ofDigits_append, mul_comm]

end Jones1980
