import GowersSzemeredi.Proofs15FejerSelection
import GowersSzemeredi.Proofs15ProductToRestriction

/-! **Lemma 15.6 with the Fejér exponent** (Notes L.16).

Lemma 15.6 turns the product property into a large restriction on which
almost every 8-arrangement is respected. Its arrangement density
`(βγ/2)^(2^(2^(k+5)))` is the source of the printed `θ₁` of Section 16.
The proof applies Lemma 15.5 at `α = β^(7·4^(k+1))·γ^(21k·4^(k+1))`,
`η = 2^(−44)`, and dominates every exponent by `2^(3k+7)` times the Lemma 15.5
exponent (`lemma156_scale_ratio_bound`). With the Fejér Lemma 15.5
(`fejer_arrangement_restriction`) the same proof gives the single-exponential
density `(βγ/2)^(fejerProductExponent k)`, where
`fejerProductExponent k = 2^(3k+7)·2^(k+4)·(k+6)`
(`fejer_product_restriction`). This implies the printed Lemma 15.6
(`lemma_15_6_of_fejer_product`), since
`fejerProductExponent k ≤ 2^(5k+14) ≤ 2^(2^(k+5))`.

`fejer_product_of_density_lower`, `fejer_product_restriction` and
`lemma_15_6_of_fejer_product` are in `Proofs15FejerProductSide`, outside the
final route. -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

/-- The arrangement exponent of Lemma 15.6 after the Fejér selection. -/
def fejerProductExponent (k : Nat) : Nat := 2 ^ (3 * k + 7) * fejerSelectionExponent k

/-- The Fejér exponent of Lemma 15.6 is single-exponential: at most
`2^(5k+14)`, against the printed `2^(2^(k+5))`. -/
theorem fejerProductExponent_le (k : Nat) :
    fejerProductExponent k ≤ 2 ^ (5 * k + 14) := by
  unfold fejerProductExponent fejerSelectionExponent
  have hk : k + 6 ≤ 2 ^ (k + 3) := by
    have := Nat.lt_two_pow_self (n := k)
    have e : 2 ^ (k + 3) = 8 * 2 ^ k := by rw [pow_add]; ring
    rw [e]
    have := Nat.one_le_two_pow (n := k)
    omega
  calc 2 ^ (3 * k + 7) * (2 ^ (k + 4) * (k + 6))
      ≤ 2 ^ (3 * k + 7) * (2 ^ (k + 4) * 2 ^ (k + 3)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hk)
    _ = 2 ^ (5 * k + 14) := by rw [← pow_add, ← pow_add]; congr 1; omega

/-! ### The density-uniform form used by Lemma 16.4 -/

theorem fejer_coefficient_without_density_factor (k : Nat) (hk : 1 ≤ k)
    {beta gamma : Real} (hb : 0 < beta) (hb1 : beta ≤ 1)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    (beta * gamma / 2) ^ fejerProductExponent k ≤
      (beta ^ (7 * 4 ^ (k + 1)) * gamma ^ (21 * k * 4 ^ (k + 1)) *
        ((2 : Real)⁻¹ ^ 44) / 4) ^ fejerSelectionExponent k := by
  have hT (A : Nat) (h : A ≤ 2 ^ (3 * k + 7)) :
      A * fejerSelectionExponent k ≤ fejerProductExponent k := Nat.mul_le_mul_right _ h
  rw [div_eq_mul_inv, mul_pow, mul_pow, mul_div_assoc,
    show (2 : Real)⁻¹ ^ 44 / 4 = (2 : Real)⁻¹ ^ 46 by norm_num, mul_pow, mul_pow,
    ← pow_mul, ← pow_mul, ← pow_mul]
  gcongr ?_ * ?_ * ?_
  · exact pow_le_pow_of_le_one hb.le hb1
      (hT _ (by have := lemma156_beta_base_exponent k hk; omega))
  · exact pow_le_pow_of_le_one hg.le hg1 (hT _ (lemma156_gamma_base_exponent k))
  · exact pow_le_pow_of_le_one (by norm_num) (by norm_num)
      (hT _ (lemma156_constant_base_exponent k))

/-- The explicit threshold of the density-uniform Fejér Lemma 15.6: the Fejér
selection threshold at `α = β^(7·4^(k+1))·γ^(21k·4^(k+1))`, `η = 2^(−44)`,
scale 1. -/
def fejerProductThreshold (k : Nat) (beta gamma : Real) : Real :=
  fejerExplicitThreshold k (beta ^ (7 * 4 ^ (k + 1)) * gamma ^ (21 * k * 4 ^ (k + 1))) 1
    ((2 : Real)⁻¹ ^ 44)

/-- **The Fejér Lemma 15.6 with a density lower bound, explicit threshold**: the
threshold depends only on a lower bound `β` for the density of `B`. This is the form that
Lemma 16.4 consumes (`lemma_15_6_of_density_lower`), with
`fejerProductExponent k ≤ 2^(5k+14)` in place of `2^(2^(k+5))`. -/
theorem fejer_product_of_density_lower_explicit (k : Nat) (beta gamma : Real)
    (hk : 1 ≤ k) (hb : 0 < beta) (hb1 : beta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    ∀ (N : Nat) [NeZero N], fejerProductThreshold k beta gamma ≤ (N : Real) →
      N.Prime → Odd N →
      ∀ (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N),
        beta * (N : Real) ^ (k + 1) ≤ B.card → HasProductProperty B phi gamma →
        ∃ B' : Finset (Point N (k + 1)), B' ⊆ B ∧
          (beta * gamma / 2) ^ fejerProductExponent k * (N : Real) ^ (17 * k + 15) ≤
            generalArrangementCount 8 B' ∧
          (1 - (2 : Real)⁻¹ ^ 44) * generalArrangementCount 8 B' ≤
            respectedGeneralArrangementCount 8 B' phi := by
  intro N _ hN hp ho B phi hB hprod
  let alpha := beta ^ (7 * 4 ^ (k + 1)) * gamma ^ (21 * k * 4 ^ (k + 1))
  have hNp : 0 < (N : Real) ^ (k + 1) := pow_pos (by exact_mod_cast NeZero.pos N) _
  let b : Real := (B.card : Real) / (N : Real) ^ (k + 1)
  have hbb : beta ≤ b := (le_div_iff₀ hNp).mpr hB
  have hbpos : 0 < b := hb.trans_le hbb
  have hcard : (B.card : Real) = b * (N : Real) ^ (k + 1) := (div_mul_cancel₀ _ hNp.ne').symm
  have hbupper : b ≤ 1 := (div_le_one hNp).mpr (by exact_mod_cast (show B.card ≤ N ^ (k + 1) by
    simpa [Point, ZMod.card] using Finset.card_le_univ B))
  have hu : (generalArrangementCount 8 B : Real) ≤ 1 * (N : Real) ^ (17 * k + 15) :=
    (selection_arrangement_real_upper b B hcard).trans
      (mul_le_mul_of_nonneg_right (pow_le_one₀ hbpos.le hbupper) (by positivity))
  have hl : alpha * 1 * (N : Real) ^ (17 * k + 15) ≤ respectedGeneralArrangementCount 8 B phi :=
    le_trans (by simp only [alpha, mul_one]; gcongr)
      (lemma_14_8_holds N k b gamma B phi hk hbpos hg hg1 hcard hprod)
  obtain ⟨B', hsub, hcount, hrespect⟩ := fejer_scale_estimate_explicit k alpha 1
    ((2 : Real)⁻¹ ^ 44) hk (by positivity) one_pos (by positivity)
    (pow_le_one₀ (by norm_num) (by norm_num)) N hN hp ho B phi hu hl
  exact ⟨B', hsub, (mul_le_mul_of_nonneg_right (fejer_coefficient_without_density_factor k hk
    hb hb1 hg hg1) (by positivity)).trans (by simpa [alpha] using hcount), hrespect⟩

end LeanProofs.GowersSzemeredi
