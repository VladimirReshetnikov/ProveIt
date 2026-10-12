import GowersSzemeredi.Proofs18TightClassesFejerX

/-! **The exact class table to dimension `14`** (Notes L.16o).

`tDegX` uses the exact split degrees up to `l = 12` and the invariant at
class constant `5/2` beyond. Two more exact dimensions,
`⌈log₂(a_l + D_l + l + 1)⌉ = 20323, 40154` for `l = 13, 14` (kernel-evaluated,
`D₁₄ ≈ 2^40154`), lower the thresholds of `d + 2` and `L + 0` by one:
* `tDegZ`: the exact table up to `l = 14`, then `5·2^(l−1) + 3(l+4)² + 2`
  (`split_pair_small_half`);
* `split_pair_small_le_uDegZ`, `polyCoverAt_classZ`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The exact class log-degrees in dimensions `0, …, 14`. -/
def tTableZ : List Nat :=
  [17, 17, 49, 85, 136, 210, 326, 524, 881, 1550, 2841, 5371, 10375, 20323, 40154]

/-- The class log-degree: exact up to dimension `14`, constant `5/2` beyond. -/
def tDegZ (l : Nat) : Nat := if l ≤ 14 then tTableZ.getD l 0 else 5 * 2 ^ (l - 1) + 3 * (l + 4) ^ 2 + 2

/-- The class degree from the table to dimension `14`. -/
def uDegZ (l : Nat) : Nat := 2 ^ tDegZ l

theorem uDegZ_eq (l : Nat) : uDegZ l = 2 ^ tDegZ l := rfl

theorem tDegZ_eq_of_ge {l : Nat} (hl : 15 ≤ l) :
    tDegZ l = 5 * 2 ^ (l - 1) + 3 * (l + 4) ^ 2 + 2 := by
  unfold tDegZ; rw [if_neg (by omega)]

theorem seventeen_le_tDegZ (l : Nat) : 17 ≤ tDegZ l := by
  rcases Nat.lt_or_ge l 15 with h | h
  · interval_cases l <;> decide
  · rw [tDegZ_eq_of_ge h]
    have : 16 ≤ (l + 4) ^ 2 := by nlinarith
    omega

theorem tDegZ_le_succ (l : Nat) : tDegZ l ≤ tDegZ (l + 1) := by
  rcases Nat.lt_or_ge l 15 with h | h
  · interval_cases l <;> decide
  · rw [tDegZ_eq_of_ge h, tDegZ_eq_of_ge (by omega)]
    have h1 : 2 ^ (l - 1) ≤ 2 ^ (l + 1 - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : (l + 4) ^ 2 ≤ (l + 1 + 4) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega

theorem tDegZ_mono {l k : Nat} (hl : l ≤ k) : tDegZ l ≤ tDegZ k := by
  induction k, hl using Nat.le_induction with
  | base => exact le_rfl
  | succ k _ ih => exact ih.trans (tDegZ_le_succ k)

theorem uDegZ_le_pow {l k : Nat} (hl : l ≤ k) : uDegZ l ≤ 2 ^ tDegZ k := by
  rw [uDegZ_eq]; exact Nat.pow_le_pow_right (by norm_num) (tDegZ_mono hl)

/-- The η side condition `3(k+4)²` fits the class degree. -/
theorem sq_le_three_tDegZ (k : Nat) : 3 * (k + 4) ^ 2 ≤ 3 * tDegZ k + 5 * k + 37 := by
  rcases Nat.lt_or_ge k 15 with h | h
  · interval_cases k <;> decide
  · rw [tDegZ_eq_of_ge h]; omega

/-- **The split degrees fit `uDegZ`**, kernel-evaluated up to dimension `14`. -/
theorem split_pair_small_le_uDegZ {l : Nat} (hl : 2 ≤ l) :
    (splitPairWith splitSeedSmallA splitSeedSmallD l).1 +
      (splitPairWith splitSeedSmallA splitSeedSmallD l).2 + l + 1 ≤ uDegZ l := by
  rcases Nat.lt_or_ge l 15 with h | h
  · interval_cases l <;> decide +kernel
  · have h1 := split_pair_small_le_uDegX hl
    have h2 : uDegX l = uDegZ l := by
      unfold uDegX uDegZ; rw [tDegX_eq_of_ge (by omega), tDegZ_eq_of_ge h]
    rwa [h2] at h1

/-- **The class cover in dimension `l` at degree `uDegZ l`.** -/
theorem polyCoverAt_classZ (Kc pc : Nat → Nat) (hK : ∀ k, 1 ≤ Kc k) (hp : ∀ k, 0 < pc k)
    (hlem : ∀ k, 1 ≤ k → AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor (Kc k)) (familyWidthDivisor k (pc k))))
    {l : Nat} (hl1 : 1 ≤ l) :
    PolyCoverAt l (uCount (classV Kc pc l) (uDegZ l)) (uExp (classV Kc pc l) (uDegZ l)) := by
  have hVl := one_le_classV Kc pc l
  rcases Nat.lt_or_ge l 2 with hl | hl
  · obtain rfl : l = 1 := by omega
    refine polyCoverAt_one_uniform_low hVl ?_
    unfold uDegZ
    exact Nat.pow_le_pow_right (by norm_num) (seventeen_le_tDegZ 1)
  · obtain ⟨C⟩ := splitUniformClass_all_small Kc pc hK hp hlem l hl
    have hfit := split_pair_small_le_uDegZ hl
    have P0 := (C.toPower hVl).polyCoverAt (by omega) hVl (D := uDegZ l) (by omega) (by omega)
      (by omega)
    refine P0.weaken ?_ ?_ ?_
    · intro g t s hg hg1 ht ht1 hs hs1
      rw [uCount_eq hVl _ hg hg1 ht ht1 hs hs1]
    · intro g t s _ _ _ _ _ _
      exact (uExp_pos_le _ _ g t s).1
    · intro g t s hg hg1 ht ht1 hs hs1
      show (uCount _ _ g t s)⁻¹ ≤ _
      rw [uCount_eq hVl _ hg hg1 ht ht1 hs hs1]

end LeanProofs.GowersSzemeredi
