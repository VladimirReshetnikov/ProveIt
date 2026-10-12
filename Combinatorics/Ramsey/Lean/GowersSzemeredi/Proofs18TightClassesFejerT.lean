import GowersSzemeredi.Proofs18TightClassesFejerS

/-! **The exact small-dimension class degrees** (Notes L.16k).

The invariant of `Proofs18TightClassesFejerS` bounds the class degree by
`4·2^l + 3(l+4)² + 32`. In small dimensions the additive slack `3(l+4)² + 32`
dominates, and it alone keeps `d + 5` and `L + 3` from small degrees. The
split degrees `splitPairWith 32 (2^48) l` are explicit numbers, and up to
`l = 12` the kernel evaluates them (`decide +kernel`):
* `tDeg l`: the table `17, 49, 85, 136, 210, 326, 524, 881, 1550, 2841,
  5371, 10375` for `l = 1, …, 12`, and `4·2^l + 3(l+4)² + 32` beyond. Each
  entry is `⌈log₂(a_l + D_l + l + 1)⌉`, and `2^17` covers dimension one;
* `split_pair_small_le_uDegT`: the split degrees fit `uDegT l = 2^tDeg l`;
* `tDeg_mono`, `seventeen_le_tDeg`, `tDeg_eq_of_ge`;
* `polyCoverAt_classT`: the class covers at degree `uDegT l`.

The ratio `tDeg l / 2^l` peaks at `12.25` at `l = 2` and falls to `2.5` at
`l = 12`, against `39` and `4.2` for `sDeg`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The exact class log-degrees in dimensions `0, …, 12`. -/
def tTable : List Nat := [17, 17, 49, 85, 136, 210, 326, 524, 881, 1550, 2841, 5371, 10375]

/-- The class log-degree: exact up to dimension `12`, the invariant beyond. -/
def tDeg (l : Nat) : Nat := if l ≤ 12 then tTable.getD l 0 else 4 * 2 ^ l + 3 * (l + 4) ^ 2 + 32

/-- The class degree from the exact table. -/
def uDegT (l : Nat) : Nat := 2 ^ tDeg l

theorem tDeg_eq_of_ge {l : Nat} (hl : 13 ≤ l) : tDeg l = 4 * 2 ^ l + 3 * (l + 4) ^ 2 + 32 := by
  unfold tDeg; rw [if_neg (by omega)]

theorem seventeen_le_tDeg (l : Nat) : 17 ≤ tDeg l := by
  rcases Nat.lt_or_ge l 13 with h | h
  · interval_cases l <;> decide
  · rw [tDeg_eq_of_ge h]; omega

theorem tDeg_le_succ (l : Nat) : tDeg l ≤ tDeg (l + 1) := by
  rcases Nat.lt_or_ge l 13 with h | h
  · interval_cases l <;> decide
  · rw [tDeg_eq_of_ge h, tDeg_eq_of_ge (by omega)]
    have h1 : 2 ^ l ≤ 2 ^ (l + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : (l + 4) ^ 2 ≤ (l + 1 + 4) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega

theorem tDeg_mono {l k : Nat} (hl : l ≤ k) : tDeg l ≤ tDeg k := by
  induction k, hl using Nat.le_induction with
  | base => exact le_rfl
  | succ k _ ih => exact ih.trans (tDeg_le_succ k)

/-- **The split degrees fit the exact table**, kernel-evaluated up to
dimension `12`. -/
theorem split_pair_small_le_uDegT {l : Nat} (hl : 2 ≤ l) :
    (splitPairWith splitSeedSmallA splitSeedSmallD l).1 +
      (splitPairWith splitSeedSmallA splitSeedSmallD l).2 + l + 1 ≤ uDegT l := by
  rcases Nat.lt_or_ge l 13 with h | h
  · interval_cases l <;> decide +kernel
  · have h1 := split_pair_small_le_uDegS hl
    unfold uDegS at h1
    unfold uDegT
    rw [tDeg_eq_of_ge h]
    exact h1

/-- **The class cover in dimension `l` at degree `uDegT l`.** -/
theorem polyCoverAt_classT (Kc pc : Nat → Nat) (hK : ∀ k, 1 ≤ Kc k) (hp : ∀ k, 0 < pc k)
    (hlem : ∀ k, 1 ≤ k → AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor (Kc k)) (familyWidthDivisor k (pc k))))
    {l : Nat} (hl1 : 1 ≤ l) :
    PolyCoverAt l (uCount (classV Kc pc l) (uDegT l)) (uExp (classV Kc pc l) (uDegT l)) := by
  have hVl := one_le_classV Kc pc l
  rcases Nat.lt_or_ge l 2 with hl | hl
  · obtain rfl : l = 1 := by omega
    refine polyCoverAt_one_uniform_low hVl ?_
    unfold uDegT
    exact Nat.pow_le_pow_right (by norm_num) (seventeen_le_tDeg 1)
  · obtain ⟨C⟩ := splitUniformClass_all_small Kc pc hK hp hlem l hl
    have hfit := split_pair_small_le_uDegT hl
    have P0 := (C.toPower hVl).polyCoverAt (by omega) hVl (D := uDegT l) (by omega) (by omega)
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
