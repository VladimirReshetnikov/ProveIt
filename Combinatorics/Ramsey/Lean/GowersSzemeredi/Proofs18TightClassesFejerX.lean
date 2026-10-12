import GowersSzemeredi.Proofs18FejerEnvelopeBaseW

/-! **The split invariant at class constant `5/2` from the exact twelfth
dimension** (Notes L.16n).

The invariant of `Proofs18TightClassesFejerS` starts at dimension two and
carries the constant `4`. The true class constant is about `2.4`. Started
from the exact split degrees at `l = 12` (`2^18·a₁₂ < 2^9885`,
`D₁₂ < 2^10376`), the same step propagates the constant `5/2`:
* `split_step_gen`: the split step at any exponent `e` and slack `s`,
  `2^(k+6)·a ≤ 2^e`, `D ≤ 2^(e+s)` ⟹ `2^(k+7)·a′ ≤ 2^(2e)`,
  `D′ ≤ 2^(2e + s + 5k + 22)`;
* `split_pair_small_half`: `2^(l+6)·a_l ≤ 2^(5·2^(l−1))` and
  `D_l ≤ 2^(5·2^(l−1) + 3(l+4)²)` for every `l ≥ 12`, with the base case
  kernel-evaluated;
* `tDegX`: the exact table up to `l = 12`, then `5·2^(l−1) + 3(l+4)² + 2`;
  `split_pair_small_le_uDegX`, `polyCoverAt_classX`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- **The split step at any exponent and slack.** -/
theorem split_step_gen {k a D a' D' P T e s : Nat} (ha : 1 ≤ a)
    (hA : 2 ^ (k + 6) * a ≤ 2 ^ e) (hDb : D ≤ 2 ^ (e + s))
    (ha' : a' ≤ 2 ^ (k + 5) * (a * a)) (hD' : D' ≤ 2 ^ (k + 6) * (a * (a + D)) * P + T)
    (hP : P ≤ 2 ^ (5 * k + 20)) (hT : T ≤ 2 ^ (5 * k + 19)) :
    2 ^ (k + 1 + 6) * a' ≤ 2 ^ (2 * e) ∧ D' ≤ 2 ^ (2 * e + s + (5 * k + 22)) := by
  constructor
  · calc 2 ^ (k + 1 + 6) * a' ≤ 2 ^ (k + 1 + 6) * (2 ^ (k + 5) * (a * a)) :=
          Nat.mul_le_mul_left _ ha'
      _ = (2 ^ (k + 6) * a) * (2 ^ (k + 6) * a) := by ring
      _ ≤ 2 ^ e * 2 ^ e := Nat.mul_le_mul hA hA
      _ = 2 ^ (2 * e) := by rw [← pow_add, two_mul]
  · set X := 2 ^ e with hXdef
    set Y := 2 ^ (e + s) with hYdef
    set Z := 2 ^ (5 * k + 19) with hZdef
    have haX : a ≤ X := le_trans (Nat.le_mul_of_pos_left a (Nat.two_pow_pos _)) hA
    have hXY : X ≤ Y := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hsum : a + D ≤ 2 * Y := by omega
    have e20 : 2 ^ (5 * k + 20) = 2 * Z := by
      rw [hZdef, show 5 * k + 20 = (5 * k + 19) + 1 by ring, pow_succ]; ring
    have hX1 : 1 ≤ X := Nat.one_le_two_pow
    have hY1 : 1 ≤ Y := Nat.one_le_two_pow
    have hprod : 8 * Z * X * Y = 2 ^ (2 * e + s + (5 * k + 22)) := by
      rw [hXdef, hYdef, hZdef, show 2 * e + s + (5 * k + 22) = e + (e + s) + ((5 * k + 19) + 3) by ring,
        pow_add, pow_add, pow_add]
      ring
    calc D' ≤ 2 ^ (k + 6) * (a * (a + D)) * P + T := hD'
      _ = (2 ^ (k + 6) * a) * (a + D) * P + T := by ring
      _ ≤ X * (2 * Y) * (2 * Z) + Z :=
          Nat.add_le_add (Nat.mul_le_mul (Nat.mul_le_mul hA hsum) (e20 ▸ hP)) hT
      _ ≤ 8 * Z * X * Y := split_step_arith _ _ _ hX1 hY1
      _ = _ := hprod

/-- The exact twelfth dimension fits the invariant at constant `5/2`. -/
theorem split_pair_twelve_half :
    2 ^ (12 + 6) * (splitPairWith splitSeedSmallA splitSeedSmallD 12).1 ≤ 2 ^ (5 * 2 ^ (12 - 1)) ∧
      (splitPairWith splitSeedSmallA splitSeedSmallD 12).2 ≤
        2 ^ (5 * 2 ^ (12 - 1) + 3 * (12 + 4) ^ 2) := by
  constructor <;> decide +kernel

/-- **The split invariants at class constant `5/2` in every dimension `l ≥ 12`.** -/
theorem split_pair_small_half : ∀ l, 12 ≤ l →
    1 ≤ (splitPairWith splitSeedSmallA splitSeedSmallD l).1 ∧
      1 ≤ (splitPairWith splitSeedSmallA splitSeedSmallD l).2 ∧
      2 ^ (l + 6) * (splitPairWith splitSeedSmallA splitSeedSmallD l).1 ≤ 2 ^ (5 * 2 ^ (l - 1)) ∧
      (splitPairWith splitSeedSmallA splitSeedSmallD l).2 ≤
        2 ^ (5 * 2 ^ (l - 1) + 3 * (l + 4) ^ 2) := by
  intro l hl
  induction l, hl using Nat.le_induction with
  | base =>
    obtain ⟨ha, hD, -, -⟩ := split_pair_small_quad 12 (by norm_num)
    exact ⟨ha, hD, split_pair_twelve_half⟩
  | succ k hk ih =>
    obtain ⟨ha, hDp, hAb, hDb⟩ := ih
    rw [splitPairWith_succ _ _ (by omega)]
    set a := (splitPairWith splitSeedSmallA splitSeedSmallD k).1
    set D := (splitPairWith splitSeedSmallA splitSeedSmallD k).2
    obtain ⟨h1, h2⟩ := split_step_gen ha hAb hDb (splitStepA_le ha)
      (splitStepDWith_le ha hDp (fejerStepP_ge k)) (fejerStepP_le k) (fejerStepT_le k)
    have he : 2 * (5 * 2 ^ (k - 1)) = 5 * 2 ^ (k + 1 - 1) := by
      rw [show k + 1 - 1 = (k - 1) + 1 by omega, pow_succ]; ring
    refine ⟨?_, ?_, he ▸ h1, h2.trans (Nat.pow_le_pow_right (by norm_num) ?_)⟩
    · unfold splitStepA sCountN; omega
    · unfold splitStepDWith wCountW; omega
    · have hs : 3 * (k + 1 + 4) ^ 2 = 3 * (k + 4) ^ 2 + 6 * k + 27 := by ring
      rw [← he, hs]
      omega

/-- The class log-degree: exact up to dimension `12`, constant `5/2` beyond. -/
def tDegX (l : Nat) : Nat := if l ≤ 12 then tTable.getD l 0 else 5 * 2 ^ (l - 1) + 3 * (l + 4) ^ 2 + 2

/-- The class degree at constant `5/2`. -/
def uDegX (l : Nat) : Nat := 2 ^ tDegX l

theorem uDegX_eq (l : Nat) : uDegX l = 2 ^ tDegX l := rfl

theorem tDegX_eq_of_ge {l : Nat} (hl : 13 ≤ l) :
    tDegX l = 5 * 2 ^ (l - 1) + 3 * (l + 4) ^ 2 + 2 := by
  unfold tDegX; rw [if_neg (by omega)]

theorem seventeen_le_tDegX (l : Nat) : 17 ≤ tDegX l := by
  rcases Nat.lt_or_ge l 13 with h | h
  · interval_cases l <;> decide
  · rw [tDegX_eq_of_ge h]
    have : 16 ≤ (l + 4) ^ 2 := by nlinarith
    omega

theorem tDegX_le_succ (l : Nat) : tDegX l ≤ tDegX (l + 1) := by
  rcases Nat.lt_or_ge l 13 with h | h
  · interval_cases l <;> decide
  · rw [tDegX_eq_of_ge h, tDegX_eq_of_ge (by omega)]
    have h1 : 2 ^ (l - 1) ≤ 2 ^ (l + 1 - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : (l + 4) ^ 2 ≤ (l + 1 + 4) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega

theorem tDegX_mono {l k : Nat} (hl : l ≤ k) : tDegX l ≤ tDegX k := by
  induction k, hl using Nat.le_induction with
  | base => exact le_rfl
  | succ k _ ih => exact ih.trans (tDegX_le_succ k)

theorem uDegX_le_pow {l k : Nat} (hl : l ≤ k) : uDegX l ≤ 2 ^ tDegX k := by
  rw [uDegX_eq]; exact Nat.pow_le_pow_right (by norm_num) (tDegX_mono hl)

/-- The η side condition `3(k+4)²` fits the class degree. -/
theorem sq_le_three_tDegX (k : Nat) : 3 * (k + 4) ^ 2 ≤ 3 * tDegX k + 5 * k + 37 := by
  rcases Nat.lt_or_ge k 13 with h | h
  · interval_cases k <;> decide
  · rw [tDegX_eq_of_ge h]; omega

/-- **The split degrees fit `uDegX`.** -/
theorem split_pair_small_le_uDegX {l : Nat} (hl : 2 ≤ l) :
    (splitPairWith splitSeedSmallA splitSeedSmallD l).1 +
      (splitPairWith splitSeedSmallA splitSeedSmallD l).2 + l + 1 ≤ uDegX l := by
  rcases Nat.lt_or_ge l 13 with h | h
  · have h1 := split_pair_small_le_uDegT hl
    have h2 : uDegT l = uDegX l := by
      unfold uDegT uDegX tDeg tDegX; rw [if_pos (by omega), if_pos (by omega)]
    rwa [h2] at h1
  · obtain ⟨-, -, hA, hD⟩ := split_pair_small_half l (by omega)
    unfold uDegX
    rw [tDegX_eq_of_ge h]
    set a := (splitPairWith splitSeedSmallA splitSeedSmallD l).1
    set D := (splitPairWith splitSeedSmallA splitSeedSmallD l).2
    set Y := 2 ^ (5 * 2 ^ (l - 1) + 3 * (l + 4) ^ 2) with hYdef
    have ha : a ≤ Y := by
      have h1 : a ≤ 2 ^ (5 * 2 ^ (l - 1)) :=
        le_trans (Nat.le_mul_of_pos_left a (Nat.two_pow_pos _)) hA
      exact h1.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hl1 : l + 1 ≤ Y := by
      have h1 : l + 1 ≤ 2 ^ (l + 1) := Nat.lt_two_pow_self.le
      have h2 : l + 1 ≤ 5 * 2 ^ (l - 1) + 3 * (l + 4) ^ 2 := by
        have : l + 1 ≤ (l + 4) ^ 2 := by nlinarith
        omega
      exact h1.trans (Nat.pow_le_pow_right (by norm_num) h2)
    have h4 : 2 ^ (5 * 2 ^ (l - 1) + 3 * (l + 4) ^ 2 + 2) = 4 * Y := by
      rw [hYdef, pow_add]; ring
    rw [h4]
    omega

/-- **The class cover in dimension `l` at degree `uDegX l`.** -/
theorem polyCoverAt_classX (Kc pc : Nat → Nat) (hK : ∀ k, 1 ≤ Kc k) (hp : ∀ k, 0 < pc k)
    (hlem : ∀ k, 1 ≤ k → AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor (Kc k)) (familyWidthDivisor k (pc k))))
    {l : Nat} (hl1 : 1 ≤ l) :
    PolyCoverAt l (uCount (classV Kc pc l) (uDegX l)) (uExp (classV Kc pc l) (uDegX l)) := by
  have hVl := one_le_classV Kc pc l
  rcases Nat.lt_or_ge l 2 with hl | hl
  · obtain rfl : l = 1 := by omega
    refine polyCoverAt_one_uniform_low hVl ?_
    unfold uDegX
    exact Nat.pow_le_pow_right (by norm_num) (seventeen_le_tDegX 1)
  · obtain ⟨C⟩ := splitUniformClass_all_small Kc pc hK hp hlem l hl
    have hfit := split_pair_small_le_uDegX hl
    have P0 := (C.toPower hVl).polyCoverAt (by omega) hVl (D := uDegX l) (by omega) (by omega)
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
