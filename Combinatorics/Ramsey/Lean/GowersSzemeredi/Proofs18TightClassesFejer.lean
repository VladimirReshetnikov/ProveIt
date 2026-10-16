import GowersSzemeredi.Proofs18UniformCovers
import GowersSzemeredi.Proofs16SplitStepFejer

/-! **The class covers at degree `2^(23·2^l)` under the Fejér θ₁** (Notes L.16d).

The Fejér analogue of `Proofs18TightClasses`. The split classes of
`splitUniformClass_all_fejer` have degrees `(a_l, D_l)` with
`2^(l+6)·a_l ≤ 2^(14·2^l)` and `D_l ≤ 2^(22·2^l)`
(`split_pair_with_bounds 14`, `split_pair_fejer_bound`), against the printed
`68·2^l`. So:
* `uDeg23 l = 2^(23·2^l)` and `split_pair_fejer_le_uDeg23`:
  `a_l + D_l + l + 1 ≤ uDeg23 l`;
* `polyCoverAt_one_uniform_low`: the dimension-one cover at any degree
  `D ≥ 2^17`. The printed `polyCoverAt_one_uniform` asks for `2^132`, the
  dimension-two exponent; in dimension one the count is at most `w^(2^15)`
  and the inverse exponent at most `w^(2^17)`;
* `polyCoverAt_class23`: **the class cover in dimension `l` at degree
  `uDeg23 l`**, the input of the Section 18 envelope. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The class degree in dimension `l` under the Fejér θ₁. -/
def uDeg23 (l : Nat) : Nat := 2 ^ (23 * 2 ^ l)

/-- The Fejér split degrees fit `uDeg23`. -/
theorem split_pair_fejer_le_uDeg23 {l : Nat} (hl : 2 ≤ l) :
    (splitPairWith splitSeedFejer splitSeedFejer l).1 +
      (splitPairWith splitSeedFejer splitSeedFejer l).2 + l + 1 ≤ uDeg23 l := by
  have h14 := split_pair_with_bounds 14 (seedA := splitSeedFejer) (seedD := splitSeedFejer)
    Nat.one_le_two_pow Nat.one_le_two_pow
    (by unfold splitSeedFejer; rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by norm_num))
    (by unfold splitSeedFejer; exact Nat.pow_le_pow_right (by norm_num) (by norm_num)) l hl
  obtain ⟨-, -, hA, -⟩ := h14
  have hD := split_pair_fejer_bound l hl
  unfold uDeg23
  set a := (splitPairWith splitSeedFejer splitSeedFejer l).1
  set D := (splitPairWith splitSeedFejer splitSeedFejer l).2
  set E := 2 ^ l with hEdef
  have hE4 : 4 ≤ E := by
    rw [hEdef]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ l := Nat.pow_le_pow_right (by norm_num) hl
  have ha : a ≤ 2 ^ (22 * E) := by
    have h1 : a ≤ 2 ^ (14 * E) := le_trans (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)) hA
    exact h1.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hl1 : l + 1 ≤ 2 ^ (22 * E) := by
    have h1 : l + 1 ≤ 2 ^ (l + 1) := Nat.lt_two_pow_self.le
    have h2 : l + 1 ≤ 22 * E := by
      have := Nat.lt_two_pow_self (n := l); omega
    exact h1.trans (Nat.pow_le_pow_right (by norm_num) h2)
  have h4 : 4 * 2 ^ (22 * E) ≤ 2 ^ (23 * E) := by
    rw [show 23 * E = 2 + 22 * E + (E - 2) by omega, pow_add, pow_add]
    have : 1 ≤ 2 ^ (E - 2) := Nat.one_le_two_pow
    calc 4 * 2 ^ (22 * E) = 2 ^ 2 * 2 ^ (22 * E) * 1 := by norm_num
      _ ≤ 2 ^ 2 * 2 ^ (22 * E) * 2 ^ (E - 2) := Nat.mul_le_mul_left _ this
  omega

/-- **The class cover in dimension `l` at degree `uDeg23 l`.** -/
theorem polyCoverAt_class23 (Kc pc : Nat → Nat) (hK : ∀ k, 1 ≤ Kc k) (hp : ∀ k, 0 < pc k)
    (hlem : ∀ k, 1 ≤ k → AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor (Kc k)) (familyWidthDivisor k (pc k))))
    {l : Nat} (hl1 : 1 ≤ l) :
    PolyCoverAt l (uCount (classV Kc pc l) (uDeg23 l)) (uExp (classV Kc pc l) (uDeg23 l)) := by
  have hVl := one_le_classV Kc pc l
  rcases Nat.lt_or_ge l 2 with hl | hl
  · obtain rfl : l = 1 := by omega
    refine polyCoverAt_one_uniform_low hVl ?_
    unfold uDeg23
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  · obtain ⟨C⟩ := splitUniformClass_all_fejer Kc pc hK hp hlem l hl
    have hfit := split_pair_fejer_le_uDeg23 hl
    have P0 := (C.toPower hVl).polyCoverAt (by omega) hVl (D := uDeg23 l) (by omega) (by omega)
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
