import GowersSzemeredi.Proofs18TightClassesFejer

/-! **The Fejér split classes with additive slack** (Notes L.16i).

`split_pair_with_bounds` proves `log₂ D_l ≤ (c+8)·2^l`, with a uniform slack
`8·2^l`. The recursion `D_{l+1} ≤ 2^(l+6)·a_l·(a_l + D_l)·P + T`, with
`P ≤ 2^(5l+20)` and `T ≤ 2^(5l+19)`, only needs the slack to grow
additively, by `5l + 22` per step:
* `fejer_split_step_quad`: the invariants `2^(l+6)·a_l ≤ 2^(14·2^l)` and
  `D_l ≤ 2^(14·2^l + 3(l+4)²)` propagate
  (`3(l+5)² − 3(l+4)² = 6l + 27 ≥ 5l + 22`);
* `split_pair_fejer_quad`: they hold in every dimension `l ≥ 2` from the
  seed `2^46` of `splitUniformClass_two_fejer`;
* `uDegQ l = 2^(14·2^l + 3(l+4)² + 2)` and `split_pair_fejer_le_uDegQ`;
* `polyCoverAt_classQ`: the class covers at degree `uDegQ l`.

Asymptotically the class constant is `14`, against `23` for `uDeg23`. This is
the first step of the `d + 5` / `L + 3` plan of Notes L.16i. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The exponent arithmetic of the step, with `2^k` and `(k+4)²` as atoms. -/
theorem quad_exponent_step (k : Nat) :
    14 * 2 ^ k + (14 * 2 ^ k + 3 * (k + 4) ^ 2) + (5 * k + 22) ≤
      14 * 2 ^ (k + 1) + 3 * (k + 1 + 4) ^ 2 := by
  have h1 : 3 * (k + 1 + 4) ^ 2 = 3 * (k + 4) ^ 2 + 6 * k + 27 := by ring
  have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  rw [h1, h2]
  omega

/-- **The invariants with additive slack propagate.** -/
theorem fejer_split_step_quad {k a D a' D' P T : Nat} (ha : 1 ≤ a)
    (hA : 2 ^ (k + 6) * a ≤ 2 ^ (14 * 2 ^ k)) (hDb : D ≤ 2 ^ (14 * 2 ^ k + 3 * (k + 4) ^ 2))
    (ha' : a' ≤ 2 ^ (k + 5) * (a * a)) (hD' : D' ≤ 2 ^ (k + 6) * (a * (a + D)) * P + T)
    (hP : P ≤ 2 ^ (5 * k + 20)) (hT : T ≤ 2 ^ (5 * k + 19)) :
    2 ^ (k + 1 + 6) * a' ≤ 2 ^ (14 * 2 ^ (k + 1)) ∧
      D' ≤ 2 ^ (14 * 2 ^ (k + 1) + 3 * (k + 1 + 4) ^ 2) := by
  constructor
  · calc 2 ^ (k + 1 + 6) * a' ≤ 2 ^ (k + 1 + 6) * (2 ^ (k + 5) * (a * a)) :=
          Nat.mul_le_mul_left _ ha'
      _ = (2 ^ (k + 6) * a) * (2 ^ (k + 6) * a) := by ring
      _ ≤ 2 ^ (14 * 2 ^ k) * 2 ^ (14 * 2 ^ k) := Nat.mul_le_mul hA hA
      _ = 2 ^ (14 * 2 ^ (k + 1)) := by rw [← pow_add, double_exponent 14 k]
  · set X := 2 ^ (14 * 2 ^ k) with hXdef
    set Y := 2 ^ (14 * 2 ^ k + 3 * (k + 4) ^ 2) with hYdef
    set Z := 2 ^ (5 * k + 19) with hZdef
    have haX : a ≤ X := le_trans (Nat.le_mul_of_pos_left a (Nat.two_pow_pos _)) hA
    have hXY : X ≤ Y := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hsum : a + D ≤ 2 * Y := by omega
    have e20 : 2 ^ (5 * k + 20) = 2 * Z := by
      rw [hZdef, show 5 * k + 20 = (5 * k + 19) + 1 by ring, pow_succ]; ring
    have hX1 : 1 ≤ X := Nat.one_le_two_pow
    have hY1 : 1 ≤ Y := Nat.one_le_two_pow
    have hprod : 8 * Z * X * Y = 2 ^ (14 * 2 ^ k + (14 * 2 ^ k + 3 * (k + 4) ^ 2) + (5 * k + 22)) := by
      rw [hXdef, hYdef, hZdef, pow_add, pow_add, show 5 * k + 22 = (5 * k + 19) + 3 by ring, pow_add]
      ring
    calc D' ≤ 2 ^ (k + 6) * (a * (a + D)) * P + T := hD'
      _ = (2 ^ (k + 6) * a) * (a + D) * P + T := by ring
      _ ≤ X * (2 * Y) * (2 * Z) + Z :=
          Nat.add_le_add (Nat.mul_le_mul (Nat.mul_le_mul hA hsum) (e20 ▸ hP)) hT
      _ ≤ 8 * Z * X * Y := split_step_arith _ _ _ hX1 hY1
      _ = _ := hprod
      _ ≤ 2 ^ (14 * 2 ^ (k + 1) + 3 * (k + 1 + 4) ^ 2) :=
          Nat.pow_le_pow_right (by norm_num) (quad_exponent_step k)

/-- **The refined split invariants in every dimension `l ≥ 2`**, from the
Fejér seed `2^46`. -/
theorem split_pair_fejer_quad : ∀ l, 2 ≤ l →
    1 ≤ (splitPairWith splitSeedFejer splitSeedFejer l).1 ∧
      1 ≤ (splitPairWith splitSeedFejer splitSeedFejer l).2 ∧
      2 ^ (l + 6) * (splitPairWith splitSeedFejer splitSeedFejer l).1 ≤ 2 ^ (14 * 2 ^ l) ∧
      (splitPairWith splitSeedFejer splitSeedFejer l).2 ≤ 2 ^ (14 * 2 ^ l + 3 * (l + 4) ^ 2) := by
  intro l hl
  induction l, hl using Nat.le_induction with
  | base =>
    rw [splitPairWith_two]
    unfold splitSeedFejer
    refine ⟨Nat.one_le_two_pow, Nat.one_le_two_pow, ?_, ?_⟩
    · rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
    · exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  | succ k hk ih =>
    obtain ⟨ha, hDp, hAb, hDb⟩ := ih
    rw [splitPairWith_succ _ _ hk]
    set a := (splitPairWith splitSeedFejer splitSeedFejer k).1
    set D := (splitPairWith splitSeedFejer splitSeedFejer k).2
    obtain ⟨h1, h2⟩ := fejer_split_step_quad ha hAb hDb (splitStepA_le ha)
      (splitStepDWith_le ha hDp (fejerStepP_ge k)) (fejerStepP_le k) (fejerStepT_le k)
    refine ⟨?_, ?_, h1, h2⟩
    · unfold splitStepA sCountN; omega
    · unfold splitStepDWith wCountW; omega

/-- The class degree with additive slack. -/
def uDegQ (l : Nat) : Nat := 2 ^ (14 * 2 ^ l + 3 * (l + 4) ^ 2 + 2)

/-- The Fejér split degrees fit `uDegQ`. -/
theorem split_pair_fejer_le_uDegQ {l : Nat} (hl : 2 ≤ l) :
    (splitPairWith splitSeedFejer splitSeedFejer l).1 +
      (splitPairWith splitSeedFejer splitSeedFejer l).2 + l + 1 ≤ uDegQ l := by
  obtain ⟨-, -, hA, hD⟩ := split_pair_fejer_quad l hl
  unfold uDegQ
  set a := (splitPairWith splitSeedFejer splitSeedFejer l).1
  set D := (splitPairWith splitSeedFejer splitSeedFejer l).2
  set Y := 2 ^ (14 * 2 ^ l + 3 * (l + 4) ^ 2) with hYdef
  have ha : a ≤ Y := by
    have h1 : a ≤ 2 ^ (14 * 2 ^ l) := le_trans (Nat.le_mul_of_pos_left a (Nat.two_pow_pos _)) hA
    exact h1.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hl1 : l + 1 ≤ Y := by
    have h1 : l + 1 ≤ 2 ^ (l + 1) := Nat.lt_two_pow_self.le
    have h2 : l + 1 ≤ 14 * 2 ^ l + 3 * (l + 4) ^ 2 := by
      have := Nat.lt_two_pow_self (n := l); omega
    exact h1.trans (Nat.pow_le_pow_right (by norm_num) h2)
  have h4 : 2 ^ (14 * 2 ^ l + 3 * (l + 4) ^ 2 + 2) = 4 * Y := by
    rw [hYdef, pow_add]; ring
  rw [h4]
  omega

/-- **The class cover in dimension `l` at degree `uDegQ l`.** -/
theorem polyCoverAt_classQ (Kc pc : Nat → Nat) (hK : ∀ k, 1 ≤ Kc k) (hp : ∀ k, 0 < pc k)
    (hlem : ∀ k, 1 ≤ k → AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor (Kc k)) (familyWidthDivisor k (pc k))))
    {l : Nat} (hl1 : 1 ≤ l) :
    PolyCoverAt l (uCount (classV Kc pc l) (uDegQ l)) (uExp (classV Kc pc l) (uDegQ l)) := by
  have hVl := one_le_classV Kc pc l
  rcases Nat.lt_or_ge l 2 with hl | hl
  · obtain rfl : l = 1 := by omega
    refine polyCoverAt_one_uniform_low hVl ?_
    unfold uDegQ
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  · obtain ⟨C⟩ := splitUniformClass_all_fejer Kc pc hK hp hlem l hl
    have hfit := split_pair_fejer_le_uDegQ hl
    have P0 := (C.toPower hVl).polyCoverAt (by omega) hVl (D := uDegQ l) (by omega) (by omega)
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
