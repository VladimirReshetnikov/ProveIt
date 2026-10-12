import GowersSzemeredi.Proofs18TightClassesFejerQ
import GowersSzemeredi.Proofs16UniformCoverTwoSplit

/-! **The Fejér split classes from the small dimension-two seed** (Notes L.16j).

`splitUniformClass_two_small` gives dimension two at family exponent
`a₂ = 32` and parameter degree `D₂ = 2^48`. The split recursion squares the
family exponent, so the class constant drops from `14` (seed `2^46`,
`Proofs18TightClassesFejerQ`) to `4`:
* `fejer_split_step_quad4`: the invariants `2^(l+6)·a_l ≤ 2^(4·2^l)` and
  `D_l ≤ 2^(4·2^l + 3(l+4)² + 30)` propagate (the constant `30` is carried
  unchanged, and `3(l+5)² − 3(l+4)² = 6l + 27 ≥ 5l + 22`);
* `split_pair_small_quad`: they hold in every dimension `l ≥ 2` from the
  seed `(32, 2^48)` (`2^8·32 = 2^13 ≤ 2^16`, `2^48 ≤ 2^154`);
* `splitUniformClass_all_small`: the split class in every dimension `l ≥ 2`
  at `splitPairWith 32 (2^48) l`;
* `uDegS l = 2^(4·2^l + 3(l+4)² + 32)` and `split_pair_small_le_uDegS`;
* `polyCoverAt_classS`: the class covers at degree `uDegS l`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The family exponent of the small dimension-two seed. -/
def splitSeedSmallA : Nat := 32

/-- The parameter degree of the small dimension-two seed. -/
def splitSeedSmallD : Nat := 2 ^ 48

/-- The exponent arithmetic of the step, with `2^k` and `(k+4)²` as atoms. -/
theorem quad4_exponent_step (k : Nat) :
    4 * 2 ^ k + (4 * 2 ^ k + 3 * (k + 4) ^ 2 + 30) + (5 * k + 22) ≤
      4 * 2 ^ (k + 1) + 3 * (k + 1 + 4) ^ 2 + 30 := by
  have h1 : 3 * (k + 1 + 4) ^ 2 = 3 * (k + 4) ^ 2 + 6 * k + 27 := by ring
  have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  rw [h1, h2]
  omega

/-- **The invariants at class constant `4` propagate.** -/
theorem fejer_split_step_quad4 {k a D a' D' P T : Nat} (ha : 1 ≤ a)
    (hA : 2 ^ (k + 6) * a ≤ 2 ^ (4 * 2 ^ k)) (hDb : D ≤ 2 ^ (4 * 2 ^ k + 3 * (k + 4) ^ 2 + 30))
    (ha' : a' ≤ 2 ^ (k + 5) * (a * a)) (hD' : D' ≤ 2 ^ (k + 6) * (a * (a + D)) * P + T)
    (hP : P ≤ 2 ^ (5 * k + 20)) (hT : T ≤ 2 ^ (5 * k + 19)) :
    2 ^ (k + 1 + 6) * a' ≤ 2 ^ (4 * 2 ^ (k + 1)) ∧
      D' ≤ 2 ^ (4 * 2 ^ (k + 1) + 3 * (k + 1 + 4) ^ 2 + 30) := by
  constructor
  · calc 2 ^ (k + 1 + 6) * a' ≤ 2 ^ (k + 1 + 6) * (2 ^ (k + 5) * (a * a)) :=
          Nat.mul_le_mul_left _ ha'
      _ = (2 ^ (k + 6) * a) * (2 ^ (k + 6) * a) := by ring
      _ ≤ 2 ^ (4 * 2 ^ k) * 2 ^ (4 * 2 ^ k) := Nat.mul_le_mul hA hA
      _ = 2 ^ (4 * 2 ^ (k + 1)) := by rw [← pow_add, double_exponent 4 k]
  · set X := 2 ^ (4 * 2 ^ k) with hXdef
    set Y := 2 ^ (4 * 2 ^ k + 3 * (k + 4) ^ 2 + 30) with hYdef
    set Z := 2 ^ (5 * k + 19) with hZdef
    have haX : a ≤ X := le_trans (Nat.le_mul_of_pos_left a (Nat.two_pow_pos _)) hA
    have hXY : X ≤ Y := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hsum : a + D ≤ 2 * Y := by omega
    have e20 : 2 ^ (5 * k + 20) = 2 * Z := by
      rw [hZdef, show 5 * k + 20 = (5 * k + 19) + 1 by ring, pow_succ]; ring
    have hX1 : 1 ≤ X := Nat.one_le_two_pow
    have hY1 : 1 ≤ Y := Nat.one_le_two_pow
    have hprod : 8 * Z * X * Y =
        2 ^ (4 * 2 ^ k + (4 * 2 ^ k + 3 * (k + 4) ^ 2 + 30) + (5 * k + 22)) := by
      rw [hXdef, hYdef, hZdef, pow_add, pow_add, show 5 * k + 22 = (5 * k + 19) + 3 by ring, pow_add]
      ring
    calc D' ≤ 2 ^ (k + 6) * (a * (a + D)) * P + T := hD'
      _ = (2 ^ (k + 6) * a) * (a + D) * P + T := by ring
      _ ≤ X * (2 * Y) * (2 * Z) + Z :=
          Nat.add_le_add (Nat.mul_le_mul (Nat.mul_le_mul hA hsum) (e20 ▸ hP)) hT
      _ ≤ 8 * Z * X * Y := split_step_arith _ _ _ hX1 hY1
      _ = _ := hprod
      _ ≤ 2 ^ (4 * 2 ^ (k + 1) + 3 * (k + 1 + 4) ^ 2 + 30) :=
          Nat.pow_le_pow_right (by norm_num) (quad4_exponent_step k)

/-- **The split invariants at class constant `4` in every dimension `l ≥ 2`**,
from the small seed `(32, 2^48)`. -/
theorem split_pair_small_quad : ∀ l, 2 ≤ l →
    1 ≤ (splitPairWith splitSeedSmallA splitSeedSmallD l).1 ∧
      1 ≤ (splitPairWith splitSeedSmallA splitSeedSmallD l).2 ∧
      2 ^ (l + 6) * (splitPairWith splitSeedSmallA splitSeedSmallD l).1 ≤ 2 ^ (4 * 2 ^ l) ∧
      (splitPairWith splitSeedSmallA splitSeedSmallD l).2 ≤
        2 ^ (4 * 2 ^ l + 3 * (l + 4) ^ 2 + 30) := by
  intro l hl
  induction l, hl using Nat.le_induction with
  | base =>
    rw [splitPairWith_two]
    unfold splitSeedSmallA splitSeedSmallD
    refine ⟨by norm_num, Nat.one_le_two_pow, by norm_num, ?_⟩
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  | succ k hk ih =>
    obtain ⟨ha, hDp, hAb, hDb⟩ := ih
    rw [splitPairWith_succ _ _ hk]
    set a := (splitPairWith splitSeedSmallA splitSeedSmallD k).1
    set D := (splitPairWith splitSeedSmallA splitSeedSmallD k).2
    obtain ⟨h1, h2⟩ := fejer_split_step_quad4 ha hAb hDb (splitStepA_le ha)
      (splitStepDWith_le ha hDp (fejerStepP_ge k)) (fejerStepP_le k) (fejerStepT_le k)
    refine ⟨?_, ?_, h1, h2⟩
    · unfold splitStepA sCountN; omega
    · unfold splitStepDWith wCountW; omega

/-- **A split uniform class in every dimension `k ≥ 2` from the small seed**,
at degrees `splitPairWith 32 (2^48) k`. -/
theorem splitUniformClass_all_small (Kc pc : Nat → Nat) (hK : ∀ k, 1 ≤ Kc k) (hp : ∀ k, 0 < pc k)
    (hlem : ∀ k, 1 ≤ k → AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor (Kc k)) (familyWidthDivisor k (pc k)))) :
    ∀ k, 2 ≤ k →
      Nonempty (SplitUniformClass k (classV Kc pc k)
        (splitPairWith splitSeedSmallA splitSeedSmallD k).1
        (splitPairWith splitSeedSmallA splitSeedSmallD k).2) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    have hV1 := one_le_classV Kc pc 2
    have hc1 := const_le_classV_succ Kc pc 1
    rw [splitPairWith_two]
    exact splitUniformClass_two_small (hK 1) (hp 1) (hlem 1 le_rfl) hV1 (hc1.1.trans le_rfl)
      (hc1.2.trans le_rfl)
  | succ k hk ih =>
    obtain ⟨C⟩ := ih
    obtain ⟨ha, hD, -, -⟩ := split_pair_small_quad k hk
    have hV1 := one_le_classV Kc pc k
    have hc := const_le_classV_succ Kc pc k
    rw [splitPairWith_succ _ _ hk, ← splitStepDFejer_eq]
    exact splitUniformClass_succ_fejer (by omega) hV1 ha hD C (hK k) (hp k) (hlem k (by omega))
      (classV_le_succ Kc pc k) hc.1 hc.2

/-- The class degree at class constant `4`. -/
def uDegS (l : Nat) : Nat := 2 ^ (4 * 2 ^ l + 3 * (l + 4) ^ 2 + 32)

/-- The small-seed split degrees fit `uDegS`. -/
theorem split_pair_small_le_uDegS {l : Nat} (hl : 2 ≤ l) :
    (splitPairWith splitSeedSmallA splitSeedSmallD l).1 +
      (splitPairWith splitSeedSmallA splitSeedSmallD l).2 + l + 1 ≤ uDegS l := by
  obtain ⟨-, -, hA, hD⟩ := split_pair_small_quad l hl
  unfold uDegS
  set a := (splitPairWith splitSeedSmallA splitSeedSmallD l).1
  set D := (splitPairWith splitSeedSmallA splitSeedSmallD l).2
  set Y := 2 ^ (4 * 2 ^ l + 3 * (l + 4) ^ 2 + 30) with hYdef
  have ha : a ≤ Y := by
    have h1 : a ≤ 2 ^ (4 * 2 ^ l) := le_trans (Nat.le_mul_of_pos_left a (Nat.two_pow_pos _)) hA
    exact h1.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hl1 : l + 1 ≤ Y := by
    have h1 : l + 1 ≤ 2 ^ (l + 1) := Nat.lt_two_pow_self.le
    have h2 : l + 1 ≤ 4 * 2 ^ l + 3 * (l + 4) ^ 2 + 30 := by
      have := Nat.lt_two_pow_self (n := l); omega
    exact h1.trans (Nat.pow_le_pow_right (by norm_num) h2)
  have h4 : 2 ^ (4 * 2 ^ l + 3 * (l + 4) ^ 2 + 32) = 4 * Y := by
    rw [hYdef, show 4 * 2 ^ l + 3 * (l + 4) ^ 2 + 32 = (4 * 2 ^ l + 3 * (l + 4) ^ 2 + 30) + 2 by ring,
      pow_add]; ring
  rw [h4]
  omega

/-- **The class cover in dimension `l` at degree `uDegS l`.** -/
theorem polyCoverAt_classS (Kc pc : Nat → Nat) (hK : ∀ k, 1 ≤ Kc k) (hp : ∀ k, 0 < pc k)
    (hlem : ∀ k, 1 ≤ k → AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor (Kc k)) (familyWidthDivisor k (pc k))))
    {l : Nat} (hl1 : 1 ≤ l) :
    PolyCoverAt l (uCount (classV Kc pc l) (uDegS l)) (uExp (classV Kc pc l) (uDegS l)) := by
  have hVl := one_le_classV Kc pc l
  rcases Nat.lt_or_ge l 2 with hl | hl
  · obtain rfl : l = 1 := by omega
    refine polyCoverAt_one_uniform_low hVl ?_
    unfold uDegS
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  · obtain ⟨C⟩ := splitUniformClass_all_small Kc pc hK hp hlem l hl
    have hfit := split_pair_small_le_uDegS hl
    have P0 := (C.toPower hVl).polyCoverAt (by omega) hVl (D := uDegS l) (by omega) (by omega)
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
