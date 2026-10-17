import GowersSzemeredi.Proofs16SplitAllDimensions
import GowersSzemeredi.Proofs16AllDimensionsSide
import GowersSzemeredi.Proofs16SplitStepBoundsSide
import GowersSzemeredi.Proofs16SplitUniformClassSide

/-! Declarations of `Proofs16SplitAllDimensions` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

section
open BaseCase

theorem splitStepD_le {k a D : Nat} (ha : 1 ≤ a) (hD : 1 ≤ D) :
    splitStepD k a D ≤ 2 ^ (k + 6) * (a * (a + D)) * stepP k + stepT k := by
  have h4 : 2 ^ (k + 2) = 2 ^ k * 4 := by rw [pow_add]; norm_num
  have h6 : 2 ^ (k + 6) = 2 ^ k * 64 := by rw [pow_add]; norm_num
  have h := split_degree_poly (a := a) (D := D) (P := stepP k) (A := 2 ^ k) (T := stepT k)
    (k := k) (Y := sStepY k a D) (SW := sSW k a D) (PbW := sPbW k a D) (CW := sCountW k a D)
    (EbW := sEbW k a D) (ErW := sErW k a D) (BqW := sBqW k a D) (LW := sLW k a D)
    (ZW := sZW k a D) (EW := sExpW k a D) (Th := stepThrDeg k D)
    ha hD Nat.one_le_two_pow (stepP_ge9 k) h4 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  rw [h6]
  exact h

theorem split_invariant_succ {k a D : Nat} (ha : 1 ≤ a) (hD : 1 ≤ D)
    (hA : 2 ^ (k + 6) * a ≤ 2 ^ (35 * 2 ^ k)) (hDb : D ≤ 2 ^ (75 * 2 ^ k)) :
    2 ^ (k + 1 + 6) * splitStepA k a ≤ 2 ^ (35 * 2 ^ (k + 1)) ∧
      splitStepD k a D ≤ 2 ^ (75 * 2 ^ (k + 1)) := by
  have hE : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  constructor
  · calc 2 ^ (k + 1 + 6) * splitStepA k a ≤ 2 ^ (k + 1 + 6) * (2 ^ (k + 5) * (a * a)) :=
          Nat.mul_le_mul_left _ (splitStepA_le ha)
      _ = (2 ^ (k + 6) * a) * (2 ^ (k + 6) * a) := by ring
      _ ≤ 2 ^ (35 * 2 ^ k) * 2 ^ (35 * 2 ^ k) := Nat.mul_le_mul hA hA
      _ = 2 ^ (35 * 2 ^ (k + 1)) := by
          rw [← pow_add, pow_succ]; congr 1; ring
  · have haE : a ≤ 2 ^ (35 * 2 ^ k) :=
      le_trans (Nat.le_mul_of_pos_left a (Nat.two_pow_pos _)) hA
    have h3575 : 2 ^ (35 * 2 ^ k) ≤ 2 ^ (75 * 2 ^ k) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hsum : a + D ≤ 2 ^ (75 * 2 ^ k + 1) := by rw [pow_succ]; omega
    have hP : stepP k = 2 ^ (32 * 2 ^ k + 6) := by
      unfold stepP; congr 1; rw [pow_add]; ring
    have hT : stepT k = 2 ^ (64 * 2 ^ k) := by
      unfold stepT; congr 1; rw [pow_add]; ring
    have he : 35 * 2 ^ k + (75 * 2 ^ k + 1) + (32 * 2 ^ k + 6) = 142 * 2 ^ k + 7 := by ring
    calc splitStepD k a D ≤ 2 ^ (k + 6) * (a * (a + D)) * stepP k + stepT k := splitStepD_le ha hD
      _ = (2 ^ (k + 6) * a) * (a + D) * 2 ^ (32 * 2 ^ k + 6) + 2 ^ (64 * 2 ^ k) := by
          rw [hP, hT]; ring
      _ ≤ 2 ^ (35 * 2 ^ k) * 2 ^ (75 * 2 ^ k + 1) * 2 ^ (32 * 2 ^ k + 6) + 2 ^ (142 * 2 ^ k + 7) :=
          add_le_add (Nat.mul_le_mul (Nat.mul_le_mul hA hsum) le_rfl)
            (Nat.pow_le_pow_right (by norm_num) (by omega))
      _ = 2 ^ (142 * 2 ^ k + 7) + 2 ^ (142 * 2 ^ k + 7) := by rw [← pow_add, ← pow_add, he]
      _ = 2 ^ (142 * 2 ^ k + 8) := by rw [pow_succ]; ring
      _ ≤ 2 ^ (75 * 2 ^ (k + 1)) :=
          Nat.pow_le_pow_right (by norm_num) (by rw [pow_succ]; omega)

theorem split_pair_bounds : ∀ k, 2 ≤ k →
    1 ≤ (splitPair k).1 ∧ 1 ≤ (splitPair k).2 ∧
      2 ^ (k + 6) * (splitPair k).1 ≤ 2 ^ (35 * 2 ^ k) ∧ (splitPair k).2 ≤ 2 ^ (75 * 2 ^ k) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    rw [splitPair_two]
    unfold splitSeed
    refine ⟨Nat.one_le_two_pow, Nat.one_le_two_pow, ?_, Nat.pow_le_pow_right (by norm_num) (by norm_num)⟩
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  | succ k hk ih =>
    obtain ⟨ha, hD, hA, hDb⟩ := ih
    rw [splitPair_succ hk]
    obtain ⟨h1, h2⟩ := split_invariant_succ ha hD hA hDb
    refine ⟨?_, ?_, h1, h2⟩
    · unfold splitStepA sCountN; omega
    · unfold splitStepD sCountW; omega

/-- **A split uniform class in every dimension `k ≥ 2`**, with degrees
`splitPair k`, so `log a_k ≤ 35·2^k` and `log D_k ≤ 75·2^k`
(`split_pair_bounds`). -/
theorem splitUniformClass_all (Kc pc : Nat → Nat) (hK : ∀ k, 1 ≤ Kc k) (hp : ∀ k, 0 < pc k)
    (hlem : ∀ k, 1 ≤ k → AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor (Kc k)) (familyWidthDivisor k (pc k)))) :
    ∀ k, 2 ≤ k →
      Nonempty (SplitUniformClass k (classV Kc pc k) (splitPair k).1 (splitPair k).2) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    have hV1 := one_le_classV Kc pc 2
    have hc1 := const_le_classV_succ Kc pc 1
    rw [splitPair_two]
    exact splitUniformClass_two (hK 1) (hp 1) (hlem 1 le_rfl) hV1 (hc1.1.trans le_rfl)
      (hc1.2.trans le_rfl) (by unfold splitSeed; exact Nat.pow_le_pow_right (by norm_num) (by norm_num))
  | succ k hk ih =>
    obtain ⟨C⟩ := ih
    obtain ⟨ha, hD, -, -⟩ := split_pair_bounds k hk
    have hV1 := one_le_classV Kc pc k
    have hc := const_le_classV_succ Kc pc k
    rw [splitPair_succ hk]
    exact splitUniformClass_succ (by omega) hV1 ha hD C (hK k) (hp k) (hlem k (by omega))
      (classV_le_succ Kc pc k) hc.1 hc.2

end

end LeanProofs.GowersSzemeredi
