import GowersSzemeredi.Proofs16AllDimensions
import GowersSzemeredi.Proofs16BaseCaseEndpoint
import GowersSzemeredi.Proofs16BaseCaseZero
import GowersSzemeredi.Proofs16ClassStepDegreesSide
import GowersSzemeredi.Proofs16PowerUniformClassSide
import GowersSzemeredi.Proofs16CorollaryFromInduction

/-! Declarations of `Proofs16AllDimensions` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace LeanProofs.GowersSzemeredi

section
open BaseCase

theorem stepP_ge9 (k : Nat) : k + 9 ≤ stepP k := by
  unfold stepP
  have h1 := two_pow_k5_ge k
  have h2 : 2 ^ (k + 5) + 6 < 2 ^ (2 ^ (k + 5) + 6) := Nat.lt_two_pow_self
  omega

/-- **The degrees of the step are at most `2^(k+7)·D²·P²`.** -/
theorem step_degrees_le {k D : Nat} (hD : 1 ≤ D) :
    stepCountDeg k D + stepExpDeg k D + stepThrDeg k D ≤
      2 ^ (k + 7) * (D * D) * (stepP k * stepP k) := by
  have hP := stepP_ge9 k
  have hT := stepT_le_sq k
  have hA : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hkA : k < 2 ^ k := Nat.lt_two_pow_self
  have h2 : 2 ^ (k + 2) = 2 ^ k * 4 := by rw [pow_add]; norm_num
  have h7 : 2 ^ (k + 7) = 2 ^ k * 128 := by rw [pow_add]; norm_num
  unfold stepCountDeg stepExpDeg stepThrDeg stepZDeg stepLDeg stepBqDeg stepErDeg stepEbDeg
    stepPbDeg stepSDeg stepQrDeg stepY1
  rw [h2, h7]
  set P := stepP k
  set T := stepT k
  set A := 2 ^ k
  have hP1 : 1 ≤ P := by omega
  have hDP : D ≤ D * D := Nat.le_mul_of_pos_left _ hD
  have hPP : P ≤ P * P := Nat.le_mul_of_pos_left _ hP1
  nlinarith [Nat.mul_le_mul hDP hPP, Nat.mul_le_mul hA hDP, Nat.mul_le_mul (Nat.mul_le_mul hA hD) hPP,
    Nat.mul_le_mul (Nat.mul_le_mul hA hDP) hPP, Nat.mul_le_mul hD hPP, Nat.zero_le (A * D * P),
    Nat.zero_le (A * (D * D) * P), Nat.zero_le (D * P), Nat.zero_le (A * D)]

/-- **The class degree is closed under the step.** -/
theorem step_degree_closed (k : Nat) :
    2 ^ (k + 7) * (classDeg k * classDeg k) * (stepP k * stepP k) ≤ classDeg (k + 1) := by
  unfold classDeg stepP
  set a := 2 ^ (k + 5) with ha
  set B := 2 ^ a with hB
  have ha32 : 32 ≤ a := by
    rw [ha]; calc 32 = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ (k + 5) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hak : k + 5 ≤ a := two_pow_k5_ge k
  have hB2a : 2 * a ≤ B := two_pow_ge_double (by omega)
  have hsq : 2 ^ (k + 1 + 5) = 2 * a := by rw [ha, show k + 1 + 5 = (k + 5) + 1 by omega, pow_succ]; ring
  have hBB : 2 ^ (2 ^ (k + 1 + 5)) = B * B := by rw [hsq, hB, ← pow_add]; ring_nf
  rw [hBB]
  calc 2 ^ (k + 7) * (2 ^ B * 2 ^ B) * (2 ^ (a + 6) * 2 ^ (a + 6))
      = 2 ^ (k + 7 + (B + B) + ((a + 6) + (a + 6))) := by
        rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]
    _ ≤ 2 ^ (B * B) := by
        apply Nat.pow_le_pow_right (by norm_num)
        nlinarith

theorem classDeg_add_le (k : Nat) :
    classDeg k + k + 1 ≤ (2 : Nat) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 6))) := by
  unfold classDeg
  set a := 2 ^ (k + 5) with ha
  set B := 2 ^ a with hB
  have hak : k + 5 ≤ a := two_pow_k5_ge k
  have hBa : a < B := Nat.lt_two_pow_self
  have hkB : k + 1 < 2 ^ B := lt_of_lt_of_le (by omega) (Nat.lt_two_pow_self (n := B)).le
  have hsq : 2 ^ (k + 6) = 2 * a := by rw [ha, show k + 6 = (k + 5) + 1 by omega, pow_succ]; ring
  have hBB : 2 ^ (2 ^ (k + 6)) = B * B := by rw [hsq, hB, ← pow_add]; ring_nf
  rw [hBB]
  calc 2 ^ B + k + 1 ≤ 2 ^ B + 2 ^ B := by omega
    _ = 2 ^ (B + 1) := by rw [pow_succ]; ring
    _ ≤ 2 ^ (B * B) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)

/-- **A uniform class in every dimension `k ≥ 2`.** -/
theorem powerUniformClass_all (Kc pc : Nat → Nat) (hK : ∀ k, 1 ≤ Kc k) (hp : ∀ k, 0 < pc k)
    (hlem : ∀ k, 1 ≤ k → AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor (Kc k)) (familyWidthDivisor k (pc k)))) :
    ∀ k, 2 ≤ k →
      Nonempty (PowerUniformClass k (classV Kc pc k) (classDeg k) (classDeg k) (classDeg k)) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    have hV1 := one_le_classV Kc pc 2
    have hc1 := const_le_classV_succ Kc pc 1
    obtain ⟨C⟩ := powerUniformClass_two (hK 1) (hp 1) (hlem 1 le_rfl) hV1
      (hc1.1.trans le_rfl) (hc1.2.trans le_rfl)
    have hdeg : ∀ d : Nat, d ≤ 2 ^ 130 → d ≤ classDeg 2 := by
      intro d hd
      refine hd.trans ?_
      unfold classDeg
      exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
    exact ⟨C.weaken hV1 le_rfl (hdeg _ (by norm_num)) (hdeg _ le_rfl) (hdeg _ (by norm_num))⟩
  | succ k hk ih =>
    obtain ⟨C⟩ := ih
    have hV1 := one_le_classV Kc pc k
    have hc := const_le_classV_succ Kc pc k
    obtain ⟨C'⟩ := powerUniformClass_succ (by omega) hV1 (classDeg_pos k) C (hK k) (hp k)
      (hlem k (by omega)) (classV_le_succ Kc pc k) hc.1 hc.2
    have hsum := (step_degrees_le (k := k) (classDeg_pos k)).trans (step_degree_closed k)
    exact ⟨C'.weaken (one_le_classV Kc pc (k + 1)) le_rfl (by omega) (by omega) (by omega)⟩

/-- **Theorem 16.2 in every dimension**, from the family Lemma 16.6 in every
dimension with constants of at most triple-exponential size. -/
theorem theorem_16_2_of_family_lemmas (Kc pc : Nat → Nat) (hK : ∀ k, 1 ≤ Kc k)
    (hp : ∀ k, 0 < pc k)
    (hlem : ∀ k, 1 ≤ k → AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor (Kc k)) (familyWidthDivisor k (pc k))))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5)))) :
    theorem_16_2 := by
  intro k
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k
    · exact theorem_16_2_zero
    · exact lemma_16_3_holds
  · obtain ⟨C⟩ := powerUniformClass_all Kc pc hK hp hlem k hk
    exact C.theorem162At_tower (by omega) (one_le_classV Kc pc k) (classV_bound Kc pc hconst hk)
      (D := classDeg k + k + 1) (by omega) (by omega) le_rfl (classDeg_add_le k)

/-- **Corollary 16.11 in every dimension**, under the same hypotheses. -/
theorem corollary_16_11_of_family_lemmas (Kc pc : Nat → Nat) (hK : ∀ k, 1 ≤ Kc k)
    (hp : ∀ k, 0 < pc k)
    (hlem : ∀ k, 1 ≤ k → AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor (Kc k)) (familyWidthDivisor k (pc k))))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5)))) :
    corollary_16_11 := by
  exact corollary_16_11_of_theorem_16_2
    (theorem_16_2_of_family_lemmas Kc pc hK hp hlem hconst)

/-- **Theorem 16.2 in every dimension from the recurrence profiles.** -/
theorem theorem_16_2_of_profiles_all (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k)
    (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5)))) :
    theorem_16_2 ∧ corollary_16_11 := by
  have hlem : ∀ k, 1 ≤ k → AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor (Kc k)) (familyWidthDivisor k (pc k))) :=
    fun k hk => abstractFamilyLemma166At_of k (hK k) (hp k) (hrec k hk)
  have hK1 : ∀ k, 1 ≤ Kc k := fun k => le_trans (by norm_num) (hK k)
  exact ⟨theorem_16_2_of_family_lemmas Kc pc hK1 hp hlem hconst,
    corollary_16_11_of_family_lemmas Kc pc hK1 hp hlem hconst⟩

end

end LeanProofs.GowersSzemeredi
