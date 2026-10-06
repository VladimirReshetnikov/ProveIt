import GowersSzemeredi.Proofs05MultilinearScale
import GowersSzemeredi.Proofs05PolynomialPartition
import GowersSzemeredi.Proofs05LinearRecurrence

/-! # Explicit constants for the multilinear height induction -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The threshold after h monomial eliminations. -/
def multilinearHeightThreshold (k h : Nat) : Nat :=
  (2 * polynomialPartitionThreshold k) ^ (multilinearPartitionConstant k ^ h)

/-- The width exponent after h monomial eliminations. -/
def multilinearHeightExponent (k h : Nat) : Real :=
  ((multilinearPartitionConstant k : Real) ^ h)⁻¹

/-- The diameter coefficient reserves 2^-k for each eliminated monomial. -/
def multilinearHeightCoefficient (k h : Nat) : Real :=
  1 + (h : Real) / (2 : Real) ^ k

theorem multilinearPartitionConstant_eight_le {k : Nat} (hk : 2 ≤ k) :
    8 ≤ multilinearPartitionConstant k := by
  unfold multilinearPartitionConstant
  have hp : 2 ≤ 2 ^ (k + 3) := by
    simpa using Nat.pow_le_pow_right (n := 2) (by norm_num) (show 1 ≤ k + 3 by omega)
  nlinarith

theorem polynomialPartitionThreshold_monotone {d k : Nat} (hdk : d ≤ k) :
    polynomialPartitionThreshold d ≤ polynomialPartitionThreshold k := by
  unfold polynomialPartitionThreshold weylThreshold
  gcongr <;> norm_num

/-- The recurrence exponent pays exactly four times the total degree in the
coarse-scale variable. -/
theorem multilinearPartitionConstant_recurrence {k : Nat} (hk : 1 ≤ k) :
    (multilinearPartitionConstant k : Real) *
      ((k : Real) * (2 : Real) ^ (k + 1))⁻¹ = 4 * k := by
  have hk0 : (k : Real) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  unfold multilinearPartitionConstant
  push_cast
  rw [show k + 3 = (k + 1) + 2 by omega, pow_add]
  field_simp
  ring

/-- Every height threshold is positive and at least the one-polynomial threshold. -/
theorem multilinearHeightThreshold_bounds {k : Nat} (hk : 2 ≤ k) (h : Nat) :
    2 ≤ multilinearHeightThreshold k h ∧
      polynomialPartitionThreshold k ≤ multilinearHeightThreshold k h := by
  have hT : 1 ≤ polynomialPartitionThreshold k := by
    unfold polynomialPartitionThreshold weylThreshold
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hK := multilinearPartitionConstant_eight_le hk
  have he : 1 ≤ multilinearPartitionConstant k ^ h := one_le_pow₀ (by omega)
  have hb : 2 * polynomialPartitionThreshold k ≤ multilinearHeightThreshold k h := by
    simpa only [pow_one, multilinearHeightThreshold] using Nat.pow_le_pow_right (by omega : 0 < 2 * polynomialPartitionThreshold k) he
  constructor <;> omega

/-- The next threshold is exactly the K-th power of the preceding one. -/
theorem multilinearHeightThreshold_succ (k h : Nat) :
    multilinearHeightThreshold k (h + 1) =
      multilinearHeightThreshold k h ^ multilinearPartitionConstant k := by
  unfold multilinearHeightThreshold
  rw [pow_succ, pow_mul]

/-- The explicit height thresholds satisfy the upward-rounded scale budget. -/
theorem multilinear_height_scale_exists {k h m : Nat} (hk : 2 ≤ k)
    (hm : multilinearHeightThreshold k (h + 1) ≤ m) :
    ∃ u : Nat, 2 ≤ u ∧ u ^ 4 ≤ m ∧ multilinearHeightThreshold k h ≤ u - 1 ∧
      (m : Real) ^ multilinearHeightExponent k (h + 1) ≤
        ((u - 1 : Nat) : Real) ^ multilinearHeightExponent k h ∧
      ((u - 1 : Nat) : Real) ^ (-multilinearHeightExponent k h) ≤
        (m : Real) ^ (-multilinearHeightExponent k (h + 1)) ∧
      (u : Real) ^ k * (m : Real) ^ (-((k : Real) * (2 : Real) ^ (k + 1))⁻¹) ≤
        (2 : Real) ^ (-(k : Real)) * (m : Real) ^ (-multilinearHeightExponent k (h + 1)) := by
  let K := multilinearPartitionConstant k
  let T := multilinearHeightThreshold k h
  let x : Real := (m : Real) ^ (K : Real)⁻¹
  have hK : 8 ≤ K := multilinearPartitionConstant_eight_le hk
  have hKpos : 0 < K := by omega
  have hKr : (K : Real) ≠ 0 := by exact_mod_cast hKpos.ne'
  have hm0 : (0 : Real) ≤ m := Nat.cast_nonneg _
  have hx0 : 0 ≤ x := Real.rpow_nonneg hm0 _
  have hr : (m : Real) = x ^ K := by
    dsimp [x]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm0, inv_mul_cancel₀ hKr, Real.rpow_one]
  have hTpow : T ^ K ≤ m := by simpa only [multilinearHeightThreshold_succ] using hm
  have hTx : (T : Real) ≤ x := by
    have h : (T : Real) ^ K ≤ x ^ K := by rw [← hr]; exact_mod_cast hTpow
    exact le_of_pow_le_pow_left₀ hKpos.ne' hx0 h
  have hT2 : (2 : Real) ≤ T := by exact_mod_cast (multilinearHeightThreshold_bounds hk h).1
  have hx : 2 ≤ x := hT2.trans hTx
  have hgamma : ((4 * k : Nat) : Real) ≤ (K : Real) *
      ((k : Real) * (2 : Real) ^ (k + 1))⁻¹ := by
    rw [multilinearPartitionConstant_recurrence (by omega : 1 ≤ k)]
    norm_cast
  exact multilinear_height_rounding K k h T m x _ hK (by omega) hx hr hTx hgamma

/-- Square-root recurrence with a common exponent valid for every nonconstant
square-free monomial in k coordinates. -/
theorem multilinear_coefficient_recurrence {N k d m : Nat} [NeZero N]
    (hk : 2 ≤ k) (hd : 1 ≤ d) (hdk : d ≤ k)
    (hm : polynomialPartitionThreshold k ≤ m) (hmN : m ≤ N) (a : ZMod N) :
    ∃ p : Nat, 1 ≤ p ∧ p ^ 2 ≤ m ∧
      (centeredAbs ((p : ZMod N) ^ d * a) : Real) ≤
        (m : Real) ^ (-((k : Real) * (2 : Real) ^ (k + 1))⁻¹) * N := by
  by_cases hd1 : d = 1
  · subst d
    have hm4 : 4 ≤ m := by
      have hT0 : polynomialPartitionThreshold 0 = 4 := by norm_num [polynomialPartitionThreshold, weylThreshold]
      rw [← hT0]
      exact (polynomialPartitionThreshold_monotone (Nat.zero_le k)).trans hm
    have hs : 2 ≤ Nat.sqrt m := Nat.le_sqrt'.2 hm4
    obtain ⟨p, hp, hps, hrec⟩ := linear_small_multiplier (Nat.sqrt m) hs a
    refine ⟨p, by omega, (Nat.pow_le_pow_left hps 2).trans (Nat.sqrt_le' m), ?_⟩
    simp only [pow_one]
    apply hrec.trans
    have hm0 : (0 : Real) < m := by exact_mod_cast (show 0 < m by omega)
    have hm1 : (1 : Real) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
    have hk0 : (0 : Real) < k := by exact_mod_cast (show 0 < k by omega)
    have hpow : (1 : Real) ≤ (2 : Real) ^ (k + 1) := one_le_pow₀ (by norm_num)
    have hden : (2 : Real) ≤ (k : Real) * (2 : Real) ^ (k + 1) := by
      have hk2 : (2 : Real) ≤ k := by exact_mod_cast hk
      nlinarith
    have hgamma : ((k : Real) * (2 : Real) ^ (k + 1))⁻¹ ≤ 1 / 2 := by
      simpa using inv_anti₀ (by norm_num : (0 : Real) < 2) hden
    have hroot : (m : Real) ^ (((k : Real) * (2 : Real) ^ (k + 1))⁻¹) ≤
        (Nat.sqrt m : Real) + 1 := by
      calc
        _ ≤ (m : Real) ^ ((1 : Real) / 2) := Real.rpow_le_rpow_of_exponent_le hm1 hgamma
        _ = Real.sqrt m := (Real.sqrt_eq_rpow _).symm
        _ ≤ (Nat.sqrt m : Real) + 1 := by
          apply Real.sqrt_le_iff.mpr
          constructor
          · positivity
          · exact_mod_cast (show m ≤ (Nat.sqrt m + 1) ^ 2 by simpa only [Nat.succ_eq_add_one] using (Nat.lt_succ_sqrt' m).le)
    rw [Real.rpow_neg hm0.le]
    have hinv := inv_anti₀ (Real.rpow_pos_of_pos hm0 _) hroot
    simpa only [div_eq_mul_inv, mul_comm] using
      mul_le_mul_of_nonneg_left hinv (Nat.cast_nonneg N)
  · have hd2 : 2 ≤ d := by omega
    have hmD : polynomialPartitionThreshold d ≤ m :=
      (polynomialPartitionThreshold_monotone hdk).trans hm
    obtain ⟨p, hp, hp2, hrec⟩ := lemma_5_5_square_root_auxiliary_holds d m N hd2 hmD hmN a
    refine ⟨p, hp, hp2, hrec.trans ?_⟩
    have hm1 : (1 : Real) ≤ m := by
      have hp1 : 1 ≤ p ^ 2 := one_le_pow₀ hp
      exact_mod_cast hp1.trans hp2
    have hd0 : (0 : Real) < d := by exact_mod_cast (show 0 < d by omega)
    have hden : (d : Real) * (2 : Real) ^ (d + 1) ≤ (k : Real) * (2 : Real) ^ (k + 1) := by
      gcongr
      norm_num
    have hinv := inv_anti₀ (show (0 : Real) < (d : Real) * 2 ^ (d + 1) by positivity) hden
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hm1 (neg_le_neg hinv)) (Nat.cast_nonneg N)

end LeanProofs.GowersSzemeredi
