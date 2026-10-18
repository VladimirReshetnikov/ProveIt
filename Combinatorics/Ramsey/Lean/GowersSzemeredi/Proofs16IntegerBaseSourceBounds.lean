import GowersSzemeredi.Proofs16IntegerBaseCover
import GowersSzemeredi.Proofs16BaseFamilyPowerBound
import GowersSzemeredi.Proofs16RegimeSplittingSide

/-! The genuine cubic base cover implies the printed dimension-one controls.
The source iteration budget absorbs the fixed family size with room to spare. -/
set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem section16_integer_base_source_budget {gamma theta : Real}
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1) :
    128 * (section16BaseFamilyBound gamma theta : Real) ≤
      gamma ^ (-(2 : Int)) * multipleS theta gamma 1 := by
  let b := 2 / (gamma * theta)
  have hp : 0 < gamma * theta := mul_pos hg ht
  have hb2 : 2 ≤ b := (le_div_iff₀ hp).mpr (by nlinarith only [hg1, ht1, hg, ht])
  have hb1 : 1 ≤ b := by linarith only [hb2]
  have h128 : (128 : Real) ≤ b ^ (7 : Nat) := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : Real) ≤ 2) hb2 7
    norm_num at h ⊢
    exact h
  have hq := section16BaseFamilyBound_le_power hg hg1 ht ht1
  change (section16BaseFamilyBound gamma theta : Real) ≤ b ^ (10002 : Nat) at hq
  have hginv : (1 : Real) ≤ gamma ^ (-(2 : Int)) := by
    rw [zpow_neg, zpow_ofNat]
    exact (one_le_inv₀ (pow_pos hg 2)).mpr (pow_le_one₀ hg.le hg1)
  have hS0 : (0 : Real) ≤ multipleS theta gamma 1 := by
    unfold multipleS
    exact pow_nonneg (by positivity : (0 : Real) ≤ 2 / (theta * gamma)) _
  calc
    _ ≤ b ^ (7 : Nat) * b ^ (10002 : Nat) :=
      mul_le_mul h128 hq (Nat.cast_nonneg _) (by positivity)
    _ = b ^ (10009 : Nat) := by rw [← pow_add]
    _ ≤ multipleS theta gamma 1 := by
      unfold multipleS
      rw [mul_comm theta gamma]
      change b ^ (10009 : Nat) ≤ b ^ ((2 : Nat) ^ ((2 : Nat) ^ (1 + 6)))
      exact pow_le_pow_right₀ hb1
        (by norm_num : (10009 : Nat) ≤ (2 : Nat) ^ ((2 : Nat) ^ (1 + 6)))
    _ ≤ _ := le_mul_of_one_le_left hS0 hginv

theorem integer_cubic_base_controls_fit {gamma r sigma : Real} {q : Nat}
    (hq : 0 < q) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (hrq : 128 * (q : Real) ≤ r) (hs : 0 < sigma) (hs1 : sigma ≤ 1) :
    (3 * q : Nat) ≤ (multipleQ (r⁻¹ * sigma) gamma 1) ^ r ∧
      (multipleC (r⁻¹ * sigma) gamma 1) ^ r ≤ cubicBaseExponent q sigma := by
  have hq1 : (1 : Real) ≤ q := by exact_mod_cast hq
  have hr1 : 1 ≤ r := by linarith only [hq1, hrq]
  have hr : 0 < r := zero_lt_one.trans_le hr1
  let u := gamma * (r⁻¹ * sigma)
  have hu : 0 < u := mul_pos hg (mul_pos (inv_pos.mpr hr) hs)
  have hu1 : u ≤ 1 := by
    have hri : r⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hr1
    exact mul_le_one₀ hg1 (by positivity) (mul_le_one₀ hri hs.le hs1)
  have hEnat : (4 : Nat) ≤ (2 : Nat) ^ ((2 : Nat) ^ (1 + 8)) := by
    change (2 : Nat) ^ (2 : Nat) ≤ _
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hE : (4 : Real) ≤ ((2 : Nat) ^ ((2 : Nat) ^ (1 + 8)) : Nat) := by exact_mod_cast hEnat
  have hEr : (4 : Real) ≤ (((2 : Nat) ^ ((2 : Nat) ^ (1 + 8)) : Nat) : Real) * r :=
    hE.trans (le_mul_of_one_le_right (by positivity) hr1)
  have hpow : (multipleC (r⁻¹ * sigma) gamma 1) ^ r ≤ u ^ (4 : Nat) := by
    unfold multipleC
    change (u ^ ((2 : Nat) ^ ((2 : Nat) ^ (1 + 8)))) ^ r ≤ u ^ (4 : Nat)
    rw [← Real.rpow_natCast, ← Real.rpow_mul hu.le]
    simpa only [Real.rpow_ofNat] using
      Real.rpow_le_rpow_of_exponent_ge hu hu1 hEr
  have hus : u ≤ sigma / r := by
    dsimp [u]
    have h := mul_le_mul_of_nonneg_right hg1 (by positivity : 0 ≤ r⁻¹ * sigma)
    simpa only [one_mul, mul_one, div_eq_mul_inv, mul_comm] using h
  have hden : (2 : Real) ^ (27 : Nat) * (q : Real) ^ (4 : Nat) ≤ r ^ (4 : Nat) := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ 128 * (q : Real)) hrq 4
    rw [mul_pow] at h
    norm_num only [show (128 : Real) ^ (4 : Nat) = 268435456 by norm_num,
      show (2 : Real) ^ (27 : Nat) = 134217728 by norm_num]
    have hq4 := pow_nonneg (Nat.cast_nonneg q : (0 : Real) ≤ q) 4
    nlinarith only [h, hq4]
  have hsig : sigma ^ (4 : Nat) ≤ sigma ^ (3 : Nat) :=
    pow_le_pow_of_le_one hs.le hs1 (by omega)
  have hinv : (r ^ (4 : Nat))⁻¹ ≤ ((2 : Real) ^ (27 : Nat))⁻¹ / (q : Real) ^ (4 : Nat) := by
    have h := inv_anti₀ (by positivity : (0 : Real) < (2 : Real) ^ (27 : Nat) * (q : Real) ^ (4 : Nat)) hden
    simpa only [mul_inv_rev, div_eq_mul_inv, mul_comm] using h
  have hwidth : (multipleC (r⁻¹ * sigma) gamma 1) ^ r ≤ cubicBaseExponent q sigma := by
    calc
      _ ≤ u ^ (4 : Nat) := hpow
      _ ≤ (sigma / r) ^ (4 : Nat) := pow_le_pow_left₀ hu.le hus _
      _ = sigma ^ (4 : Nat) * (r ^ (4 : Nat))⁻¹ := by rw [div_pow, div_eq_mul_inv]
      _ ≤ sigma ^ (3 : Nat) * (((2 : Real) ^ (27 : Nat))⁻¹ / (q : Real) ^ (4 : Nat)) :=
        mul_le_mul hsig hinv (by positivity) (by positivity)
      _ = _ := by
        unfold cubicBaseExponent
        rw [Real.rpow_neg (by norm_num : (0 : Real) ≤ 2)]
        ring
  have hucap : u ≤ r⁻¹ := by
    calc
      u = (gamma * sigma) * r⁻¹ := by dsimp [u]; ring
      _ ≤ 1 * r⁻¹ := mul_le_mul_of_nonneg_right (mul_le_one₀ hg1 hs.le hs1) (by positivity)
      _ = r⁻¹ := one_mul _
  have hwcap : (multipleC (r⁻¹ * sigma) gamma 1) ^ r ≤ r⁻¹ := by
    apply hpow.trans
    have h := pow_le_pow_of_le_one hu.le hu1 (by omega : 1 ≤ (4 : Nat))
    have huPow : u ^ (4 : Nat) ≤ u := by simpa only [pow_one] using h
    exact huPow.trans hucap
  have hc : 0 < multipleC (r⁻¹ * sigma) gamma 1 := multipleC_pos _ (by positivity) hg
  have hident : (multipleQ (r⁻¹ * sigma) gamma 1) ^ r =
      ((multipleC (r⁻¹ * sigma) gamma 1) ^ r)⁻¹ := by
    unfold multipleQ
    exact Real.inv_rpow hc.le _
  refine ⟨?_, hwidth⟩
  rw [hident]
  have hri := inv_anti₀ (Real.rpow_pos_of_pos hc r) hwcap
  rw [inv_inv] at hri
  have h3 : ((3 * q : Nat) : Real) ≤ r := by push_cast; linarith only [hrq, hq1]
  exact h3.trans hri

theorem IntegerMultiplyLinearWith.base_source_controls {N q : Nat} [NeZero N]
    {gamma r : Real} {Gamma : Finset (Point N 1 × ZMod N)}
    (hq : 0 < q) (hg : 0 < gamma) (hg1 : gamma ≤ 1) (hrq : 128 * (q : Real) ≤ r)
    (h : IntegerMultiplyLinearWith (fun _ => ((3 * q : Nat) : Real)) (cubicBaseExponent q) Gamma) :
    IntegerMultiplyLinearWith
      (fun sigma => (multipleQ (r⁻¹ * sigma) gamma 1) ^ r)
      (fun sigma => (multipleC (r⁻¹ * sigma) gamma 1) ^ r) Gamma := by
  apply h.weaken
  · intro sigma hs hs1; exact (integer_cubic_base_controls_fit hq hg hg1 hrq hs hs1).1
  · intro sigma hs _
    have hq1 : (1 : Real) ≤ q := by exact_mod_cast hq
    have hr : 0 < r := by linarith only [hrq, hq1]
    exact Real.rpow_pos_of_pos (multipleC_pos _ (by positivity) hg) _
  · intro sigma hs hs1; exact (integer_cubic_base_controls_fit hq hg hg1 hrq hs hs1).2

def lemma_16_3_integer_representatives : Prop :=
  ∀ (N : Nat) [NeZero N] [Fact N.Prime] (gamma theta : Real),
    0 < gamma → gamma ≤ 1 → 0 < theta → theta ≤ 1 →
    ∀ Gamma : Finset (Point N 1 × ZMod N),
      (Gamma.card : Real) ≤ gamma ^ (-(2 : Int)) * N →
      RelationProductProperty gamma Gamma →
      ∃ J : Finset (Point N 1), (1 - theta) * (N : Real) ≤ J.card ∧
        let r := gamma ^ (-(2 : Int)) * multipleS theta gamma 1
        IntegerMultiplyLinearWith
          (fun sigma => (multipleQ (r⁻¹ * sigma) gamma 1) ^ r)
          (fun sigma => (multipleC (r⁻¹ * sigma) gamma 1) ^ r) (restrictRelation Gamma J)

theorem lemma_16_3_integer_representatives_holds : lemma_16_3_integer_representatives := by
  intro N _ _ gamma theta hg hg1 ht ht1 Gamma hsize hprod
  obtain ⟨J, hJ, hcover⟩ := section16_product_relation_integer_cubic_cover hg hg1 ht ht1 Gamma hsize hprod
  exact ⟨J, hJ, hcover.base_source_controls (section16BaseFamilyBound_pos gamma theta)
    hg hg1 (section16_integer_base_source_budget hg hg1 ht ht1)⟩

end LeanProofs.GowersSzemeredi
