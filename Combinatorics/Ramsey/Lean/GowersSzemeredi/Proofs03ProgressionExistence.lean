import GowersSzemeredi.Proofs03Basic
import GowersSzemeredi.Proofs03ProgressionCount

/-!
# Existence of modular progressions from higher uniformity

This module proves the corrected prime-modulus form of Corollary 3.6.  The
printed interval argument has an invalid numerical comparison; for the
modular conclusion, applying Corollary 3.3 directly with every set equal to
`A` gives a stronger lower bound and avoids that issue.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

private lemma cor36_balanced_discValued {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) : DiscValued (balanced A) := by
  intro x
  classical
  have hd0 : 0 ≤ density A := density_nonneg A
  have hd1 : density A ≤ 1 := density_le_one A
  by_cases hx : x ∈ A
  · simp only [balanced, indicator, hx, if_true]
    norm_cast
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hd1)]
    linarith
  · simp only [balanced, indicator, hx, if_false, zero_sub]
    norm_cast
    rw [Real.norm_eq_abs, abs_neg, abs_of_nonneg hd0]
    exact hd1

private lemma cor36_rpow_half_pow_two (eta : Real) (heta : 0 ≤ eta) (n : Nat) :
    (eta ^ (2 ^ (n + 1) : Nat)) ^ ((1 : Real) / 2) =
      eta ^ (2 ^ n : Nat) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul heta, ← Real.rpow_natCast]
  congr 1
  push_cast
  rw [pow_succ]
  ring

private lemma cor36_uniform_descend_steps {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (eta : Real) (heta : 0 ≤ eta) (d t : Nat)
    (hU : UniformSetOfDegree A (eta ^ (2 ^ (d + t + 1) : Nat)) (d + t)) :
    UniformSetOfDegree A (eta ^ (2 ^ (d + 1) : Nat)) d := by
  induction t with
  | zero => simpa
  | succ t ih =>
      apply ih
      have hstep := lemma_3_4_holds N (d + t + 1) (balanced A)
        (eta ^ (2 ^ (d + t + 2) : Nat)) (by omega)
        (cor36_balanced_discValued A) hU
      change UniformOfDegree (balanced A)
        ((eta ^ (2 ^ (d + t + 2) : Nat)) ^ ((1 : Real) / 2))
        (d + t + 1 - 1) at hstep
      change UniformOfDegree (balanced A)
        (eta ^ (2 ^ (d + t + 1) : Nat)) (d + t)
      convert hstep using 1
      · exact (by
          simpa [Nat.add_assoc] using
            (cor36_rpow_half_pow_two eta heta (d + t + 1)).symm)
      · omega

private lemma cor36_two_pow_eta_le {k : Nat} (hk : 2 ≤ k)
    {alpha delta eta : Real} (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (halpha0 : 0 ≤ alpha)
    (heta : eta = alpha ^ ((1 : Real) / (2 : Real) ^ (k - 1)))
    (halpha : alpha ≤ (delta / 2) ^ ((k : Real) * 2 ^ k)) :
    (2 : Real) ^ k * eta ≤ delta ^ k / 2 := by
  have hbase : 0 ≤ delta / 2 := by positivity
  have hExp : 0 ≤ (1 : Real) / (2 : Real) ^ (k - 1) := by positivity
  have hetaUpper0 := Real.rpow_le_rpow halpha0 halpha hExp
  have hpowSucc : (2 : Real) ^ k = 2 * (2 : Real) ^ (k - 1) := by
    calc
      (2 : Real) ^ k = 2 ^ ((k - 1) + 1) := by congr 1; omega
      _ = 2 * 2 ^ (k - 1) := by rw [pow_succ]; ring
  have hExpMul :
      ((k : Real) * (2 : Real) ^ k) *
          ((1 : Real) / (2 : Real) ^ (k - 1)) = 2 * (k : Real) := by
    rw [hpowSucc]
    field_simp [pow_ne_zero]
  have hetaUpper : eta ≤ (delta / 2) ^ (2 * (k : Real)) := by
    rw [heta]
    calc
      alpha ^ ((1 : Real) / (2 : Real) ^ (k - 1)) ≤
          ((delta / 2) ^ ((k : Real) * 2 ^ k)) ^
            ((1 : Real) / (2 : Real) ^ (k - 1)) := hetaUpper0
      _ = (delta / 2) ^
          (((k : Real) * 2 ^ k) *
            ((1 : Real) / (2 : Real) ^ (k - 1))) := by
              rw [← Real.rpow_mul hbase]
      _ = (delta / 2) ^ (2 * (k : Real)) := by rw [hExpMul]
  let p : Real := delta ^ k
  let q : Real := (2 : Real) ^ k
  have hp0 : 0 ≤ p := pow_nonneg hdelta0.le _
  have hp1 : p ≤ 1 := by
    exact pow_le_one₀ hdelta0.le hdelta1
  have hq0 : 0 < q := by positivity
  have hq2 : 2 ≤ q := by
    have hp : (2 : Nat) ^ 1 ≤ 2 ^ k :=
      Nat.pow_le_pow_right (by omega) (by omega)
    dsimp only [q]
    exact_mod_cast hp
  have hbasePower :
      (delta / 2) ^ (2 * (k : Real)) = p ^ 2 / q ^ 2 := by
    rw [show 2 * (k : Real) = ((2 * k : Nat) : Real) by norm_num,
      Real.rpow_natCast, div_pow]
    change delta ^ (2 * k) / (2 : Real) ^ (2 * k) = p ^ 2 / q ^ 2
    simp only [p, q]
    rw [show 2 * k = k * 2 by omega, pow_mul, pow_mul]
  have hpSq : p ^ 2 ≤ p := by nlinarith
  calc
    q * eta ≤ q * (p ^ 2 / q ^ 2) := by
      rw [← hbasePower]
      exact mul_le_mul_of_nonneg_left hetaUpper hq0.le
    _ = p ^ 2 / q := by field_simp [ne_of_gt hq0]
    _ ≤ p / q := div_le_div_of_nonneg_right hpSq hq0.le
    _ ≤ p / 2 := div_le_div_of_nonneg_left hp0 (by norm_num) hq2

private lemma cor36_count_le_modulus_of_no_ap {N k : Nat} [NeZero N]
    (A : Finset (ZMod N)) (hno : ¬ HasModAP A k) :
    translatedIntersectionCount (fun _ : Fin k ↦ A) ≤ N := by
  classical
  unfold translatedIntersectionCount countWhere
  rw [Finset.filter_congr_decidable]
  calc
    ((Finset.univ.filter fun p : ZMod N × ZMod N =>
        ∀ i : Fin k, p.2 - ((i : Nat) + 1) * p.1 ∈
          (fun _ : Fin k ↦ A) i).card) ≤
        (Finset.univ.filter fun p : ZMod N × ZMod N => p.1 = 0).card := by
      apply Finset.card_le_card
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      by_contra hr
      apply hno
      refine ⟨p.2 - p.1, -p.1, bne_iff_ne.mpr (neg_ne_zero.mpr hr), ?_⟩
      intro i hi
      have hm := hp ⟨i, hi⟩
      convert hm using 1
      push_cast
      ring
    _ = N := by
      rw [show (Finset.univ.filter fun p : ZMod N × ZMod N => p.1 = 0) =
          ({0} : Finset (ZMod N)) ×ˢ Finset.univ by
        ext p
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_product, Finset.mem_singleton]
        tauto]
      simp [ZMod.card]

/-- The corrected modular form of Gowers's Corollary 3.6. -/
theorem corollary_3_6_holds : corollary_3_6 := by
  intro N k _ _ hkN A alpha delta hdelta hk hcard hUniform halpha hlarge
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hdelta1 : delta ≤ 1 := by
    calc
      delta = (A.card : Real) / N := by rw [hcard]; field_simp
      _ ≤ N / N := by
        gcongr
        have hcardle : A.card ≤ N := by
          simpa [ZMod.card] using A.card_le_univ
        exact_mod_cast hcardle
      _ = 1 := div_self (ne_of_gt hN)
  have halpha0 : 0 ≤ alpha := by
    unfold UniformSetOfDegree UniformOfDegree at hUniform
    have hsum : 0 ≤ ∑ a : Point N (k - 2),
        ‖∑ s : ZMod N, cubeDifference (balanced A) a s‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
    have hmul : 0 ≤ alpha * (N : Real) ^ (k - 2 + 2) := hsum.trans hUniform
    exact nonneg_of_mul_nonneg_left hmul (pow_pos hN _)
  let eta : Real := alpha ^ ((1 : Real) / (2 : Real) ^ (k - 1))
  have heta0 : 0 ≤ eta := Real.rpow_nonneg halpha0 _
  have hetaTop : eta ^ (2 ^ (k - 1) : Nat) = alpha := by
    dsimp only [eta]
    convert Real.rpow_inv_natCast_pow halpha0
      (show 2 ^ (k - 1) ≠ 0 by positivity) using 1
    norm_num
  have hUniformTop : UniformSetOfDegree A (eta ^ (2 ^ (k - 1) : Nat)) (k - 2) := by
    rwa [hetaTop]
  have hUniformEach : ∀ i : Fin k, 3 ≤ (i : Nat) + 1 →
      UniformSetOfDegree A (eta ^ (2 ^ (i : Nat) : Nat)) ((i : Nat) - 1) := by
    intro i hi
    have hid : (i : Nat) - 1 ≤ k - 2 := by omega
    have hsum : (i : Nat) - 1 + ((k - 2) - ((i : Nat) - 1)) = k - 2 := by
      omega
    have hdesc := cor36_uniform_descend_steps A eta heta0 ((i : Nat) - 1)
      ((k - 2) - ((i : Nat) - 1))
    rw [hsum] at hdesc
    have htop' : UniformSetOfDegree A
        (eta ^ (2 ^ ((k - 2) + 1) : Nat)) (k - 2) := by
      simpa only [show k - 2 + 1 = k - 1 by omega] using hUniformTop
    have := hdesc htop'
    simpa only [show (i : Nat) - 1 + 1 = (i : Nat) by omega] using this
  have hcor := corollary_3_3_holds N k hkN (fun _ : Fin k ↦ A)
    (fun _ : Fin k ↦ delta) eta heta0 (by intro i; exact hcard) hUniformEach
  have hprod : (∏ _i : Fin k, delta) = delta ^ k := by simp
  rw [hprod] at hcor
  have herror : (2 : Real) ^ k * eta ≤ delta ^ k / 2 :=
    cor36_two_pow_eta_le hk hdelta hdelta1 halpha0 rfl halpha
  have hcountLower : delta ^ k * (N : Real) ^ 2 / 2 ≤
      (translatedIntersectionCount (fun _ : Fin k ↦ A) : Real) := by
    have herrN := mul_le_mul_of_nonneg_right herror (sq_nonneg (N : Real))
    have hlower := (abs_le.mp hcor).1
    nlinarith
  have hdeltaPow : 0 < delta ^ k := pow_pos hdelta _
  have hinv : delta ^ (-(k : Real)) = (delta ^ k)⁻¹ := by
    rw [Real.rpow_neg hdelta.le, Real.rpow_natCast]
  rw [hinv] at hlarge
  have hscale : 32 * (k : Real) ^ 2 ≤ delta ^ k * N := by
    have := mul_le_mul_of_nonneg_right hlarge hdeltaPow.le
    field_simp [ne_of_gt hdeltaPow] at this
    nlinarith
  have hkSq : (1 : Real) < 16 * (k : Real) ^ 2 := by
    have hkReal : (2 : Real) ≤ k := by exact_mod_cast hk
    nlinarith [sq_nonneg ((k : Real) - 2)]
  have hcountLarge : (N : Real) <
      (translatedIntersectionCount (fun _ : Fin k ↦ A) : Real) := by
    calc
      (N : Real) < 16 * (k : Real) ^ 2 * N := by nlinarith
      _ ≤ delta ^ k * (N : Real) ^ 2 / 2 := by
        have hs := mul_le_mul_of_nonneg_right hscale hN.le
        nlinarith
      _ ≤ _ := hcountLower
  by_contra hno
  have hcountUpper := cor36_count_le_modulus_of_no_ap A hno
  have : (translatedIntersectionCount (fun _ : Fin k ↦ A) : Real) ≤ N := by
    exact_mod_cast hcountUpper
  linarith

end LeanProofs.GowersSzemeredi
