import GowersSzemeredi.Proofs05PolynomialPartition
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Removing polynomial phases on the Section 5 partition

This module isolates the analytic deduction of Corollary 5.7 from the
target-length partition in Corollary 5.6.  Keeping this implication separate
lets the quantitative Weyl/recurrence proof supply the sole remaining input.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

@[simp] private lemma cor57_norm_exponential {N : Nat} [NeZero N]
    (x : ZMod N) : ‖exponential x‖ = 1 := by
  exact AddChar.norm_apply (ZMod.stdAddChar (N := N)) x

@[simp] private lemma cor57_exponential_add {N : Nat} [NeZero N]
    (x y : ZMod N) :
    exponential (x + y) = exponential x * exponential y := by
  exact AddChar.map_add_eq_mul (ZMod.stdAddChar (N := N)) x y

private lemma cor57_exponential_eq_exp_valMinAbs {N : Nat} [NeZero N]
    (x : ZMod N) :
    exponential x =
      Complex.exp
        (Complex.I * (2 * Real.pi * (x.valMinAbs : Real) / N : Real)) := by
  calc
    exponential x = ZMod.stdAddChar ((x.valMinAbs : Int) : ZMod N) := by
      simp [exponential]
    _ = Complex.exp (2 * Real.pi * Complex.I * (x.valMinAbs : Int) / N) :=
      ZMod.stdAddChar_coe x.valMinAbs
    _ = Complex.exp
        (Complex.I * (2 * Real.pi * (x.valMinAbs : Real) / N : Real)) := by
      congr 1
      push_cast
      ring

private lemma cor57_norm_exponential_sub_one_le {N : Nat} [NeZero N]
    (x : ZMod N) :
    ‖exponential x - 1‖ ≤ 2 * Real.pi * centeredAbs x / N := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have habsval : |(x.valMinAbs : Real)| = (centeredAbs x : Real) := by
    rw [centeredAbs, ← Int.cast_abs, Int.abs_eq_natAbs]
    rfl
  rw [cor57_exponential_eq_exp_valMinAbs]
  calc
    ‖Complex.exp
        (Complex.I * (2 * Real.pi * (x.valMinAbs : Real) / N : Real)) - 1‖ ≤
        ‖2 * Real.pi * (x.valMinAbs : Real) / N‖ :=
      Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = 2 * Real.pi * centeredAbs x / N := by
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul,
        abs_of_nonneg (by norm_num : (0 : Real) ≤ 2),
        abs_of_pos Real.pi_pos, habsval, abs_of_pos hN]

private lemma cor57_centeredAbs_natCast_le {N i : Nat} [NeZero N] :
    centeredAbs (i : ZMod N) ≤ i := by
  rw [centeredAbs, ZMod.valMinAbs_natAbs_eq_min, ZMod.val_natCast]
  exact (Nat.min_le_left _ _).trans (Nat.mod_le i N)

private lemma cor57_centeredAbs_neg_natCast_le {N i : Nat} [NeZero N] :
    centeredAbs (-(i : ZMod N)) ≤ i := by
  rw [centeredAbs, ZMod.natAbs_valMinAbs_neg]
  exact cor57_centeredAbs_natCast_le

private lemma cor57_phase_close_of_mem_interval {N d : Nat} [NeZero N]
    (a y : ZMod N) (hy : y ∈ (modInterval N a (d + 1)).carrier) :
    ‖exponential (-y) - exponential (-a)‖ ≤
      2 * Real.pi * d / N := by
  classical
  unfold ModAP.carrier modInterval at hy
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hy
  obtain ⟨i, rfl⟩ := hy
  have hi : (i : Nat) ≤ d := by omega
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  simp only [mul_one]
  calc
    ‖exponential (-(a + (i : ZMod N))) - exponential (-a)‖ =
        ‖exponential (-a) * (exponential (-(i : ZMod N)) - 1)‖ := by
      congr 1
      rw [show -(a + (i : ZMod N)) = -a + -(i : ZMod N) by ring]
      rw [cor57_exponential_add]
      ring
    _ = ‖exponential (-(i : ZMod N)) - 1‖ := by
      rw [norm_mul, cor57_norm_exponential, one_mul]
    _ ≤ 2 * Real.pi * centeredAbs (-(i : ZMod N)) / N :=
      cor57_norm_exponential_sub_one_le _
    _ ≤ 2 * Real.pi * d / N := by
      apply div_le_div_of_nonneg_right _ hN.le
      gcongr
      exact_mod_cast
        (cor57_centeredAbs_neg_natCast_le (N := N) (i := (i : Nat))).trans hi

private lemma cor57_sum_partition {X : Type*} [DecidableEq X] {m : Nat}
    (P : Fin m → Finset X) (S : Finset X) (hpartition : IsPartition P S)
    (g : X → Complex) :
    ∑ j, ∑ x ∈ P j, g x = ∑ x ∈ S, g x := by
  classical
  have hpair : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint P := by
    intro i _ j _ hij
    exact hpartition.2 i j (bne_iff_ne.mpr hij)
  have hunion : (Finset.univ : Finset (Fin m)).biUnion P = S := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact (hpartition.1 x).symm
  rw [show (∑ j, ∑ x ∈ P j, g x) =
      ∑ j ∈ (Finset.univ : Finset (Fin m)), ∑ x ∈ P j, g x by simp]
  rw [← Finset.sum_biUnion hpair, hunion]

private lemma cor57_card_partition {X : Type*} [DecidableEq X] {m : Nat}
    (P : Fin m → Finset X) (S : Finset X) (hpartition : IsPartition P S) :
    ∑ j, (P j).card = S.card := by
  apply Nat.cast_injective (R := Complex)
  calc
    ((∑ j, (P j).card : Nat) : Complex) =
        ∑ j, ∑ _x ∈ P j, (1 : Complex) := by simp
    _ = ∑ _x ∈ S, (1 : Complex) :=
      cor57_sum_partition P S hpartition _
    _ = (S.card : Complex) := by simp

private lemma cor57_alpha_le_one {N r : Nat} [NeZero N]
    (f : ZMod N → Complex) (phi : ZMod N → ZMod N) (alpha : Real)
    (hr : 0 < r) (hf : DiscValued f)
    (hpremise : alpha * r ≤
      ‖∑ x ∈ Finset.range r,
        f (x : ZMod N) * exponential (-(phi (x : ZMod N)))‖) :
    alpha ≤ 1 := by
  have hnorm :
      ‖∑ x ∈ Finset.range r,
        f (x : ZMod N) * exponential (-(phi (x : ZMod N)))‖ ≤ r := by
    calc
      _ ≤ ∑ x ∈ Finset.range r,
          ‖f (x : ZMod N) * exponential (-(phi (x : ZMod N)))‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _x ∈ Finset.range r, (1 : Real) := by
        apply Finset.sum_le_sum
        intro x hx
        rw [norm_mul, cor57_norm_exponential, mul_one]
        exact hf _
      _ = r := by simp
  have hrReal : (0 : Real) < r := by exact_mod_cast hr
  nlinarith

private lemma cor57_partition_constant_pos (k : Nat) :
    0 < polynomialPartitionConstant k := by
  unfold polynomialPartitionConstant
  positivity

private lemma cor57_scale_lt {k r : Nat} (alpha : Real)
    (halpha : 0 < alpha)
    (hlarge :
      (4 * Real.pi / alpha) ^ polynomialPartitionConstant k < (r : Real)) :
    (r : Real) ^ (-(polynomialPartitionConstant k : Real)⁻¹) <
      alpha / (4 * Real.pi) := by
  let K := polynomialPartitionConstant k
  have hK : 0 < K := cor57_partition_constant_pos k
  have hKReal : (0 : Real) < K := by exact_mod_cast hK
  have hr : (0 : Real) < r := by
    have hbase : 0 < 4 * Real.pi / alpha := by positivity
    exact (pow_nonneg hbase.le K).trans_lt hlarge
  have hbase : 0 < 4 * Real.pi / alpha := by positivity
  have hroot : 4 * Real.pi / alpha < (r : Real) ^ (K : Real)⁻¹ := by
    rw [Real.lt_rpow_inv_iff_of_pos hbase.le hr.le hKReal]
    simpa only [Real.rpow_natCast] using hlarge
  have hrootPos : 0 < (r : Real) ^ (K : Real)⁻¹ :=
    Real.rpow_pos_of_pos hr _
  have hinv : ((r : Real) ^ (K : Real)⁻¹)⁻¹ <
      (4 * Real.pi / alpha)⁻¹ :=
    (inv_lt_inv₀ hrootPos hbase).2 hroot
  rw [Real.rpow_neg hr.le]
  have hright : (4 * Real.pi / alpha)⁻¹ = alpha / (4 * Real.pi) := by
    field_simp
  simpa only [K, hright] using hinv

private lemma cor57_cell_norm_le {N : Nat} [NeZero N]
    (S : Finset Nat) (f : ZMod N → Complex) (phi : ZMod N → ZMod N)
    (alpha scale : Real) (hf : DiscValued f)
    (hdiam : diameterAtMostReal (S.image fun x : Nat => phi (x : ZMod N)) scale)
    (hscale : scale ≤ alpha * N / (4 * Real.pi)) :
    ‖∑ s ∈ S, f (s : ZMod N) * exponential (-(phi (s : ZMod N)))‖ ≤
      ‖∑ s ∈ S, f (s : ZMod N)‖ + alpha / 2 * S.card := by
  classical
  obtain ⟨d, ⟨a, hsubset⟩, hdscale⟩ := hdiam
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hphase (s : Nat) (hs : s ∈ S) :
      ‖exponential (-(phi (s : ZMod N))) - exponential (-a)‖ ≤ alpha / 2 := by
    have himage : phi (s : ZMod N) ∈
        S.image (fun x : Nat => phi (x : ZMod N)) :=
      Finset.mem_image.mpr ⟨s, hs, rfl⟩
    calc
      _ ≤ 2 * Real.pi * d / N :=
        cor57_phase_close_of_mem_interval a _ (hsubset himage)
      _ ≤ 2 * Real.pi * scale / N := by gcongr
      _ ≤ alpha / 2 := by
        have hpi : (0 : Real) < 4 * Real.pi := by positivity
        have hscaled : scale * (4 * Real.pi) ≤ alpha * N :=
          (le_div_iff₀ hpi).1 hscale
        apply (div_le_iff₀ hN).2
        nlinarith [Real.pi_pos]
  let twisted := ∑ s ∈ S,
    f (s : ZMod N) * exponential (-(phi (s : ZMod N)))
  let plain := ∑ s ∈ S, f (s : ZMod N)
  let err := ∑ s ∈ S,
    f (s : ZMod N) *
      (exponential (-(phi (s : ZMod N))) - exponential (-a))
  have hdecomp : twisted = exponential (-a) * plain + err := by
    dsimp only [twisted, plain, err]
    rw [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    ring
  have herr : ‖err‖ ≤ alpha / 2 * S.card := by
    dsimp only [err]
    calc
      _ ≤ ∑ s ∈ S,
          ‖f (s : ZMod N) *
            (exponential (-(phi (s : ZMod N))) - exponential (-a))‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _s ∈ S, alpha / 2 := by
        apply Finset.sum_le_sum
        intro s hs
        rw [norm_mul]
        calc
          ‖f (s : ZMod N)‖ *
              ‖exponential (-(phi (s : ZMod N))) - exponential (-a)‖ ≤
              1 * (alpha / 2) :=
            mul_le_mul (hf _) (hphase s hs) (norm_nonneg _) (by norm_num)
          _ = alpha / 2 := one_mul _
      _ = alpha / 2 * S.card := by simp [mul_comm]
  change ‖twisted‖ ≤ ‖plain‖ + alpha / 2 * S.card
  rw [hdecomp]
  calc
    ‖exponential (-a) * plain + err‖ ≤
        ‖exponential (-a) * plain‖ + ‖err‖ := norm_add_le _ _
    _ ≤ ‖plain‖ + alpha / 2 * S.card := by
      rw [norm_mul, cor57_norm_exponential, one_mul]
      gcongr

/-- The analytic part of Corollary 5.7, conditional only on the corrected
target-length form of Corollary 5.6. -/
theorem corollary_5_7_holds_of_corollary_5_6
    (h56 : corollary_5_6) : corollary_5_7 := by
  classical
  intro N k r v _ phi alpha hk hphi halpha hlarge hrN hv hvupper
  have hr : 0 < r := by
    have hthreshold : (0 : Real) ≤ polynomialPartitionThreshold k := by positivity
    have : (0 : Real) < r := hthreshold.trans_lt (lt_of_le_of_lt
      (le_max_left _ _) hlarge)
    exact_mod_cast this
  have hthreshold : polynomialPartitionThreshold k < r := by
    exact_mod_cast (lt_of_le_of_lt (le_max_left _ _) hlarge)
  obtain ⟨M, P, hM, hpartition, hproper, hdiameter⟩ :=
    h56 N k r v phi hk hphi hthreshold hrN hv hvupper
  refine ⟨M, P, hM, hpartition, hproper, ?_⟩
  intro f hf hpremise
  have hpolyLarge :
      (4 * Real.pi / alpha) ^ polynomialPartitionConstant k < (r : Real) :=
    lt_of_le_of_lt (le_max_right _ _) hlarge
  have hscale :
      (r : Real) ^ (-(polynomialPartitionConstant k : Real)⁻¹) * N ≤
        alpha * N / (4 * Real.pi) := by
    have := (cor57_scale_lt alpha halpha hpolyLarge).le
    have hN : (0 : Real) ≤ N := by positivity
    calc
      (r : Real) ^ (-(polynomialPartitionConstant k : Real)⁻¹) * N ≤
          (alpha / (4 * Real.pi)) * N := mul_le_mul_of_nonneg_right this hN
      _ = alpha * N / (4 * Real.pi) := by ring
  have hcell (j : Fin M) :
      ‖∑ s ∈ (P j).carrier,
          f (s : ZMod N) * exponential (-(phi (s : ZMod N)))‖ ≤
        ‖∑ s ∈ (P j).carrier, f (s : ZMod N)‖ +
          alpha / 2 * (P j).carrier.card :=
    cor57_cell_norm_le (P j).carrier f phi alpha
      ((r : Real) ^ (-(polynomialPartitionConstant k : Real)⁻¹) * N)
      hf (hdiameter j) hscale
  have htwisted :
      (∑ j, ∑ s ∈ (P j).carrier,
          f (s : ZMod N) * exponential (-(phi (s : ZMod N)))) =
        ∑ s ∈ Finset.range r,
          f (s : ZMod N) * exponential (-(phi (s : ZMod N))) :=
    cor57_sum_partition (fun j => (P j).carrier) (Finset.range r)
      hpartition _
  have hcards :
      ∑ j, ((P j).carrier.card : Real) = r := by
    have hc := cor57_card_partition (fun j => (P j).carrier)
      (Finset.range r) hpartition
    rw [Finset.card_range] at hc
    exact_mod_cast hc
  calc
    alpha / 2 * r ≤ alpha * r - alpha / 2 * r := by
      ring_nf
      exact le_rfl
    _ ≤ ‖∑ s ∈ Finset.range r,
          f (s : ZMod N) * exponential (-(phi (s : ZMod N)))‖ -
        alpha / 2 * r := sub_le_sub_right hpremise _
    _ = ‖∑ j, ∑ s ∈ (P j).carrier,
          f (s : ZMod N) * exponential (-(phi (s : ZMod N)))‖ -
        alpha / 2 * r := by rw [htwisted]
    _ ≤ (∑ j, ‖∑ s ∈ (P j).carrier,
          f (s : ZMod N) * exponential (-(phi (s : ZMod N)))‖) -
        alpha / 2 * r := by gcongr; exact norm_sum_le _ _
    _ ≤ (∑ j, (‖∑ s ∈ (P j).carrier, f (s : ZMod N)‖ +
          alpha / 2 * (P j).carrier.card)) - alpha / 2 * r := by
      gcongr
      exact hcell _
    _ = ∑ j, ‖∑ s ∈ (P j).carrier, f (s : ZMod N)‖ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hcards]
      ring

end LeanProofs.GowersSzemeredi
