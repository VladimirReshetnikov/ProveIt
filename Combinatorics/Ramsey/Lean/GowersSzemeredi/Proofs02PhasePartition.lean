import GowersSzemeredi.Proofs02Partition
import GowersSzemeredi.ProofInfrastructure
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Phase-removing progression partitions in Gowers's Section 2

This module audits and proves the rounding-corrected form of Corollary 2.4.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

@[simp] private lemma cor24_norm_exponential {N : Nat} [NeZero N]
    (x : ZMod N) : ‖exponential x‖ = 1 := by
  exact AddChar.norm_apply (ZMod.stdAddChar (N := N)) x

@[simp] private lemma cor24_exponential_add {N : Nat} [NeZero N]
    (x y : ZMod N) :
    exponential (x + y) = exponential x * exponential y := by
  exact AddChar.map_add_eq_mul (ZMod.stdAddChar (N := N)) x y

private lemma cor24_exponential_eq_exp_valMinAbs {N : Nat} [NeZero N]
    (x : ZMod N) :
    exponential x =
      Complex.exp (Complex.I * (2 * Real.pi * (x.valMinAbs : Real) / N : Real)) := by
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

private lemma cor24_norm_exponential_sub_one_le {N : Nat} [NeZero N]
    (x : ZMod N) :
    ‖exponential x - 1‖ <= 2 * Real.pi * centeredAbs x / N := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have habsval : |(x.valMinAbs : Real)| = (centeredAbs x : Real) := by
    rw [centeredAbs, ← Int.cast_abs, Int.abs_eq_natAbs]
    rfl
  rw [cor24_exponential_eq_exp_valMinAbs]
  calc
    ‖Complex.exp
        (Complex.I * (2 * Real.pi * (x.valMinAbs : Real) / N : Real)) - 1‖ <=
        ‖2 * Real.pi * (x.valMinAbs : Real) / N‖ :=
      Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = 2 * Real.pi * centeredAbs x / N := by
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul,
        abs_of_nonneg (by norm_num : (0 : Real) <= 2),
        abs_of_pos Real.pi_pos, habsval, abs_of_pos hN]

private lemma cor24_centeredAbs_natCast_le {N i : Nat} [NeZero N] :
    centeredAbs (i : ZMod N) <= i := by
  rw [centeredAbs, ZMod.valMinAbs_natAbs_eq_min, ZMod.val_natCast]
  exact (Nat.min_le_left _ _).trans (Nat.mod_le i N)

private lemma cor24_centeredAbs_neg_natCast_le {N i : Nat} [NeZero N] :
    centeredAbs (-(i : ZMod N)) <= i := by
  rw [centeredAbs, ZMod.natAbs_valMinAbs_neg]
  exact cor24_centeredAbs_natCast_le

private lemma cor24_phase_close_of_mem_interval {N s : Nat} [NeZero N]
    (a y : ZMod N) (hy : y ∈ (modInterval N a (s + 1)).carrier) :
    ‖exponential (-y) - exponential (-a)‖ <=
      2 * Real.pi * s / N := by
  classical
  unfold ModAP.carrier modInterval at hy
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hy
  obtain ⟨i, rfl⟩ := hy
  have hi : (i : Nat) <= s := by omega
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  simp only [mul_one]
  calc
    ‖exponential (-(a + (i : ZMod N))) - exponential (-a)‖ =
        ‖exponential (-a) * (exponential (-(i : ZMod N)) - 1)‖ := by
      congr 1
      rw [show -(a + (i : ZMod N)) = -a + -(i : ZMod N) by ring]
      rw [cor24_exponential_add]
      ring
    _ = ‖exponential (-(i : ZMod N)) - 1‖ := by
      rw [norm_mul, cor24_norm_exponential, one_mul]
    _ <= 2 * Real.pi * centeredAbs (-(i : ZMod N)) / N :=
      cor24_norm_exponential_sub_one_le _
    _ <= 2 * Real.pi * s / N := by
      apply div_le_div_of_nonneg_right _ hN.le
      gcongr
      exact_mod_cast (cor24_centeredAbs_neg_natCast_le (N := N) (i := (i : Nat))).trans hi

private lemma cor24_sum_partition {X : Type*} [DecidableEq X] {m : Nat}
    (P : Fin m -> Finset X) (S : Finset X)
    (hpartition : IsPartition P S) (g : X -> Complex) :
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

private def cor24Singleton (x : Nat) : NatAP where
  start := x
  step := 1
  length := 1

@[simp] private lemma cor24Singleton_carrier (x : Nat) :
    (cor24Singleton x).carrier = {x} := by
  classical
  ext y
  simp [cor24Singleton, NatAP.carrier]

private lemma cor24Singleton_partition (r : Nat) :
    IsNatAPPartition (fun i : Fin r => cor24Singleton i) (Finset.range r) := by
  classical
  constructor
  · intro x
    simp only [Finset.mem_range, cor24Singleton_carrier, Finset.mem_singleton]
    constructor
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      exact i.isLt
  · intro i j hij
    change Disjoint (cor24Singleton (i : Nat)).carrier
      (cor24Singleton (j : Nat)).carrier
    rw [cor24Singleton_carrier, cor24Singleton_carrier]
    exact Finset.disjoint_singleton.mpr fun h =>
      bne_iff_ne.mp hij (Fin.ext h)

private lemma cor24_alpha_le_one {N r : Nat} [NeZero N]
    (f : Nat -> Complex) (phi : ZMod N -> ZMod N) (alpha : Real)
    (hr : 0 < r) (hf : ∀ x, x < r -> ‖f x‖ <= 1)
    (hpremise : alpha * r <=
      ‖∑ x ∈ Finset.range r, f x * exponential (-(phi x))‖) :
    alpha <= 1 := by
  have hnorm :
      ‖∑ x ∈ Finset.range r, f x * exponential (-(phi x))‖ <= r := by
    calc
      _ <= ∑ x ∈ Finset.range r,
          ‖f x * exponential (-(phi x))‖ := norm_sum_le _ _
      _ <= ∑ _x ∈ Finset.range r, (1 : Real) := by
        apply Finset.sum_le_sum
        intro x hx
        rw [norm_mul, cor24_norm_exponential, mul_one]
        exact hf x (Finset.mem_range.mp hx)
      _ = r := by simp
  have hrReal : (0 : Real) < r := by exact_mod_cast hr
  nlinarith

private lemma cor24_exists_integer_scale {N r : Nat} [NeZero N]
    (alpha : Real) (hrN : r <= N) (hscale : 8 * Real.pi <= alpha * r)
    (halpha : 0 < alpha) (halphaOne : alpha <= 1) :
    exists s : Nat, 0 < s /\ s <= N /\ N <= r * s /\
      alpha * N / (8 * Real.pi) <= s /\
      (s : Real) <= alpha * N / (4 * Real.pi) := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hrNReal : (r : Real) <= N := by exact_mod_cast hrN
  have hdenEight : (0 : Real) < 8 * Real.pi := by positivity
  have hdenFour : (0 : Real) < 4 * Real.pi := by positivity
  let x : Real := alpha * N / (8 * Real.pi)
  let s : Nat := Nat.ceil x
  have hxOne : 1 <= x := by
    dsimp only [x]
    apply (le_div_iff₀ hdenEight).2
    nlinarith [mul_le_mul_of_nonneg_left hrNReal halpha.le]
  have hxNonneg : 0 <= x := le_trans (by norm_num) hxOne
  have hsLower : x <= (s : Real) := by
    simpa only [s] using Nat.le_ceil x
  have hsLt : (s : Real) < x + 1 := by
    simpa only [s] using Nat.ceil_lt_add_one hxNonneg
  have hsUpper : (s : Real) <= alpha * N / (4 * Real.pi) := by
    calc
      (s : Real) <= 2 * x := by linarith
      _ = alpha * N / (4 * Real.pi) := by
        dsimp only [x]
        field_simp
        ring
  have hsPos : 0 < s := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : Real) < 1) (hxOne.trans hsLower)
  have hsNReal : (s : Real) <= N := by
    calc
      (s : Real) <= alpha * N / (4 * Real.pi) := hsUpper
      _ <= N := by
        apply (div_le_iff₀ hdenFour).2
        nlinarith [Real.pi_gt_three]
  have hsN : s <= N := by exact_mod_cast hsNReal
  have hrsReal : (N : Real) <= r * s := by
    calc
      (N : Real) <= (r : Real) * x := by
        dsimp only [x]
        rw [show (r : Real) * (alpha * N / (8 * Real.pi)) =
            (alpha * r * N) / (8 * Real.pi) by ring]
        apply (le_div_iff₀ hdenEight).2
        nlinarith
      _ <= (r : Real) * s := by
        gcongr
  have hrs : N <= r * s := by exact_mod_cast hrsReal
  exact ⟨s, hsPos, hsN, hrs, by simpa only [x] using hsLower, hsUpper⟩

private lemma cor24_reciprocal_scales (alpha : Real) (r : Nat)
    (halpha : 0 < alpha) (hr : 0 < r) :
    Real.sqrt (alpha * r / (128 * Real.pi)) *
        Real.sqrt (128 * Real.pi * r / alpha) = r := by
  have hA : 0 <= alpha * (r : Real) / (128 * Real.pi) := by positivity
  rw [← Real.sqrt_mul hA]
  have hprod :
      (alpha * (r : Real) / (128 * Real.pi)) *
          (128 * Real.pi * r / alpha) = (r : Real) ^ 2 := by
    field_simp
  rw [hprod, Real.sqrt_sq_eq_abs, abs_of_nonneg]
  positivity

private def corollary_2_4_before_rounding_repair : Prop :=
  forall (N r : Nat) [NeZero N] (f : Nat -> Complex) (phi : ZMod N -> ZMod N)
      (alpha : Real),
    (∀ x, x < r → ‖f x‖ <= 1) -> LinearOn Finset.univ phi -> 0 < alpha ->
    alpha * r <= ‖∑ x ∈ Finset.range r, f x * exponential (-(phi x))‖ ->
    exists m : Nat, exists P : Fin m -> NatAP,
      IsNatAPPartition P (Finset.range r) /\
      (m : Real) <= Real.sqrt (16 * Real.pi * r / alpha) /\
      (alpha / 2) * r <= ∑ j, ‖∑ x ∈ (P j).carrier, f x‖ /\
      (forall j, Real.sqrt (alpha * r / Real.pi) / 4 <= (P j).length /\
        ((P j).length : Real) <= Real.sqrt (alpha * r / Real.pi) / 2)

/-- The unqualified finite statement is false at its smallest admissible
parameter: its asserted upper length can be strictly below one. -/
theorem corollary_2_4_before_rounding_repair_false :
    ¬ corollary_2_4_before_rounding_repair := by
  intro h
  obtain ⟨m, P, hpartition, _hm, _hsum, hlength⟩ :=
    h 1 1 (fun _ => 1) (fun _ => 0) 1
      (by intro x hx; simp)
      (by refine ⟨0, 0, ?_⟩; simp)
      (by norm_num)
      (by norm_num [exponential])
  have hzero : 0 ∈ Finset.range 1 := by simp
  obtain ⟨j, hj⟩ := (hpartition.1 0).mp hzero
  have hlenPos : 0 < (P j).length := by
    have hcardPos : 0 < (P j).carrier.card := Finset.card_pos.mpr ⟨0, hj⟩
    have hcardLe : (P j).carrier.card ≤ (P j).length := by
      unfold NatAP.carrier
      calc
        (Finset.univ.image fun i : Fin (P j).length =>
            (P j).start + (i : Nat) * (P j).step).card ≤
            (Finset.univ : Finset (Fin (P j).length)).card :=
          Finset.card_image_le
        _ = (P j).length := by simp
    exact hcardPos.trans_le hcardLe
  have hlenOne : (1 : Real) ≤ (P j).length := by exact_mod_cast hlenPos
  have hfrac : (1 : Real) / Real.pi < 1 := by
    exact (div_lt_one Real.pi_pos).2 (lt_trans (by norm_num) Real.pi_gt_three)
  have hsqrt : Real.sqrt ((1 : Real) / Real.pi) < 1 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : Real) < 1)]
    simpa using hfrac
  have hupper := (hlength j).2
  norm_num only [Nat.cast_one, one_mul] at hupper
  nlinarith

/-- **Gowers, Corollary 2.4.**  On the finite scale where its integer
diameter parameter exists, the phase can be removed cell by cell from the
rounding-corrected progression partition of Lemma 2.3. -/
theorem corollary_2_4_holds : corollary_2_4 := by
  intro N r _ f phi alpha hrN hscale hf hlinear halpha hpremise
  classical
  have hN : 0 < N := NeZero.pos N
  have hprodPos : (0 : Real) < alpha * r :=
    lt_of_lt_of_le (by positivity : (0 : Real) < 4 * Real.pi) hscale
  have hr : 0 < r := by
    by_contra hr0
    have : r = 0 := Nat.eq_zero_of_not_pos hr0
    subst r
    norm_num at hprodPos
  have hrReal : (0 : Real) < r := by exact_mod_cast hr
  have halphaOne : alpha <= 1 :=
    cor24_alpha_le_one f phi alpha hr hf hpremise
  by_cases hlarge : 8 * Real.pi <= alpha * r
  swap
  · have hsmall : alpha * r < 8 * Real.pi := lt_of_not_ge hlarge
    have hsmall128 : alpha * r <= 128 * Real.pi := by
      nlinarith [Real.pi_pos]
    have hradLowerNonneg :
        0 <= alpha * r / (128 * Real.pi) := by positivity
    have hradLowerOne : alpha * r / (128 * Real.pi) <= 1 := by
      exact (div_le_one (by positivity : (0 : Real) < 128 * Real.pi)).2 hsmall128
    have hLowerOne : Real.sqrt (alpha * r / (128 * Real.pi)) <= 1 := by
      nlinarith [Real.sq_sqrt hradLowerNonneg,
        Real.sqrt_nonneg (alpha * r / (128 * Real.pi))]
    have hradUpperOne : 1 <= alpha * r / (4 * Real.pi) := by
      apply (le_div_iff₀ (by positivity : (0 : Real) < 4 * Real.pi)).2
      simpa only [one_mul] using hscale
    have hUpperOne : 1 <= Real.sqrt (alpha * r / (4 * Real.pi)) := by
      exact Real.one_le_sqrt.mpr hradUpperOne
    have hradCountNonneg :
        0 <= 128 * Real.pi * r / alpha := by positivity
    have hcountSq : (r : Real) ^ 2 <= 128 * Real.pi * r / alpha := by
      apply (le_div_iff₀ halpha).2
      have hmul := mul_le_mul_of_nonneg_right hsmall128 hrReal.le
      nlinarith
    have hcount : (r : Real) <= Real.sqrt (128 * Real.pi * r / alpha) := by
      nlinarith [Real.sq_sqrt hradCountNonneg,
        Real.sqrt_nonneg (128 * Real.pi * r / alpha)]
    have hnorm :
        ‖∑ x ∈ Finset.range r, f x * exponential (-(phi x))‖ <=
          ∑ x ∈ Finset.range r, ‖f x‖ := by
      calc
        _ <= ∑ x ∈ Finset.range r,
            ‖f x * exponential (-(phi x))‖ := norm_sum_le _ _
        _ = ∑ x ∈ Finset.range r, ‖f x‖ := by
          apply Finset.sum_congr rfl
          intro x _
          rw [norm_mul, cor24_norm_exponential, mul_one]
    have hsum :
        (alpha / 2) * r <= ∑ j : Fin r,
          ‖∑ x ∈ (cor24Singleton j).carrier, f x‖ := by
      have hraw : (alpha / 2) * r <= ∑ x ∈ Finset.range r, ‖f x‖ := by
        calc
          (alpha / 2) * r <= alpha * r := by nlinarith
          _ <= ‖∑ x ∈ Finset.range r,
              f x * exponential (-(phi x))‖ := hpremise
          _ <= ∑ x ∈ Finset.range r, ‖f x‖ := hnorm
      calc
        (alpha / 2) * r <= ∑ x ∈ Finset.range r, ‖f x‖ := hraw
        _ = ∑ j : Fin r, ‖∑ x ∈ (cor24Singleton j).carrier, f x‖ := by
          rw [Finset.sum_fin_eq_sum_range]
          apply Finset.sum_congr rfl
          intro x hx
          simp [cor24Singleton_carrier, Finset.mem_range.mp hx]
    refine ⟨r, fun i : Fin r => cor24Singleton i,
      cor24Singleton_partition r, hcount, hsum, ?_⟩
    intro j
    refine ⟨?_, by simpa [cor24Singleton] using hLowerOne,
      by simpa [cor24Singleton] using hUpperOne⟩
    · constructor
      · simp [cor24Singleton]
      · rw [cor24Singleton_carrier]
        simp [cor24Singleton]
  obtain ⟨s, hs, hsN, hrs, hsLower, hsUpper⟩ :=
    cor24_exists_integer_scale alpha hrN hlarge halpha halphaOne
  have hNatLinear : NatToZModLinear r (fun x : Nat => phi x) := by
    rcases hlinear with ⟨a, b, hab⟩
    exact ⟨a, b, fun x hx => hab (x : ZMod N) (Finset.mem_univ _)⟩
  obtain ⟨m, P, hpartition, hP⟩ :=
    lemma_2_3_holds N r s hN hr hs hrN hsN hrs
      (fun x : Nat => phi x) hNatLinear
  have hNReal : (0 : Real) < N := by exact_mod_cast hN
  have hrNonneg : (0 : Real) <= r := by positivity
  have hradLower :
      alpha * r / (128 * Real.pi) <= (r : Real) * s / (16 * N) := by
    calc
      alpha * r / (128 * Real.pi) =
          ((r : Real) / (16 * N)) *
            (alpha * N / (8 * Real.pi)) := by
        field_simp
        ring
      _ <= ((r : Real) / (16 * N)) * s := by
        exact mul_le_mul_of_nonneg_left hsLower (by positivity)
      _ = (r : Real) * s / (16 * N) := by ring
  have hradUpper :
      (r : Real) * s / N <= alpha * r / (4 * Real.pi) := by
    calc
      (r : Real) * s / N = ((r : Real) / N) * s := by ring
      _ <= ((r : Real) / N) * (alpha * N / (4 * Real.pi)) := by
        exact mul_le_mul_of_nonneg_left hsUpper (by positivity)
      _ = alpha * r / (4 * Real.pi) := by
        field_simp
  have hlength (j : Fin m) :
      (P j).IsProper /\
      Real.sqrt (alpha * r / (128 * Real.pi)) <= (P j).length /\
        ((P j).length : Real) <= Real.sqrt (alpha * r / (4 * Real.pi)) := by
    exact ⟨(hP j).1, (Real.sqrt_le_sqrt hradLower).trans (hP j).2.2.1,
      (hP j).2.2.2.trans (Real.sqrt_le_sqrt hradUpper)⟩
  have hsumLengthNat : ∑ j, (P j).length = r := by
    calc
      ∑ j, (P j).length = ∑ j, (P j).carrier.card := by
        apply Finset.sum_congr rfl
        intro j _
        exact (hP j).1.2.symm
      _ = (Finset.range r).card := IsPartition.sum_card hpartition
      _ = r := Finset.card_range r
  have hsumLength : ∑ j, ((P j).length : Real) = r := by
    exact_mod_cast hsumLengthNat
  have hmTimesLower :
      (m : Real) * Real.sqrt (alpha * r / (128 * Real.pi)) <= r := by
    calc
      (m : Real) * Real.sqrt (alpha * r / (128 * Real.pi)) =
          ∑ _j : Fin m, Real.sqrt (alpha * r / (128 * Real.pi)) := by
        simp [mul_comm]
      _ <= ∑ j, ((P j).length : Real) := by
        apply Finset.sum_le_sum
        intro j _
        exact (hlength j).2.1
      _ = r := hsumLength
  have hLowerPos : 0 < Real.sqrt (alpha * r / (128 * Real.pi)) := by
    positivity
  have hreciprocal := cor24_reciprocal_scales alpha r halpha hr
  have hm :
      (m : Real) <= Real.sqrt (128 * Real.pi * r / alpha) := by
    apply le_of_mul_le_mul_left _ hLowerPos
    rw [hreciprocal]
    simpa only [mul_comm] using hmTimesLower
  let center : Fin m -> ZMod N := fun j => Classical.choose (hP j).2.1
  have hcenter (j : Fin m) :
      (P j).carrier.image (fun x : Nat => phi x) ⊆
        (modInterval N (center j) (s + 1)).carrier :=
    Classical.choose_spec (hP j).2.1
  have hphase (j : Fin m) (x : Nat) (hx : x ∈ (P j).carrier) :
      ‖exponential (-(phi x)) - exponential (-(center j))‖ <= alpha / 2 := by
    have hxImage : phi x ∈ (P j).carrier.image (fun y : Nat => phi y) := by
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
    calc
      ‖exponential (-(phi x)) - exponential (-(center j))‖ <=
          2 * Real.pi * s / N :=
        cor24_phase_close_of_mem_interval _ _ (hcenter j hxImage)
      _ <= 2 * Real.pi * (alpha * N / (4 * Real.pi)) / N := by
        gcongr
      _ = alpha / 2 := by
        field_simp
        ring
  have herror (j : Fin m) :
      ‖(∑ x ∈ (P j).carrier, f x * exponential (-(phi x))) -
          exponential (-(center j)) * (∑ x ∈ (P j).carrier, f x)‖ <=
        (alpha / 2) * (P j).carrier.card := by
    calc
      ‖(∑ x ∈ (P j).carrier, f x * exponential (-(phi x))) -
          exponential (-(center j)) * (∑ x ∈ (P j).carrier, f x)‖ =
          ‖∑ x ∈ (P j).carrier,
            f x * (exponential (-(phi x)) - exponential (-(center j)))‖ := by
        congr 1
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ <= ∑ x ∈ (P j).carrier,
          ‖f x * (exponential (-(phi x)) - exponential (-(center j)))‖ :=
        norm_sum_le _ _
      _ <= ∑ _x ∈ (P j).carrier, alpha / 2 := by
        apply Finset.sum_le_sum
        intro x hx
        rw [norm_mul]
        have hxRange := IsPartition.cell_subset hpartition j hx
        have hfx := hf x (Finset.mem_range.mp hxRange)
        calc
          ‖f x‖ * ‖exponential (-(phi x)) - exponential (-(center j))‖ <=
              1 * (alpha / 2) :=
            mul_le_mul hfx (hphase j x hx) (norm_nonneg _) (by norm_num)
          _ = alpha / 2 := one_mul _
      _ = (alpha / 2) * (P j).carrier.card := by
        simp [mul_comm]
  have hcell (j : Fin m) :
      ‖∑ x ∈ (P j).carrier, f x * exponential (-(phi x))‖ <=
        ‖∑ x ∈ (P j).carrier, f x‖ +
          (alpha / 2) * (P j).carrier.card := by
    let V := ∑ x ∈ (P j).carrier, f x * exponential (-(phi x))
    let U := ∑ x ∈ (P j).carrier, f x
    let C := exponential (-(center j)) * U
    have hVC : V = C + (V - C) := by ring
    have herror' : ‖V - C‖ <= (alpha / 2) * (P j).carrier.card := by
      exact herror j
    calc
      ‖∑ x ∈ (P j).carrier, f x * exponential (-(phi x))‖ = ‖V‖ := rfl
      _ = ‖C + (V - C)‖ := congrArg norm hVC
      _ <= ‖C‖ + ‖V - C‖ := norm_add_le _ _
      _ <= ‖U‖ + (alpha / 2) * (P j).carrier.card := by
        have hC : ‖C‖ = ‖U‖ := by
          dsimp only [C]
          rw [norm_mul, cor24_norm_exponential, one_mul]
        rw [hC]
        simpa only [add_comm] using add_le_add_left herror' ‖U‖
      _ = ‖∑ x ∈ (P j).carrier, f x‖ +
          (alpha / 2) * (P j).carrier.card := rfl
  have hphasedTotal :
      ‖∑ x ∈ Finset.range r, f x * exponential (-(phi x))‖ <=
        ∑ j, ‖∑ x ∈ (P j).carrier,
          f x * exponential (-(phi x))‖ := by
    rw [← cor24_sum_partition (fun j => (P j).carrier) (Finset.range r)
      hpartition (fun x => f x * exponential (-(phi x)))]
    exact norm_sum_le _ _
  have hcards : ∑ j, ((P j).carrier.card : Real) = r := by
    have hcardsNat := IsPartition.sum_card hpartition
    rw [Finset.card_range] at hcardsNat
    exact_mod_cast hcardsNat
  have hcellTotal :
      (∑ j, ‖∑ x ∈ (P j).carrier,
          f x * exponential (-(phi x))‖) <=
        (∑ j, ‖∑ x ∈ (P j).carrier, f x‖) + (alpha / 2) * r := by
    calc
      _ <= ∑ j, (‖∑ x ∈ (P j).carrier, f x‖ +
          (alpha / 2) * (P j).carrier.card) := by
        apply Finset.sum_le_sum
        intro j _
        exact hcell j
      _ = (∑ j, ‖∑ x ∈ (P j).carrier, f x‖) +
          (alpha / 2) * ∑ j, ((P j).carrier.card : Real) := by
        rw [Finset.sum_add_distrib]
        congr 1
        rw [Finset.mul_sum]
      _ = (∑ j, ‖∑ x ∈ (P j).carrier, f x‖) +
          (alpha / 2) * r := by rw [hcards]
  refine ⟨m, P, hpartition, hm, ?_, hlength⟩
  have hcombined := hpremise.trans (hphasedTotal.trans hcellTotal)
  nlinarith

end LeanProofs.GowersSzemeredi
