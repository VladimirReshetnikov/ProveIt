import GowersSzemeredi.Proofs07AdditiveRestriction
import GowersSzemeredi.Proofs07ProgressionLinearity
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Long affine restrictions of somewhat additive maps

This module proves Gowers's Corollary 7.10.  The main ingredients are the
order-eight restriction from Corollary 7.6, the Bohr-set linearity statement
from Corollary 7.9, and a finite translation-averaging argument.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

private lemma zmod_natCast_injective_below {N i j : Nat} [NeZero N]
    (hi : i < N) (hj : j < N) (h : (i : ZMod N) = (j : ZMod N)) : i = j := by
  have hv := congrArg ZMod.val h
  simpa [ZMod.val_natCast_of_lt hi, ZMod.val_natCast_of_lt hj] using hv

private lemma prime_modAP_isProper {N m : Nat} [NeZero N] [Fact N.Prime]
    (a d : ZMod N) (hd : d ≠ 0) (hm : m ≤ N) :
    ({ start := a, step := d, length := m } : ModAP N).IsProper := by
  classical
  unfold ModAP.IsProper ModAP.carrier
  change #(Finset.univ.image fun i : Fin m => a + (i : Nat) * d) = m
  rw [Finset.card_image_iff.mpr]
  · simp
  · intro i _ j _ hij
    apply Fin.ext
    apply zmod_natCast_injective_below (N := N)
    · exact i.isLt.trans_le hm
    · exact j.isLt.trans_le hm
    have hmul : ((i : ZMod N) - (j : ZMod N)) * d = 0 := by
      rw [sub_mul]
      linear_combination hij
    have hcast : (i : ZMod N) = (j : ZMod N) := by
      rcases mul_eq_zero.mp hmul with hzero | hzero
      · exact sub_eq_zero.mp hzero
      · exact (hd hzero).elim
    exact hcast

private def affineProgression {N : Nat} (a d : ZMod N) (m : Nat) : ModAP N :=
  { start := a, step := d, length := m }

private def affineHits {N : Nat} [NeZero N] (m : Nat)
    (B : Finset (ZMod N)) (d a : ZMod N) : Nat :=
  ((Finset.univ : Finset (Fin m)).filter (fun i : Fin m =>
    a + (i.val : ZMod N) * d ∈ B)).card

private lemma sum_add_indicator {N : Nat} [NeZero N]
    (B : Finset (ZMod N)) (t : ZMod N) :
    ∑ a : ZMod N, (if a + t ∈ B then (1 : Nat) else 0) = B.card := by
  classical
  rw [Finset.sum_boole]
  apply Finset.card_bij (fun a _ => a + t)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun _ h => h
  · intro a _ b _ hab
    exact add_right_cancel hab
  · intro b hb
    refine ⟨b - t, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, sub_add_cancel]
    exact hb

private lemma sum_affineHits {N m : Nat} [NeZero N]
    (B : Finset (ZMod N)) (d : ZMod N) :
    ∑ a : ZMod N, affineHits m B d a = m * B.card := by
  classical
  simp only [affineHits, Finset.card_filter]
  rw [Finset.sum_comm]
  calc
    ∑ i : Fin m, ∑ a : ZMod N,
        (if a + (i.val : ZMod N) * d ∈ B then (1 : Nat) else 0) =
      ∑ _i : Fin m, B.card := by
        apply Finset.sum_congr rfl
        intro i _
        exact sum_add_indicator B ((i.val : ZMod N) * d)
    _ = m * B.card := by simp

private lemma exists_affineHits_large {N m : Nat} [NeZero N]
    (B : Finset (ZMod N)) (delta : Real)
    (hcard : (B.card : Real) = delta * N) (d : ZMod N) :
    ∃ a : ZMod N, delta * m ≤ affineHits m B d a := by
  classical
  have hsum :
      ∑ _a : ZMod N, delta * (m : Real) =
        ∑ a : ZMod N, (affineHits m B d a : Real) := by
    rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul,
      ← Nat.cast_sum, sum_affineHits]
    push_cast
    rw [hcard]
    ring
  obtain ⟨a, _, ha⟩ := Finset.exists_le_of_sum_le
    (s := (Finset.univ : Finset (ZMod N)))
    Finset.univ_nonempty hsum.le
  exact ⟨a, ha⟩

private def affineHitSet {N : Nat} [NeZero N] (m : Nat)
    (B : Finset (ZMod N)) (d a : ZMod N) : Finset (ZMod N) := by
  classical
  exact ((Finset.univ : Finset (Fin m)).filter (fun i : Fin m =>
    a + (i.val : ZMod N) * d ∈ B)).image
      (fun i : Fin m => a + (i.val : ZMod N) * d)

private lemma affineHitSet_subset_progression {N m : Nat} [NeZero N]
    (B : Finset (ZMod N)) (d a : ZMod N) :
    affineHitSet m B d a ⊆ (affineProgression a d m).carrier := by
  classical
  intro x hx
  rw [affineHitSet, Finset.mem_image] at hx
  obtain ⟨i, _, rfl⟩ := hx
  unfold affineProgression ModAP.carrier
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

private lemma affineHitSet_subset {N m : Nat} [NeZero N]
    (B : Finset (ZMod N)) (d a : ZMod N) : affineHitSet m B d a ⊆ B := by
  classical
  intro x hx
  rw [affineHitSet, Finset.mem_image] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  exact (Finset.mem_filter.mp hi).2

private lemma affineHitSet_card {N m : Nat} [NeZero N] [Fact N.Prime]
    (B : Finset (ZMod N)) (d a : ZMod N) (hd : d ≠ 0) (hm : m ≤ N) :
    (affineHitSet m B d a).card = affineHits m B d a := by
  classical
  unfold affineHitSet affineHits
  rw [Finset.card_image_iff.mpr]
  intro i hi j hj hij
  apply Fin.ext
  apply zmod_natCast_injective_below (N := N)
  · exact i.isLt.trans_le hm
  · exact j.isLt.trans_le hm
  have hmul : ((i : ZMod N) - (j : ZMod N)) * d = 0 := by
    rw [sub_mul]
    linear_combination hij
  rcases mul_eq_zero.mp hmul with hzero | hzero
  · exact sub_eq_zero.mp hzero
  · exact (hd hzero).elim

private lemma sub_mem_symmetric_of_mem_affineProgression {N m : Nat}
    [NeZero N] (a d x y : ZMod N)
    (hx : x ∈ (affineProgression a d m).carrier)
    (hy : y ∈ (affineProgression a d m).carrier) :
    x - y ∈ symmetricMultiples d m := by
  classical
  unfold affineProgression ModAP.carrier at hx hy
  rw [Finset.mem_image] at hx hy
  obtain ⟨i, _, rfl⟩ := hx
  obtain ⟨j, _, rfl⟩ := hy
  have him : i.val < m := i.isLt
  have hjm : j.val < m := j.isLt
  rw [symmetricMultiples, Finset.mem_image]
  refine ⟨(i.val : Int) - (j.val : Int), Finset.mem_Icc.mpr ?_, ?_⟩
  · constructor
    · have hi : (i.val : Int) ≤ m := by exact_mod_cast him.le
      have hj : (0 : Int) ≤ j.val := by positivity
      omega
    · have hj : (j.val : Int) ≤ m := by exact_mod_cast hjm.le
      have hi : (0 : Int) ≤ i.val := by positivity
      omega
  · push_cast
    ring

private lemma linearOn_of_pairwise_difference {N : Nat}
    (H : Finset (ZMod N)) (phi : ZMod N → ZMod N) (c : ZMod N)
    (hH : H.Nonempty)
    (hdiff : ∀ x, x ∈ H → ∀ y, y ∈ H →
      phi x - phi y = c * (x - y)) : LinearOn H phi := by
  obtain ⟨y, hy⟩ := hH
  refine ⟨c, phi y - c * y, ?_⟩
  intro x hx
  have hxy := hdiff x hx y hy
  linear_combination hxy

private def cor710Beta (alpha gamma : Real) : Real :=
  (2 : Real) ^ (-(1882 : Real)) * gamma ^ 1164 * alpha

private def cor710Exponent (alpha gamma : Real) : Real :=
  (2 : Real) ^ (-(3770 : Real)) * gamma ^ 2328 * alpha ^ 2

private lemma cor710Exponent_eq (alpha gamma : Real) :
    cor710Exponent alpha gamma = cor710Beta alpha gamma ^ 2 / 64 := by
  have htwo :
      (2 : Real) ^ (-(3770 : Real)) =
        ((2 : Real) ^ (-(1882 : Real))) ^ 2 / 64 := by
    calc
      (2 : Real) ^ (-(3770 : Real)) =
          (2 : Real) ^ ((-(1882 : Real)) * 2 + (-(6 : Real))) := by norm_num
      _ = (2 : Real) ^ ((-(1882 : Real)) * 2) *
          (2 : Real) ^ (-(6 : Real)) := by
            rw [Real.rpow_add (by positivity)]
      _ = ((2 : Real) ^ (-(1882 : Real))) ^ 2 *
          (2 : Real) ^ (-(6 : Real)) := by
            rw [Real.rpow_mul (by positivity)]
            norm_num [Real.rpow_natCast]
      _ = ((2 : Real) ^ (-(1882 : Real))) ^ 2 / 64 := by
            norm_num [Real.rpow_neg, Real.rpow_natCast]
            ring
  unfold cor710Exponent cor710Beta
  rw [htwo]
  ring

private def cor710Threshold (alpha gamma : Real) : Nat :=
  let beta := cor710Beta alpha gamma
  let e := cor710Exponent alpha gamma
  Nat.ceil (max 2 (((128 * Real.pi / beta) ^ e⁻¹) + 1))

private lemma cor710_large_power {alpha gamma : Real}
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    {N : Nat} (hN : cor710Threshold alpha gamma ≤ N) :
    128 * Real.pi / cor710Beta alpha gamma <
      (N : Real) ^ cor710Exponent alpha gamma := by
  let beta := cor710Beta alpha gamma
  let e := cor710Exponent alpha gamma
  have hbeta : 0 < beta := by
    dsimp only [beta, cor710Beta]
    positivity
  have he : 0 < e := by
    dsimp only [e, cor710Exponent]
    positivity
  have hbase : 0 < 128 * Real.pi / beta := by positivity
  have hceil :
      max 2 (((128 * Real.pi / beta) ^ e⁻¹) + 1) ≤
        (cor710Threshold alpha gamma : Real) := by
    exact Nat.le_ceil _
  have hthreshold : (cor710Threshold alpha gamma : Real) ≤ N := by
    exact_mod_cast hN
  have hroot_lt : (128 * Real.pi / beta) ^ e⁻¹ < (N : Real) := by
    dsimp only [cor710Threshold] at hceil
    have := le_trans (le_max_right 2 (((128 * Real.pi / beta) ^ e⁻¹) + 1))
      (hceil.trans hthreshold)
    linarith
  have hrpow := Real.rpow_lt_rpow (le_of_lt (Real.rpow_pos_of_pos hbase e⁻¹))
    hroot_lt he
  rw [Real.rpow_inv_rpow hbase.le he.ne'] at hrpow
  simpa only [beta, e] using hrpow

private lemma cor710_two_le {alpha gamma : Real} {N : Nat}
    (hN : cor710Threshold alpha gamma ≤ N) : 2 ≤ N := by
  have hceil :
      max 2 (((128 * Real.pi / cor710Beta alpha gamma) ^
        (cor710Exponent alpha gamma)⁻¹) + 1) ≤
        (cor710Threshold alpha gamma : Real) := by
    exact Nat.le_ceil _
  have hthreshold : (cor710Threshold alpha gamma : Real) ≤ N := by
    exact_mod_cast hN
  have : (2 : Real) ≤ N :=
    (le_max_left _ _).trans (hceil.trans hthreshold)
  exact_mod_cast this

private def cor710Length (N : Nat) (alpha gamma : Real) : Nat :=
  Nat.ceil ((N : Real) ^ cor710Exponent alpha gamma)

private lemma cor710Length_pos {N : Nat} [NeZero N]
    (alpha gamma : Real) :
    0 < cor710Length N alpha gamma := by
  apply Nat.ceil_pos.mpr
  exact Real.rpow_pos_of_pos (by exact_mod_cast NeZero.pos N) _

private lemma cor710Length_lower {N : Nat} (alpha gamma : Real) :
    (N : Real) ^ cor710Exponent alpha gamma ≤ cor710Length N alpha gamma := by
  exact Nat.le_ceil _

private lemma cor710Length_lt_two_mul {N : Nat} [NeZero N]
    {alpha gamma : Real} (halpha : 0 < alpha) (hgamma : 0 < gamma) :
    (cor710Length N alpha gamma : Real) <
      2 * (N : Real) ^ cor710Exponent alpha gamma := by
  have hpow : 1 ≤ (N : Real) ^ cor710Exponent alpha gamma := by
    apply Real.one_le_rpow
    · exact_mod_cast (NeZero.pos N)
    · unfold cor710Exponent
      positivity
  calc
    (cor710Length N alpha gamma : Real) <
        (N : Real) ^ cor710Exponent alpha gamma + 1 := by
          unfold cor710Length
          exact Nat.ceil_lt_add_one (Real.rpow_nonneg (by positivity) _)
    _ ≤ 2 * (N : Real) ^ cor710Exponent alpha gamma := by linarith

private lemma cor710Length_le_modulus {N : Nat} [NeZero N]
    {alpha gamma : Real} (he_one : cor710Exponent alpha gamma ≤ 1) :
    cor710Length N alpha gamma ≤ N := by
  rw [cor710Length, Nat.ceil_le]
  calc
    (N : Real) ^ cor710Exponent alpha gamma ≤ (N : Real) ^ (1 : Real) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast NeZero.pos N) he_one
    _ = N := by rw [Real.rpow_one]

private lemma exists_nonzero_bohr_cor710 {alpha gamma beta delta : Real}
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hbeta : beta = cor710Beta alpha gamma)
    (hdelta : 0 < delta) (hbeta_delta : beta ≤ delta) (hdelta_one : delta ≤ 1)
    {N : Nat} [NeZero N] (hN : cor710Threshold alpha gamma ≤ N)
    (K : Finset (ZMod N))
    (hKcard : (K.card : Real) ≤ 16 * delta ^ (-(2 : Real))) :
    ∃ d : ZMod N,
      d ∈ bohr K
        (delta / (32 * Real.pi * cor710Length N alpha gamma)) ∧ d ≠ 0 := by
  classical
  let e := cor710Exponent alpha gamma
  let m := cor710Length N alpha gamma
  have hNtwo : 2 ≤ N := cor710_two_le hN
  have hNone : (1 : Real) ≤ N := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
  have hmpos : 0 < m := by
    dsimp only [m]
    exact cor710Length_pos alpha gamma
  have hmposR : (0 : Real) < m := by exact_mod_cast hmpos
  have hbeta_pos : 0 < beta := by
    rw [hbeta]
    unfold cor710Beta
    positivity
  have he_pos : 0 < e := by
    dsimp only [e, cor710Exponent]
    positivity
  have he_eq : e = beta ^ 2 / 64 := by
    dsimp only [e]
    rw [hbeta, cor710Exponent_eq]
  have hbeta_one : beta ≤ 1 := hbeta_delta.trans hdelta_one
  have he_one : e ≤ 1 := by
    rw [he_eq]
    nlinarith [sq_nonneg beta]
  have hmle : m ≤ N := by
    dsimp only [m, e] at he_one ⊢
    exact cor710Length_le_modulus he_one
  have hradius_pos :
      0 < delta / (32 * Real.pi * (m : Real)) := by positivity
  have hradius_one :
      delta / (32 * Real.pi * (m : Real)) ≤ 1 := by
    have hpi : (1 : Real) ≤ 32 * Real.pi * m := by
      have hpi' : (1 : Real) < 32 * Real.pi := by
        have := Real.pi_gt_three
        nlinarith
      have hmone : (1 : Real) ≤ m := by exact_mod_cast hmpos
      calc
        (1 : Real) ≤ 32 * Real.pi := hpi'.le
        _ ≤ 32 * Real.pi * m := by
          nlinarith [Real.pi_pos]
    exact (div_le_one (by positivity)).mpr (hdelta_one.trans hpi)
  by_cases hKempty : K = ∅
  · haveI : Fact (1 < N) := ⟨lt_of_lt_of_le Nat.one_lt_two hNtwo⟩
    refine ⟨1, ?_, one_ne_zero⟩
    simp [hKempty, bohr]
  have hKne : K.Nonempty := Finset.nonempty_iff_ne_empty.mpr hKempty
  have hKpos : (0 : Real) < K.card := by
    exact_mod_cast Finset.card_pos.mpr hKne
  have hKbound : (K.card : Real) * delta ^ 2 ≤ 16 := by
    have hKcard' := hKcard
    rw [Real.rpow_neg hdelta.le] at hKcard'
    norm_num [Real.rpow_natCast] at hKcard'
    calc
      (K.card : Real) * delta ^ 2 ≤
          (16 * (delta ^ 2)⁻¹) * delta ^ 2 := by gcongr
      _ = 16 := by field_simp
  have hinvK : beta ^ 2 / 16 ≤ (K.card : Real)⁻¹ := by
    have hdelta_sq : beta ^ 2 ≤ delta ^ 2 := by nlinarith
    rw [inv_eq_one_div, le_div_iff₀ hKpos]
    calc
      beta ^ 2 / 16 * K.card ≤ delta ^ 2 / 16 * K.card := by
        gcongr
      _ ≤ 1 := by nlinarith
  have hexponent : -(K.card : Real)⁻¹ ≤ -4 * e := by
    rw [he_eq]
    linarith
  have hrpow_exponent :
      (N : Real) ^ (-(K.card : Real)⁻¹) ≤ (N : Real) ^ (-4 * e) :=
    Real.rpow_le_rpow_of_exponent_le hNone hexponent
  let x : Real := (N : Real) ^ e
  have hxpos : 0 < x := Real.rpow_pos_of_pos (by positivity) _
  have hxone : 1 ≤ x := Real.one_le_rpow hNone he_pos.le
  have hlarge : 128 * Real.pi / beta < x := by
    rw [hbeta]
    simpa only [x, e] using cor710_large_power halpha hgamma hN
  have hCtwo : (2 : Real) < 128 * Real.pi / beta := by
    have hpi := Real.pi_gt_three
    have hdiv : 128 * Real.pi ≤ 128 * Real.pi / beta := by
      rw [le_div_iff₀ hbeta_pos]
      nlinarith
    nlinarith
  have hxtwo : (2 : Real) < x := hCtwo.trans hlarge
  have hmupper : (m : Real) < 2 * x := by
    dsimp only [m, x, e]
    exact cor710Length_lt_two_mul halpha hgamma
  have hscale : 2 * (N : Real) ^ (-4 * e) <
      beta / (64 * Real.pi * (m : Real)) := by
    have hneg : (N : Real) ^ (-4 * e) = (x ^ (4 : Real))⁻¹ := by
      calc
        (N : Real) ^ (-4 * e) = (N : Real) ^ (e * (-(4 : Real))) := by
          congr 1
          ring
        _ = x ^ (-(4 : Real)) := by
          rw [Real.rpow_mul (by positivity)]
        _ = (x ^ (4 : Real))⁻¹ := by rw [Real.rpow_neg hxpos.le]
    have hcross :
        2 * (64 * Real.pi * (m : Real)) < beta * x ^ 4 := by
      have h128 : 128 * Real.pi < beta * x := by
        rw [div_lt_iff₀ hbeta_pos] at hlarge
        simpa [mul_comm] using hlarge
      have hx_sq : (2 : Real) < x ^ 2 := by nlinarith
      have hpi128 : 0 < 128 * Real.pi := by positivity
      have h256 : 256 * Real.pi < beta * x ^ 3 := by
        calc
          256 * Real.pi = (128 * Real.pi) * 2 := by ring
          _ < (128 * Real.pi) * x ^ 2 :=
            mul_lt_mul_of_pos_left hx_sq hpi128
          _ < (beta * x) * x ^ 2 :=
            mul_lt_mul_of_pos_right h128 (pow_pos hxpos 2)
          _ = beta * x ^ 3 := by ring
      calc
        2 * (64 * Real.pi * (m : Real)) = 128 * Real.pi * m := by ring
        _ < 128 * Real.pi * (2 * x) :=
          mul_lt_mul_of_pos_left hmupper hpi128
        _ = 256 * Real.pi * x := by ring
        _ < (beta * x ^ 3) * x := mul_lt_mul_of_pos_right h256 hxpos
        _ = beta * x ^ 4 := by ring
    rw [hneg]
    have hxpow : 0 < x ^ (4 : Real) := Real.rpow_pos_of_pos hxpos _
    have hden : 0 < 64 * Real.pi * (m : Real) := by positivity
    rw [show 2 * (x ^ (4 : Real))⁻¹ = 2 / x ^ (4 : Real) by
      rw [div_eq_mul_inv]]
    exact (div_lt_div_iff₀ hxpow hden).mpr
      (by simpa [Real.rpow_natCast, mul_assoc] using hcross)
  have hthreshold :
      2 * (N : Real) ^ (-(1 / (K.card : Real))) <
        delta / (32 * Real.pi * (m : Real)) := by
    have hfirst :
        2 * (N : Real) ^ (-(1 / (K.card : Real))) ≤
          2 * (N : Real) ^ (-4 * e) := by
      have hrewrite : -(1 / (K.card : Real)) = -(K.card : Real)⁻¹ := by
        rw [one_div]
      rw [hrewrite]
      gcongr
    have hmiddle :
        beta / (64 * Real.pi * (m : Real)) ≤
          delta / (32 * Real.pi * (m : Real)) := by
      have hden : 0 < 64 * Real.pi * (m : Real) := by positivity
      have hden' : 0 < 32 * Real.pi * (m : Real) := by positivity
      rw [div_le_div_iff₀ hden hden']
      nlinarith
    exact lt_of_le_of_lt hfirst (hscale.trans_le hmiddle)
  obtain ⟨_, hnonzero⟩ := lemma_7_7_holds N K
    (delta / (32 * Real.pi * (m : Real))) hNtwo hradius_pos hradius_one
  obtain ⟨d, hdmem, hd⟩ := hnonzero hKne hthreshold
  exact ⟨d, by simpa only [m] using hdmem, by simpa only [bne_iff_ne] using hd⟩

/-- **Gowers, Corollary 7.10.** A somewhat additive map has a long affine
restriction. -/
theorem corollary_7_10_holds : corollary_7_10 := by
  classical
  intro alpha gamma halpha hgamma
  refine ⟨cor710Threshold alpha gamma, ?_⟩
  intro N _ hprime hN B0 phi hB0card hadditive
  let beta := cor710Beta alpha gamma
  have hbeta_pos : 0 < beta := by
    dsimp only [beta, cor710Beta]
    positivity
  obtain ⟨B, hBB0, hBcard, hfreiman⟩ :=
    corollary_7_6_holds N B0 phi alpha gamma hprime halpha hgamma
      hB0card hadditive
  have hNposR : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  let delta : Real := B.card / (N : Real)
  have hdelta_card : (B.card : Real) = delta * N := by
    dsimp only [delta]
    field_simp
  have hbeta_delta : beta ≤ delta := by
    rw [← mul_le_mul_iff_right₀ hNposR]
    calc
      (N : Real) * beta = beta * N := by ring
      _ ≤ B.card := by simpa [beta, cor710Beta] using hBcard
      _ = delta * N := hdelta_card
      _ = N * delta := by ring
  have hdelta_pos : 0 < delta := hbeta_pos.trans_le hbeta_delta
  have hB_univ : B ⊆ (Finset.univ : Finset (ZMod N)) := fun _ _ => Finset.mem_univ _
  have hBcard_le : B.card ≤ N := by
    have := Finset.card_le_card hB_univ
    simpa using this
  have hdelta_one : delta ≤ 1 := by
    dsimp only [delta]
    rw [div_le_one hNposR]
    exact_mod_cast hBcard_le
  let K := section7Spectrum B delta
  obtain ⟨hKcard, _hmodel⟩ :=
    lemma_7_8_holds N B phi delta hdelta_pos hdelta_card hfreiman
  have hKcard' : (K.card : Real) ≤ 16 * delta ^ (-(2 : Real)) := by
    simpa only [K] using hKcard
  obtain ⟨d, hdBohr, hd⟩ := exists_nonzero_bohr_cor710
    halpha hgamma (beta := beta) (delta := delta) rfl hdelta_pos
    hbeta_delta hdelta_one hN K hKcard'
  let m := cor710Length N alpha gamma
  have hmpos : 0 < m := by
    dsimp only [m]
    exact cor710Length_pos alpha gamma
  have he_one : cor710Exponent alpha gamma ≤ 1 := by
    rw [cor710Exponent_eq]
    have hbeta_one : beta ≤ 1 := hbeta_delta.trans hdelta_one
    dsimp only [beta] at hbeta_one ⊢
    nlinarith [sq_nonneg (cor710Beta alpha gamma)]
  have hmle : m ≤ N := by
    dsimp only [m]
    exact cor710Length_le_modulus he_one
  obtain ⟨a, ha⟩ := exists_affineHits_large B delta hdelta_card d
  let P := affineProgression a d m
  let H := affineHitSet m B d a
  have hproper : P.IsProper := by
    letI : Fact N.Prime := ⟨hprime⟩
    exact prime_modAP_isProper a d hd hmle
  have hHcard : (H.card : Real) = affineHits m B d a := by
    letI : Fact N.Prime := ⟨hprime⟩
    exact_mod_cast affineHitSet_card B d a hd hmle
  have hHlarge : beta * P.length ≤ H.card := by
    have hbeta_m : beta * (m : Real) ≤ delta * m := by
      gcongr
    dsimp only [P, affineProgression]
    rw [hHcard]
    exact hbeta_m.trans ha
  have hHsubsetP : H ⊆ P.carrier :=
    affineHitSet_subset_progression B d a
  have hHsubsetB : H ⊆ B := affineHitSet_subset B d a
  have hHnonempty : H.Nonempty := by
    apply Finset.card_pos.mp
    have hPlength : (0 : Real) < P.length := by
      dsimp only [P, affineProgression]
      exact_mod_cast hmpos
    have : (0 : Real) < H.card :=
      (mul_pos hbeta_pos hPlength).trans_le hHlarge
    exact_mod_cast this
  have hpairwise : ∃ c : ZMod N, ∀ x, x ∈ H → ∀ y, y ∈ H →
      phi x - phi y = c * (x - y) := by
    have hlinear := corollary_7_9_holds N B phi delta hprime hdelta_pos
      hdelta_card hfreiman m hmpos d
    have hdBohr' :
        d ∈ bohr (section7Spectrum B delta)
          (delta / (32 * Real.pi * m)) := by
      simpa only [K, m] using hdBohr
    obtain ⟨c, hc⟩ := hlinear hdBohr'
    refine ⟨c, ?_⟩
    intro x hx y hy
    exact hc x (hHsubsetB hx) y (hHsubsetB hy)
      (sub_mem_symmetric_of_mem_affineProgression a d x y
        (hHsubsetP hx) (hHsubsetP hy))
  obtain ⟨c, hc⟩ := hpairwise
  refine ⟨P, H, hproper, ?_, hHsubsetP, ?_, ?_,
    linearOn_of_pairwise_difference H phi c hHnonempty hc⟩
  · simpa only [P, affineProgression, bne_iff_ne] using hd
  · dsimp only [P, affineProgression, m]
    exact cor710Length_lower alpha gamma
  · simpa [beta, cor710Beta, P] using hHlarge

end LeanProofs.GowersSzemeredi
