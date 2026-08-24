import GowersSzemeredi.Proofs02PhasePartition
import GowersSzemeredi.ProofInfrastructure

/-!
# Fourier density increments in Gowers's Section 2

This module proves Corollary 2.5.  The preparatory lemmas identify the standard
representatives with `ZMod N` and formalize the exact positive/negative mass
split for a real, mean-zero function on a finite partition.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

private lemma cor25_sum_range_zmod {N : Nat} [NeZero N]
    {R : Type*} [AddCommMonoid R] (g : ZMod N → R) :
    ∑ x ∈ Finset.range N, g (x : ZMod N) = ∑ z : ZMod N, g z := by
  rw [← Fin.sum_univ_eq_sum_range]
  calc
    _ = ∑ x : Fin N, g (ZMod.finEquiv N x) := by
      apply Finset.sum_congr rfl
      intro x _hx
      congr 1
      apply ZMod.val_injective
      rw [ZMod.val_natCast_of_lt x.isLt]
      cases N with
      | zero => exact (NeZero.ne 0 rfl).elim
      | succ _n => rfl
    _ = _ := (ZMod.finEquiv N).sum_comp g

private def cor25BalancedReal {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (x : ZMod N) : Real :=
  (if x ∈ A then 1 else 0) - density A

private lemma cor25_balanced_eq_real {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (x : ZMod N) :
    balanced A x = (cor25BalancedReal A x : Complex) := by
  classical
  by_cases hx : x ∈ A <;> simp [balanced, indicator, cor25BalancedReal, hx]

private lemma cor25_density_bounds {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) : 0 ≤ density A ∧ density A ≤ 1 := by
  have hcard : A.card ≤ N := by
    calc
      A.card ≤ (Finset.univ : Finset (ZMod N)).card :=
        Finset.card_le_card (Finset.subset_univ A)
      _ = N := by simp
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  constructor
  · unfold density
    positivity
  · unfold density
    rw [div_le_one hN]
    exact_mod_cast hcard

private lemma cor25_balancedReal_abs_le_one {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (x : ZMod N) :
    |cor25BalancedReal A x| ≤ 1 := by
  classical
  obtain ⟨hd0, hd1⟩ := cor25_density_bounds A
  by_cases hx : x ∈ A
  · simp only [cor25BalancedReal, hx, if_true]
    rw [abs_of_nonneg (sub_nonneg.mpr hd1)]
    linarith
  · simp only [cor25BalancedReal, hx, if_false, zero_sub, abs_neg]
    rw [abs_of_nonneg hd0]
    exact hd1

private lemma cor25_balancedReal_sum_zero {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) :
    ∑ x : ZMod N, cor25BalancedReal A x = 0 := by
  classical
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  simp only [cor25BalancedReal, Finset.sum_sub_distrib]
  have hindicator :
      (∑ x : ZMod N, if x ∈ A then (1 : Real) else 0) = A.card := by
    rw [← Finset.sum_filter]
    simp
  rw [hindicator]
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  unfold density
  field_simp
  ring

private lemma cor25_fourier_indicator_eq_sum {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (r : ZMod N) :
    fourier (indicator A) r = ∑ x ∈ A, exponential (-(x * r)) := by
  classical
  rw [fourier, ZMod.dft_apply]
  simp only [indicator, smul_eq_mul]
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite]
  simp [exponential]

private lemma cor25_fourier_indicator_norm_le_card {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (r : ZMod N) :
    ‖fourier (indicator A) r‖ ≤ A.card := by
  classical
  rw [cor25_fourier_indicator_eq_sum]
  calc
    ‖∑ x ∈ A, exponential (-(x * r))‖ ≤
        ∑ x ∈ A, ‖exponential (-(x * r))‖ := norm_sum_le _ _
    _ = A.card := by simp [exponential]

private lemma cor25_sum_exponential_mul_zero {N : Nat} [NeZero N]
    (r : ZMod N) (hr : r ≠ 0) :
    ∑ x : ZMod N, exponential (-(x * r)) = 0 := by
  simpa [exponential, mul_comm, hr] using
    AddChar.sum_mulShift (-r) (ZMod.isPrimitive_stdAddChar N)

private lemma cor25_fourier_indicator_eq_neg_complement_sum {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (r : ZMod N) (hr : r ≠ 0) :
    fourier (indicator A) r =
      -∑ x ∈ ((Finset.univ : Finset (ZMod N)) \ A), exponential (-(x * r)) := by
  classical
  rw [cor25_fourier_indicator_eq_sum]
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (ZMod N)) (fun x => x ∈ A)
      (fun x => exponential (-(x * r)))
  have htotal := cor25_sum_exponential_mul_zero r hr
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter] at hsplit
  rw [← hsplit] at htotal
  have hfilter :
      (Finset.univ : Finset (ZMod N)).filter (fun x => x ∉ A) =
        Finset.univ \ A := by
    ext x
    simp
  rw [hfilter] at htotal
  exact eq_neg_of_add_eq_zero_left htotal

private lemma cor25_fourier_indicator_norm_le_complement_card
    {N : Nat} [NeZero N] (A : Finset (ZMod N)) (r : ZMod N) (hr : r ≠ 0) :
    ‖fourier (indicator A) r‖ ≤
      ((Finset.univ : Finset (ZMod N)) \ A).card := by
  classical
  rw [cor25_fourier_indicator_eq_neg_complement_sum A r hr, norm_neg]
  calc
    ‖∑ x ∈ ((Finset.univ : Finset (ZMod N)) \ A),
        exponential (-(x * r))‖ ≤
      ∑ x ∈ ((Finset.univ : Finset (ZMod N)) \ A),
        ‖exponential (-(x * r))‖ := norm_sum_le _ _
    _ = ((Finset.univ : Finset (ZMod N)) \ A).card := by
      simp [exponential]

private lemma cor25_fourier_balanced_eq_indicator_of_ne_zero
    {N : Nat} [NeZero N] (A : Finset (ZMod N)) (r : ZMod N) (hr : r ≠ 0) :
    fourier (balanced A) r = fourier (indicator A) r := by
  rw [fourier, fourier, ZMod.dft_apply, ZMod.dft_apply]
  simp only [balanced, smul_eq_mul]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  have hzero := cor25_sum_exponential_mul_zero r hr
  have hconst :
      (∑ j : ZMod N, ZMod.stdAddChar (-(j * r)) * (density A : Complex)) = 0 := by
    rw [← Finset.sum_mul]
    simpa [exponential] using congrArg (fun z : Complex => z * density A) hzero
  rw [hconst, sub_zero]

private lemma cor25_range_phase_sum_eq_fourier_balanced
    {N : Nat} [NeZero N] (A : Finset (ZMod N)) (r : ZMod N) :
    (∑ x ∈ Finset.range N,
      balanced A (x : ZMod N) * exponential (-(r * (x : ZMod N)))) =
        fourier (balanced A) r := by
  change (∑ x ∈ Finset.range N,
    (fun z : ZMod N => balanced A z * exponential (-(r * z))) (x : ZMod N)) = _
  calc
    _ = ∑ z : ZMod N, balanced A z * exponential (-(r * z)) :=
      cor25_sum_range_zmod (fun z : ZMod N =>
        balanced A z * exponential (-(r * z)))
    _ = fourier (balanced A) r := by
      rw [fourier, ZMod.dft_apply]
      apply Finset.sum_congr rfl
      intro x _hx
      simp only [smul_eq_mul]
      rw [mul_comm]
      congr 2
      ring

private lemma cor25_alpha_bounds {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (alpha : Real) (r : ZMod N) (hr : r ≠ 0)
    (hlarge : alpha * N ≤ ‖fourier (indicator A) r‖) :
    alpha ≤ density A ∧ alpha ≤ 1 - density A := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hcard : A.card ≤ N := by
    calc
      A.card ≤ (Finset.univ : Finset (ZMod N)).card :=
        Finset.card_le_card (Finset.subset_univ A)
      _ = N := by simp
  have hA := cor25_fourier_indicator_norm_le_card A r
  have hC := cor25_fourier_indicator_norm_le_complement_card A r hr
  constructor
  · unfold density
    rw [le_div_iff₀ hN]
    exact hlarge.trans hA
  · have hcomp :
        (((Finset.univ : Finset (ZMod N)) \ A).card : Real) =
          (N : Real) - A.card := by
      rw [Finset.card_sdiff]
      simp only [Finset.inter_eq_left.mpr (Finset.subset_univ A),
        Finset.card_univ, ZMod.card]
      rw [Nat.cast_sub hcard]
    unfold density
    rw [hcomp] at hC
    calc
      alpha ≤ ((N : Real) - A.card) / N := by
        rw [le_div_iff₀ hN]
        exact hlarge.trans hC
      _ = 1 - (A.card : Real) / N := by field_simp

private def cor25SingletonAP (x : Nat) : NatAP where
  start := x
  step := 1
  length := 1

@[simp] private lemma cor25SingletonAP_carrier (x : Nat) :
    (cor25SingletonAP x).carrier = {x} := by
  classical
  simp [cor25SingletonAP, NatAP.carrier]

private lemma cor25SingletonAP_proper (x : Nat) :
    (cor25SingletonAP x).IsProper := by
  constructor
  · simp [cor25SingletonAP]
  · rw [cor25SingletonAP_carrier]
    simp [cor25SingletonAP]

private lemma cor25_sum_partition {X R : Type*} [DecidableEq X] {m : Nat}
    [AddCommMonoid R] (P : Fin m → Finset X) (S : Finset X)
    (hpartition : IsPartition P S) (g : X → R) :
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

private lemma cor25_balancedReal_sum_eq_inter_card {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (S : Finset Nat) (hS : S ⊆ Finset.range N) :
    ∑ x ∈ S, cor25BalancedReal A (x : ZMod N) =
      ((S ∩ standardRepresentatives A).card : Real) - density A * S.card := by
  classical
  have hfilter :
      S.filter (fun x : Nat => (x : ZMod N) ∈ A) =
        S ∩ standardRepresentatives A := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_inter]
    constructor
    · intro hx
      refine ⟨hx.1, ?_⟩
      have hxRange := hS hx.1
      simpa [standardRepresentatives, hxRange] using hx.2
    · intro hx
      refine ⟨hx.1, ?_⟩
      have hx' : x ∈ Finset.range N ∧ (x : ZMod N) ∈ A := by
        simpa [standardRepresentatives] using hx.2
      exact hx'.2
  simp only [cor25BalancedReal, Finset.sum_sub_distrib]
  have hindicator :
      (∑ x ∈ S, if (x : ZMod N) ∈ A then (1 : Real) else 0) =
        ((S ∩ standardRepresentatives A).card : Real) := by
    rw [← hfilter]
    simp
  rw [hindicator]
  simp [mul_comm]

private lemma cor25_sum_abs_eq_two_mul_sum_max {m : Nat} (g : Fin m → Real)
    (hzero : ∑ j, g j = 0) :
    ∑ j, |g j| = 2 * ∑ j, max (g j) 0 := by
  have hpoint (x : Real) : |x| = 2 * max x 0 - x := by
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx, max_eq_left hx]
      ring
    · have hx' : x ≤ 0 := le_of_not_ge hx
      rw [abs_of_nonpos hx', max_eq_right hx']
      ring
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib, hzero, sub_zero, ← Finset.mul_sum]

private lemma cor25_exists_large_positive {m : Nat} (hm : 0 < m)
    (g : Fin m → Real) (c : Real) (hc : 0 < c)
    (hzero : ∑ j, g j = 0) (hlarge : c ≤ ∑ j, |g j|) :
    ∃ j, c / (2 * m) ≤ g j := by
  have hmax : c / 2 ≤ ∑ j, max (g j) 0 := by
    rw [cor25_sum_abs_eq_two_mul_sum_max g hzero] at hlarge
    linarith
  have hmReal : (0 : Real) < m := by exact_mod_cast hm
  have hconst :
      (∑ _j : Fin m, c / (2 * m)) = c / 2 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have havg :
      (∑ _j : Fin m, c / (2 * m)) ≤ ∑ j, max (g j) 0 := by
    rw [hconst]
    exact hmax
  have huniv : (Finset.univ : Finset (Fin m)).Nonempty :=
    ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  obtain ⟨j, _, hj⟩ := Finset.exists_le_of_sum_le
    (s := (Finset.univ : Finset (Fin m))) huniv havg
  refine ⟨j, ?_⟩
  have hthreshold : 0 < c / (2 * (m : Real)) := by positivity
  have hjpos : 0 < g j := by
    by_contra h
    have hnonpos : g j ≤ 0 := le_of_not_gt h
    rw [max_eq_right hnonpos] at hj
    exact (not_le_of_gt hthreshold) hj
  simpa only [max_eq_left hjpos.le] using hj

private lemma cor25_small_scale {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (alpha : Real) (halpha : 0 < alpha)
    (r : ZMod N) (hr : r ≠ 0)
    (hlarge : alpha * N ≤ ‖fourier (indicator A) r‖)
    (hscale : ¬ 4 * Real.pi ≤ alpha * N) :
    ∃ P : NatAP, P.IsProper ∧ P.carrier ⊆ Finset.range N ∧
      Real.sqrt (alpha ^ 3 * N / (128 * Real.pi)) ≤ P.length ∧
    (density A + alpha / 8) * P.length ≤
        ((P.carrier ∩ standardRepresentatives A).card : Real) := by
  classical
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  obtain ⟨halphaDensity, halphaComplement⟩ :=
    cor25_alpha_bounds A alpha r hr hlarge
  obtain ⟨_densityNonneg, hdensityOne⟩ := cor25_density_bounds A
  have halphaOne : alpha ≤ 1 := halphaDensity.trans hdensityOne
  have hcardPosReal : (0 : Real) < A.card := by
    exact (mul_pos halpha hN).trans_le
      (hlarge.trans (cor25_fourier_indicator_norm_le_card A r))
  have hcardPos : 0 < A.card := by exact_mod_cast hcardPosReal
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hcardPos
  let P := cor25SingletonAP a.val
  have hcarrier : P.carrier = {a.val} := by
    exact cor25SingletonAP_carrier a.val
  have hsubset : P.carrier ⊆ Finset.range N := by
    rw [hcarrier]
    simpa using ZMod.val_lt a
  have hrepresentative : a.val ∈ standardRepresentatives A := by
    simp [standardRepresentatives, ZMod.val_lt a, ZMod.natCast_zmod_val a, ha]
  have hinterCard :
      (P.carrier ∩ standardRepresentatives A).card = 1 := by
    rw [hcarrier]
    simp [hrepresentative]
  have hscale' : alpha * N < 4 * Real.pi := lt_of_not_ge hscale
  have halphaSq : alpha ^ 2 ≤ 1 := by nlinarith [sq_nonneg alpha]
  have hnumStrict : alpha ^ 3 * (N : Real) < 128 * Real.pi := by
    calc
      alpha ^ 3 * (N : Real) = alpha ^ 2 * (alpha * N) := by ring
      _ < alpha ^ 2 * (4 * Real.pi) := by
        exact mul_lt_mul_of_pos_left hscale' (pow_pos halpha 2)
      _ ≤ 1 * (4 * Real.pi) := by
        gcongr
      _ ≤ 128 * Real.pi := by nlinarith [Real.pi_pos]
  have hnum : alpha ^ 3 * (N : Real) ≤ 128 * Real.pi := hnumStrict.le
  have hradicand : alpha ^ 3 * (N : Real) / (128 * Real.pi) ≤ 1 := by
    rw [div_le_one (by positivity : (0 : Real) < 128 * Real.pi)]
    exact hnum
  have hlength :
      Real.sqrt (alpha ^ 3 * (N : Real) / (128 * Real.pi)) ≤ P.length := by
    simpa [P, cor25SingletonAP] using Real.sqrt_le_one.mpr hradicand
  have hdensityIncrement : density A + alpha / 8 ≤ 1 := by
    linarith
  refine ⟨P, cor25SingletonAP_proper a.val, hsubset, hlength, ?_⟩
  rw [hinterCard]
  simpa [P, cor25SingletonAP] using hdensityIncrement

private lemma cor25_large_scale {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (alpha : Real) (halpha : 0 < alpha)
    (r : ZMod N) (hr : r ≠ 0)
    (hlarge : alpha * N ≤ ‖fourier (indicator A) r‖)
    (hscale : 4 * Real.pi ≤ alpha * N) :
    ∃ P : NatAP, P.IsProper ∧ P.carrier ⊆ Finset.range N ∧
      Real.sqrt (alpha ^ 3 * N / (128 * Real.pi)) ≤ P.length ∧
      (density A + alpha / 8) * P.length ≤
        ((P.carrier ∩ standardRepresentatives A).card : Real) := by
  classical
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  let fNat : Nat → Complex := fun x => balanced A (x : ZMod N)
  let phi : ZMod N → ZMod N := fun x => r * x
  have hfNat : ∀ x, x < N → ‖fNat x‖ ≤ 1 := by
    intro x _hx
    rw [show fNat x = (cor25BalancedReal A (x : ZMod N) : Complex) by
      exact cor25_balanced_eq_real A (x : ZMod N)]
    simpa [Real.norm_eq_abs] using cor25_balancedReal_abs_le_one A (x : ZMod N)
  have hphi : LinearOn (Finset.univ : Finset (ZMod N)) phi := by
    refine ⟨r, 0, ?_⟩
    intro x _hx
    dsimp only [phi]
    ring
  have hphaseSum :
      (∑ x ∈ Finset.range N, fNat x * exponential (-(phi (x : ZMod N)))) =
        fourier (indicator A) r := by
    calc
      _ = fourier (balanced A) r := by
        simpa only [fNat, phi] using cor25_range_phase_sum_eq_fourier_balanced A r
      _ = fourier (indicator A) r :=
        cor25_fourier_balanced_eq_indicator_of_ne_zero A r hr
  have hpremise :
      alpha * N ≤
        ‖∑ x ∈ Finset.range N, fNat x * exponential (-(phi (x : ZMod N)))‖ := by
    rw [hphaseSum]
    exact hlarge
  obtain ⟨m, P, hpartition, _hm, hsum, hlength⟩ :=
    corollary_2_4_holds N N fNat phi alpha (le_refl N) hscale
      hfNat hphi halpha hpremise
  let g : Fin m → Real := fun j =>
    ∑ x ∈ (P j).carrier, cor25BalancedReal A (x : ZMod N)
  have hzero : ∑ j, g j = 0 := by
    calc
      ∑ j, g j = ∑ x ∈ Finset.range N,
          cor25BalancedReal A (x : ZMod N) := by
        exact cor25_sum_partition (fun j => (P j).carrier) (Finset.range N)
          hpartition (fun x => cor25BalancedReal A (x : ZMod N))
      _ = ∑ z : ZMod N, cor25BalancedReal A z :=
        cor25_sum_range_zmod (cor25BalancedReal A)
      _ = 0 := cor25_balancedReal_sum_zero A
  have hcellNorm (j : Fin m) :
      ‖∑ x ∈ (P j).carrier, fNat x‖ = |g j| := by
    have hcast :
        (∑ x ∈ (P j).carrier, fNat x) = (g j : Complex) := by
      calc
        _ = ∑ x ∈ (P j).carrier,
            (cor25BalancedReal A (x : ZMod N) : Complex) := by
          apply Finset.sum_congr rfl
          intro x _hx
          exact cor25_balanced_eq_real A (x : ZMod N)
        _ = (g j : Complex) := by
          exact (Complex.ofReal_sum (P j).carrier
            (fun x => cor25BalancedReal A (x : ZMod N))).symm
    rw [hcast, Complex.norm_real, Real.norm_eq_abs]
  have hsumAbs : (alpha / 2) * N ≤ ∑ j, |g j| := by
    calc
      (alpha / 2) * N ≤ ∑ j, ‖∑ x ∈ (P j).carrier, fNat x‖ := hsum
      _ = ∑ j, |g j| := by
        apply Finset.sum_congr rfl
        intro j _hj
        exact hcellNorm j
  have hpositiveMass : (alpha / 4) * N ≤ ∑ j, max (g j) 0 := by
    rw [cor25_sum_abs_eq_two_mul_sum_max g hzero] at hsumAbs
    nlinarith
  have hlengthSumNat : ∑ j, (P j).length = N := by
    calc
      ∑ j, (P j).length = ∑ j, (P j).carrier.card := by
        apply Finset.sum_congr rfl
        intro j _hj
        exact (hlength j).1.2.symm
      _ = (Finset.range N).card := IsPartition.sum_card hpartition
      _ = N := Finset.card_range N
  have hlengthSum : ∑ j, ((P j).length : Real) = N := by
    exact_mod_cast hlengthSumNat
  have hthresholdSum :
      (∑ j, (alpha / 4) * ((P j).length : Real)) = (alpha / 4) * N := by
    rw [← Finset.mul_sum, hlengthSum]
  have hmPos : 0 < m := by
    have hzeroRange : 0 ∈ Finset.range N := by simp [NeZero.pos N]
    obtain ⟨j, _hj⟩ := (hpartition.1 0).mp hzeroRange
    exact Fin.pos_iff_nonempty.mpr ⟨j⟩
  have huniv : (Finset.univ : Finset (Fin m)).Nonempty :=
    ⟨⟨0, hmPos⟩, Finset.mem_univ _⟩
  have havg :
      (∑ j, (alpha / 4) * ((P j).length : Real)) ≤
        ∑ j, max (g j) 0 := by
    rw [hthresholdSum]
    exact hpositiveMass
  obtain ⟨j, _hj, hj⟩ := Finset.exists_le_of_sum_le
    (s := (Finset.univ : Finset (Fin m))) huniv havg
  have hlenPos : 0 < (P j).length := by
    have hlowerPos :
        0 < Real.sqrt (alpha * N / (128 * Real.pi)) := by
      exact Real.sqrt_pos.2 (div_pos (mul_pos halpha hN) (by positivity))
    have : (0 : Real) < (P j).length := hlowerPos.trans_le (hlength j).2.1
    exact_mod_cast this
  have hthresholdPos : 0 < (alpha / 4) * ((P j).length : Real) := by
    positivity
  have hgjPos : 0 < g j := by
    by_contra h
    have hnonpos : g j ≤ 0 := le_of_not_gt h
    rw [max_eq_right hnonpos] at hj
    exact (not_le_of_gt hthresholdPos) hj
  have hj' : (alpha / 4) * ((P j).length : Real) ≤ g j := by
    simpa only [max_eq_left hgjPos.le] using hj
  have hcellSubset : (P j).carrier ⊆ Finset.range N :=
    IsPartition.cell_subset hpartition j
  have hcellFormula :=
    cor25_balancedReal_sum_eq_inter_card A (P j).carrier hcellSubset
  have hcardLength : ((P j).carrier.card : Real) = (P j).length := by
    exact_mod_cast (hlength j).1.2
  dsimp only [g] at hj'
  rw [hcellFormula, hcardLength] at hj'
  obtain ⟨halphaDensity, _halphaComplement⟩ :=
    cor25_alpha_bounds A alpha r hr hlarge
  have halphaOne : alpha ≤ 1 := halphaDensity.trans (cor25_density_bounds A).2
  have halphaCube : alpha ^ 3 ≤ alpha := by
    nlinarith [sq_nonneg alpha, mul_nonneg halpha.le (sub_nonneg.mpr halphaOne)]
  have hrad :
      alpha ^ 3 * (N : Real) / (128 * Real.pi) ≤
        alpha * N / (128 * Real.pi) := by
    gcongr
  have hprogressionLength :
      Real.sqrt (alpha ^ 3 * (N : Real) / (128 * Real.pi)) ≤ (P j).length :=
    (Real.sqrt_le_sqrt hrad).trans (hlength j).2.1
  refine ⟨P j, (hlength j).1, hcellSubset, hprogressionLength, ?_⟩
  nlinarith [mul_nonneg halpha.le (Nat.cast_nonneg (P j).length)]

/-- **Gowers, Corollary 2.5.**  A large nonzero Fourier coefficient gives a
density increment on a proper progression.  The small finite scale is handled
by a singleton; at the large scale the weighted cell average actually gives
an `alpha / 4` increment, twice the bound asserted here. -/
theorem corollary_2_5_holds : corollary_2_5 := by
  intro N _ A alpha halpha hspectrum
  obtain ⟨r, hr, hlarge⟩ := hspectrum
  have hr' : r ≠ 0 := bne_iff_ne.mp hr
  by_cases hscale : 4 * Real.pi ≤ alpha * N
  · exact cor25_large_scale A alpha halpha r hr' hlarge hscale
  · exact cor25_small_scale A alpha halpha r hr' hlarge hscale

end LeanProofs.GowersSzemeredi
