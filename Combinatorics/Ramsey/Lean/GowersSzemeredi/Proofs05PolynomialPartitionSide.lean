import GowersSzemeredi.Proofs05PolynomialPartition

/-! Declarations of `Proofs05PolynomialPartition` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

private theorem polynomial_missing_interval_witness
    {N k t M : Nat} [NeZero N] (a : ZMod N) (gamma : Real)
    (ht : 2 ≤ t) (htN : t ≤ N) (hM : 0 < M) (hMeven : Even M)
    (hMN : 2 * M ≤ N)
    (hMscale : (M : Real) ≤ (t : Real) ^ (-gamma) * N)
    (hno : ∀ p : Nat, 1 ≤ p → p ≤ t →
      (t : Real) ^ (-gamma) * N <
        (centeredAbs (((p : ZMod N) ^ k) * a) : Real)) :
    ∃ r : ZMod N, r ≠ 0 ∧
      (centeredAbs r : Real) ≤ (N : Real) ^ 2 / (M : Real) ^ 2 ∧
      (t : Real) * M / (4 * N) ≤
        ‖weylSum (-(a * r).valMinAbs / (N : Real)) k t‖ := by
  have hN : 1 < N := lt_of_lt_of_le (by omega : 1 < t) htN
  let w : ZMod N → Nat := polynomialValueMultiplicity k t a
  have hmass : ∑ x : ZMod N, w x = t :=
    polynomialValueMultiplicity_mass a
  have havoid : ∀ s ∈ Finset.Icc 1 t,
      ((s : ZMod N) ^ k) * a ∉ centeredInterval N M := by
    intro s hs hscentered
    have hsBounds := Finset.mem_Icc.mp hs
    have habsNat := centeredAbs_le_of_mem_centeredInterval hMN hscentered
    have habsReal :
        (centeredAbs (((s : ZMod N) ^ k) * a) : Real) ≤ M := by
      exact_mod_cast habsNat
    exact (not_lt_of_ge (habsReal.trans hMscale))
      (hno s hsBounds.1 hsBounds.2)
  have hzero : ∀ x ∈ centeredInterval N M, w x = 0 :=
    polynomialValueMultiplicity_zero_of_avoids a havoid
  obtain ⟨r, hr0, hrsize, hrlarge⟩ :=
    weighted_missing_interval_fourier N M t w hN hM hMeven hMN hmass hzero
  refine ⟨r, hr0, hrsize, ?_⟩
  rwa [fourier_polynomialValueMultiplicity_eq_weylSum] at hrlarge

private theorem polynomial_weyl_witness
    {N k t : Nat} [NeZero N] (a : ZMod N)
    (hk : 2 ≤ k) (ht : weylThreshold k ≤ t) (htN : t ≤ N)
    (hno : ∀ p : Nat, 1 ≤ p → p ≤ t →
      (t : Real) ^
          (-(((k : Real) * (2 : Real) ^ (k + 1))⁻¹)) * N <
        (centeredAbs (((p : ZMod N) ^ k) * a) : Real)) :
    ∃ r : ZMod N, r ≠ 0 ∧
      (centeredAbs r : Real) ≤
        16 * (t : Real) ^
          (2 * (((k : Real) * (2 : Real) ^ (k + 1))⁻¹)) ∧
      (t : Real) ^
          (1 - (((k : Real) * (2 : Real) ^ (k + 1))⁻¹)) / 16 ≤
        ‖weylSum (-(a * r).valMinAbs / (N : Real)) k t‖ := by
  let gamma : Real := ((k : Real) * (2 : Real) ^ (k + 1))⁻¹
  let scale : Real := (t : Real) ^ (-gamma) * N
  let M : Nat := 2 * Nat.floor (scale / 4)
  have htTwo : 2 ≤ t := by
    exact (by norm_num : 2 ≤ 64).trans
      ((weylThreshold_sixtyFour_le hk).trans ht)
  have hscaleEight : 8 ≤ scale := by
    simpa only [scale, gamma] using recurrenceScale_eight_le hk ht htN
  obtain ⟨hMpos, hMeven, hMupper, hMlower⟩ :=
    twice_floor_quarter_bounds hscaleEight
  have hscaleN : scale ≤ N := by
    simpa only [scale, gamma] using recurrenceScale_le_N (k := k) (N := N)
      (show 1 ≤ t by omega)
  have hMNReal : (2 : Real) * M ≤ N := by
    calc
      (2 : Real) * M ≤ 2 * (scale / 2) := by gcongr
      _ = scale := by ring
      _ ≤ N := hscaleN
  have hMN : 2 * M ≤ N := by exact_mod_cast hMNReal
  have hMscale : (M : Real) ≤ (t : Real) ^ (-gamma) * N := hMupper.trans (by linarith [hscaleEight])
  obtain ⟨r, hr0, hrsize, hrlarge⟩ :=
    polynomial_missing_interval_witness a gamma htTwo htN hMpos hMeven hMN
      hMscale (by simpa only [gamma] using hno)
  have htPos : (0 : Real) < t := by exact_mod_cast (show 0 < t by omega)
  have hNPos : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hMPosReal : (0 : Real) < M := by exact_mod_cast hMpos
  have hpowersCancel : (t : Real) ^ gamma * (t : Real) ^ (-gamma) = 1 := by
    rw [← Real.rpow_add htPos]
    simp
  have hNM : (N : Real) ≤ 4 * (t : Real) ^ gamma * M := by
    have hscaled := mul_le_mul_of_nonneg_left hMlower (show 0 ≤ 4 *
      (t : Real) ^ gamma by positivity)
    dsimp only [scale] at hscaled
    have hleft :
        4 * (t : Real) ^ gamma *
            (((t : Real) ^ (-gamma) * N) / 4) = N := by
      calc
        4 * (t : Real) ^ gamma *
            (((t : Real) ^ (-gamma) * N) / 4) =
            ((t : Real) ^ gamma * (t : Real) ^ (-gamma)) * N := by ring
        _ = N := by rw [hpowersCancel, one_mul]
    rw [hleft] at hscaled
    exact hscaled
  have hratio :
      (N : Real) ^ 2 / (M : Real) ^ 2 ≤
        16 * (t : Real) ^ (2 * gamma) := by
    have hsquare : (N : Real) ^ 2 ≤
        (4 * (t : Real) ^ gamma * M) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hNM 2
    have hrpow :
        (t : Real) ^ (2 * gamma) = ((t : Real) ^ gamma) ^ 2 := by
      rw [show 2 * gamma = gamma + gamma by ring, Real.rpow_add htPos]
      ring
    rw [hrpow]
    apply (div_le_iff₀ (sq_pos_of_pos hMPosReal)).2
    calc
      (N : Real) ^ 2 ≤ (4 * (t : Real) ^ gamma * M) ^ 2 := hsquare
      _ = (16 * ((t : Real) ^ gamma) ^ 2) * M ^ 2 := by ring
  have hlower :
      (t : Real) ^ (1 - gamma) / 16 ≤
        (t : Real) * M / (4 * N) := by
    have hscaled := mul_le_mul_of_nonneg_left hMlower
      (show 0 ≤ (t : Real) / (4 * N) by positivity)
    have hcombine :
        (t : Real) * ((t : Real) ^ (-gamma) * N) / (16 * N) =
          (t : Real) ^ (1 - gamma) / 16 := by
      rw [show 1 - gamma = 1 + -gamma by ring, Real.rpow_add htPos,
        Real.rpow_one]
      field_simp [ne_of_gt hNPos]
    dsimp only [scale] at hscaled
    calc
      (t : Real) ^ (1 - gamma) / 16 =
          (t : Real) * ((t : Real) ^ (-gamma) * N) / (16 * N) :=
        hcombine.symm
      _ = ((t : Real) / (4 * N)) *
          (((t : Real) ^ (-gamma) * N) / 4) := by ring
      _ ≤ ((t : Real) / (4 * N)) * M := hscaled
      _ = (t : Real) * M / (4 * N) := by ring
  refine ⟨r, hr0, ?_, ?_⟩
  · exact hrsize.trans (by simpa only [gamma] using hratio)
  · have hlower' :
        (t : Real) ^
            (1 - (((k : Real) * (2 : Real) ^ (k + 1))⁻¹)) / 16 ≤
          (t : Real) * M / (4 * N) := by
      simpa only [gamma] using hlower
    exact hlower'.trans hrlarge

private lemma lemma55_threshold_weyl_gap {k t : Nat} (hk : 2 ≤ k)
    (ht : weylThreshold k ≤ t) :
    (48000 : Real) < (t : Real) ^
      (2 * (((k : Real) * (2 : Real) ^ (k + 1))⁻¹)) := by
  let D := k * 2 ^ k
  have hkpow : k ≤ 2 ^ k :=
    (Nat.le_succ k).trans (nat_succ_le_two_pow k)
  have hkCube : k ≤ k ^ 3 := nat_le_cube (by omega)
  have hexponent : 2 * k + 4 ≤ 40 * k ^ 3 := by
    calc
      2 * k + 4 ≤ 4 * k := by omega
      _ ≤ 4 * k ^ 3 := Nat.mul_le_mul_left 4 hkCube
      _ ≤ 40 * k ^ 3 := Nat.mul_le_mul_right (k ^ 3) (by norm_num)
  have hD : 0 < D := by dsimp only [D]; positivity
  have hD16 : D * 16 ≤ 2 ^ (40 * k ^ 3) := by
    calc
      D * 16 = k * 2 ^ k * 16 := rfl
      _ ≤ 2 ^ k * 2 ^ k * 16 :=
        Nat.mul_le_mul_right 16 (Nat.mul_le_mul_right (2 ^ k) hkpow)
      _ = 2 ^ (2 * k + 4) := by
        rw [show 16 = 2 ^ 4 by norm_num, ← pow_add, ← pow_add]
        congr 1
        omega
      _ ≤ 2 ^ (40 * k ^ 3) :=
        Nat.pow_le_pow_right (by norm_num) hexponent
  have hroot := lemma55_threshold_root hD hD16 ht
  have hkReal : (0 : Real) < k := by positivity
  have hpow : (2 : Real) ^ (k + 1) = 2 * (2 : Real) ^ k := by
    rw [pow_succ]
    ring
  have hgamma :
      ((D : Real)⁻¹) =
        2 * (((k : Real) * (2 : Real) ^ (k + 1))⁻¹) := by
    dsimp only [D]
    push_cast
    rw [hpow]
    field_simp [ne_of_gt hkReal]
  calc
    (48000 : Real) < (2 : Real) ^ 16 := by norm_num
    _ ≤ (t : Real) ^ ((D : Real)⁻¹) := hroot
    _ = (t : Real) ^
        (2 * (((k : Real) * (2 : Real) ^ (k + 1))⁻¹)) := by rw [hgamma]

private lemma lemma55_threshold_constant {k t : Nat} (hk : 2 ≤ k)
    (ht : weylThreshold k ≤ t) :
    (16 : Real) ^ (k - 1) ≤
      (t : Real) ^ ((4 * (k : Real))⁻¹) := by
  let D := 4 * k
  let E := 4 * (k - 1)
  have hD : 0 < D := by dsimp only [D]; positivity
  have hkSqCube : k ^ 2 ≤ k ^ 3 :=
    pow_le_pow_right₀ (by omega : 1 ≤ k) (by norm_num)
  have hpoly : D * E ≤ 40 * k ^ 3 := by
    calc
      D * E = 16 * k * (k - 1) := by dsimp only [D, E]; ring
      _ ≤ 16 * k * k := by gcongr; omega
      _ = 16 * k ^ 2 := by ring
      _ ≤ 16 * k ^ 3 := Nat.mul_le_mul_left 16 hkSqCube
      _ ≤ 40 * k ^ 3 := Nat.mul_le_mul_right (k ^ 3) (by norm_num)
  have hDE : D * E ≤ 2 ^ (40 * k ^ 3) :=
    hpoly.trans <| (Nat.le_succ (40 * k ^ 3)).trans
      (nat_succ_le_two_pow (40 * k ^ 3))
  have hroot := lemma55_threshold_root hD hDE ht
  have hbase : (16 : Real) ^ (k - 1) = (2 : Real) ^ E := by
    dsimp only [E]
    rw [show (16 : Real) = 2 ^ 4 by norm_num, pow_mul]
  have hDcast : (D : Real) = 4 * (k : Real) := by
    dsimp only [D]
    push_cast
    rfl
  rw [hbase, ← hDcast]
  exact hroot

private lemma lemma55_exponent_budget {k : Nat} (hk : 2 ≤ k) :
    (4 * (k : Real))⁻¹ +
        (2 * (((k : Real) * (2 : Real) ^ (k + 1))⁻¹) +
          (k : Real)⁻¹) * (k - 1) ≤
      1 - (((k : Real) * (2 : Real) ^ (k + 1))⁻¹) := by
  have hkReal : (0 : Real) < k := by positivity
  have hkpow : k ≤ 2 ^ (k - 1) := by
    have h := nat_succ_le_two_pow (k - 1)
    rwa [Nat.sub_add_cancel (by omega : 1 ≤ k)] at h
  have htwok : 2 * k ≤ 2 ^ k := by
    calc
      2 * k ≤ 2 * 2 ^ (k - 1) := Nat.mul_le_mul_left 2 hkpow
      _ = 2 ^ (k - 1) * 2 := by ring
      _ = 2 ^ ((k - 1) + 1) := (pow_succ _ _).symm
      _ = 2 ^ k := by rw [Nat.sub_add_cancel (by omega : 1 ≤ k)]
  have hpowNat : 4 * (2 * k - 1) ≤ 3 * 2 ^ (k + 1) := by
    calc
      4 * (2 * k - 1) ≤ 8 * k := by omega
      _ = 4 * (2 * k) := by ring
      _ ≤ 4 * 2 ^ k := Nat.mul_le_mul_left 4 htwok
      _ = 2 * 2 ^ (k + 1) := by rw [pow_succ]; ring
      _ ≤ 3 * 2 ^ (k + 1) :=
        Nat.mul_le_mul_right (2 ^ (k + 1)) (by norm_num)
  have hpowReal :
      4 * (2 * (k : Real) - 1) ≤ 3 * (2 : Real) ^ (k + 1) := by
    have hsubCast : ((2 * k - 1 : Nat) : Real) = 2 * (k : Real) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ 2 * k)]
      push_cast
      ring
    rw [← hsubCast]
    exact_mod_cast hpowNat
  have hpowPos : (0 : Real) < (2 : Real) ^ (k + 1) := by positivity
  field_simp [ne_of_gt hkReal, ne_of_gt hpowPos]
  nlinarith

private lemma lemma55_dirichlet_denominator_le {k t q : Nat}
    (hk : 2 ≤ k) (ht : weylThreshold k ≤ t) (hq : 1 ≤ q)
    (hqt : q ≤ t) (alpha : Real)
    (hlower :
      (t : Real) ^
          (1 - (((k : Real) * (2 : Real) ^ (k + 1))⁻¹)) / 16 ≤
        ‖weylSum alpha k t‖)
    (hupper :
      ‖weylSum alpha k t‖ ≤
        1000 * (t : Real) ^
            (1 + (((k : Real) * (2 : Real) ^ (k + 1))⁻¹)) *
          (((q : Real)⁻¹ + (t : Real)⁻¹ +
            (q : Real) * (t : Real) ^ (-(k : Real))) ^
              ((2 : Real) ^ (k - 1))⁻¹)) :
    (q : Real) ≤ (t : Real) ^ ((k : Real)⁻¹) := by
  let gamma : Real := ((k : Real) * (2 : Real) ^ (k + 1))⁻¹
  let K : Real := (2 : Real) ^ (k - 1)
  let X : Real := (t : Real) ^ (-(k : Real)⁻¹)
  let B : Real := (q : Real)⁻¹ + (t : Real)⁻¹ +
    (q : Real) * (t : Real) ^ (-(k : Real))
  have htOneNat : 1 ≤ t := (show 1 ≤ q by exact hq).trans hqt
  have htOne : (1 : Real) ≤ t := by exact_mod_cast htOneNat
  have htPos : (0 : Real) < t := by positivity
  have hqPos : (0 : Real) < q := by exact_mod_cast (show 0 < q by omega)
  have hkReal : (0 : Real) < k := by positivity
  have hKOne : (1 : Real) ≤ K := by
    dsimp only [K]
    exact one_le_pow₀ (by norm_num)
  have hKPos : (0 : Real) < K := lt_of_lt_of_le zero_lt_one hKOne
  have hKInvNonneg : (0 : Real) ≤ K⁻¹ := by positivity
  have hBNonneg : 0 ≤ B := by dsimp only [B]; positivity
  by_contra hqBound
  have hqLarge : (t : Real) ^ ((k : Real)⁻¹) < q :=
    lt_of_not_ge hqBound
  have hrootPos : (0 : Real) < (t : Real) ^ ((k : Real)⁻¹) :=
    Real.rpow_pos_of_pos htPos _
  have hqInv : (q : Real)⁻¹ ≤ X := by
    dsimp only [X]
    rw [Real.rpow_neg htPos.le]
    exact (inv_le_inv₀ hqPos hrootPos).2 hqLarge.le
  have hkInvLeOne : (k : Real)⁻¹ ≤ 1 :=
    (inv_le_one₀ hkReal).2 (by exact_mod_cast (show 1 ≤ k by omega))
  have htInv : (t : Real)⁻¹ ≤ X := by
    dsimp only [X]
    calc
      (t : Real)⁻¹ = (t : Real) ^ (-1 : Real) :=
        (Real.rpow_neg_one _).symm
      _ ≤ (t : Real) ^ (-(k : Real)⁻¹) :=
        Real.rpow_le_rpow_of_exponent_le htOne (by linarith)
  have hexponent : (1 : Real) - k ≤ -(k : Real)⁻¹ := by
    rw [show -(k : Real)⁻¹ = (-1 : Real) / (k : Real) by
      simp [div_eq_mul_inv]]
    apply (le_div_iff₀ hkReal).2
    have hkTwo : (2 : Real) ≤ k := by exact_mod_cast hk
    nlinarith [sq_nonneg ((k : Real) - 1)]
  have hqTerm :
      (q : Real) * (t : Real) ^ (-(k : Real)) ≤ X := by
    have hqtReal : (q : Real) ≤ t := by exact_mod_cast hqt
    calc
      (q : Real) * (t : Real) ^ (-(k : Real)) ≤
          (t : Real) * (t : Real) ^ (-(k : Real)) := by
        gcongr
      _ = (t : Real) ^ (1 - (k : Real)) := by
        calc
          (t : Real) * (t : Real) ^ (-(k : Real)) =
              (t : Real) ^ (1 : Real) *
                (t : Real) ^ (-(k : Real)) := by rw [Real.rpow_one]
          _ = (t : Real) ^ ((1 : Real) + -(k : Real)) := by
            rw [Real.rpow_add htPos]
          _ = (t : Real) ^ (1 - (k : Real)) := by congr 1
      _ ≤ X := by
        dsimp only [X]
        exact Real.rpow_le_rpow_of_exponent_le htOne hexponent
  have hB : B ≤ 3 * X := by
    dsimp only [B]
    linarith
  have hKInvLeOne : K⁻¹ ≤ 1 := (inv_le_one₀ hKPos).2 hKOne
  have hthree : (3 : Real) ^ K⁻¹ ≤ 3 := by
    calc
      (3 : Real) ^ K⁻¹ ≤ (3 : Real) ^ (1 : Real) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hKInvLeOne
      _ = 3 := Real.rpow_one 3
  have hBroot :
      B ^ K⁻¹ ≤ 3 *
        (t : Real) ^ ((-(k : Real)⁻¹) * K⁻¹) := by
    calc
      B ^ K⁻¹ ≤ (3 * X) ^ K⁻¹ :=
        Real.rpow_le_rpow hBNonneg hB hKInvNonneg
      _ = (3 : Real) ^ K⁻¹ * X ^ K⁻¹ := by
        rw [Real.mul_rpow (by norm_num) (by positivity)]
      _ ≤ 3 * X ^ K⁻¹ := by gcongr
      _ = 3 * (t : Real) ^ ((-(k : Real)⁻¹) * K⁻¹) := by
        dsimp only [X]
        rw [← Real.rpow_mul htPos.le]
  have hpow : (2 : Real) ^ (k + 1) = 4 * K := by
    dsimp only [K]
    rw [show k + 1 = (k - 1) + 2 by omega, pow_add]
    norm_num
    <;> ring
  have hrootExponent :
      (-(k : Real)⁻¹) * K⁻¹ = -4 * gamma := by
    dsimp only [gamma]
    rw [hpow]
    field_simp [ne_of_gt hkReal, ne_of_gt hKPos]
  have hupper' :
      ‖weylSum alpha k t‖ ≤
        3000 * (t : Real) ^ (1 - 3 * gamma) := by
    calc
      ‖weylSum alpha k t‖ ≤
          1000 * (t : Real) ^ (1 + gamma) * B ^ K⁻¹ := by
        simpa only [gamma, K, B] using hupper
      _ ≤ 1000 * (t : Real) ^ (1 + gamma) *
          (3 * (t : Real) ^ ((-(k : Real)⁻¹) * K⁻¹)) := by
        exact mul_le_mul_of_nonneg_left hBroot (by positivity)
      _ = 3000 * (t : Real) ^ (1 - 3 * gamma) := by
        rw [hrootExponent]
        have hcombine :
            (t : Real) ^ (1 + gamma) * (t : Real) ^ (-4 * gamma) =
              (t : Real) ^ (1 - 3 * gamma) := by
          rw [← Real.rpow_add htPos]
          congr 1
          ring
        calc
          1000 * (t : Real) ^ (1 + gamma) *
              (3 * (t : Real) ^ (-4 * gamma)) =
              3000 * ((t : Real) ^ (1 + gamma) *
                (t : Real) ^ (-4 * gamma)) := by ring
          _ = 3000 * (t : Real) ^ (1 - 3 * gamma) := by rw [hcombine]
  have hcombined :
      (t : Real) ^ (1 - gamma) / 16 ≤
        3000 * (t : Real) ^ (1 - 3 * gamma) := by
    have hlower' :
        (t : Real) ^ (1 - gamma) / 16 ≤ ‖weylSum alpha k t‖ := by
      simpa only [gamma] using hlower
    exact hlower'.trans hupper'
  have hfactor :
      (t : Real) ^ (1 - gamma) =
        (t : Real) ^ (1 - 3 * gamma) * (t : Real) ^ (2 * gamma) := by
    rw [← Real.rpow_add htPos]
    congr 1
    ring
  have hproduct :
      (t : Real) ^ (1 - 3 * gamma) * (t : Real) ^ (2 * gamma) ≤
        (t : Real) ^ (1 - 3 * gamma) * 48000 := by
    calc
      (t : Real) ^ (1 - 3 * gamma) * (t : Real) ^ (2 * gamma) =
          (t : Real) ^ (1 - gamma) := hfactor.symm
      _ ≤ (3000 * (t : Real) ^ (1 - 3 * gamma)) * 16 :=
        (div_le_iff₀ (by norm_num : (0 : Real) < 16)).1 hcombined
      _ = (t : Real) ^ (1 - 3 * gamma) * 48000 := by ring
  have hgapUpper : (t : Real) ^ (2 * gamma) ≤ 48000 :=
    le_of_mul_le_mul_left hproduct
      (Real.rpow_pos_of_pos htPos (1 - 3 * gamma))
  have hgapLower : (48000 : Real) < (t : Real) ^ (2 * gamma) := by
    simpa only [gamma] using lemma55_threshold_weyl_gap hk ht
  exact (not_le_of_gt hgapLower) hgapUpper

/-- Lemma 5.5, with the collision-safe weighted Fourier argument supplying
the large Weyl sum and the repaired explicit Weyl inequality supplying the
rational-denominator bound. -/
theorem lemma_5_5_holds : lemma_5_5 := by
  unfold lemma_5_5
  intro k t N _ hk ht htN a
  by_contra hrecurrence
  let gamma : Real := ((k : Real) * (2 : Real) ^ (k + 1))⁻¹
  have hno : ∀ p : Nat, 1 ≤ p → p ≤ t →
      (t : Real) ^ (-gamma) * N <
        (centeredAbs (((p : ZMod N) ^ k) * a) : Real) := by
    intro p hp hpt
    apply lt_of_not_ge
    intro hpClose
    apply hrecurrence
    exact ⟨p, hp, hpt, by simpa only [gamma] using hpClose⟩
  obtain ⟨r, hr0, hrsize, hrlarge⟩ :=
    polynomial_weyl_witness a hk ht htN (by
      simpa only [gamma] using hno)
  let c : Int := (a * r).valMinAbs
  let alpha : Real := -(c : Real) / (N : Real)
  have htOne : 1 ≤ t :=
    (show 1 ≤ 64 by norm_num).trans ((weylThreshold_sixtyFour_le hk).trans ht)
  obtain ⟨b, q, hq, hqt, hbq, happrox⟩ :=
    lemma_5_4_holds alpha t htOne
  have hqPos : (0 : Real) < q := by exact_mod_cast (show 0 < q by omega)
  have htPos : (0 : Real) < t := by exact_mod_cast (show 0 < t by omega)
  have hNPos : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hqInt : (0 : Int) < q := by exact_mod_cast (show 0 < q by omega)
  have hgcd : Int.gcd b (q : Int) = 1 := by
    rw [Int.gcd_eq_natAbs, Int.natAbs_natCast]
    exact hbq.gcd_eq_one
  have happroxSq :
      |alpha - (b : Real) / (q : Real)| ≤ ((q : Real) ^ 2)⁻¹ := by
    have hqtReal : (q : Real) ≤ t := by exact_mod_cast hqt
    have hden : (q : Real) ^ 2 ≤ (q : Real) * t := by
      rw [pow_two]
      exact mul_le_mul_of_nonneg_left hqtReal hqPos.le
    exact happrox.trans <|
      (inv_le_inv₀ (mul_pos hqPos htPos) (sq_pos_of_pos hqPos)).2 hden
  have hweyl :=
    (lemma_5_3_holds k (by omega)).2 t b (q : Int) alpha ht hqInt hgcd
      (by simpa using happroxSq)
  have hrlarge' :
      (t : Real) ^ (1 - gamma) / 16 ≤ ‖weylSum alpha k t‖ := by
    simpa only [gamma, alpha, c] using hrlarge
  have hqBound :
      (q : Real) ≤ (t : Real) ^ ((k : Real)⁻¹) := by
    apply lemma55_dirichlet_denominator_le hk ht hq hqt alpha hrlarge'
    simpa using hweyl
  let s : Nat := centeredAbs r
  let p : Nat := s * q
  have hsPos : 0 < s := by
    apply Nat.pos_of_ne_zero
    intro hsZero
    have hvalMin : r.valMinAbs = 0 := by
      apply Int.natAbs_eq_zero.mp
      simpa only [s, centeredAbs] using hsZero
    exact hr0 ((ZMod.valMinAbs_eq_zero r).mp hvalMin)
  have hpOne : 1 ≤ p := by
    dsimp only [p]
    exact Nat.one_le_iff_ne_zero.mpr
      (mul_ne_zero (Nat.ne_of_gt hsPos) (Nat.ne_of_gt (by omega)))
  have hsBound :
      (s : Real) ≤ 16 * (t : Real) ^ (2 * gamma) := by
    simpa only [s, gamma] using hrsize
  have hpBound :
      (p : Real) ≤
        16 * (t : Real) ^ (2 * gamma + (k : Real)⁻¹) := by
    calc
      (p : Real) = (s : Real) * q := by dsimp only [p]; push_cast; rfl
      _ ≤ (16 * (t : Real) ^ (2 * gamma)) *
          (t : Real) ^ ((k : Real)⁻¹) :=
        mul_le_mul hsBound hqBound (by positivity) (by positivity)
      _ = 16 * (t : Real) ^ (2 * gamma + (k : Real)⁻¹) := by
        rw [Real.rpow_add htPos]
        ring
  have hconst :
      (16 : Real) ^ (k - 1) ≤
        (t : Real) ^ ((4 * (k : Real))⁻¹) :=
    lemma55_threshold_constant hk ht
  have hbudget :
      (4 * (k : Real))⁻¹ +
          (2 * gamma + (k : Real)⁻¹) * (k - 1) ≤ 1 - gamma := by
    simpa only [gamma] using lemma55_exponent_budget hk
  have hkSubCast : ((k - 1 : Nat) : Real) = (k : Real) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k)]
    norm_num
  have htpow :
      (((t : Real) ^ (2 * gamma + (k : Real)⁻¹)) ^ (k - 1)) =
        (t : Real) ^
          ((2 * gamma + (k : Real)⁻¹) * ((k : Real) - 1)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul htPos.le, hkSubCast]
  have hpPow :
      (p : Real) ^ (k - 1) ≤ (t : Real) ^ (1 - gamma) := by
    calc
      (p : Real) ^ (k - 1) ≤
          (16 * (t : Real) ^
            (2 * gamma + (k : Real)⁻¹)) ^ (k - 1) :=
        pow_le_pow_left₀ (by positivity) hpBound (k - 1)
      _ = (16 : Real) ^ (k - 1) *
          (t : Real) ^
            ((2 * gamma + (k : Real)⁻¹) * ((k : Real) - 1)) := by
        rw [mul_pow, htpow]
      _ ≤ (t : Real) ^ ((4 * (k : Real))⁻¹) *
          (t : Real) ^
            ((2 * gamma + (k : Real)⁻¹) * ((k : Real) - 1)) := by
        exact mul_le_mul_of_nonneg_right hconst (by positivity)
      _ = (t : Real) ^
          ((4 * (k : Real))⁻¹ +
            (2 * gamma + (k : Real)⁻¹) * ((k : Real) - 1)) := by
        rw [Real.rpow_add htPos]
      _ ≤ (t : Real) ^ (1 - gamma) :=
        Real.rpow_le_rpow_of_exponent_le
          (by exact_mod_cast htOne : (1 : Real) ≤ t) hbudget
  have hpLeT : p ≤ t := by
    have hpLePow : p ≤ p ^ (k - 1) := by
      simpa only [pow_one] using
        pow_le_pow_right₀ hpOne (by omega : 1 ≤ k - 1)
    have hpLePowReal : (p : Real) ≤ (p : Real) ^ (k - 1) := by
      exact_mod_cast hpLePow
    have hgammaNonneg : 0 ≤ gamma := by dsimp only [gamma]; positivity
    have hpowLeT : (t : Real) ^ (1 - gamma) ≤ t := by
      calc
        (t : Real) ^ (1 - gamma) ≤ (t : Real) ^ (1 : Real) :=
          Real.rpow_le_rpow_of_exponent_le
            (by exact_mod_cast htOne : (1 : Real) ≤ t) (by linarith)
        _ = t := Real.rpow_one _
    exact_mod_cast hpLePowReal.trans (hpPow.trans hpowLeT)
  let e₀ : Int := -c * (q : Int) - b * (N : Int)
  let E : Int := e₀ * (p : Int) ^ (k - 1)
  have hfraction :
      alpha - (b : Real) / (q : Real) =
        (e₀ : Real) / ((N : Real) * (q : Real)) := by
    dsimp only [alpha, e₀]
    push_cast
    field_simp [ne_of_gt hNPos, ne_of_gt hqPos]
  have happrox' :
      |(e₀ : Real)| / ((N : Real) * (q : Real)) ≤
        ((q : Real) * t)⁻¹ := by
    have hdenAbs : |(N : Real) * (q : Real)| =
        (N : Real) * (q : Real) :=
      abs_of_pos (mul_pos hNPos hqPos)
    calc
      |(e₀ : Real)| / ((N : Real) * (q : Real)) =
          |(e₀ : Real)| / |(N : Real) * (q : Real)| := by rw [hdenAbs]
      _ = |(e₀ : Real) / ((N : Real) * (q : Real))| :=
        (abs_div _ _).symm
      _ = |alpha - (b : Real) / (q : Real)| := by rw [hfraction]
      _ ≤ ((q : Real) * t)⁻¹ := happrox
  have he₀Bound : |(e₀ : Real)| ≤ (N : Real) / t := by
    calc
      |(e₀ : Real)| ≤
          ((q : Real) * t)⁻¹ * ((N : Real) * (q : Real)) :=
        (div_le_iff₀ (mul_pos hNPos hqPos)).1 happrox'
      _ = (N : Real) / t := by
        field_simp [ne_of_gt hqPos, ne_of_gt htPos]
  have hEabsCast : (E.natAbs : Real) = |(E : Real)| := by
    have hInt : (E.natAbs : Int) = |E| := by
      rw [Int.abs_eq_natAbs]
    calc
      (E.natAbs : Real) = ((E.natAbs : Int) : Real) := (Int.cast_natCast E.natAbs).symm
      _ = ((|E| : Int) : Real) :=
        congrArg (fun z : Int => (z : Real)) hInt
      _ = |(E : Real)| := by rw [Int.cast_abs]
  have hEBound :
      (E.natAbs : Real) ≤
        ((N : Real) / t) * (p : Real) ^ (k - 1) := by
    calc
      (E.natAbs : Real) = |(e₀ : Real)| * (p : Real) ^ (k - 1) := by
        rw [hEabsCast]
        dsimp only [E]
        push_cast
        rw [abs_mul, abs_pow, abs_of_nonneg (by positivity : (0 : Real) ≤ p)]
      _ ≤ ((N : Real) / t) * (p : Real) ^ (k - 1) :=
        mul_le_mul_of_nonneg_right he₀Bound (by positivity)
  have hcCast : (c : ZMod N) = a * r := by
    dsimp only [c]
    exact ZMod.coe_valMinAbs _
  have he₀Cast : (e₀ : ZMod N) =
      -(c : ZMod N) * (q : ZMod N) := by
    dsimp only [e₀]
    push_cast
    simp
  have hECast : (E : ZMod N) =
      (-(c : ZMod N) * (q : ZMod N)) *
        (p : ZMod N) ^ (k - 1) := by
    dsimp only [E]
    push_cast
    rw [he₀Cast]
  have hpCast : (p : ZMod N) =
      (s : ZMod N) * (q : ZMod N) := by
    dsimp only [p]
    push_cast
    rfl
  have hkSplit : k = (k - 1) + 1 := by omega
  have hpPowSplit : (p : ZMod N) ^ k =
      (p : ZMod N) ^ (k - 1) * (p : ZMod N) := by
    calc
      (p : ZMod N) ^ k = (p : ZMod N) ^ ((k - 1) + 1) :=
        congrArg (fun n : Nat => (p : ZMod N) ^ n) hkSplit
      _ = (p : ZMod N) ^ (k - 1) * (p : ZMod N) := pow_succ _ _
  have htarget :
      ((p : ZMod N) ^ k) * a = (E : ZMod N) ∨
        ((p : ZMod N) ^ k) * a = -(E : ZMod N) := by
    rcases lemma55_natCast_centeredAbs_eq_or_neg r with hsCast | hsCast
    · right
      calc
        ((p : ZMod N) ^ k) * a =
            (((p : ZMod N) ^ (k - 1)) * (p : ZMod N)) * a := by
          rw [hpPowSplit]
        _ = -(E : ZMod N) := by
          rw [hECast, hpCast, hsCast, hcCast]
          ring
    · left
      calc
        ((p : ZMod N) ^ k) * a =
            (((p : ZMod N) ^ (k - 1)) * (p : ZMod N)) * a := by
          rw [hpPowSplit]
        _ = (E : ZMod N) := by
          rw [hECast, hpCast, hsCast, hcCast]
          ring
  have hcenterNat :
      centeredAbs (((p : ZMod N) ^ k) * a) ≤ E.natAbs := by
    rcases htarget with htarget | htarget
    · rw [htarget]
      exact lemma55_centeredAbs_intCast_le E
    · rw [htarget, lemma55_centeredAbs_neg]
      exact lemma55_centeredAbs_intCast_le E
  have hcenterReal :
      (centeredAbs (((p : ZMod N) ^ k) * a) : Real) ≤ E.natAbs := by
    exact_mod_cast hcenterNat
  have hfinal :
      (centeredAbs (((p : ZMod N) ^ k) * a) : Real) ≤
        (t : Real) ^ (-gamma) * N := by
    calc
      (centeredAbs (((p : ZMod N) ^ k) * a) : Real) ≤ E.natAbs :=
        hcenterReal
      _ ≤ ((N : Real) / t) * (p : Real) ^ (k - 1) := hEBound
      _ ≤ ((N : Real) / t) * (t : Real) ^ (1 - gamma) :=
        mul_le_mul_of_nonneg_left hpPow (by positivity)
      _ = (t : Real) ^ (-gamma) * N := by
        rw [show 1 - gamma = -gamma + 1 by ring,
          Real.rpow_add htPos, Real.rpow_one]
        field_simp [ne_of_gt htPos]
  exact (not_lt_of_ge hfinal) (hno p hpOne hpLeT)

/-!
The arithmetic part of the counterexample is developed for an abstract odd
integer `Q`.  This is intentional: reducing the displayed threshold
`2^(2^40)` during elaboration is both unnecessary and very expensive.  The
final specialization will take `Q = 2 * polynomialPartitionThreshold 1 + 1`.
-/

private def cor56CounterR (Q : Nat) : Nat := Q ^ 16

private def cor56CounterM (Q : Nat) : Nat := Q ^ 15

private lemma cor56Counter_constant : polynomialPartitionConstant 1 = 16 := by
  norm_num [polynomialPartitionConstant]

private lemma polynomialPartitionThreshold_pos (k : Nat) :
    0 < polynomialPartitionThreshold k := by
  unfold polynomialPartitionThreshold
  apply pow_pos
  unfold weylThreshold
  exact pow_pos (by norm_num) _

private lemma cor56Counter_threshold_lt_r {Q : Nat}
    (hQ : polynomialPartitionThreshold 1 < Q) :
    polynomialPartitionThreshold 1 < cor56CounterR Q := by
  have hqOne : 1 ≤ Q := by
    have := polynomialPartitionThreshold_pos 1
    omega
  have hqPow : Q ≤ Q ^ 16 := by
    simpa only [pow_one] using
      pow_le_pow_right₀ hqOne (by norm_num : (1 : Nat) ≤ 16)
  exact hQ.trans_le hqPow

private lemma cor56Counter_m_le_r {Q : Nat} (hQ : 1 ≤ Q) :
    cor56CounterM Q ≤ cor56CounterR Q := by
  unfold cor56CounterM cor56CounterR
  exact pow_le_pow_right₀ hQ (by norm_num)

private lemma cor56Counter_scale_lower {Q : Nat} (hQ : 0 < Q) :
    (cor56CounterR Q : Real) ^
        (1 - (polynomialPartitionConstant 1 : Real)⁻¹) ≤ cor56CounterM Q := by
  rw [cor56Counter_constant]
  unfold cor56CounterR cor56CounterM
  push_cast
  have hq : (0 : Real) ≤ Q := by positivity
  rw [← Real.rpow_natCast, ← Real.rpow_mul hq]
  norm_num [Real.rpow_natCast]

private lemma cor56Counter_scale_lt_one {Q : Nat} (hQ : 2 < Q) :
    (cor56CounterR Q : Real) ^
        (-(polynomialPartitionConstant 1 : Real)⁻¹) * 2 < 1 := by
  rw [cor56Counter_constant]
  unfold cor56CounterR
  push_cast
  have hq : (0 : Real) ≤ Q := by positivity
  rw [← Real.rpow_natCast, ← Real.rpow_mul hq]
  have hmul : ((16 : Nat) : Real) * (-(16 : Real)⁻¹) = -1 := by norm_num
  rw [hmul, Real.rpow_neg_one]
  have hqpos : (0 : Real) < Q := by positivity
  have hqreal : (2 : Real) < Q := by exact_mod_cast hQ
  simpa [div_eq_mul_inv, mul_comm] using (div_lt_one hqpos).2 hqreal

private lemma diameterAtMostReal_subsingleton_of_lt_one {N : Nat}
    {A : Finset (ZMod N)} {s : Real} (hA : diameterAtMostReal A s) (hs : s < 1)
    {x y : ZMod N} (hx : x ∈ A) (hy : y ∈ A) : x = y := by
  obtain ⟨d, ⟨a, ha⟩, hd⟩ := hA
  have hdReal : (d : Real) < 1 := hd.trans_lt hs
  have hdNat : d < 1 := by exact_mod_cast hdReal
  have hdZero : d = 0 := by omega
  subst d
  have hxa : x ∈ ({a} : Finset (ZMod N)) := by
    rw [← modInterval_one_carrier]
    exact ha hx
  have hya : y ∈ ({a} : Finset (ZMod N)) := by
    rw [← modInterval_one_carrier]
    exact ha hy
  exact (mem_singleton.mp hxa).trans (mem_singleton.mp hya).symm

private lemma identity_polynomialOn_zmod_two :
    PolynomialOn 1 Finset.univ (fun x : ZMod 2 => x) := by
  refine ⟨![0, 1], ?_⟩
  intro x _
  simp [Fin.sum_univ_two]

private lemma balanced_lengths_eq_average {m q : Nat} (f : Fin m → Nat)
    (hsum : ∑ i, f i = m * q) (hbalanced : ∀ i j, f i ≤ f j + 1) :
    ∀ i, f i = q := by
  intro i
  rcases lt_trichotomy (f i) q with hlt | heq | hgt
  · have hle : ∀ j ∈ (Finset.univ : Finset (Fin m)), f j ≤ q := by
      intro j _
      exact (hbalanced j i).trans (by omega)
    have hsums : ∑ j, f j = ∑ _j : Fin m, q := by
      simpa using hsum
    exact (sum_eq_sum_iff_of_le hle).mp hsums i (mem_univ i)
  · exact heq
  · have hle : ∀ j ∈ (Finset.univ : Finset (Fin m)), q ≤ f j := by
      intro j _
      have := hbalanced i j
      omega
    have hsums : ∑ _j : Fin m, q = ∑ j, f j := by
      simpa using hsum.symm
    exact ((sum_eq_sum_iff_of_le hle).mp hsums i (mem_univ i)).symm

private lemma isPartition_filter {X : Type*} [DecidableEq X] {m : Nat}
    {P : Fin m → Finset X} {S : Finset X} (hP : IsPartition P S)
    (p : X → Prop) [DecidablePred p] :
    IsPartition (fun i => (P i).filter p) (S.filter p) := by
  constructor
  · intro x
    constructor
    · intro hx
      obtain ⟨hxS, hpx⟩ := mem_filter.mp hx
      obtain ⟨i, hxi⟩ := (hP.1 x).mp hxS
      exact ⟨i, mem_filter.mpr ⟨hxi, hpx⟩⟩
    · rintro ⟨i, hxi⟩
      obtain ⟨hxiP, hpx⟩ := mem_filter.mp hxi
      exact mem_filter.mpr ⟨(hP.1 x).mpr ⟨i, hxiP⟩, hpx⟩
  · intro i j hij
    exact (hP.2 i j hij).mono (filter_subset p (P i)) (filter_subset p (P j))

private lemma card_filter_even_range : ∀ n : Nat,
    ((Finset.range n).filter Even).card = (n + 1) / 2 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [range_add_one, filter_insert]
      by_cases hn : Even n
      · rw [if_pos hn, card_insert_of_notMem]
        · rw [ih]
          obtain ⟨a, rfl⟩ := hn
          omega
        · simp
      · rw [if_neg hn, ih]
        obtain ⟨a, rfl⟩ := Nat.not_even_iff_odd.mp hn
        omega

private lemma cor56Counter_r_eq_m_mul_q (Q : Nat) :
    cor56CounterR Q = cor56CounterM Q * Q := by
  unfold cor56CounterR cor56CounterM
  rw [show 16 = 15 + 1 by norm_num, pow_succ]

private lemma exists_large_odd (T : Nat) (hT : 0 < T) :
    ∃ Q : Nat, 2 < Q ∧ Odd Q ∧ T < Q := by
  refine ⟨2 * T + 1, ?_, ⟨T, by omega⟩, ?_⟩ <;> omega

/-- The former exact-cell-count formulation of Corollary 5.6.  It is retained
only so that the concrete counterexample remains checkable after the live
Section 5 statement is repaired. -/
def corollary_5_6_exact_cell_legacy : Prop :=
  ∀ (N k r m : Nat) [NeZero N] (phi : ZMod N → ZMod N),
    1 ≤ k → PolynomialOn k Finset.univ phi →
    polynomialPartitionThreshold k < r →
    (r : Real) ^ (1 - (polynomialPartitionConstant k : Real)⁻¹) ≤ m → m ≤ r →
      ∃ P : Fin m → NatAP,
        IsNatAPPartition P (Finset.range r) ∧
        (∀ j, (P j).IsProper) ∧ NatAPLengthsDifferAtMostOne P ∧
        ∀ j, diameterAtMostReal
          ((P j).carrier.image fun x : Nat => phi (x : ZMod N))
          ((r : Real) ^ (-(polynomialPartitionConstant k : Real)⁻¹) * N)

/-- A parameterized counterexample to the exact-cell, balanced version of
Corollary 5.6.  Keeping `Q` abstract prevents Lean from evaluating the
doubly-exponential numerical threshold. -/
private theorem corollary_5_6_counterexample_of_Q (Q : Nat) (hQ : 2 < Q)
    (hQodd : Odd Q) (hthreshold : polynomialPartitionThreshold 1 < Q) :
    ¬ corollary_5_6_exact_cell_legacy := by
  intro h56
  unfold corollary_5_6_exact_cell_legacy at h56
  obtain ⟨P, hpartition, hproper, hbalanced, hdiameter⟩ :=
    h56 2 1 (cor56CounterR Q) (cor56CounterM Q) (fun x : ZMod 2 => x)
      (by norm_num) identity_polynomialOn_zmod_two
      (cor56Counter_threshold_lt_r hthreshold)
      (cor56Counter_scale_lower (by omega))
      (cor56Counter_m_le_r (by omega))
  have hsumLengths :
      ∑ j, (P j).length = cor56CounterR Q := by
    calc
      ∑ j, (P j).length = ∑ j, (P j).carrier.card := by
        apply sum_congr rfl
        intro j _
        exact (hproper j).2.symm
      _ = (Finset.range (cor56CounterR Q)).card := hpartition.sum_card
      _ = cor56CounterR Q := card_range _
  have hlength : ∀ j, (P j).length = Q := by
    apply balanced_lengths_eq_average (fun j => (P j).length)
    · exact hsumLengths.trans (cor56Counter_r_eq_m_mul_q Q)
    · exact hbalanced
  have hscale :
      (cor56CounterR Q : Real) ^
          (-(polynomialPartitionConstant 1 : Real)⁻¹) * 2 < 1 :=
    cor56Counter_scale_lt_one hQ
  have hsameCast (j : Fin (cor56CounterM Q)) {x y : Nat}
      (hx : x ∈ (P j).carrier) (hy : y ∈ (P j).carrier) :
      (x : ZMod 2) = (y : ZMod 2) := by
    apply diameterAtMostReal_subsingleton_of_lt_one (hdiameter j) hscale
    · exact mem_image.mpr ⟨x, hx, rfl⟩
    · exact mem_image.mpr ⟨y, hy, rfl⟩
  have hsameParity (j : Fin (cor56CounterM Q)) {x y : Nat}
      (hx : x ∈ (P j).carrier) (hy : y ∈ (P j).carrier) :
      Even x ↔ Even y := by
    have hxy := hsameCast j hx hy
    constructor
    · intro hxeven
      have hxzero : (x : ZMod 2) = 0 :=
        ZMod.natCast_eq_zero_iff_even.mpr hxeven
      exact ZMod.natCast_eq_zero_iff_even.mp (hxy.symm.trans hxzero)
    · intro hyeven
      have hyzero : (y : ZMod 2) = 0 :=
        ZMod.natCast_eq_zero_iff_even.mpr hyeven
      exact ZMod.natCast_eq_zero_iff_even.mp (hxy.trans hyzero)
  have hcellDvd (j : Fin (cor56CounterM Q)) :
      Q ∣ ((P j).carrier.filter Even).card := by
    by_cases hex : ∃ x ∈ (P j).carrier, Even x
    · obtain ⟨x, hx, hxeven⟩ := hex
      have hfilter : (P j).carrier.filter Even = (P j).carrier := by
        apply filter_eq_self.mpr
        intro y hy
        exact (hsameParity j hx hy).mp hxeven
      rw [hfilter, (hproper j).2, hlength j]
    · have hfilter : (P j).carrier.filter Even = ∅ := by
        apply filter_eq_empty_iff.mpr
        intro x hx hxeven
        exact hex ⟨x, hx, hxeven⟩
      rw [hfilter]
      simp
  have hevenPartition :
      IsPartition (fun j => (P j).carrier.filter Even)
        ((Finset.range (cor56CounterR Q)).filter Even) :=
    isPartition_filter hpartition Even
  have hglobalDvd :
      Q ∣ ((Finset.range (cor56CounterR Q)).filter Even).card := by
    rw [← hevenPartition.sum_card]
    exact Finset.dvd_sum fun j _ => hcellDvd j
  rw [card_filter_even_range] at hglobalDvd
  have hrOdd : Odd (cor56CounterR Q) := hQodd.pow
  have hrSuccEven : Even (cor56CounterR Q + 1) := hrOdd.add_one
  have hQdvdSucc : Q ∣ cor56CounterR Q + 1 := by
    have hmul := hglobalDvd.mul_right 2
    rwa [Nat.div_two_mul_two_of_even hrSuccEven] at hmul
  have hQdvdR : Q ∣ cor56CounterR Q := by
    unfold cor56CounterR
    exact dvd_pow_self Q (by norm_num)
  have hQdvdOne : Q ∣ 1 := by
    simpa using Nat.dvd_sub hQdvdSucc hQdvdR
  have hQone : Q = 1 := Nat.dvd_one.mp hQdvdOne
  omega

/-- The former exact-cell statement of Corollary 5.6 is false.  The
obstruction already occurs for a linear polynomial modulo two. -/
theorem corollary_5_6_exact_partition_counterexample :
    ¬ corollary_5_6_exact_cell_legacy := by
  obtain ⟨Q, hQ, hQodd, hthreshold⟩ :=
    exists_large_odd (polynomialPartitionThreshold 1)
      (polynomialPartitionThreshold_pos 1)
  exact corollary_5_6_counterexample_of_Q Q hQ hQodd hthreshold

end LeanProofs.GowersSzemeredi
