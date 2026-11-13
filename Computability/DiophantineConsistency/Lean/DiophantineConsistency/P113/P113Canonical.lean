import DiophantineConsistency.P138.P138Canonical
import DiophantineConsistency.P113.P113Cone

/-! # Canonical data for the completeness of package 113: the strict cones

`canonical_strict` is `P138Canonical.canonical`, re-run verbatim (the record `Canonical V` is
package 138's), with one more conclusion: the canonical cone registers are strictly below `q`,

    2^1113 F < q,    C 2^666104 < q,

by `P113Cone.strict_cones` on the fine cell window (`P113Cone.fine_cells_of_word`, from the same
`Source34Word.halt_packed_word` cells as `P138Cone.cones`). The record only stores package 138's
calibration `q ≤ 2·2^1113 F ≤ 3q`, `q ≤ 2 C 2^666104 ≤ 3q`; package 113's guard `G > 0` needs the
strict upper bounds (`P113Complete.guard_pos`). The construction is copied rather than extended in
place so that package 138's accepted record and its dependents are untouched; the copy is
generated from `P138Canonical.lean` with exactly these two edits. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
noncomputable section
namespace DiophantineConsistency.P113Canonical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing ZRowsCoprimeSquares P138Value P138Ports P138Bootstrap P138Canonical
open ArithmeticPow ArithmeticPacking ArithmeticRepunit ArithmeticPellRecurrence ArithmeticOuterSeed
  ArithmeticBinaryPopulation ArithmeticBinomLegendre ArithmeticHalfBinomial ArithmeticBinomFactorial
open Mixed121Kernel (rho)
open Source34Kernel Source34ConstructedRank Source34Word Source34Seeds
open Mixed121Word (haltRow haltLength haltStride)
open Mixed121Column (perturb perturb_definable)
open P72ConvArith (exp_odd_mod_three)
open P72Root (ι_tsub)
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC

attribute [local irreducible] paramKernel rho Source34Ports.lowNat Source34Ports.highNat
  Source34Ports.betaNat coneA coneB

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- **C1 with the strict cones.** An internal halt gives the canonical data of package 138, with
`2^1113 F < q` and `C 2^666104 < q`. -/
theorem canonical_strict (T : V) (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0) :
    ∃ Cn : Canonical V, Exp.exp 1113 * Cn.F < Cn.q ∧ Cn.C * Exp.exp 666104 < Cn.q := by
  obtain ⟨δ, hδd, hbool, _, hpack, hx, hresult⟩ := halt_first_gamma T hT
  letI : 𝚺₁-Function₁ δ := hδd
  have hword := (halt_packed_word T δ hT).2.1
  let Xf := perturb (baseCell (haltRow T)) δ
  letI : 𝚺₁-Function₁ Xf := hx
  let N := haltLength T
  let stride := haltStride T
  let K : V := paramKernel rho
  let u : V := 1064921 * N
  let R := rank K N stride Xf
  let q := Exp.exp u
  let wX := Exp.exp (R - u)
  obtain ⟨_, z, hz, hqw, htrv, sY, n, eta, zeta, gammaOld, hsY, _, he, hzz, _,
    hseed, _, _, _, _⟩ := hresult
  have hp : PackingInput 1064921 K low high N stride Xf := hpack
  obtain ⟨hpop, hR4, hR2u⟩ := properties hp
  -- the packing coordinates
  let Cv := Cw 1064921 N Xf
  let Fv := Fw 1064921 K N stride Xf
  let αv := alpha 1064921 K N stride Xf
  have hF : 0 < Fv := F_pos hp
  have hC : 0 < Cv := C_pos hp
  obtain ⟨hα, hsum⟩ := packing_alpha hp
  have hqsum : q = Fv + (Cv + αv) := by
    have h : q = Cv + Fv + αv := hsum.symm
    rw [h]; ring
  let J := rep 1064921 N
  have hq1 : 1 ≤ q := one_le_exp _
  have hqJ' : (Exp.exp (1064921 : V) - 1) * J + 1 = q := repunit_identity 1064921 N
  dsimp only [SeedRelations] at hseed
  obtain ⟨hτn, hdn, hcy, hdx, r', hRr, hτx, hkB⟩ := hseed
  replace hRr : R = 2 * r' + 1 := hRr
  let Xv : V := Exp.exp R
  let Y : V := sY * q ^ 3
  let E : V := Xv * Y
  let k : V := eta + zeta
  let c : V := k * Y + eta
  let a : V := E + Y
  let τ : V := E * n + k - R
  let B : V := 2 * (E * Y - 1) + 1
  let d : V := Xv + a * c + gammaOld * (4 * a + 3)
  have hτn' : τ * τ = 1 + (E * Y) * (E * Y + 1) * k * k := hτn
  have hcy' : c = ycoord R a := hcy
  have hdx' : d = xcoord R a := hdx
  have hdn' : d * d = 1 + (a + 1) * (a + 3) * c * c := hdn
  have hkB' : k = 2 * ycoord (r' + 1) B := hkB
  have hτx' : τ = xcoord (r' + 1) B := hτx
  -- sizes
  have hN0 : 0 < N := power_pos _ _ (by norm_num)
  have hN1 : 1 ≤ N := pos_iff_one_le.mp hN0
  have hu0 : (1064921 : V) ≤ u := le_mul_of_one_le_right (Arithmetic.zero_le _) hN1
  have hq16 : 16 ≤ q := by
    have h := exp_monotone_le.mpr (le_trans (by norm_num : (4 : V) ≤ 1064921) hu0)
    have e4 : Exp.exp (4 : V) = 16 := by
      rw [show (4 : V) = 0 + 1 + 1 + 1 + 1 by norm_num, exp_succ, exp_succ, exp_succ, exp_succ,
        exp_zero]
      norm_num
    rwa [e4] at h
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq16
  have hq3c : 1 ≤ q ^ 3 := one_le_pow₀ hq1
  have hY0 : 0 < Y := mul_pos hsY (lt_of_lt_of_le (by norm_num) hq3c)
  have hY1 : 1 ≤ Y := pos_iff_one_le.mp hY0
  have hXv1 : 1 ≤ Xv := one_le_exp _
  have hE1 : 1 ≤ E := one_le_mul_of_one_le_of_one_le hXv1 hY1
  have hEY1 : 1 ≤ E * Y := one_le_mul_of_one_le_of_one_le hE1 hY1
  have hr6 : 6 ≤ r' := by
    by_contra hlt
    have h1 : 2 * r' + 1 < 2 * 6 + 1 :=
      (add_lt_add_iff_right 1).mpr (mul_lt_mul_of_pos_left (not_le.mp hlt) (by norm_num))
    have h2 : (2 * 6 + 1 : V) ≤ 2 * u := le_trans (by norm_num)
      (mul_le_mul_of_nonneg_left hu0 (by norm_num))
    have : R < R := by
      calc R = 2 * r' + 1 := hRr
        _ < 2 * 6 + 1 := h1
        _ ≤ 2 * u := h2
        _ < R := hR2u
    exact _root_.lt_irrefl _ this
  have hr1 : 1 ≤ r' := le_trans (by norm_num) hr6
  have hk4 : 4 * (B + 2) ≤ k := P72ConvArith.k_large r' B k hr1 hkB'
  have hB2 : B + 2 = 2 * (E * Y) + 1 := by
    show 2 * (E * Y - 1) + 1 + 2 = 2 * (E * Y) + 1
    have := tsub_add_cancel_of_le hEY1
    calc 2 * (E * Y - 1) + 1 + 2 = 2 * (E * Y - 1 + 1) + 1 := by ring
      _ = 2 * (E * Y) + 1 := by rw [this]
  -- k = R + 1 + 4EYs'
  have hB1 : 2 * (E * Y) ∣ B + 1 := ⟨1, by
    have : B + 1 + 1 = 2 * (E * Y) + 1 := by rw [← hB2]; ring
    rw [mul_one]; exact add_right_cancel this⟩
  obtain ⟨_, s', _, hys⟩ := ArithmeticPellCongruences.residue_quotients (r' + 1) B (2 * (E * Y)) hB1
  have hk2 : k = R + 1 + 4 * (E * Y) * s' := by rw [hkB', hys, hRr]; ring
  have hs'1 : 1 ≤ s' := by
    rcases (Arithmetic.zero_le s').lt_or_eq with h | h
    · exact pos_iff_one_le.mp h
    · exfalso
      rw [← h, mul_zero, add_zero] at hk2
      have hRE : R < E * Y := lt_of_lt_of_le (lt_exp R) (le_trans (le_mul_of_one_le_right
        (Arithmetic.zero_le _) hY1) (le_mul_of_one_le_right (Arithmetic.zero_le _) hY1))
      have : R + 1 < 4 * (B + 2) := by
        rw [hB2]
        calc R + 1 < E * Y + 1 := (add_lt_add_iff_right 1).mpr hRE
          _ ≤ 4 * (2 * (E * Y) + 1) := by
            rw [show (4 : V) * (2 * (E * Y) + 1) = (E * Y + 1) + (7 * (E * Y) + 3) by ring]
            exact le_add_of_nonneg_right (Arithmetic.zero_le _)
      exact absurd (le_trans hk4 (le_of_eq hk2)) (not_le_of_gt this)
  -- N odd, u odd
  obtain ⟨nN, hnN⟩ := power_odd (V := V) ((2 * T + 3) + 1)
  have hNodd : N = 2 * nN + 1 := hnN
  have hu_odd : u = 2 * (1064921 * nN + 532460) + 1 := by
    show 1064921 * N = _
    rw [hNodd]; ring
  -- J ≡ 1 (mod 6)
  have hq3 : q % 3 = 2 := by show Exp.exp u % 3 = 2; rw [hu_odd]; exact exp_odd_mod_three _
  have hqeven : q = 2 * Exp.exp (2 * (1064921 * nN + 532460)) := by
    show Exp.exp u = _; rw [hu_odd, exp_succ]
  have hqreg : ι q = portsR 0 * ι J + 1 := by
    rw [port0, ← map_mul, ← map_one ι, ← map_add, hqJ']
  obtain ⟨jj, hjj⟩ : ∃ jj : V, J = 6 * jj + 1 := by
    obtain ⟨mb, hmb⟩ := (portFacts (V := V)).beta_mod
    have h1 := congrArg (ι (V := V)) hqeven
    have h2 := congrArg (ι (V := V)) (div_add_mod q 3).symm
    rw [hq3] at h2
    simp only [map_add, map_mul, map_ofNat] at h1 h2
    have hq' := hqreg
    rw [hmb] at hq'
    refine affine_nat 6 1 (by norm_num) (t := ι (Exp.exp (2 * (1064921 * nN + 532460))) -
      ι (q / 3) - 1 - mb * ι J) ?_
    rw [map_ofNat, map_one]
    linear_combination 3 * h1 - 2 * h2 - hq'
  -- W ≡ 4 (mod 12)
  set mu : V := 1064921 * nN + 532460 with hmu
  have hrmu : mu + 1 ≤ r' := by
    by_contra hlt
    have h1 : r' ≤ mu := lt_succ_iff_le.mp (not_le.mp hlt)
    have : R < R := by
      calc R = 2 * r' + 1 := hRr
        _ ≤ 2 * mu + 1 := (add_le_add_iff_right 1).mpr (mul_le_mul_of_nonneg_left h1 (by norm_num))
        _ ≤ 2 * (2 * mu + 1) := by
            rw [show 2 * (2 * mu + 1) = (2 * mu + 1) + (2 * mu + 1) by ring]
            exact le_add_of_nonneg_right (Arithmetic.zero_le _)
        _ = 2 * u := by rw [hu_odd]
        _ < R := hR2u
    exact _root_.lt_irrefl _ this
  obtain ⟨e, he_def⟩ : ∃ e, r' = mu + 1 + e := ⟨r' - (mu + 1), (add_tsub_cancel_of_le hrmu).symm⟩
  have hRu : R - u = 2 * e + 2 := by
    apply tsub_eq_of_eq_add
    rw [hRr, he_def, hu_odd]; ring
  have hwX : wX = 4 * Exp.exp (2 * e) := by
    show Exp.exp (R - u) = _
    rw [hRu, show 2 * e + 2 = 2 * e + 1 + 1 by ring, exp_succ, exp_succ]; ring
  obtain ⟨ww, hww⟩ : ∃ ww : V, wX = 12 * ww + 4 := by
    have h3 := exp_odd_mod_three (V := V) e
    have hd := (div_add_mod (Exp.exp (2 * e + 1)) 3).symm
    rw [h3] at hd
    have he1 : Exp.exp (2 * e + 1) = 2 * Exp.exp (2 * e) := exp_succ _
    have h1 := congrArg (ι (V := V)) hwX
    have h2 := congrArg (ι (V := V)) hd
    have h3' := congrArg (ι (V := V)) he1
    simp only [map_add, map_mul, map_ofNat] at h1 h2 h3'
    refine affine_nat 12 4 (by norm_num) (t := 2 * ι (Exp.exp (2 * e + 1) / 3) + 1 -
      ι (Exp.exp (2 * e))) ?_
    rw [map_ofNat, map_ofNat]
    linear_combination h1 + 8 * h2 - 8 * h3'
  -- sY odd
  have hpr : population r' = 3 * u + 1 := by
    show population r' = 3 * (1064921 * N) + 1
    have h : population R = 3 * (1064921 * N) + 2 := hpop
    rw [hRr, population_odd] at h
    exact add_right_cancel (h.trans (by ring))
  have hXr : Xv = Exp.exp (2 * r' + 1) := by show Exp.exp R = _; rw [hRr]
  have hck : ycoord (2 * r' + 1) (Y * (Xv + 1)) =
      2 * ycoord (r' + 1) (2 * (Xv * Y * Y - 1) + 1) * Y + eta := by
    rw [← hRr, show Y * (Xv + 1) = a by show _ = Xv * Y + Y; ring, ← hcy']
    show k * Y + eta = 2 * ycoord (r' + 1) B * Y + eta
    rw [← hkB']
  have hk' : 2 * ycoord (r' + 1) (2 * (Xv * Y * Y - 1) + 1) = eta + zeta := hkB'.symm
  obtain ⟨vv, hvv⟩ : ∃ vv : V, sY = 2 * vv + 1 := by
    obtain ⟨t, ht | ht⟩ := even_or_odd sY
    · exfalso
      obtain ⟨w', hw'⟩ := half_binomial Xv Y r' eta zeta (le_trans (by norm_num) hr6) hXr hY1
        hck hk' he hzz
      have hq3e : q ^ 3 = Exp.exp (3 * u) := by
        show Exp.exp u ^ 3 = _
        rw [show 3 * u = u + u + u by ring, exp_add, exp_add]; ring
      have hd1 : Exp.exp (3 * u + 2) ∣ 2 * Y := ⟨t, by
        show 2 * (sY * q ^ 3) = _
        rw [ht, hq3e, show 3 * u + 2 = 3 * u + 1 + 1 by ring, exp_succ, exp_succ]; ring⟩
      have hpopR : 3 * u + 2 ≤ R := by
        have := le_trans (population_le R).1 (population_le R).2
        rwa [show population R = 3 * u + 2 from hpop] at this
      have hd2 : Exp.exp (3 * u + 2) ∣ w' * Xv :=
        dvd_mul_of_dvd_right (by rw [hXr, ← hRr]; exact exp_dvd_exp_of_le' hpopR) _
      rw [hw'] at hd1
      have hd3 := dvd_of_dvd_add hd1 hd2
      have := le_population_of_exp_dvd_central r' (3 * u + 2) hd3
      rw [hpr] at this
      exact absurd this (not_le.mpr (by
        rw [show 3 * u + 2 = 3 * u + 1 + 1 by ring]; exact lt_add_one _))
    · exact ⟨t, ht⟩
  -- the main ordinate modulo four
  obtain ⟨cm, hcm⟩ : ∃ cm : V, c = 4 * cm + 3 := by
    have hR := (div_add_mod R 4).symm
    rw [show R % 4 = 3 from hR4] at hR
    rw [hcy', hR]
    exact ycoord_mod_four _ _
  -- 4 η < k
  have hquarter : 4 * eta < k :=
    P138Quarter.eta_quarter' Xv Y r' k eta hr6 hXr hY1
      (by rw [← hRr, show Y * (Xv + 1) = a by show _ = Xv * Y + Y; ring, ← hcy'])
      hkB' he (lt_add_of_pos_right _ hzz)
  -- cones
  obtain ⟨hc1, hc2, hc3, hc4⟩ := P138Cone.cones (N := N) (s := stride) (X := Xf) hN0
    (P138Cone.cells_of_word (haltRow T) δ N hword.tile_ne hbool)
  obtain ⟨hs1, hs2⟩ := P113Cone.strict_cones (N := N) (s := stride) (X := Xf) hN0
    (P113Cone.fine_cells_of_word (haltRow T) δ N hword.tile_ne hbool)
  -- the rank in the ring of differences
  have hFq : Fv ≤ q := le_of_lt (lt_of_lt_of_le (F_lt_M hp) tsub_le_self)
  have hq2' : 1 ≤ q ^ 2 := one_le_pow₀ hq1
  have hRR : ι R = (ι q * (ι q - ι Fv) - ι Cv) * (ι q ^ 2 - 1) +
      (portsR 2 + ι q * portsR 3) * ι J := by
    rw [port2, port3]
    have h0 : ι R = ι (((q-1)*(q-Fv)+αv)*(q^2-1) + ((low:V)+q*(high+(Exp.exp (1064921:V)-1)))*J) :=
      rfl
    have hιq : ι q = ι Fv + (ι Cv + ι αv) := by rw [hqsum]; simp only [map_add]
    rw [h0]
    simp only [map_add, map_mul, ι_tsub hq1, ι_tsub hFq, ι_tsub hq2', map_one, map_pow]
    linear_combination (1 - ι q ^ 2) * hιq
  -- H ∣ K
  have hK : ι Xv * (3 * ι c - 2 * ι Xv) + 2 = (4 * ι a + 3) *
      (ι Xv * ι c - 2 * ι c ^ 2 + 2 * ι gammaOld * (ι d + ι Xv + ι a * ι c)) := by
    have hd1 : ι d = ι Xv + ι a * ι c + ι gammaOld * (4 * ι a + 3) := by
      show ι (Xv + a * c + gammaOld * (4 * a + 3)) = _
      simp only [map_add, map_mul, map_ofNat]
    have hd2 := congrArg (ι (V := V)) hdn'
    simp only [map_add, map_mul, map_one, map_ofNat] at hd2
    linear_combination (-2) * hd2 + (2 * (ι d + ι Xv + ι a * ι c)) * hd1
  -- the transport, in the ring of differences
  have hFreg : ι Fv = (portsR 1 + ι wX) * ι Cv - ι z * (ι q - 1) := by
    have h := congrArg ι htrv
    simp only [map_add, map_mul] at h
    rw [ι_tsub hq1, map_one] at h
    have e1 : portsR (V := V) 1 = ι K := port1
    rw [e1]
    linear_combination -h
  exact ⟨{
    j := jj, C := Cv, z := z, h := 4 * Y * s', v := vv, w := ww, c := c,
    J := J, q := q, W := wX, X := Xv, Y := Y, E := E, a := a, F := Fv, α := αv, R := R, r := r',
    k := k, η := eta, ζ := zeta, τ := τ, d := d, γ := gammaOld,
    κ := ι Xv * ι c - 2 * ι c ^ 2 + 2 * ι gammaOld * (ι d + ι Xv + ι a * ι c),
    J_eq := hjj, q_reg := hqreg, q_ge := hq16, W_eq := hww, X_eq := hqw.symm, X_exp := rfl,
    Y_eq := by show sY * q ^ 3 = _; rw [hvv],
    E_eq := rfl, a_eq := rfl, F_reg := hFreg, q_split := hqsum, F_pos := hF, C_pos := hC,
    α_pos := hα, z_pos := hz, R_reg := hRR, R_odd := hRr,
    R_mod := ⟨R / 4, by
      have hR := (div_add_mod R 4).symm
      rwa [show R % 4 = 3 from hR4] at hR⟩,
    r_ge := hr6, k_eq := by rw [hk2]; ring,
    h_pos := mul_pos (mul_pos (by norm_num) hY0) (lt_of_lt_of_le (by norm_num) hs'1),
    k_first := hkB', τ_first := hτx', τ_norm := hτn', c_main := hcy', d_main := hdx',
    d_norm := hdn', d_split := rfl, c_mod := ⟨cm, hcm⟩, c_eta := rfl, k_split := rfl,
    η_pos := he, ζ_pos := hzz, eta_quarter := hquarter, K_split := hK,
    cone_F := ⟨hc1, hc2⟩, cone_C := ⟨hc3, hc4⟩ }, hs1, hs2⟩

#print axioms canonical_strict

end DiophantineConsistency.P113Canonical
