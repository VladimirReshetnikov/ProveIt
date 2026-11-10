import DiophantineConsistency.Mixed121.Short15ConvZero
import DiophantineConsistency.Compact44.C44Short15Facts
import DiophantineConsistency.Compact44.P72Converse

/-! # Fifteen-positive converse: the canonical compact44 halt data

The compact44 counterpart of `Short15ConvData.canonical`. From the canonical
halt data (`CompactHaltFirstGamma.halt_first_gamma`, extracted as in
`P64Converse`), `canonical` gives the witnesses common to the fifteen-positive
forms: `J = rep N`, `F = Fw`, `α = alpha`, `z + 1`, `f`, `h = 4Ys'`, `s = sY`,
`w = 2^(R−u)`, `η`, `ζ`, `γ = γold`, and the halt's `i`, `T`, `τ`, `y` and
auxiliary ordinate `wa < y`. At every valuation `W` that reads these eleven
coordinates, it gives `Nt = Nk = N1 = 1`, `N0 = 1` at `τ`, the normalized strong
norm `f² − Δ(ic²)² = 1`, the auxiliary ordinate `f²(cT − R) − c = wa`, and the
auxiliary norm `Aaux(wa² − y²) + y² = 1`, all at the compact44 ports.

For the integral-root forms of package 66 it also gives:

* `ℓ + s < τ` (as in `P64Converse`, from `3s ≤ k` and `s ≤ ℓ`);
* `w < γ`: the main root `D = X + ac + γH` exceeds `(a + 1)c`, and
  `c = y_R(a) ≥ y_3(a) ≥ 2(a + 2)² ≥ X(4a + 4)` since `Y ≥ 3`; with `w ≤ X`,
  `γ ≤ w` would give `D ≤ X + ac + XH < (a + 1)c`;
* `J = 3j + 1` with `0 < j` (as in `P65Converse`);
* `z = z₀ + 1` with `0 < z₀`, the halt data's transport quotient. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section
namespace C44Short15ConvData
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 ModelDifferenceRing Ordinary12FreeJ
open ArithmeticPow ArithmeticPacking ArithmeticRepunit ArithmeticPellRecurrence ArithmeticOuterSeed
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts
open CompactWordLowFields CompactCanonicalPerturbation CompactHaltPackedWord
open CompactConstructedRank CompactRankResidueJoin CompactHaltFirstSeed CompactHaltFirstPositive
open CompactHaltFirstGamma CompactPositiveValuation CompactAuxOrdinateOrder
open FreeJAdaptiveLift FreeJModelRankBinding FreeJModelZeroJoin
open Short15Graph P72ConvArith
open C44Short15Facts (c44 intPorts)
open P72Root (ι_tsub)
open P72Converse (rankExpr_eval)
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
attribute [local irreducible] paramKernel rho highNat CompactFixedBeta.betaNat lowNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem aux_gt {I w y : DiffRing V} (h : I * I * w * w + y * y = 1 + I * I * y * y)
    (hy : 2 ≤ y) (hw : 0 ≤ w) : w < y := by
  by_contra hlt
  have hle : y ≤ w := le_of_not_gt hlt
  have h1 : I * I * y * y ≤ I * I * w * w := by
    have := mul_le_mul hle hle (by linarith) hw
    nlinarith [mul_self_nonneg I]
  nlinarith

private theorem tau_gt {τ ell k s : DiffRing V} (hτ : τ * τ = 1 + ell * (ell + k)) (hτ0 : 0 ≤ τ)
    (hk : 3 * s ≤ k) (hs : s ≤ ell) (hs0 : 0 ≤ s) : ell + s < τ := by
  by_contra hlt
  have hle : τ ≤ ell + s := le_of_not_gt hlt
  have hl0 : 0 ≤ ell := le_trans hs0 hs
  have h1 : τ * τ ≤ (ell + s) * (ell + s) := mul_le_mul hle hle hτ0 (by linarith)
  nlinarith

/-- `y_3(a) ≥ 2(a + 2)²`. -/
theorem y_three (a : V) : 2 * (a + 2) * (a + 2) ≤ ycoord 3 a := by
  have e1 : ycoord 1 a = 1 := by
    have h := y_succ (0 : V) a; rw [zero_add] at h; rw [h]; simp
  have ex1 : xcoord 1 a = a + 2 := by
    have h := x_succ (0 : V) a; rw [zero_add] at h; rw [h]; simp
  have e2 : ycoord 2 a = 2 * (a + 2) := by
    have h := y_succ (1 : V) a; rw [show (1 : V) + 1 = 2 by norm_num] at h; rw [h, e1, ex1]; ring
  have h := y_succ (2 : V) a
  rw [show (2 : V) + 1 = 3 by norm_num] at h
  rw [h, e2]
  calc 2 * (a + 2) * (a + 2) = (a + 2) * (2 * (a + 2)) := by ring
    _ ≤ xcoord 2 a + (a + 2) * (2 * (a + 2)) := le_add_of_nonneg_left (Arithmetic.zero_le _)

/-- The main ordinate `γ` exceeds `w` once `c ≥ 2(a + 2)²`, `a = xY + Y`, `Y ≥ 3` and `w ≤ x`. -/
theorem gamma_gt {x A C G W Y : DiffRing V}
    (hD : (x + A * C + G * (4 * A + 3)) * (x + A * C + G * (4 * A + 3)) = (A * A + (4 * A + 3)) * (C * C) + 1)
    (hA : A = x * Y + Y) (hC : 2 * (A + 2) * (A + 2) ≤ C) (hY : 3 ≤ Y) (hx : 0 ≤ x) (hW : W ≤ x)
    (hG : 0 ≤ G) : W < G := by
  by_contra hle
  have hGW : G ≤ W := le_of_not_gt hle
  have hA0 : 0 ≤ A := by rw [hA]; nlinarith
  have hAx : x ≤ A := by rw [hA]; nlinarith
  have hA3 : 3 * (x + 1) ≤ A := by rw [hA]; nlinarith
  have hC0 : 0 ≤ C := le_trans (by nlinarith) hC
  set D : DiffRing V := x + A * C + G * (4 * A + 3) with hDdef
  have hD0 : 0 ≤ D := by
    have : 0 ≤ A * C := mul_nonneg hA0 hC0
    have : 0 ≤ G * (4 * A + 3) := mul_nonneg hG (by linarith)
    linarith
  -- D > (a + 1)c
  have h1 : (A + 1) * C < D := by
    by_contra hle'
    have hle2 : D ≤ (A + 1) * C := le_of_not_gt hle'
    have h2 : D * D ≤ ((A + 1) * C) * ((A + 1) * C) :=
      mul_le_mul hle2 hle2 hD0 (mul_nonneg (by linarith) hC0)
    have h3 : 0 ≤ (2 * A + 2) * (C * C) := mul_nonneg (by linarith) (mul_self_nonneg C)
    nlinarith
  -- D ≤ x + ac + xH
  have h4 : D ≤ x + A * C + x * (4 * A + 3) := by
    have : G * (4 * A + 3) ≤ x * (4 * A + 3) :=
      mul_le_mul_of_nonneg_right (le_trans hGW hW) (by linarith)
    linarith
  -- C ≥ x(4a + 4)
  have h5 : x * (4 * A + 4) ≤ C := by
    have e1 : 2 * A * (3 * (x + 1)) ≤ 2 * A * A := mul_le_mul_of_nonneg_left hA3 (by linarith)
    have e2 : 4 * x ≤ 6 * A := by linarith
    have e3 : 0 ≤ 2 * A * x := by nlinarith
    nlinarith
  nlinarith

theorem canonical (T : V) (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0) :
    ∃ J F α z f h iH TH s w τ η ζ y wa γ ellM ΔM : V,
      0 < J ∧ 0 < F ∧ 0 < α ∧ 0 < z ∧ 0 < f ∧ 0 < h ∧ 0 < iH ∧ 0 < TH ∧ 0 < s ∧ 0 < w ∧
      0 < τ ∧ 0 < η ∧ 0 < ζ ∧ 0 < y ∧ wa < y ∧ 0 < γ ∧ 0 < ΔM ∧ ellM < τ ∧
      ellM + s < τ ∧ w < γ ∧ (∃ j : V, 0 < j ∧ J = 3 * j + 1) ∧ (∃ z0 : V, 0 < z0 ∧ z = z0 + 1) ∧
      ∀ W : Fin 15 → DiffRing V, W 0 = ι J → W 1 = ι F → W 2 = ι α → W 3 = ι z → W 4 = ι f →
        W 5 = ι h → W 8 = ι s → W 9 = ι w → W 11 = ι η → W 12 = ι ζ → W 14 = ι γ →
        (vals intPorts W).ell = ι ellM ∧ (vals intPorts W).Delta = ι ΔM ∧
        rNt intPorts W = 1 ∧ rNk intPorts W = 1 ∧ rN1 intPorts W = 1 ∧ rN0 intPorts W (ι τ) = 1 ∧
        W 4 * W 4 - (vals intPorts W).Delta * ((ι iH * ((vals intPorts W).c * (vals intPorts W).c)) *
          (ι iH * ((vals intPorts W).c * (vals intPorts W).c))) = 1 ∧
        W 4 * W 4 * ((vals intPorts W).c * ι TH - (vals intPorts W).RR) - (vals intPorts W).c = ι wa ∧
        rNa (vals intPorts W).Aaux (ι wa) (ι y) = 1 := by
  obtain ⟨δ, _, _, _, hpack, hx, hresult⟩ := halt_first_gamma T hT
  let Xf := perturb (baseCell (haltRow T)) δ
  letI : 𝚺₁-Function₁ Xf := hx
  let N := haltLength T
  let stride := haltStride T
  let K : V := paramKernel rho
  let u : V := 590069 * N
  let R := rank K N stride Xf
  let q := Exp.exp u
  let wX := Exp.exp (R - u)
  obtain ⟨_, z, hz, hqw, htrv, sY, n, eta, zeta, gammaOld, hsY, _, he, hzz, hγ,
    hseed, _, haux, _, hgam⟩ := hresult
  obtain ⟨f, i, auxT, auxw, y, hf, hi, hTaux, _, hy, hfx, hyic, hstrong,
    hydef, _, _, _, _, hlit, _, hauxnorm, _, _, _, _, hnorm⟩ := haux
  obtain ⟨t, _, _, hk, _⟩ := hgam
  have hp : PackingInput 590069 K low high N stride Xf := by
    simpa only [Xf, N, stride, K, low, high, highNat] using hpack
  -- the packing coordinates
  let Cv := Cw 590069 N Xf
  let Fv := Fw 590069 K N stride Xf
  let αv := alpha 590069 K N stride Xf
  have hF : 0 < Fv := F_pos hp
  obtain ⟨hα, hsum⟩ := packing_alpha hp
  have hqsum : q = Fv + (Cv + αv) := by
    have h : q = Cv + Fv + αv := hsum.symm
    rw [h]; ring
  -- q = 1 + Jβ and J ≡ 1 (mod 3)
  let J := rep 590069 N
  let β : V := CompactFixedBeta.betaNat
  have hbetaD : ι J * ι β = ι (q - 1) := by
    have h := CompactSymbolicBetaCast.beta_product (V := V) N
    rw [Int.cast_natCast, ← map_natCast ι CompactFixedBeta.betaNat] at h
    exact h
  have hq1 : 1 ≤ q := one_le_exp _
  have hqJ : q = 1 + J * β := by
    have h : ι (J * β) = ι (q - 1) := by rw [map_mul]; exact hbetaD
    have h2 := ι_injective h
    rw [h2, add_tsub_cancel_of_le hq1]
  obtain ⟨b3, hb3⟩ := P72Mu.beta_cast_mod β rfl
  have hNodd : ∃ a : V, N = 2 * a + 1 :=
    odd_of_mod_two (ArithmeticControllerChoiceCompact44Triangle.power_p_odd _)
  obtain ⟨aN, haN⟩ := hNodd
  have hq3 : q % 3 = 2 := by
    show Exp.exp (590069 * N) % 3 = 2
    rw [haN, show (590069 : V) * (2 * aN + 1) = 2 * (590069 * aN + 295034) + 1 by ring]
    exact exp_odd_mod_three _
  obtain ⟨j, hj⟩ := J_mod_three q J β b3 hqJ hb3 hq3
  dsimp only [SeedRelations] at hseed
  obtain ⟨hτn, hdn, hcy, _, r', hRr, _, hkB⟩ := hseed
  -- the registers
  let Xv : V := Exp.exp R
  let Y : V := sY * q ^ 3
  let E : V := Xv * Y
  let k : V := eta + zeta
  let c : V := k * Y + eta
  let a : V := E + Y
  let ell : V := E * Y * k
  let τ : V := E * n + k - R
  let B : V := 2 * (E * Y - 1) + 1
  have hτn' : τ * τ = 1 + ell * (ell + k) := by
    have h : τ * τ = 1 + (E * Y) * (E * Y + 1) * k * k := hτn
    rw [h]; ring
  have hcy' : c = ycoord R a := hcy
  have hkB' : k = 2 * ycoord (r' + 1) B := hkB
  -- sizes
  have hN1 : 1 ≤ N := by rw [haN]; exact le_add_of_nonneg_left (Arithmetic.zero_le _)
  have hu1 : 1 ≤ u := le_trans hN1 (le_mul_of_one_le_left (Arithmetic.zero_le _) (by norm_num))
  have hq2 : 2 ≤ q := by
    have h := exp_monotone_le.mpr hu1
    have e1 : Exp.exp (1 : V) = 2 := by
      have := exp_succ (0 : V); rw [zero_add, exp_zero, mul_one] at this; exact this
    rwa [e1] at h
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq2
  have hq3c : 1 ≤ q ^ 3 := one_le_pow₀ (le_trans (by norm_num) hq2)
  have hY0 : 0 < Y := mul_pos hsY (lt_of_lt_of_le (by norm_num) hq3c)
  have hsYY : sY ≤ Y := le_mul_of_one_le_right (Arithmetic.zero_le _) hq3c
  have hXv1 : 1 ≤ Xv := one_le_exp _
  have hE1 : 1 ≤ E := one_le_mul_of_one_le_of_one_le hXv1 (pos_iff_one_le.mp hY0)
  have hEY1 : 1 ≤ E * Y := one_le_mul_of_one_le_of_one_le hE1 (pos_iff_one_le.mp hY0)
  have hR3 : 3 ≤ R := by
    have h : 2 * u < R := (properties hp).2.2
    calc (3 : V) = 2 * 1 + 1 := by norm_num
      _ ≤ 2 * u + 1 := (add_le_add_iff_right 1).mpr (mul_le_mul_of_nonneg_left hu1 (by simp))
      _ ≤ R := lt_iff_succ_le.mp h
  have hr1 : 1 ≤ r' := by
    have h : 2 * 1 + 1 ≤ 2 * r' + 1 := by
      calc (2 * 1 + 1 : V) = 3 := by norm_num
        _ ≤ R := hR3
        _ = 2 * r' + 1 := hRr
    exact le_of_mul_le_mul_left ((add_le_add_iff_right 1).mp h) (by norm_num)
  have hk4 : 4 * (B + 2) ≤ k := k_large r' B k hr1 hkB'
  have hB2 : B + 2 = 2 * (E * Y) + 1 := by
    show 2 * (E * Y - 1) + 1 + 2 = 2 * (E * Y) + 1
    have := tsub_add_cancel_of_le hEY1
    calc 2 * (E * Y - 1) + 1 + 2 = 2 * (E * Y - 1 + 1) + 1 := by ring
      _ = 2 * (E * Y) + 1 := by rw [this]
  -- y > auxw
  have hwy : auxw < y := by
    have hy2 : (2 : DiffRing V) ≤ ι y := by
      have h : 2 ≤ y := by
        rw [hydef]; exact le_trans (le_trans (by norm_num) hR3) (time_le_y _ _)
      have h' := (ι_le_ι (V := V)).mpr h; rwa [map_ofNat] at h'
    have hn := congrArg ι hauxnorm
    simp only [map_add, map_mul, map_one] at hn
    exact (ι_lt_ι (V := V)).mp (aux_gt hn hy2 (ι_nonneg _))
  -- τ > ell + s
  have hτs : ell + sY < τ := by
    have hk3 : 3 * sY ≤ k := by
      calc 3 * sY ≤ 3 * Y := mul_le_mul_of_nonneg_left hsYY (by norm_num)
        _ ≤ 4 * (2 * (E * Y) + 1) := by
          have : Y ≤ E * Y := le_mul_of_one_le_left (Arithmetic.zero_le _) hE1
          calc 3 * Y ≤ 8 * (E * Y) := mul_le_mul (by norm_num) this (Arithmetic.zero_le _) (by norm_num)
            _ ≤ 4 * (2 * (E * Y) + 1) := by
              rw [show (4 : V) * (2 * (E * Y) + 1) = 8 * (E * Y) + 4 by ring]
              exact le_add_of_nonneg_right (Arithmetic.zero_le _)
        _ = 4 * (B + 2) := by rw [hB2]
        _ ≤ k := hk4
    have hsl : sY ≤ ell := by
      have hk1 : 1 ≤ k := pos_iff_one_le.mp (add_pos he hzz)
      calc sY ≤ Y := hsYY
        _ ≤ E * Y := le_mul_of_one_le_left (Arithmetic.zero_le _) hE1
        _ ≤ E * Y * k := le_mul_of_one_le_right (Arithmetic.zero_le _) hk1
    have h := congrArg ι hτn'
    simp only [map_add, map_mul, map_one] at h
    have hk3' : 3 * ι sY ≤ ι k := by
      have := (ι_le_ι (V := V)).mpr hk3; rwa [map_mul, map_ofNat] at this
    exact (ι_lt_ι (V := V)).mp (by
      rw [map_add]; exact tau_gt h (ι_nonneg _) hk3' ((ι_le_ι (V := V)).mpr hsl) (ι_nonneg _))
  -- t = 4·t4
  have hB1 : 2 * (E * Y) ∣ B + 1 := ⟨1, by
    have : B + 1 + 1 = 2 * (E * Y) + 1 := by rw [← hB2]; ring
    rw [mul_one]; exact add_right_cancel this⟩
  obtain ⟨_, s', _, hys⟩ := ArithmeticPellCongruences.residue_quotients (r' + 1) B (2 * (E * Y)) hB1
  have hRr' : R = 2 * r' + 1 := hRr
  have hk2 : k = R + 1 + 4 * (E * Y) * s' := by rw [hkB', hys, hRr']; ring
  have hX : Xv = q * wX := hqw.symm
  have hs'1 : 1 ≤ s' := by
    rcases (Arithmetic.zero_le s').lt_or_eq with h | h
    · exact pos_iff_one_le.mp h
    · exfalso
      rw [← h, mul_zero, add_zero] at hk2
      have hRE : R < E * Y := lt_of_lt_of_le (lt_exp R) (le_trans (le_mul_of_one_le_right
        (Arithmetic.zero_le _) (pos_iff_one_le.mp hY0)) (le_mul_of_one_le_right (Arithmetic.zero_le _)
        (pos_iff_one_le.mp hY0)))
      have : R + 1 < 4 * (B + 2) := by
        rw [hB2]
        calc R + 1 < E * Y + 1 := (add_lt_add_iff_right 1).mpr hRE
          _ ≤ 4 * (2 * (E * Y) + 1) := by
            rw [show (4 : V) * (2 * (E * Y) + 1) = (E * Y + 1) + (7 * (E * Y) + 3) by ring]
            exact le_add_of_nonneg_right (Arithmetic.zero_le _)
      exact absurd (le_trans hk4 (le_of_eq hk2)) (not_le_of_gt this)
  have hwX1 : 1 ≤ wX := one_le_exp _
  -- the derived witnesses
  have hJ0 : 0 < J := by
    rcases (Arithmetic.zero_le J).lt_or_eq with h | h
    · exact h
    · exfalso
      have hq' : q = 1 := by rw [hqJ, ← h, zero_mul, add_zero]
      rw [hq'] at hq2
      exact absurd hq2 (by norm_num)
  have hwX0 : 0 < wX := lt_of_lt_of_le (by norm_num) hwX1
  let z55 : V := z + 1
  have hz55 : 0 < z55 := lt_of_lt_of_le (by simp) le_add_self
  have hτ0 : 0 < τ := by
    rcases (Arithmetic.zero_le τ).lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, mul_zero] at hτn'
      exact absurd hτn'.symm (ne_of_gt (lt_of_lt_of_le _root_.zero_lt_one le_self_add))
  -- j > 0: N ≥ 581197, so q > β + 1 and J > 1
  have hN2 : 2 ≤ N := by
    show 2 ≤ power 581197 ((2 * T + 3) + 1)
    rw [power_succ]
    exact le_trans (by norm_num : (2 : V) ≤ 581197)
      (le_mul_of_one_le_right (Arithmetic.zero_le _) (one_le_power _ _ (by norm_num)))
  have hβq : β + 1 < q := by
    have hb : β + 1 = Exp.exp ((67 : V) * 8807) := CompactFixedBeta.beta_identity
    rw [hb]
    show Exp.exp ((67 : V) * 8807) < Exp.exp (590069 * N)
    apply exp_monotone.mpr
    calc (67 : V) * 8807 = 590069 * 1 := by norm_num
      _ < 590069 * N := mul_lt_mul_of_pos_left (lt_of_lt_of_le (by norm_num) hN2) (by norm_num)
  have hJ1 : 1 < J := by
    by_contra hle
    have hJle : J ≤ 1 := le_of_not_gt hle
    have hq' : q ≤ 1 + β := by
      rw [hqJ]
      exact (add_le_add_iff_left 1).mpr (by simpa using mul_le_mul_of_nonneg_right hJle (Arithmetic.zero_le β))
    have h := lt_of_lt_of_le hβq hq'
    rw [add_comm (1 : V) β] at h
    exact _root_.lt_irrefl _ h
  have hj0 : 0 < j := by
    rcases (Arithmetic.zero_le j).lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, mul_zero, zero_add] at hj
      rw [hj] at hJ1
      exact _root_.lt_irrefl _ hJ1
  -- casts
  let Kn : ℕ := paramKernel rho
  let p : Fin 4 → ℤ := intPorts
  have cp0 : ((p 0 : ℤ) : DiffRing V) = ι β := by
    show ((((ports CompactFixedBeta.betaNat Kn lowNat highNat 0 : ℕ)) : ℤ) : DiffRing V) = _
    rw [CompactGenericPortProjections.at_zero, Int.cast_natCast, ← map_natCast ι]
  have cp1 : ((p 1 : ℤ) : DiffRing V) = ι K := CompactSymbolicPortProjections.kernel Kn
  have cp2 : ((p 2 : ℤ) : DiffRing V) = ι (low : V) := CompactSymbolicPortProjections.low Kn
  have cp3 : ((p 3 : ℤ) : DiffRing V) = ι (high + (Exp.exp (590069 : V) - 1)) :=
    CompactSymbolicPortProjections.high Kn
  have hιq : ι q = ι Fv + (ι Cv + ι αv) := by rw [hqsum]; simp [map_add]
  have hJβ : ι J * ι β = ι q - 1 := by rw [hbetaD]; exact ι_tsub hq1
  -- the rank
  let v12 : Fin 12 → V := ![J, Fv, αv, 1, 1, 1, 1, 1, 1, 1, 1, 1]
  have hb12 : ι (v12 0) * ((p 0 : ℤ) : DiffRing V) = ι (Exp.exp (590069 * N) - 1) := by
    rw [cp0]; exact hbetaD
  have hrank := graph_rank_of_packing p v12 hp rfl rfl rfl hb12 cp2 cp3
  simp only [rankExpr_eval] at hrank
  rw [show v12 0 = J from rfl, show v12 1 = Fv from rfl, show v12 2 = αv from rfl, cp0, cp2, cp3,
    hJβ] at hrank
  have hRR : ((ι q - 1) * (ι q - ι Fv) + ι αv) * (ι q * ι q - 1) +
      (((p 2 : ℤ) : DiffRing V) + ι q * ((p 3 : ℤ) : DiffRing V)) * ι J = ι R := by
    rw [cp2, cp3]
    linear_combination hrank
  -- register casts
  have hιE : ι E = ι Xv * ι Y := by simp only [E, map_mul]
  have hιk : ι k = ι eta + ι zeta := by simp only [k, map_add]
  have hιc : ι c = ι k * ι Y + ι eta := by simp only [c, map_add, map_mul]
  have hιa : ι a = ι E + ι Y := by simp only [a, map_add]
  have hιell : ι ell = ι E * (ι k * ι Y) := by simp only [ell, map_mul]; ring
  have hιc' : ι c = ι eta + ι Y * (ι eta + ι zeta) := by rw [hιc, hιk]; ring
  have hιa' : ι a = ι Xv * ι Y + ι Y := by rw [hιa, hιE]
  -- the halt-side relations
  have hYr : ι Y = ι sY * ((ι q * ι q) * ι q) := by
    show ι (sY * q ^ 3) = _; rw [map_mul, map_pow]; ring
  have hTr : (((p 1 : ℤ) : DiffRing V) + ι wX) * ((ι q - ι Fv) - ι αv) =
      ι Fv + (ι z55 - 1) * (ι q - 1) := by
    rw [cp1]
    have h := congrArg ι htrv
    simp only [map_add, map_mul] at h
    rw [ι_tsub hq1, map_one] at h
    simp only [z55, map_add, map_one]
    linear_combination h + (ι K + ι wX) * hιq
  have hdr : (ι Xv + (ι Xv * ι Y + ι Y) * (ι eta + ι Y * (ι eta + ι zeta)) +
        ι gammaOld * (3 + 4 * (ι Xv * ι Y + ι Y))) *
      (ι Xv + (ι Xv * ι Y + ι Y) * (ι eta + ι Y * (ι eta + ι zeta)) +
        ι gammaOld * (3 + 4 * (ι Xv * ι Y + ι Y))) =
      1 + ((3 + 4 * (ι Xv * ι Y + ι Y)) + (ι Xv * ι Y + ι Y) * (ι Xv * ι Y + ι Y)) *
        ((ι eta + ι Y * (ι eta + ι zeta)) * (ι eta + ι Y * (ι eta + ι zeta))) := by
    have h := congrArg ι hdn
    simp only [Xv, Y, E, k, c, a, ell, q, u, N, R] at h ⊢
    simp only [map_add, map_mul, map_one, map_ofNat, map_pow] at h ⊢
    linear_combination h
  have hd55 : (ι Xv + ι a * ι c + ι gammaOld * (4 * ι a + 3)) *
      (ι Xv + ι a * ι c + ι gammaOld * (4 * ι a + 3)) =
      (ι a * ι a + (4 * ι a + 3)) * (ι c * ι c) + 1 := by
    rw [hιa', hιc']; linear_combination hdr
  have hcyι : ι c = ι (ycoord R a) := by rw [hcy']
  have hlitr : ι f * ι f * ((ι eta + ι Y * (ι eta + ι zeta)) * ι auxT) =
      ι auxw + (ι eta + ι Y * (ι eta + ι zeta)) + ι f * ι f * ι R := by
    rw [← hιc', hcyι]
    have h := congrArg ι hlit
    simp only [Xv, Y, E, k, c, a, ell, q, u, N, R] at h ⊢
    simp only [map_add, map_mul, map_pow] at h ⊢
    linear_combination h
  have hlit55 : ι f * ι f * (ι c * ι auxT) = ι auxw + ι c + ι f * ι f * ι R := by
    rw [hιc']; exact hlitr
  let Ival : DiffRing V := ι (delta a * i * ycoord R a * ycoord R a)
  have hf1 : 1 ≤ f * f := one_le_mul_of_one_le_of_one_le (pos_iff_one_le.mp hf) (pos_iff_one_le.mp hf)
  have hIr : ((3 + 4 * (ι Xv * ι Y + ι Y)) + (ι Xv * ι Y + ι Y) * (ι Xv * ι Y + ι Y)) *
      (ι f * ι f - 1) = Ival * Ival := by
    have h := congrArg ι hnorm
    rw [map_mul, ι_tsub hf1, map_one] at h
    simp only [map_add, map_mul, map_one, delta, map_ofNat] at h
    simp only [Ival] at ⊢
    simp only [Xv, Y, E, k, c, a, ell, q, u, N, R] at h ⊢
    simp only [map_add, map_mul, map_one, delta, map_ofNat, map_pow] at h ⊢
    linear_combination h
  have hauxr : Ival * Ival * ι auxw * ι auxw + ι y * ι y = 1 + Ival * Ival * ι y * ι y := by
    have h := congrArg ι hauxnorm
    simp only [map_add, map_mul, map_one] at h
    simp only [Ival] at ⊢
    simp only [Xv, Y, E, k, c, a, ell, q, u, N, R] at h ⊢
    simp only [map_add, map_mul, map_one, map_pow] at h ⊢
    linear_combination h
  have hQI : (ι a * ι a + (4 * ι a + 3)) * (ι f * ι f - 1) = Ival * Ival := by
    rw [hιa']; linear_combination hIr
  have hτr : ι τ * ι τ = ι ell * (ι ell + ι k) + 1 := by
    have h := congrArg ι hτn'
    simp only [map_add, map_mul, map_one] at h
    linear_combination h
  have hqm' : ι q - 1 = ((p 0 : ℤ) : DiffRing V) * ι J := by rw [cp0, ← hJβ]; ring
  have hXq' : ι Xv = ι wX * ι q := by rw [hX, map_mul]; ring
  -- w < γ
  have hwγ : wX < gammaOld := by
    have hY3 : (3 : V) ≤ Y := by
      have h8 : (8 : V) ≤ q ^ 3 := by
        calc (8 : V) = 2 ^ 3 := by norm_num
          _ ≤ q ^ 3 := pow_le_pow_left₀ (by norm_num) hq2 3
      calc (3 : V) ≤ 8 := by norm_num
        _ ≤ q ^ 3 := h8
        _ ≤ Y := le_mul_of_one_le_left (Arithmetic.zero_le _) (pos_iff_one_le.mp hsY)
    have hc3 : 2 * (a + 2) * (a + 2) ≤ c := by
      rw [hcy']
      exact le_trans (y_three a) ((ordinate_strictMono a).monotone hR3)
    have hwx : wX ≤ Xv := by
      rw [hX]; exact le_mul_of_one_le_left (Arithmetic.zero_le _) hq1
    have hιY3 : (3 : DiffRing V) ≤ ι Y := by
      have h := (ι_le_ι (V := V)).mpr hY3; rwa [map_ofNat] at h
    have hιc3 : 2 * (ι a + 2) * (ι a + 2) ≤ ι c := by
      have h := (ι_le_ι (V := V)).mpr hc3
      simpa only [map_mul, map_add, map_ofNat] using h
    exact (ι_lt_ι (V := V)).mp (gamma_gt hd55 hιa' hιc3 hιY3 (ι_nonneg _) ((ι_le_ι (V := V)).mpr hwx)
      (ι_nonneg _))
  -- the fifteen-positive witnesses
  have hs'0 : 0 < s' := lt_of_lt_of_le (by norm_num) hs'1
  let h15 : V := 4 * Y * s'
  have hh15 : 0 < h15 := mul_pos (mul_pos (by norm_num) hY0) hs'0
  have hkr15 : ι k = ι R + 1 + ι h15 * ι E := by
    have h := congrArg ι hk2
    simp only [map_add, map_mul, map_one, map_ofNat] at h
    simp only [h15, map_mul, map_ofNat]
    linear_combination h
  let ΔM : V := a * a + (4 * a + 3)
  have hΔM : 0 < ΔM :=
    add_pos_of_nonneg_of_pos (Arithmetic.zero_le _)
      (add_pos_of_nonneg_of_pos (Arithmetic.zero_le _) (by norm_num))
  have hellτ : ell < τ := lt_of_le_of_lt le_self_add hτs
  have hnormr : ι f * ι f = 1 + (ι a * ι a + (4 * ι a + 3)) *
      ((ι i * (ι c * ι c)) * (ι i * (ι c * ι c))) := by
    rw [hcyι]
    have h := congrArg ι hstrong
    simp only [Xv, Y, E, k, c, a, ell, q, u, N, R] at h ⊢
    simp only [map_add, map_mul, map_one, delta, map_ofNat, map_pow] at h ⊢
    linear_combination h
  refine ⟨J, Fv, αv, z55, f, h15, i, auxT, sY, wX, τ, eta, zeta, y, auxw, gammaOld, ell, ΔM,
    hJ0, hF, hα, hz55, hf, hh15, hi, hTaux, hsY, hwX0, hτ0, he, hzz, hy, hwy, hγ, hΔM, hellτ,
    hτs, hwγ, ⟨j, hj0, hj⟩, ⟨z, hz, rfl⟩, ?_⟩
  intro W e0 e1 e2 e3 e4 e5 e8 e9 e11 e12 e14
  obtain ⟨vqm, _, _, _, vE, vk, vc, _, _, vΔ, vell, vRR, vC, vqF, vD, vA⟩ :=
    Short15ConvZero.regs intPorts W (ι q - 1) (ι q) (ι Xv) (ι Y) (ι E) (ι k) (ι c) (ι a)
      (4 * ι a + 3) (ι a * ι a + (4 * ι a + 3)) (ι ell) (ι R)
      (by rw [e0]; exact hqm') (by ring) (by rw [e9]; exact hXq') (by rw [e8]; exact hYr) hιE
      (by rw [e11, e12]; exact hιk) (by rw [e11]; exact hιc) hιa rfl rfl hιell
      (by rw [e0, e1, e2]; exact hRR)
  refine ⟨vell, by rw [vΔ]; simp only [ΔM, map_add, map_mul, map_ofNat], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Short15ConvZero.Nt_one intPorts W (ι q - 1) (ι q) vqm vC vqF (by ring)
      (by rw [e9, e1, e2, e3]; exact hTr)
  · exact Short15ConvZero.Nk_one intPorts W (ι k) (ι E) (ι R) vk vE vRR (by rw [e5]; exact hkr15)
  · exact Short15ConvZero.N1_one intPorts W (ι Xv) (ι a) (ι c) (4 * ι a + 3)
      (ι a * ι a + (4 * ι a + 3)) vD vΔ vc (by rw [e14]; exact hd55)
  · exact Short15ConvZero.N0_one intPorts W (ι ell) (ι k) (ι τ) vell vk hτr
  · rw [e4, vΔ, vc]; linear_combination hnormr
  · rw [e4, vc, vRR]; linear_combination hlit55
  · rw [rNa, vA, e4, hQI]; linear_combination hauxr

end C44Short15ConvData

#print axioms C44Short15ConvData.y_three
#print axioms C44Short15ConvData.gamma_gt
#print axioms C44Short15ConvData.canonical
