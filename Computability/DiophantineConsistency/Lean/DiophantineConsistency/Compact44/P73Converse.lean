import DiophantineConsistency.Compact44.P73ConvZero
import DiophantineConsistency.Compact44.P72Converse

/-! # Package 73's converse: an internal halt gives a positive zero

This module starts from the canonical halt data of
`CompactHaltFirstGamma.halt_first_gamma`, extracted exactly as in
`P72Converse`. The witnesses, in the order `j F α f i T X Y r η ζ u γ`, are:

* `j`, where `rep N = 3j+1`; `j > 0` because `N ≥ 581197`, so `J > 1`;
* `Fw`, `alpha`, `f`, `i` (already the normalized strong index), `T`, `2^R`,
  `sY·q³`;
* `τ + qz·W − (ℓ + k + s)`, where `W = 1 + k(q−1)` unfolds the free-J
  literal's folded transport;
* `η`, `ζ` and `y − w`;
* `γold + t − wX`. Since `k = R + 1 + q²Y·t` and `XYq = q²Y·wX`, the main
  shift `Uγ + qXY − (k − R − 1)` is `U·γold`.

`P73ConvZero.output_zero` shows that the output vanishes at them. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option linter.unusedSimpArgs false
noncomputable section
namespace P73Converse
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
open P73Graph P72ConvArith
open P72Root (ι_tsub)
open P72Converse (rankExpr_eval)
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
attribute [local irreducible] paramKernel rho highNat CompactFixedBeta.betaNat
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

theorem converse (T : V) (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0) :
    ∃ v : Fin 13 → V, (∀ j, 0 < v j) ∧
      InternalZero (graph (CompactSymbolicPortProjections.portsInt (paramKernel rho))).output v := by
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
  obtain ⟨_, z, hz, hqw, _, sY, n, eta, zeta, gammaOld, hsY, _, he, hzz, _,
    hseed, _, haux, hfirst, hgam⟩ := hresult
  obtain ⟨f, i, auxT, auxw, y, hf, hi, hTaux, _, hy, hfx, hyic, hstrong,
    hydef, _, _, _, _, hlit, _, hauxnorm, _, _, _, _, hnorm⟩ := haux
  obtain ⟨hBt, _, _, _⟩ := hfirst
  obtain ⟨t, _, _, hk, hgammarel⟩ := hgam
  have hp : PackingInput 590069 K low high N stride Xf := by
    simpa only [Xf, N, stride, K, low, high, highNat] using hpack
  -- the packing coordinates
  let Cv := Cw 590069 N Xf
  let Fv := Fw 590069 K N stride Xf
  let αv := alpha 590069 K N stride Xf
  have hC : 0 < Cv := C_pos hp
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
  have hkt : k = R + 1 + (Y * q ^ 2) * t := hk
  have hts : (Y * q ^ 2) * t = 4 * (E * Y) * s' := add_left_cancel (hkt.symm.trans hk2)
  have hX : Xv = q * wX := hqw.symm
  have ht4 : t = 4 * (q * q * wX * sY * s') := by
    have hYq0 : 0 < Y * (q * q) := mul_pos hY0 (mul_pos hq0 hq0)
    apply mul_left_cancel₀ (ne_of_gt hYq0)
    calc Y * (q * q) * t = (Y * q ^ 2) * t := by ring
      _ = 4 * (E * Y) * s' := hts
      _ = Y * (q * q) * (4 * (q * q * wX * sY * s')) := by
        show 4 * (Xv * Y * Y) * s' = _
        rw [hX]; ring
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
  let t4 : V := q * q * wX * sY * s'
  have hwX1 : 1 ≤ wX := one_le_exp _
  have ht4w : wX < t4 := by
    show wX < q * q * wX * sY * s'
    calc wX < 4 * wX := by
          calc wX = 1 * wX := (one_mul _).symm
            _ < 4 * wX := mul_lt_mul_of_pos_right (by norm_num) (lt_of_lt_of_le (by norm_num) hwX1)
      _ ≤ q * q * wX := mul_le_mul_of_nonneg_right (by
          calc (4 : V) = 2 * 2 := by norm_num
            _ ≤ q * q := mul_le_mul hq2 hq2 (by norm_num) (Arithmetic.zero_le _)) (Arithmetic.zero_le _)
      _ ≤ q * q * wX * sY := le_mul_of_one_le_right (Arithmetic.zero_le _) (pos_iff_one_le.mp hsY)
      _ ≤ q * q * wX * sY * s' := le_mul_of_one_le_right (Arithmetic.zero_le _) hs'1
  -- the derived witnesses
  let γ72 : V := gammaOld + t4 - wX
  have hγ72 : γ72 + wX = gammaOld + t4 :=
    tsub_add_cancel_of_le (le_trans (le_of_lt ht4w) (le_add_of_nonneg_left (Arithmetic.zero_le _)))
  have hγ72pos : 0 < γ72 := tsub_pos_of_lt (lt_of_lt_of_le ht4w (le_add_of_nonneg_left (Arithmetic.zero_le _)))
  let r72 : V := τ + q * z - (ell + sY)
  have hr72 : r72 + (ell + sY) = τ + q * z :=
    tsub_add_cancel_of_le (le_trans (le_of_lt hτs) (le_add_of_nonneg_right (Arithmetic.zero_le _)))
  have hr72pos : 0 < r72 := tsub_pos_of_lt (lt_of_lt_of_le hτs (le_add_of_nonneg_right (Arithmetic.zero_le _)))
  let u72 : V := y - auxw
  have hu72 : auxw + u72 = y := add_tsub_cancel_of_le (le_of_lt hwy)
  have hu72pos : 0 < u72 := tsub_pos_of_lt hwy
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
  -- the first ordinate r = τ + qzW − (ℓ + k + s)
  have hk1 : 1 ≤ k := pos_iff_one_le.mp (add_pos he hzz)
  let W73 : V := 1 + k * (q - 1)
  have hqm1 : 1 ≤ q - 1 := by
    apply (add_le_add_iff_right (1 : V)).mp
    rw [tsub_add_cancel_of_le hq1]; simpa [one_add_one_eq_two] using hq2
  have hkW : k < q * z * W73 := by
    calc k < 1 + k := lt_one_add k
      _ ≤ 1 + k * (q - 1) := (add_le_add_iff_left 1).mpr (le_mul_of_one_le_right (Arithmetic.zero_le _) hqm1)
      _ ≤ q * z * W73 := le_mul_of_one_le_left (Arithmetic.zero_le _)
          (one_le_mul_of_one_le_of_one_le (le_trans (by norm_num) hq2) (pos_iff_one_le.mp hz))
  have hrlt : ell + k + sY < τ + q * z * W73 := by
    calc ell + k + sY = (ell + sY) + k := by ring
      _ < τ + q * z * W73 := add_lt_add hτs hkW
  let r73 : V := τ + q * z * W73 - (ell + k + sY)
  have hr73 : r73 + (ell + k + sY) = τ + q * z * W73 := tsub_add_cancel_of_le (le_of_lt hrlt)
  have hr73pos : 0 < r73 := tsub_pos_of_lt hrlt
  -- the main ordinate γ = γold + t − wX
  have ht4' : t = 4 * t4 := ht4
  have hwt : wX < gammaOld + t := by
    rw [ht4']
    calc wX < t4 := ht4w
      _ ≤ 4 * t4 := le_mul_of_one_le_left (Arithmetic.zero_le _) (by norm_num)
      _ ≤ gammaOld + 4 * t4 := le_add_of_nonneg_left (Arithmetic.zero_le _)
  let γ73 : V := gammaOld + t - wX
  have hγ73 : γ73 + wX = gammaOld + t := tsub_add_cancel_of_le (le_of_lt hwt)
  have hγ73pos : 0 < γ73 := tsub_pos_of_lt hwt
  -- the valuation and its positivity
  let v13 : Fin 13 → V := ![j, Fv, αv, f, i, auxT, Xv, Y, r73, eta, zeta, u72, γ73]
  have hpos : ∀ j', 0 < v13 j' := by
    intro j'
    fin_cases j'
    exacts [hj0, hF, hα, hf, hi, hTaux, lt_of_lt_of_le (by norm_num) hXv1, hY0, hr73pos, he, hzz,
      hu72pos, hγ73pos]
  refine ⟨v13, hpos, ?_⟩
  -- casts
  let Kn : ℕ := paramKernel rho
  let p := CompactSymbolicPortProjections.portsInt Kn
  have cp0 : ((p 0 : ℤ) : DiffRing V) = ι β := by
    show ((((ports CompactFixedBeta.betaNat Kn lowNat highNat 0 : ℕ)) : ℤ) : DiffRing V) = _
    rw [CompactGenericPortProjections.at_zero, Int.cast_natCast, ← map_natCast ι]
  have cp1 : ((p 1 : ℤ) : DiffRing V) = ι K := CompactSymbolicPortProjections.kernel Kn
  have cp2 : ((p 2 : ℤ) : DiffRing V) = ι (low : V) := CompactSymbolicPortProjections.low Kn
  have cp3 : ((p 3 : ℤ) : DiffRing V) = ι (high + (Exp.exp (590069 : V) - 1)) :=
    CompactSymbolicPortProjections.high Kn
  have hιq : ι q = ι Fv + (ι Cv + ι αv) := by rw [hqsum]; simp [map_add]
  have hJβ : ι J * ι β = ι q - 1 := by rw [hbetaD]; exact ι_tsub hq1
  have hJι : ι J = 1 + 3 * ι j := by rw [hj]; simp [map_add, map_mul, map_ofNat]; ring
  -- the rank
  let v12 : Fin 12 → V := ![J, Fv, αv, 1, 1, 1, 1, 1, 1, 1, 1, 1]
  have hb12 : ι (v12 0) * ((p 0 : ℤ) : DiffRing V) = ι (Exp.exp (590069 * N) - 1) := by
    rw [cp0]; exact hbetaD
  have hrank := graph_rank_of_packing p v12 hp rfl rfl rfl hb12 cp2 cp3
  simp only [rankExpr_eval] at hrank
  rw [show v12 0 = J from rfl, show v12 1 = Fv from rfl, show v12 2 = αv from rfl, cp0, cp2, cp3,
    hJβ] at hrank
  have hRR : (ι αv + (ι q - ι Fv) * (ι q - 1)) * (ι q * ι q - 1) +
      ι J * (((p 2 : ℤ) : DiffRing V) + ((p 3 : ℤ) : DiffRing V) * ι q) = ι R := by
    rw [cp2, cp3]
    linear_combination hrank
  -- register casts
  have hιE : ι E = ι Xv * ι Y := by simp only [E, map_mul]
  have hιk : ι k = ι eta + ι zeta := by simp only [k, map_add]
  have hιc : ι c = ι eta + ι Y * ι k := by simp only [c, map_add, map_mul]; ring
  have hιa : ι a = ι E + ι Y := by simp only [a, map_add]
  have hιell : ι ell = ι E * (ι Y * ι k) := by simp only [ell, map_mul]; ring
  have hιc' : ι c = ι eta + ι Y * (ι eta + ι zeta) := by rw [hιc, hιk]
  have hιa' : ι a = ι Xv * ι Y + ι Y := by rw [hιa, hιE]
  -- the halt-side relations
  have hBtr : ((ι q - ι Fv) - ι αv) * (ι Xv + ((p 1 : ℤ) : DiffRing V) * ι q) - ι Fv * ι q =
      (ι q - 1) * (ι q * ι z) := by
    rw [cp1]
    have h := congrArg ι hBt
    simp only [map_add, map_mul] at h
    rw [ι_tsub hq1, map_one] at h
    linear_combination h + (ι Xv + ι K * ι q) * hιq
  have hYr : ι Y = ι sY * (ι q * (ι q * ι q)) := by
    show ι (sY * q ^ 3) = _; rw [map_mul, map_pow]; ring
  have hrr : ι r73 = ι τ + ι q * ι z * (1 + ι k * (ι q - 1)) - (ι ell + ι k + ι sY) := by
    have h := congrArg ι hr73
    simp only [W73, map_add, map_mul, map_one] at h
    rw [ι_tsub hq1, map_one] at h
    linear_combination h
  have hτr : ι τ * ι τ = 1 + ι ell * (ι ell + ι k) := by
    have h := congrArg ι hτn'
    simp only [map_add, map_mul, map_one] at h
    exact h
  have hkr : ι k = ι R + 1 + (ι Y * (ι q * ι q)) * ι t := by
    have h := congrArg ι hkt
    simp only [map_add, map_mul, map_one, map_pow] at h
    rw [h]; ring
  have hXr : ι Xv = ι q * ι wX := by rw [hX, map_mul]
  have hγr : ι γ73 + ι wX = ι gammaOld + ι t := by rw [← map_add, hγ73, map_add]
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
  have hd73 : (ι Xv + ι a * ι c + ι gammaOld * (3 + 4 * ι a)) *
      (ι Xv + ι a * ι c + ι gammaOld * (3 + 4 * ι a)) =
      1 + ((3 + 4 * ι a) + ι a * ι a) * (ι c * ι c) := by
    rw [hιa', hιc']; exact hdr
  have hcyι : ι eta + ι Y * (ι eta + ι zeta) = ι (ycoord R a) := by
    rw [← hcy']; simp [c, k, map_add, map_mul]; ring
  have hsr : ι f * ι f = 1 + ((3 + 4 * (ι Xv * ι Y + ι Y)) + (ι Xv * ι Y + ι Y) * (ι Xv * ι Y + ι Y)) *
      ((((ι eta + ι Y * (ι eta + ι zeta)) * (ι eta + ι Y * (ι eta + ι zeta))) * ι i) *
        (((ι eta + ι Y * (ι eta + ι zeta)) * (ι eta + ι Y * (ι eta + ι zeta))) * ι i)) := by
    rw [hcyι]
    have h := congrArg ι hstrong
    simp only [Xv, Y, E, k, c, a, ell, q, u, N, R] at h ⊢
    simp only [map_add, map_mul, map_one, delta, map_ofNat, map_pow] at h ⊢
    linear_combination h
  have hs73 : ι f * ι f = 1 + ((3 + 4 * ι a) + ι a * ι a) * ((ι c * ι c * ι i) * (ι c * ι c * ι i)) := by
    rw [hιa', hιc']; exact hsr
  have hlitr : ι f * ι f * ((ι eta + ι Y * (ι eta + ι zeta)) * ι auxT) =
      ι auxw + (ι eta + ι Y * (ι eta + ι zeta)) + ι f * ι f * ι R := by
    rw [hcyι]
    have h := congrArg ι hlit
    simp only [Xv, Y, E, k, c, a, ell, q, u, N, R] at h ⊢
    simp only [map_add, map_mul, map_pow] at h ⊢
    linear_combination h
  have hlit73 : ι f * ι f * (ι auxT * ι c) = ι auxw + ι c + ι f * ι f * ι R := by
    rw [hιc']; linear_combination hlitr
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
  have hU' : ((3 + 4 * ι a) + ι a * ι a) * (ι f * ι f - 1) = Ival * Ival := by
    rw [hιa']; exact hIr
  have hyr : ι y = ι auxw + ι u72 := by rw [← map_add, hu72]
  have haux73 : ((3 + 4 * ι a) + ι a * ι a) * (ι f * ι f - 1) * ι auxw * ι auxw +
        (ι auxw + ι u72) * (ι auxw + ι u72) =
      1 + ((3 + 4 * ι a) + ι a * ι a) * (ι f * ι f - 1) * (ι auxw + ι u72) * (ι auxw + ι u72) := by
    rw [hU', ← hyr]; exact hauxr
  have hqm' : ι q - 1 = ι J * ((p 0 : ℤ) : DiffRing V) := by rw [cp0, hJβ]
  have h0 := P73ConvZero.output_zero p (fun j' => ι (v13 j'))
    (ι J) (ι q - 1) (ι q) (ι q * (ι q * ι q)) (ι Y * (ι q * ι q)) (ι E) (ι k) (ι c) (ι a)
    (3 + 4 * ι a) ((3 + 4 * ι a) + ι a * ι a) (ι ell) (ι q * (ι q * ι q) * (ι q - 1))
    (((3 + 4 * ι a) + ι a * ι a) * (ι f * ι f - 1))
    (ι R) (ι τ) (ι sY) (ι z) (ι t) (ι wX) (ι gammaOld) (ι auxw)
    hJι hqm' (by ring) rfl rfl hιE hιk hιc hιa rfl rfl hιell rfl rfl hRR hBtr hYr hrr hτr hkr hXr hγr hd73
    hs73 hlit73 haux73
  exact (internalZero_iff _ _).mpr h0

end P73Converse

#print axioms P73Converse.converse
