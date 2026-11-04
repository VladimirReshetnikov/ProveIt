import FreeJHaltModelZero
import CompactSymbolicPortProjections
import P72ConvArithShim
import P65HaltPositiveCoordinates
import P65ConverseAlgebra
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option linter.unusedSimpArgs false
noncomputable section
namespace P65CanonicalHaltConverse
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
open P72ConvArith
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
attribute [local irreducible] paramKernel rho highNat CompactFixedBeta.betaNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem two_pow_odd_mod (n : ℕ) : (2 ^ (2 * n + 1) - 1) % 3 = 1 := by
  have h : 2 ^ (2 * n + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]; norm_num
  have hpos : 1 ≤ 2 ^ (2 * n + 1) := Nat.one_le_two_pow
  omega

/-- `2^590069 − 1 ≡ 1 (mod 3)`, by `4^n ≡ 1`. -/
private theorem betaNat_mod_three : CompactFixedBeta.betaNat % 3 = 1 := by
  unfold CompactFixedBeta.betaNat
  rw [show (67 * 8807 : ℕ) = 2 * 295034 + 1 from rfl]
  exact two_pow_odd_mod 295034
private theorem beta_cast_mod (β : V) (hβ : β = (CompactFixedBeta.betaNat : V)) : ∃ b : V, β = 3 * b + 1 := by
  refine ⟨((CompactFixedBeta.betaNat / 3 : ℕ) : V), ?_⟩
  have h := Nat.div_add_mod CompactFixedBeta.betaNat 3
  rw [betaNat_mod_three] at h
  rw [hβ]
  have := congrArg (fun n : ℕ => (n : V)) h
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at this
  exact this.symm

theorem ι_tsub {a b : V} (h : b ≤ a) : ι (a - b) = ι a - ι b := by
  rw [eq_sub_iff_add_eq, ← map_add, tsub_add_cancel_of_le h]

theorem rankExpr_eval {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (x : Fin 12 → R) :
    (rankExpr p).evalRing x =
      (x 2 + (1 + x 0 * (p 0 : R) - x 1) * (x 0 * (p 0 : R))) *
        ((1 + x 0 * (p 0 : R)) * (1 + x 0 * (p 0 : R)) - 1) +
      x 0 * ((p 2 : R) + (p 3 : R) * (1 + x 0 * (p 0 : R))) := by
  simp only [rankExpr, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, Expr.evalRing_ofNat, Nat.cast_one]

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

theorem halt_positive_zero (T : V) (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0) :
    ∃ v : Fin 14 → V, (∀ j, 0 < v j) ∧
      InternalZero (P65Graph.graph (CompactSymbolicPortProjections.portsInt (paramKernel rho))).output v := by
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
  obtain ⟨b3, hb3⟩ := beta_cast_mod β rfl
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
  -- f > j
  have hJq : J < q := by
    rw [hqJ]
    calc J < 1 + J := lt_one_add J
      _ ≤ 1 + J * β := (add_le_add_iff_left 1).mpr
          (le_mul_of_one_le_right (Arithmetic.zero_le _) (by rw [hb3]; exact le_add_of_nonneg_left (Arithmetic.zero_le _)))
  have hqY : q ≤ Y := by
    calc q ≤ q ^ 3 := by
          calc q = q ^ 1 := (pow_one q).symm
            _ ≤ q ^ 3 := pow_le_pow_right₀ (le_trans (by norm_num) hq2) (by norm_num)
      _ ≤ Y := le_mul_of_one_le_left (Arithmetic.zero_le _) (pos_iff_one_le.mp hsY)
  have hjf : j < f := by
    have hjJ : j < J := by rw [hj]; exact lt_of_lt_of_le (lt_add_one j) (by
      calc j + 1 ≤ 3 * j + 1 := (add_le_add_iff_right 1).mpr (le_mul_of_one_le_left (Arithmetic.zero_le _) (by norm_num)))
    have hyc : 1 ≤ ycoord (R * ycoord R a) a := by
      rw [hyic]
      have hc0 : 0 < ycoord R a := lt_of_lt_of_le (lt_of_lt_of_le (by norm_num) hR3) (time_le_y R a)
      exact pos_iff_one_le.mp (mul_pos (mul_pos hi hc0) hc0)
    have hx := ArithmeticOuterSeed.x_gt (R * ycoord R a) a
    have hfa : a + 1 < f := by
      rw [hfx]; exact lt_of_le_of_lt (le_mul_of_one_le_right (Arithmetic.zero_le _) hyc) hx
    have hYa : Y < a + 1 := by
      show Y < Xv * Y + Y + 1
      exact lt_of_le_of_lt (le_add_of_nonneg_left (Arithmetic.zero_le _)) (lt_add_one _)
    exact lt_trans hjJ (lt_trans hJq (lt_of_le_of_lt hqY (lt_trans hYa hfa)))
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
  let f0 : V := f - j
  have hf0 : f0 + j = f := tsub_add_cancel_of_le (le_of_lt hjf)
  have hf0pos : 0 < f0 := tsub_pos_of_lt hjf
  have hjpos : 0 < j := P65HaltPositiveCoordinates.rep_index_positive 590069 N j
    (P65HaltPositiveCoordinates.halt_length_ge_two T) hj
  have hxpos : 0 < Xv - q := P65HaltPositiveCoordinates.shifted_exp_positive u R q wX Xv
    (properties hp).2.2 hq0 rfl hX
  have hΔpos : 0 < delta a := by
    unfold delta
    exact mul_pos (lt_of_lt_of_le (by norm_num) (le_add_of_nonneg_left (Arithmetic.zero_le _)))
      (lt_of_lt_of_le (by norm_num) (le_add_of_nonneg_left (Arithmetic.zero_le _)))
  let r65 : V := τ - (ell + sY)
  have hr65 : 0 < r65 := tsub_pos_of_lt hτs
  let v14 : Fin 14 → V := ![j, Fv, αv, z, f, delta a * i, auxT, Xv-q,
    Y, r65, eta, zeta, u72, γ72]
  have hvpos : ∀ l, 0 < v14 l := by
    intro l
    fin_cases l
    exacts [hjpos, hF, hα, hz, hf, mul_pos hΔpos hi, hTaux, hxpos, hY0, hr65, he, hzz, hu72pos, hγ72pos]
  refine ⟨v14, hvpos, ?_⟩
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
  have hq1J : ι q - 1 = ι β * (3 * ι j + 1) := by
    rw [← hJβ, hj]; simp [map_add, map_mul, map_ofNat]; ring
  -- the rank
  let v12 : Fin 12 → V := ![J, Fv, αv, 1, 1, 1, 1, 1, 1, 1, 1, 1]
  have hb12 : ι (v12 0) * ((p 0 : ℤ) : DiffRing V) = ι (Exp.exp (590069 * N) - 1) := by
    rw [cp0]; exact hbetaD
  have hrank := graph_rank_of_packing p v12 hp rfl rfl rfl hb12 cp2 cp3
  simp only [rankExpr_eval] at hrank
  rw [show v12 0 = J from rfl, show v12 1 = Fv from rfl, show v12 2 = αv from rfl, cp0, cp2, cp3,
    hJβ] at hrank
  have hR : ((p 0 : ℤ) : DiffRing V) * ((ι αv + (ι Cv + ι αv) * ((ι Fv + (ι Cv + ι αv)) - 1)) *
        ((ι Fv + (ι Cv + ι αv)) * (ι Fv + (ι Cv + ι αv)) - 1)) +
      (((p 2 : ℤ) : DiffRing V) + ((p 3 : ℤ) : DiffRing V) * (ι Fv + (ι Cv + ι αv))) *
        ((ι Fv + (ι Cv + ι αv)) - 1) = ((p 0 : ℤ) : DiffRing V) * ι R := by
    rw [cp0, cp2, cp3, ← hιq, ← hrank]
    linear_combination (-(ι β * (ι q - 1) * (ι q * ι q - 1))) * hιq -
      (ι (low : V) + ι (high + (Exp.exp (590069 : V) - 1)) * ι q) * hJβ
  -- the remaining hypotheses of `residuals_zero`
  have hf0' : ι f0 + ι j = ι f := by rw [← map_add, hf0]
  have hNf : (3 * ((p 0 : ℤ) : DiffRing V)) * ι f0 +
      ((ι Fv + (ι Cv + ι αv)) - (((p 0 : ℤ) : DiffRing V) + 1)) = 3 * ((p 0 : ℤ) : DiffRing V) * ι f := by
    rw [cp0, ← hιq]; linear_combination (3 * ι β) * hf0' + hq1J
  have hYr : ι Y = ι sY * ((ι Fv + (ι Cv + ι αv)) * ((ι Fv + (ι Cv + ι αv)) * (ι Fv + (ι Cv + ι αv)))) := by
    rw [← hιq]; show ι (sY * q ^ 3) = _; rw [map_mul, map_pow]; ring
  have hBtr : ι Cv * (ι Xv + ((p 1 : ℤ) : DiffRing V) * (ι Fv + (ι Cv + ι αv))) -
      ι Fv * (ι Fv + (ι Cv + ι αv)) = ((ι Fv + (ι Cv + ι αv)) - 1) * ((ι Fv + (ι Cv + ι αv)) * ι z) := by
    rw [cp1, ← hιq]
    have h := congrArg ι hBt
    simp only [map_add, map_mul] at h
    rw [ι_tsub hq1, map_one] at h
    linear_combination h
  have hrr : ι r72 = ι τ + (ι Fv + (ι Cv + ι αv)) * ι z -
      ((ι Xv * ι Y) * (ι Y * (ι eta + ι zeta)) + ι sY) := by
    rw [← hιq]
    have h := congrArg ι hr72
    simp only [Xv, Y, E, k, c, a, ell, q, u, N, R] at h ⊢
    simp only [map_add, map_mul, map_pow] at h ⊢
    linear_combination h
  have hτr : ι τ * ι τ = 1 + ((ι Xv * ι Y) * (ι Y * (ι eta + ι zeta))) *
      ((ι Xv * ι Y) * (ι Y * (ι eta + ι zeta)) + (ι eta + ι zeta)) := by
    have h := congrArg ι hτn'
    simp only [Xv, Y, E, k, c, a, ell, q, u, N, R] at h ⊢
    simp only [map_add, map_mul, map_one, map_pow] at h ⊢
    linear_combination h
  have hkr : ι eta + ι zeta = ι R + 1 +
      (4 * (ι Y * (ι Fv + (ι Cv + ι αv))) * (ι Fv + (ι Cv + ι αv))) * ι t4 := by
    rw [← hιq]
    have ht4' : t = 4 * t4 := ht4
    have h := congrArg ι hkt
    rw [ht4'] at h
    simp only [Xv, Y, E, k, c, a, ell, q, u, N, R] at h ⊢
    simp only [map_add, map_mul, map_one, map_pow, map_ofNat] at h ⊢
    linear_combination h
  have hXr : ι Xv = (ι Fv + (ι Cv + ι αv)) * ι wX := by rw [← hιq, hX, map_mul]
  have hγr : ι γ72 + ι wX = ι gammaOld + ι t4 := by rw [← map_add, hγ72, map_add]
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
  have hlitr : ι f * ι f * ((ι eta + ι Y * (ι eta + ι zeta)) * ι auxT) =
      ι auxw + (ι eta + ι Y * (ι eta + ι zeta)) + ι f * ι f * ι R := by
    rw [hcyι]
    have h := congrArg ι hlit
    simp only [Xv, Y, E, k, c, a, ell, q, u, N, R] at h ⊢
    simp only [map_add, map_mul, map_pow] at h ⊢
    linear_combination h
  have hyr : ι y = ι auxw + ι u72 := by rw [← map_add, hu72]
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
  let w : Fin 14 → DiffRing V := fun j => ι (v14 j)
  let val := P65Graph.vals p w
  have hqv : val.q = ι q := by
    dsimp [val, w, P65Graph.vals, v14]
    rw [cp0]
    linear_combination -hq1J
  have hxcast : ι (Xv-q) = ι Xv - ι q := ι_tsub (le_of_lt (tsub_pos_iff_lt.mp hxpos))
  have hrv : ι r65 + (ι ell + ι sY) = ι τ := by
    have h := congrArg ι (tsub_add_cancel_of_le (le_of_lt hτs))
    simp only [map_add] at h
    exact h
  have hXv : val.X = ι Xv := by
    change val.q + ι (Xv-q) = ι Xv
    rw [hqv, hxcast]
    ring
  have hCv : val.C = ι Cv := by
    change val.q - ι Fv - ι αv = ι Cv
    rw [hqv, hιq]
    ring
  have hkv : val.k = ι eta + ι zeta := by rfl
  have hcv : val.c = ι eta + ι Y * (ι eta + ι zeta) := by rfl
  have hav : val.a = ι Xv * ι Y + ι Y := by
    change ι Y + ι Y * val.X = _
    rw [hXv]
    ring
  have hHv : val.H = 3 + 4 * (ι Xv * ι Y + ι Y) := by
    change 3 + 4 * val.a = _
    rw [hav]
  have hΔv : val.Delta = (3 + 4 * (ι Xv * ι Y + ι Y)) +
      (ι Xv * ι Y + ι Y) * (ι Xv * ι Y + ι Y) := by
    change val.H + val.a * val.a = _
    rw [hHv, hav]
  have hellv : val.ell = (ι Xv * ι Y) * (ι Y * (ι eta + ι zeta)) := by
    change (ι Y * val.k) * (ι Y * val.X) = _
    rw [hkv, hXv]
    ring
  have hq3v : val.q3 = ι q * (ι q * ι q) := by
    change val.q * (val.q * val.q) = _
    rw [hqv]
  have hRv : val.RR = ι R := by
    change (ι αv + ((p 0 : ℤ) : DiffRing V) * (1 + 3 * ι j) * (val.q - ι Fv)) *
      (val.q * val.q - 1) + (1 + 3 * ι j) * (((p 2 : ℤ) : DiffRing V) + ((p 3 : ℤ) : DiffRing V) * val.q) = _
    rw [hqv, cp0, cp2, cp3]
    rw [hj] at hrank
    simp only [map_add, map_mul, map_ofNat, map_one] at hrank
    have hβj : ι β * (1 + 3 * ι j) = ι q - 1 := by linear_combination -hq1J
    rw [hβj]
    simp only [map_add] at hrank ⊢
    linear_combination hrank
  have hMv : val.M = 4 * (ι Y * ι q) * ι q := by
    change (4 * (ι Y * val.q)) * val.q = _
    rw [hqv]
  have hbJv : val.bJ = ι q - 1 := by
    change ((p 0 : ℤ) : DiffRing V) * (1 + 3 * ι j) = _
    rw [cp0]
    linear_combination -hq1J
  have hI : Ival = ι (delta a * i) * (val.c * val.c) := by
    rw [hcv, hcyι]
    simp only [Ival, map_mul]
    ring
  have hres : (P65Graph.graph p).A0.evalRing w = 0 ∧
      (P65Graph.graph p).Nm.evalRing w = 0 ∧
      (P65Graph.graph p).At.evalRing w = 0 ∧
      (P65Graph.graph p).Aa.evalRing w = 0 ∧
      (P65Graph.graph p).As.evalRing w = 0 := by
    apply P65ConverseAlgebra.residuals_zero p w (ι τ) (ι sY) (ι wX)
      (ι gammaOld) (ι t4) (ι auxw) (ι y)
      (ι Xv + (ι Xv * ι Y + ι Y) * (ι eta + ι Y * (ι eta + ι zeta)) +
        ι gammaOld * (3 + 4 * (ι Xv * ι Y + ι Y)))
    · change ι Y = ι sY * val.q3
      rw [hq3v, hιq]
      exact hYr
    · change ι r65 + val.ell + ι sY = ι τ
      rw [hellv]
      simp only [ell, E, k, map_mul, map_add] at hrv
      linear_combination hrv
    · rw [hellv, hkv]
      exact hτr
    · change val.C * (val.X + ((p 1 : ℤ) : DiffRing V) * val.q) - ι Fv * val.q =
        val.bJ * val.q * ι z
      rw [hCv, hXv, hqv, hbJv, hιq]
      linear_combination hBtr
    · rw [hkv, hRv, hMv, hιq]
      exact hkr
    · rw [hXv, hqv, hιq]
      exact hXr
    · change ι γ72 + ι wX = ι gammaOld + ι t4
      exact hγr
    · rw [hXv, hcv, hav, hHv]
      ring
    · rw [hΔv, hcv]
      exact hdr
    · change (ι f * ι f) * (ι auxT * val.c) =
        ι auxw + val.c + (ι f * ι f) * val.RR
      rw [hcv, hRv]
      linear_combination hlitr
    · change ι y = ι auxw + ι u72
      exact hyr
    · change val.Delta * (ι f * ι f - 1) =
        (ι (delta a * i) * (val.c * val.c)) * (ι (delta a * i) * (val.c * val.c))
      rw [hΔv, hIr, hI]
    · change val.Delta * (ι f * ι f - 1) * ι auxw * ι auxw + ι y * ι y =
        1 + val.Delta * (ι f * ι f - 1) * ι y * ι y
      rw [hΔv, hIr]
      exact hauxr
  exact (P65Graph.zero_iff p v14).mpr ⟨(internalZero_iff _ _).mpr hres.1,
    (internalZero_iff _ _).mpr hres.2.1, (internalZero_iff _ _).mpr hres.2.2.1,
    (internalZero_iff _ _).mpr hres.2.2.2.1, (internalZero_iff _ _).mpr hres.2.2.2.2⟩
end P65CanonicalHaltConverse

#print axioms P65CanonicalHaltConverse.halt_positive_zero
