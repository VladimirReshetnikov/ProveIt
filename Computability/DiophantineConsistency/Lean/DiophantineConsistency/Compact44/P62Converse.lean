import DiophantineConsistency.Compact44.P62ConvZero
import DiophantineConsistency.Compact44.P72Converse

/-! # Package 62's converse: an internal halt gives a positive zero

This module starts from the canonical halt data of
`CompactHaltFirstGamma.halt_first_gamma`, extracted exactly as in
`P72Converse`. The witnesses, in the order `J F α z f i T s w η ζ γ t`, are:

* `J = rep N`, `Fw`, `alpha`;
* `z + 1`, because 62's transport uses the unshifted coordinate;
* `f`, the ordinary strong index `Δ·i`, and `f·T`. With `T₀` the halt
  data's `T`, `c(fT₀·f − 1) − Rf² = f²(cT₀ − R) − c` is the canonical
  auxiliary ordinate;
* `sY`, `w = 2^(R−u)`, `η`, `ζ`;
* `γold + sY·q·t4`, because `r = q²Y·4t4 = 4q⁴·(sY·q·t4)`;
* `τ − ℓ + y`, so that `t + ℓ = τ + y` and the centered norm vanishes.

`P62ConvZero.output_zero` shows that the output vanishes at them. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option linter.unusedSimpArgs false
noncomputable section
namespace P62Converse
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
open P62Graph P72ConvArith
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
  obtain ⟨_, z, hz, hqw, htrv, sY, n, eta, zeta, gammaOld, hsY, _, he, hzz, _,
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
  -- J > 0
  have hJ0 : 0 < J := by
    rcases (Arithmetic.zero_le J).lt_or_eq with h | h
    · exact h
    · exfalso
      have hq' : q = 1 := by rw [hqJ, ← h, zero_mul, add_zero]
      rw [hq'] at hq2
      exact absurd hq2 (by norm_num)
  have hwX0 : 0 < wX := lt_of_lt_of_le (by norm_num) hwX1
  -- the shifted transport, the ordinary strong index and the aux quotient
  let z62 : V := z + 1
  have hz62 : 0 < z62 := lt_of_lt_of_le (by simp) le_add_self
  let i62 : V := delta a * i
  have hi62 : 0 < i62 := by
    have hd : 0 < delta a := by
      unfold delta
      exact mul_pos (add_pos_of_nonneg_of_pos (Arithmetic.zero_le _) (by norm_num))
        (add_pos_of_nonneg_of_pos (Arithmetic.zero_le _) (by norm_num))
    exact mul_pos hd hi
  let T62 : V := f * auxT
  have hT62 : 0 < T62 := mul_pos hf hTaux
  -- the main ordinate γ = γold + sY·q·t4
  let γ62 : V := gammaOld + sY * q * t4
  have ht4pos : 0 < t4 := lt_of_lt_of_le (lt_of_lt_of_le (by norm_num) hwX1) (le_of_lt ht4w)
  have hγ62pos : 0 < γ62 :=
    add_pos_of_nonneg_of_pos (Arithmetic.zero_le _) (mul_pos (mul_pos hsY hq0) ht4pos)
  -- the centered coordinate t = τ − ℓ + y
  have hellτ : ell < τ := by
    by_contra hle
    have h' : τ ≤ ell := le_of_not_gt hle
    have h2 : τ * τ ≤ ell * ell := mul_le_mul h' h' (Arithmetic.zero_le _) (Arithmetic.zero_le _)
    have h3 : ell * ell < τ * τ := by
      rw [hτn']
      calc ell * ell ≤ ell * (ell + k) := mul_le_mul_of_nonneg_left le_self_add (Arithmetic.zero_le _)
        _ < 1 + ell * (ell + k) := lt_one_add _
    exact absurd h2 (not_le_of_gt h3)
  have hy0 : 0 < y := lt_of_le_of_lt (Arithmetic.zero_le _) hwy
  let t62 : V := τ - ell + y
  have ht62pos : 0 < t62 := add_pos_of_nonneg_of_pos (Arithmetic.zero_le _) hy0
  have ht62 : t62 + ell = τ + y := by
    show τ - ell + y + ell = τ + y
    rw [show τ - ell + y + ell = (τ - ell + ell) + y by ring, tsub_add_cancel_of_le (le_of_lt hellτ)]
  -- the valuation and its positivity
  let v13 : Fin 13 → V := ![J, Fv, αv, z62, f, i62, T62, sY, wX, eta, zeta, γ62, t62]
  have hpos : ∀ j', 0 < v13 j' := by
    intro j'
    fin_cases j'
    exacts [hJ0, hF, hα, hz62, hf, hi62, hT62, hsY, hwX0, he, hzz, hγ62pos, ht62pos]
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
      ι Fv + (ι z62 - 1) * (ι q - 1) := by
    rw [cp1]
    have h := congrArg ι htrv
    simp only [map_add, map_mul] at h
    rw [ι_tsub hq1, map_one] at h
    simp only [z62, map_add, map_one]
    linear_combination h + (ι K + ι wX) * hιq
  have ht4' : t = 4 * t4 := ht4
  have hkr : ι k = ι R + 1 + (4 * ((ι q * ι q) * (ι q * ι q))) * (ι sY * ι q * ι t4) := by
    have h := congrArg ι hkt
    rw [ht4'] at h
    simp only [Y, map_add, map_mul, map_one, map_pow, map_ofNat] at h
    linear_combination h
  have hγr : ι γ62 = ι gammaOld + ι sY * ι q * ι t4 := by simp only [γ62, map_add, map_mul]
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
  have hd62 : (ι Xv + ι a * ι c + ι gammaOld * (4 * ι a + 3)) *
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
  have hlit62 : ι f * ι f * (ι c * ι auxT) = ι auxw + ι c + ι f * ι f * ι R := by
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
  have hIval : Ival = ι i62 * (ι c * ι c) := by
    rw [hcyι]; simp only [Ival, i62, map_mul]; ring
  have hQI : (ι a * ι a + (4 * ι a + 3)) * (ι f * ι f - 1) = Ival * Ival := by
    rw [hιa']; linear_combination hIr
  have hs62 : (ι a * ι a + (4 * ι a + 3)) * (ι f * ι f - 1) =
      (ι i62 * (ι c * ι c)) * (ι i62 * (ι c * ι c)) := by rw [hQI, hIval]
  have haux62 : (ι a * ι a + (4 * ι a + 3)) * (ι f * ι f - 1) * ι auxw * ι auxw + ι y * ι y =
      1 + (ι a * ι a + (4 * ι a + 3)) * (ι f * ι f - 1) * ι y * ι y := by
    rw [hQI]; exact hauxr
  have hτr : ι ell * (ι ell + ι k) + 1 = ι τ * ι τ := by
    have h := congrArg ι hτn'
    simp only [map_add, map_mul, map_one] at h
    linear_combination -h
  have hxy : ι t62 + ι ell = ι τ + ι y := by rw [← map_add, ht62, map_add]
  have hqm' : ι q - 1 = ((p 0 : ℤ) : DiffRing V) * ι J := by rw [cp0, ← hJβ]; ring
  have hXq' : ι Xv = ι wX * ι q := by rw [hX, map_mul]; ring
  have hT0 : ι T62 = ι f * ι auxT := by simp only [T62, map_mul]
  have h0 := P62ConvZero.output_zero p (fun j' => ι (v13 j'))
    (ι q - 1) (ι q) (4 * ((ι q * ι q) * (ι q * ι q))) (ι Xv) (ι Y) (ι E) (ι k) (ι c) (ι a)
    (4 * ι a + 3) (ι a * ι a + (4 * ι a + 3)) (ι ell) (ι ell * (ι ell + ι k) + 1) (ι R)
    (ι i62 * (ι c * ι c)) ((ι a * ι a + (4 * ι a + 3)) * (ι f * ι f - 1)) (ι τ) (ι y)
    (ι sY * ι q * ι t4) (ι gammaOld) (ι auxw) (ι auxT)
    hqm' (by ring) rfl hXq' hYr hιE hιk hιc hιa rfl rfl hιell rfl hRR rfl rfl hTr hkr hγr hd62
    hs62 hT0 hlit62 haux62 hτr hxy
  exact (internalZero_iff _ _).mpr h0

end P62Converse

#print axioms P62Converse.converse
