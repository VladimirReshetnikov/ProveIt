import DiophantineConsistency.Mixed121.Short15ConvZero
import DiophantineConsistency.Mixed121.P55Converse

/-! # Fifteen-positive converse: the canonical 121x8801 halt data

From the canonical halt data (`Mixed121Seeds.halt_first_gamma`), as in
`P55Converse`, `canonical` extracts the witnesses common to all fifteen-positive
forms: `J = rep d N`, `F = Fw`, `α = alpha`, `z + 1`, `f`, `h = 4Ys'` (since
`k − R − 1 = 4(EY)s' = E·4Ys'` with `s' ≥ 1`), `s = sY`, `w = 2^(R−u)`, `η`, `ζ`,
`γ = γold` (positive by the seed's own `0 < γ`), and the halt's `i`, `T`, `τ`,
`y` and auxiliary ordinate `wa < y`. At every valuation `W` that reads these
eleven coordinates, it gives `Nt = Nk = N1 = 1`, `N0 = 1` at `τ`, the normalized
strong norm `f² − Δ(ic²)² = 1`, the auxiliary ordinate `f²(cT − R) − c = wa`, and
the auxiliary norm `Aaux(wa² − y²) + y² = 1`. The remaining four coordinates
(`i`, `T`, the first root and the auxiliary partner) are chosen per equation. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section
namespace Short15ConvData
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 ModelDifferenceRing
open ArithmeticPow ArithmeticPacking ArithmeticRepunit ArithmeticPellRecurrence ArithmeticPellHalfIndex
  ArithmeticOuterSeed
open Short15Graph Mixed121Kernel Mixed121ConstructedRank Mixed121Word Mixed121Column Mixed121Seeds
open P55Converse (cp0 cp1 cp2 cp3)
open P72ConvArith (k_large)
open P72Root (ι_tsub)
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
attribute [local irreducible] paramKernel rho Mixed121Ports.lowNat Mixed121Ports.highNat
  Mixed121Ports.betaNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The ports as integers. -/
abbrev intPorts : Fin 4 → ℤ := fun j => (Mixed121Ports.ports j : ℤ)

private theorem aux_gt {I w y : DiffRing V} (h : I * I * w * w + y * y = 1 + I * I * y * y)
    (hy : 2 ≤ y) (hw : 0 ≤ w) : w < y := by
  by_contra hlt
  have hle : y ≤ w := le_of_not_gt hlt
  have h1 : I * I * y * y ≤ I * I * w * w := by
    have := mul_le_mul hle hle (by linarith) hw
    nlinarith [mul_self_nonneg I]
  nlinarith

theorem canonical (T : V) (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0) :
    ∃ J F α z f h iH TH s w τ η ζ y wa γ ellM ΔM : V,
      0 < J ∧ 0 < F ∧ 0 < α ∧ 0 < z ∧ 0 < f ∧ 0 < h ∧ 0 < iH ∧ 0 < TH ∧ 0 < s ∧ 0 < w ∧
      0 < τ ∧ 0 < η ∧ 0 < ζ ∧ 0 < y ∧ wa < y ∧ 0 < γ ∧ 0 < ΔM ∧ ellM < τ ∧
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
  let u : V := 1064921 * N
  let R := rank K N stride Xf
  let q := Exp.exp u
  let wX := Exp.exp (R - u)
  obtain ⟨_, z, hz, hqw, htrv, sY, n, eta, zeta, gammaOld, hsY, _, he, hzz, hγ,
    hseed, _, haux, _, hgam⟩ := hresult
  obtain ⟨f, i, auxT, auxw, y, hf, hi, hTaux, _, hy, hfx, hyic, hstrong,
    hydef, _, _, _, _, hlit, _, hauxnorm, _, _, _, _, hnorm⟩ := haux
  obtain ⟨t, _, _, hk, _⟩ := hgam
  have hp : PackingInput 1064921 K low high N stride Xf := hpack
  -- the packing coordinates
  let Cv := Cw 1064921 N Xf
  let Fv := Fw 1064921 K N stride Xf
  let αv := alpha 1064921 K N stride Xf
  have hF : 0 < Fv := F_pos hp
  obtain ⟨hα, hsum⟩ := packing_alpha hp
  have hqsum : q = Fv + (Cv + αv) := by
    have h : q = Cv + Fv + αv := hsum.symm
    rw [h]; ring
  -- q = 1 + Jβ
  let J := rep 1064921 N
  let β : V := Exp.exp (1064921 : V) - 1
  have hq1 : 1 ≤ q := one_le_exp _
  have hqJ' : β * J + 1 = q := repunit_identity 1064921 N
  have hbetaD : ι J * ι β = ι (q - 1) := by
    rw [← map_mul, mul_comm, ← hqJ', add_tsub_cancel_right]
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
  have hN0 : 0 < N := power_pos _ _ (by norm_num)
  have hN1 : 1 ≤ N := pos_iff_one_le.mp hN0
  have hu1 : 1 ≤ u := le_trans hN1 (le_mul_of_one_le_left (Arithmetic.zero_le _) (by norm_num))
  have hq2 : 2 ≤ q := by
    have h := exp_monotone_le.mpr hu1
    have e1 : Exp.exp (1 : V) = 2 := by
      have := exp_succ (0 : V); rw [zero_add, exp_zero, mul_one] at this; exact this
    rwa [e1] at h
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq2
  have hq3c : 1 ≤ q ^ 3 := one_le_pow₀ (le_trans (by norm_num) hq2)
  have hY0 : 0 < Y := mul_pos hsY (lt_of_lt_of_le (by norm_num) hq3c)
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
  have ht4pos : 0 < t4 := by
    show 0 < q * q * wX * sY * s'
    exact mul_pos (mul_pos (mul_pos (mul_pos hq0 hq0) (lt_of_lt_of_le (by norm_num) hwX1)) hsY)
      (lt_of_lt_of_le (by norm_num) hs'1)
  -- the derived witnesses
  let u55 : V := y - auxw
  have hu55 : auxw + u55 = y := add_tsub_cancel_of_le (le_of_lt hwy)
  have hu55pos : 0 < u55 := tsub_pos_of_lt hwy
  have hJ0 : 0 < J := by
    rcases (Arithmetic.zero_le J).lt_or_eq with h | h
    · exact h
    · exfalso
      have hq' : q = 1 := by rw [← hqJ', ← h, mul_zero, zero_add]
      rw [hq'] at hq2
      exact absurd hq2 (by norm_num)
  have hwX0 : 0 < wX := lt_of_lt_of_le (by norm_num) hwX1
  let z55 : V := z + 1
  have hz55 : 0 < z55 := lt_of_lt_of_le (by simp) le_add_self
  let i55 : V := delta a * i
  have hi55 : 0 < i55 := by
    have hd : 0 < delta a := by
      unfold delta
      exact mul_pos (add_pos_of_nonneg_of_pos (Arithmetic.zero_le _) (by norm_num))
        (add_pos_of_nonneg_of_pos (Arithmetic.zero_le _) (by norm_num))
    exact mul_pos hd hi
  let γ55 : V := gammaOld + sY * q * t4
  have hγ55pos : 0 < γ55 :=
    add_pos_of_nonneg_of_pos (Arithmetic.zero_le _) (mul_pos (mul_pos hsY hq0) ht4pos)
  have hτ0 : 0 < τ := by
    rcases (Arithmetic.zero_le τ).lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, mul_zero] at hτn'
      exact absurd hτn'.symm (ne_of_gt (lt_of_lt_of_le _root_.zero_lt_one le_self_add))
  -- the valuation and its positivity
  let p : Fin 4 → ℤ := fun j => (Mixed121Ports.ports j : ℤ)
  have hιq : ι q = ι Fv + (ι Cv + ι αv) := by rw [hqsum]; simp [map_add]
  have hJβ : ι J * ι β = ι q - 1 := by rw [hbetaD]; exact ι_tsub hq1
  -- the rank, read from the packing
  have hFq : Fv ≤ q := le_of_lt (lt_of_lt_of_le (F_lt_M hp) tsub_le_self)
  have hRR : ((ι q - 1) * (ι q - ι Fv) + ι αv) * (ι q * ι q - 1) +
      (((p 2 : ℤ) : DiffRing V) + ι q * ((p 3 : ℤ) : DiffRing V)) * ι J = ι R := by
    rw [show ((p 2 : ℤ) : DiffRing V) = ι (low : V) from cp2,
      show ((p 3 : ℤ) : DiffRing V) = ι (high + (Exp.exp (1064921 : V) - 1)) from cp3]
    have hq2' : 1 ≤ q ^ 2 := one_le_pow₀ hq1
    change _ = ι (((q-1)*(q-Fv)+αv)*(q^2-1) + ((low:V)+q*(high+(Exp.exp (1064921:V)-1)))*J)
    simp only [map_add, map_mul, ι_tsub hq1, ι_tsub hFq, ι_tsub hq2', map_one, map_pow]
    ring
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
    rw [show ((p 1 : ℤ) : DiffRing V) = ι K from cp1]
    have h := congrArg ι htrv
    simp only [map_add, map_mul] at h
    rw [ι_tsub hq1, map_one] at h
    simp only [z55, map_add, map_one]
    linear_combination h + (ι K + ι wX) * hιq
  have ht4' : t = 4 * t4 := ht4
  have hkr : ι k = ι R + 1 + (4 * ((ι q * ι q) * (ι q * ι q))) * (ι sY * ι q * ι t4) := by
    have h := congrArg ι hkt
    rw [ht4'] at h
    simp only [Y, map_add, map_mul, map_one, map_pow, map_ofNat] at h
    linear_combination h
  have hγr : ι γ55 = ι gammaOld + ι sY * ι q * ι t4 := by simp only [γ55, map_add, map_mul]
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
  have hIval : Ival = ι i55 * (ι c * ι c) := by
    rw [hcyι]; simp only [Ival, i55, map_mul]; ring
  have hQI : (ι a * ι a + (4 * ι a + 3)) * (ι f * ι f - 1) = Ival * Ival := by
    rw [hιa']; linear_combination hIr
  have hs55 : (ι i55 * (ι c * ι c)) * (ι i55 * (ι c * ι c)) =
      (ι a * ι a + (4 * ι a + 3)) * (ι f * ι f - 1) := by rw [hQI, hIval]
  have hy' : ι auxw + ι u55 = ι y := by rw [← map_add, hu55]
  have haux55 : (ι a * ι a + (4 * ι a + 3)) * (ι f * ι f - 1) *
      (ι auxw * ι auxw - (ι auxw + ι u55) * (ι auxw + ι u55)) +
      (ι auxw + ι u55) * (ι auxw + ι u55) = 1 := by
    rw [hQI, hy']; linear_combination hauxr
  have hτr : ι τ * ι τ = ι ell * (ι ell + ι k) + 1 := by
    have h := congrArg ι hτn'
    simp only [map_add, map_mul, map_one] at h
    linear_combination h
  have hqm' : ι q - 1 = ((p 0 : ℤ) : DiffRing V) * ι J := by
    rw [show ((p 0 : ℤ) : DiffRing V) = ι (Exp.exp (1064921 : V) - 1) from cp0, ← hJβ]; ring
  have hXq' : ι Xv = ι wX * ι q := by rw [hX, map_mul]; ring
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
  have hellτ : ell < τ := by
    by_contra hle
    have h : τ ≤ ell := le_of_not_gt hle
    have h1 : τ * τ ≤ ell * ell := mul_le_mul h h (Arithmetic.zero_le _) (Arithmetic.zero_le _)
    have h2 : ell * ell ≤ ell * (ell + k) :=
      mul_le_mul_of_nonneg_left le_self_add (Arithmetic.zero_le _)
    rw [hτn'] at h1
    exact absurd (le_trans h1 h2) (not_le_of_gt (lt_add_of_pos_left _ (by norm_num)))
  have hnormr : ι f * ι f = 1 + (ι a * ι a + (4 * ι a + 3)) *
      ((ι i * (ι c * ι c)) * (ι i * (ι c * ι c))) := by
    rw [hcyι]
    have h := congrArg ι hstrong
    simp only [Xv, Y, E, k, c, a, ell, q, u, N, R] at h ⊢
    simp only [map_add, map_mul, map_one, delta, map_ofNat, map_pow] at h ⊢
    linear_combination h
  refine ⟨J, Fv, αv, z55, f, h15, i, auxT, sY, wX, τ, eta, zeta, y, auxw, gammaOld, ell, ΔM,
    hJ0, hF, hα, hz55, hf, hh15, hi, hTaux, hsY, hwX0, hτ0, he, hzz, hy, hwy, hγ, hΔM, hellτ, ?_⟩
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

end Short15ConvData

#print axioms Short15ConvData.canonical
