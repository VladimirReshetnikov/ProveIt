import DiophantineConsistency.P138.P138Bootstrap
import DiophantineConsistency.P138.P138Quarter
import DiophantineConsistency.P138.P138Cone
import DiophantineConsistency.Source34.Source34Converse
import DiophantineConsistency.ZRows.CoprimeSquares

/-! # Canonical data for the completeness of package 138 (stage C1, with C2's register form)

From an internal halt `first (run T) = 0` of machine 215, in every model `V` of `𝗜𝚺₁`, this module
builds one record `Canonical V` (`canonical`) holding every canonical quantity of the outer
source34 data that the final assembly (C8) needs, except the interpolation outputs.

## The intended assignment of the eleven unknowns (plan for C8)

The JSON variable order is `x 0 … x 10 = j C z h r v w T c n s`. The canonical record fixes

| unknown | value | defining register |
|---|---|---|
| `x 0 = j` | `ι j`, `J = rep 1064921 N = 6j + 1` | `J = 6x0 + 1`, `q = 1 + βJ` |
| `x 1 = C` | `ι C`, `C = Cw` (packed source word) | `F = (K0 + W) C − z(q−1)` |
| `x 2 = z` | `ι z`, the transport quotient | (same) |
| `x 3 = h` | `ι h`, `h = 4Y s'` | `k = R + 1 + hE` |
| `x 4 = r` | **interpolation**: `r = I/(A p0 c²)` | `U = A r c²`, `S = H r s` |
| `x 5 = v` | `ι v`, `sY = 2v + 1` | `Y = (2v+1) q³` |
| `x 6 = w` | `ι w`, `W = 2^(R−u) = 12w + 4` | `X = qW` |
| `x 7 = T` | **interpolation**: `T = T_old/p0` | `V`, `zc = K + T H` |
| `x 8 = c` | `ι c`, `c = ψ_a(R)` | `η = c − Yk`, `K = X(3c − 2X) + 2` |
| `x 9 = n` | **assembly**: `n = Ac/S + p0 f y` | `Z = nS − Ac` |
| `x 10 = s` | **guard** (`P138Guard`): `g² = 1 + D τ² s²` | `P = Dt(1 + D Dt s²)` |

`Matches Cn x` says that `x` takes the seven canonical values. Under it the registers that do not
involve `r, T, n, s` are the canonical ones (`reg_q … reg_K`): `q = 2^u`, `X = 2^R`, `R` the rank,
`k = 2ψ(r'+1)`, `η = c − kY`, `Dt = τ²`, `Dm = d²`, `K = Hκ`, and (C2, register form)
`2·Derr ≤ q²` (`canonical_derr`) and `q²k² < 4 Budget`, `64 < Budget` (`canonical_budget`).

## Parities (route C1)

* `J ≡ 1 (mod 6)`: `q = 2^u` with `u = 1064921 N`, `N = 2341^(2T+4)` odd, so `q ≡ 2 (mod 6)`,
  and `β ≡ 1 (mod 6)`;
* `W ≡ 4 (mod 12)`: `W = 2^(R−u)`, `R − u` even and `≥ 2`;
* `sY` odd: `2Y = binom(2r', r') + wX` (`ArithmeticHalfBinomial.half_binomial`) and the exact
  population `3u + 1` of `r'` (`R = 2r'+1`, `population R = 3u + 2`);
* `R ≡ 3 (mod 4)` (`Source34Seeds.properties`) and `c = ψ_a(R) ≡ 3 (mod 4)` (`ycoord_mod_four`:
  `ψ(4m+3) ≡ 3 (mod 4)` for every base);
* `H ∣ K`: `K = H κ` with `κ = Xc − 2c² + 2γ(d + X + ac)`, from `d = X + ac + γH` and
  `d² = 1 + Δ c²`.

`4η < k` is `P138Quarter.eta_quarter'`; the cone bounds are `P138Cone.cones`, with the cells
re-obtained from `Source34Word.halt_packed_word` (`tile_ne`) as the P138 risk audit requires. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
noncomputable section
namespace DiophantineConsistency.P138Canonical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing ZRowsCoprimeSquares P138Value P138Ports P138Bootstrap
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

/-! ## Small arithmetic -/

theorem affine_nat {A : V} {t : DiffRing V} (m r : V) (hr : r < m)
    (h : ι A = ι m * t + ι r) : ∃ j : V, A = m * j + r := by
  rcases int_split t with ht | ht
  · obtain ⟨j, rfl⟩ := nonneg_iff.mp ht
    exact ⟨j, ι_injective (by rw [h, map_add, map_mul])⟩
  · exfalso
    have hm : ι r < ι m := ι_lt_ι.mpr hr
    have hA := ι_nonneg A
    have hm0 : 0 ≤ ι m := ι_nonneg m
    have hr0 : 0 ≤ ι r := ι_nonneg r
    have := mul_le_mul_of_nonneg_left ht hm0
    linarith

theorem dvd_of_dvd_add {a b c : V} (h : a ∣ b + c) (hc : a ∣ c) : a ∣ b := by
  rw [← ι_dvd_iff] at h hc ⊢
  rw [map_add] at h
  have := dvd_sub h hc
  rwa [add_sub_cancel_right] at this

theorem exp_dvd_exp_of_le' {a b : V} (h : a ≤ b) : Exp.exp a ∣ Exp.exp b :=
  ⟨Exp.exp (b - a), by rw [← exp_add, add_tsub_cancel_of_le h]⟩

theorem power_odd (n : V) : ∃ m : V, power 2341 n = 2 * m + 1 := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => exact ⟨0, by simp⟩
  case succ n ih =>
    rw [power_succ]
    exact odd_mul ⟨1170, by norm_num⟩ ih

/-- `ψ(4m+3) ≡ 3 (mod 4)` at every base. -/
theorem ycoord_mod_four (m b : V) : ∃ t : V, ycoord (4*m+3) b = 4*t + 3 := by
  have hm := addition m m b
  have h2 := addition (2*m) (2*m) b
  have h3 := addition (4*m) 3 b
  rw [show m + m = 2*m by ring] at hm
  rw [show 2*m + 2*m = 4*m by ring] at h2
  have nm := norm m b
  have n2 := norm (2*m) b
  have hx1 : xcoord 1 b = b + 2 := by simpa using x_succ (0:V) b
  have hy1 : ycoord 1 b = 1 := by simpa using y_succ (0:V) b
  have hx2 := x_succ 1 b
  rw [show (1:V) + 1 = 2 by norm_num] at hx2
  have hy2 := y_succ 1 b
  rw [show (1:V) + 1 = 2 by norm_num] at hy2
  have hy3 := y_succ 2 b
  rw [show (2:V) + 1 = 3 by norm_num] at hy3
  have e := fun (u v : V) (h : u = v) => congrArg (ι (V := V)) h
  have Hm1 := e _ _ hm.1
  have Hm2 := e _ _ hm.2
  have H21 := e _ _ h2.1
  have H22 := e _ _ h2.2
  have H32 := e _ _ h3.2
  have Nm := e _ _ nm
  have N2 := e _ _ n2
  have X1 := e _ _ hx1
  have Y1 := e _ _ hy1
  have X2 := e _ _ hx2
  have Y2 := e _ _ hy2
  have Y3 := e _ _ hy3
  simp only [map_add, map_mul, map_one, map_ofNat, delta] at Hm1 Hm2 H21 H22 H32 Nm N2 X1 Y1 X2 Y2 Y3
  set xm := ι (xcoord m b); set ym := ι (ycoord m b)
  set x2 := ι (xcoord (2*m) b); set y2 := ι (ycoord (2*m) b)
  set x4 := ι (xcoord (4*m) b); set y4 := ι (ycoord (4*m) b)
  set B := ι b
  have hx2' : x2 = 2 * (xm * xm - 1) + 1 := by linear_combination Hm1 - Nm
  have hx4 : x4 = 4 * (2 * (xm * xm - 1) ^ 2 + 2 * (xm * xm - 1)) + 1 := by
    linear_combination H21 - N2 + (2 * x2 + 2 * (2 * (xm * xm - 1) + 1)) * hx2'
  have hy4 : y4 = 4 * (x2 * xm * ym) := by linear_combination H22 + 2 * x2 * Hm2
  have hy3' : ι (ycoord 3 b) = 4 * ((B + 2) ^ 2 - 1) + 3 := by
    linear_combination Y3 + X2 + (B + 2) * Y2 + (2 * (B + 2)) * X1 +
      ((B + 1) * (B + 3) + (B + 2) * (B + 2)) * Y1
  have hfin : ι (ycoord (4*m+3) b) = ι (4 : V) *
      ((2 * (xm * xm - 1) ^ 2 + 2 * (xm * xm - 1)) * (4 * ((B + 2) ^ 2 - 1) + 3) +
        ((B + 2) ^ 2 - 1) + x2 * xm * ym * ι (xcoord 3 b)) + ι 3 := by
    rw [map_ofNat, map_ofNat]
    linear_combination H32 + (ι (ycoord 3 b)) * hx4 +
      (4 * (2 * (xm * xm - 1) ^ 2 + 2 * (xm * xm - 1)) + 1) * hy3' + ι (xcoord 3 b) * hy4
  exact affine_nat 4 3 (by norm_num) hfin

/-! ## The record -/

/-- **The canonical data** of an internal halt, at the source34 ports of package 138. -/
structure Canonical (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] where
  /-- the seven canonical unknowns `x 0, x 1, x 2, x 3, x 5, x 6, x 8` -/
  j : V
  C : V
  z : V
  h : V
  v : V
  w : V
  c : V
  /-- derived canonical quantities -/
  J : V
  q : V
  W : V
  X : V
  Y : V
  E : V
  a : V
  F : V
  α : V
  R : V
  r : V
  k : V
  η : V
  ζ : V
  τ : V
  d : V
  γ : V
  κ : DiffRing V
  J_eq : J = 6 * j + 1
  q_reg : ι q = portsR 0 * ι J + 1
  q_ge : 16 ≤ q
  W_eq : W = 12 * w + 4
  X_eq : X = q * W
  X_exp : X = Exp.exp R
  Y_eq : Y = (2 * v + 1) * q ^ 3
  E_eq : E = X * Y
  a_eq : a = E + Y
  F_reg : ι F = (portsR 1 + ι W) * ι C - ι z * (ι q - 1)
  q_split : q = F + (C + α)
  F_pos : 0 < F
  C_pos : 0 < C
  α_pos : 0 < α
  z_pos : 0 < z
  R_reg : ι R = (ι q * (ι q - ι F) - ι C) * (ι q ^ 2 - 1) + (portsR 2 + ι q * portsR 3) * ι J
  R_odd : R = 2 * r + 1
  R_mod : ∃ m : V, R = 4 * m + 3
  r_ge : 6 ≤ r
  k_eq : k = R + 1 + h * E
  h_pos : 0 < h
  k_first : k = 2 * ycoord (r + 1) (2 * (X * Y * Y - 1) + 1)
  τ_first : τ = xcoord (r + 1) (2 * (X * Y * Y - 1) + 1)
  τ_norm : τ * τ = 1 + (X * Y * Y) * (X * Y * Y + 1) * k * k
  c_main : c = ycoord R a
  d_main : d = xcoord R a
  d_norm : d * d = 1 + (a + 1) * (a + 3) * c * c
  d_split : d = X + a * c + γ * (4 * a + 3)
  c_mod : ∃ m : V, c = 4 * m + 3
  c_eta : c = k * Y + η
  k_split : k = η + ζ
  η_pos : 0 < η
  ζ_pos : 0 < ζ
  eta_quarter : 4 * η < k
  K_split : ι X * (3 * ι c - 2 * ι X) + 2 = (4 * ι a + 3) * κ
  cone_F : q ≤ 2 * (Exp.exp 1113 * F) ∧ 2 * (Exp.exp 1113 * F) ≤ 3 * q
  cone_C : q ≤ 2 * (C * Exp.exp 666104) ∧ 2 * (C * Exp.exp 666104) ≤ 3 * q

/-! ## The ports, read at the source34 tuple -/

theorem port0 : portsR (V := V) 0 = ι (Exp.exp (1064921 : V) - 1) := by
  rw [show portsR (V := V) 0 = (((Source34Ports.ports 0 : ℕ) : ℤ) : DiffRing V) by
    unfold portsR ports6; rw [vec6_zero]]
  exact Source34Converse.cp0

theorem port1 : portsR (V := V) 1 = ι ((paramKernel rho : ℕ) : V) := by
  rw [show portsR (V := V) 1 = (((Source34Ports.ports 1 : ℕ) : ℤ) : DiffRing V) by
    unfold portsR ports6; rw [vec6_one]]
  exact Source34Converse.cp1

theorem port2 : portsR (V := V) 2 = ι (low : V) := by
  rw [show portsR (V := V) 2 = (((Source34Ports.ports 2 : ℕ) : ℤ) : DiffRing V) by
    unfold portsR ports6; rw [vec6_two]]
  exact Source34Converse.cp2

theorem port3 : portsR (V := V) 3 = ι (high + (Exp.exp (1064921 : V) - 1)) := by
  rw [show portsR (V := V) 3 = (((Source34Ports.ports 3 : ℕ) : ℤ) : DiffRing V) by
    unfold portsR ports6; rw [vec6_three]]
  exact Source34Converse.cp3

/-! ## Construction -/

/-- **C1.** An internal halt gives the canonical data. -/
theorem canonical (T : V) (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0) :
    Nonempty (Canonical V) := by
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
  refine ⟨{
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
    cone_F := ⟨hc1, hc2⟩, cone_C := ⟨hc3, hc4⟩ }⟩

/-! ## The registers at the canonical point -/

/-- `x` takes the seven canonical values. -/
structure Matches (Cn : Canonical V) (x : Fin 11 → DiffRing V) : Prop where
  x0 : x 0 = ι Cn.j
  x1 : x 1 = ι Cn.C
  x2 : x 2 = ι Cn.z
  x3 : x 3 = ι Cn.h
  x5 : x 5 = ι Cn.v
  x6 : x 6 = ι Cn.w
  x8 : x 8 = ι Cn.c

/-- Four times a squared cone deviation is at most `q²`. -/
theorem sq_dev {U Q : DiffRing V} (h1 : Q ≤ 2 * U) (h2 : 2 * U ≤ 3 * Q) : 4 * (U - Q) ^ 2 ≤ Q ^ 2 := by
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)]

section Registers
variable (Cn : Canonical V) {x : Fin 11 → DiffRing V} (hx : Matches Cn x)
local notation "𝓡" => regs (portsR (V := V)) x
include hx

theorem reg_J : (𝓡).J = ι Cn.J := by
  rw [J_def, hx.x0, Cn.J_eq]; simp only [map_add, map_mul, map_ofNat, map_one]; ring

theorem reg_q : (𝓡).q = ι Cn.q := by
  rw [q_eq, hx.x0, Cn.q_reg, Cn.J_eq]; simp only [map_add, map_mul, map_ofNat, map_one]

theorem reg_W : (𝓡).W = ι Cn.W := by
  rw [W_eq, hx.x6, Cn.W_eq]; simp only [map_add, map_mul, map_ofNat]

theorem reg_X : (𝓡).X = ι Cn.X := by
  rw [X_def, reg_q Cn hx, reg_W Cn hx, Cn.X_eq, map_mul]

theorem reg_Y : (𝓡).Y = ι Cn.Y := by
  rw [Y_eq, hx.x5, reg_q Cn hx, Cn.Y_eq]; simp only [map_add, map_mul, map_ofNat, map_one, map_pow]

theorem reg_E : (𝓡).E = ι Cn.E := by
  rw [E_def, reg_X Cn hx, reg_Y Cn hx, Cn.E_eq, map_mul]

theorem reg_a : (𝓡).a = ι Cn.a := by
  rw [a_def, reg_E Cn hx, reg_Y Cn hx, Cn.a_eq, map_add, add_comm]

theorem reg_A : (𝓡).A = ι Cn.a + 2 := by rw [A_eq, reg_a Cn hx]

theorem reg_H : (𝓡).H = 4 * ι Cn.a + 3 := by rw [H_eq, reg_a Cn hx]

theorem reg_Delta : (𝓡).Delta = (ι Cn.a + 1) * (ι Cn.a + 3) := by
  rw [Delta_eq, reg_A Cn hx]; ring

theorem reg_F : (𝓡).F = ι Cn.F := by
  rw [F_eq, hx.x1, hx.x2, reg_W Cn hx, reg_q Cn hx, Cn.F_reg]

theorem reg_R : (𝓡).R = ι Cn.R := by
  rw [R_eq, reg_q Cn hx, reg_F Cn hx, hx.x1, reg_J Cn hx, Cn.R_reg]

theorem reg_k : (𝓡).k = ι Cn.k := by
  rw [k_eq, reg_R Cn hx, hx.x3, reg_E Cn hx, Cn.k_eq]; simp only [map_add, map_mul, map_one]

theorem reg_eta : (𝓡).eta = ι Cn.η := by
  rw [eta_eq, hx.x8, reg_Y Cn hx, reg_k Cn hx, Cn.c_eta]; simp only [map_add, map_mul]; ring

theorem reg_Dt : (𝓡).Dt = ι Cn.τ * ι Cn.τ := by
  rw [Dt_eq, reg_X Cn hx, reg_Y Cn hx, reg_k Cn hx,
    show ι Cn.τ * ι Cn.τ = ι (Cn.τ * Cn.τ) from (map_mul _ _ _).symm, Cn.τ_norm]
  simp only [map_add, map_mul, map_one]; ring

theorem reg_Dm : (𝓡).Dm = ι Cn.d * ι Cn.d := by
  rw [Dm_eq, reg_Delta Cn hx, hx.x8,
    show ι Cn.d * ι Cn.d = ι (Cn.d * Cn.d) from (map_mul _ _ _).symm, Cn.d_norm]
  simp only [map_add, map_mul, map_one, map_ofNat]; ring

theorem reg_K : (𝓡).K = (𝓡).H * Cn.κ := by
  rw [K_eq, reg_X Cn hx, hx.x8, reg_H Cn hx, ← Cn.K_split]

/-- **C2, `canonical_derr`.** -/
theorem canonical_derr : 2 * (𝓡).Derr ≤ (𝓡).q ^ 2 := by
  have hU1 : ι Cn.q ≤ 2 * (portsR 4 * ι Cn.F) := by
    rw [p4_exp, ← map_mul, show (2 : DiffRing V) = ι 2 by rw [map_ofNat], ← map_mul]
    exact ι_le_ι.mpr Cn.cone_F.1
  have hU2 : 2 * (portsR 4 * ι Cn.F) ≤ 3 * ι Cn.q := by
    rw [p4_exp, ← map_mul, show (2 : DiffRing V) = ι 2 by rw [map_ofNat], ← map_mul,
      show (3 : DiffRing V) = ι 3 by rw [map_ofNat], ← map_mul]
    exact ι_le_ι.mpr Cn.cone_F.2
  have hV1 : ι Cn.q ≤ 2 * (portsR 5 * ι Cn.C) := by
    rw [p5_exp, ← map_mul, show (2 : DiffRing V) = ι 2 by rw [map_ofNat], ← map_mul, mul_comm (Exp.exp _)]
    exact ι_le_ι.mpr Cn.cone_C.1
  have hV2 : 2 * (portsR 5 * ι Cn.C) ≤ 3 * ι Cn.q := by
    rw [p5_exp, ← map_mul, show (2 : DiffRing V) = ι 2 by rw [map_ofNat], ← map_mul,
      show (3 : DiffRing V) = ι 3 by rw [map_ofNat], ← map_mul, mul_comm (Exp.exp _)]
    exact ι_le_ι.mpr Cn.cone_C.2
  have h1 := sq_dev hU1 hU2
  have h2 := sq_dev hV1 hV2
  rw [Derr_eq, reg_F Cn hx, reg_q Cn hx, hx.x1]
  nlinarith

/-- **C2, `canonical_budget`.** -/
theorem canonical_budget : (𝓡).q ^ 2 * (𝓡).k ^ 2 < 4 * (𝓡).Budget ∧ 64 < (𝓡).Budget := by
  have hD := canonical_derr Cn hx
  rw [reg_q Cn hx] at hD
  have hη : 4 * ι Cn.η < ι Cn.k := by
    rw [show (4 : DiffRing V) = ι 4 by rw [map_ofNat], ← map_mul]; exact ι_lt_ι.mpr Cn.eta_quarter
  have hη0 : 0 ≤ ι Cn.η := ι_nonneg _
  have hq16 : (16 : DiffRing V) ≤ ι Cn.q := by
    rw [show (16 : DiffRing V) = ι 16 by rw [map_ofNat]]; exact ι_le_ι.mpr Cn.q_ge
  have hk1 : (1 : DiffRing V) ≤ ι Cn.k := by
    have h1 : (1 : V) ≤ Cn.k := by
      rw [Cn.k_eq]
      exact le_add_of_le_of_nonneg (le_add_of_nonneg_left (Arithmetic.zero_le _))
        (Arithmetic.zero_le _)
    rw [← map_one ι]
    exact ι_le_ι.mpr h1
  rw [Budget_eq, reg_q Cn hx, reg_k Cn hx, reg_eta Cn hx]
  have h1 : ι Cn.k ^ 2 * (2 * (𝓡).Derr) ≤ ι Cn.k ^ 2 * ι Cn.q ^ 2 :=
    mul_le_mul_of_nonneg_left hD (sq_nonneg _)
  have h2 : (4 * ι Cn.η) ^ 2 < ι Cn.k ^ 2 := by nlinarith
  have hQ2 : 0 < ι Cn.q ^ 2 := pow_pos (by linarith) 2
  have h3 : ι Cn.q ^ 2 * (4 * ι Cn.η) ^ 2 < ι Cn.q ^ 2 * ι Cn.k ^ 2 :=
    mul_lt_mul_of_pos_left h2 hQ2
  have hmain : ι Cn.q ^ 2 * ι Cn.k ^ 2 <
      4 * (ι Cn.k ^ 2 * (ι Cn.q ^ 2 - (𝓡).Derr) - 4 * ι Cn.q ^ 2 * ι Cn.η ^ 2) := by
    nlinarith
  refine ⟨hmain, ?_⟩
  have hQK : (16 : DiffRing V) * 1 ≤ ι Cn.q * ι Cn.k :=
    mul_le_mul hq16 hk1 (by norm_num) (by linarith)
  have h256 : (256 : DiffRing V) ≤ ι Cn.q ^ 2 * ι Cn.k ^ 2 := by
    calc (256 : DiffRing V) = (16 * 1) * (16 * 1) := by norm_num
      _ ≤ (ι Cn.q * ι Cn.k) * (ι Cn.q * ι Cn.k) :=
          mul_le_mul hQK hQK (by norm_num) (by linarith)
      _ = ι Cn.q ^ 2 * ι Cn.k ^ 2 := by ring
  linarith

end Registers

#print axioms affine_nat
#print axioms power_odd
#print axioms ycoord_mod_four
#print axioms port0
#print axioms canonical
#print axioms reg_R
#print axioms reg_Dt
#print axioms reg_Dm
#print axioms reg_K
#print axioms canonical_derr
#print axioms canonical_budget

end DiophantineConsistency.P138Canonical
