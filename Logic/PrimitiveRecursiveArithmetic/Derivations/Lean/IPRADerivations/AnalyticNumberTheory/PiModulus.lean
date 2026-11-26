import IPRADerivations.AnalyticNumberTheory.PiAlg
import IPRADerivations.Core.Header

/-!
# Prime counting with an explicit modulus (`pnt_ipra_constructive_2026-11-14`, eq:pi-error)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `pnt_ipra.tex`, Lemma `lem:pi-conversion` and
(eq:pi-quarter): "`|π(x) log x / x − 1| ≤ 1/q + 24 log x/√x + 16/log x`". With the logarithm the harmonic
logarithm `u_x` at the mesh `K = (x + 1)⁴` over `F = L!` of `PsiModulus`, `q = p + 1`, and every `x` with
`x ≥ 2^{s_J}` and `ℓ(x) ≥ 131136 q³` (`ℓ = λ(x) − 1`, `2^ℓ < x ≤ 2^{ℓ+1}`):

  `q F x ≤ q π(x) u_x + 3 F x`  and  `q π(x) u_x ≤ q F x + 4 F x`   (`pi_modulus`),

i.e. `|π(x) u_x / (F x) − 1| ≤ 4/q`. The cut points are powers of two chosen from `ℓ`:
`r = 2^{ℓ − ⌊ℓ/2⌋ + 1}` (`r ≤ x < (r+1)²`, the prime powers), `Y = 2^{ℓ − σ}`, `σ = ⌊ℓ/(64q)⌋` (the
summation by parts), and the conditions `C1–C3` of `PiAlg` follow from `512 q² (σ + 1) ≤ 2^σ`
(`PiAlg.pow_growth`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.PiModulus

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicChebyshev (wt psi_le)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicMertens (le_scale)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicLogSquareSum (U)
open LeanProofs.IPRA.AnalyticNumberTheory.BlockChain (one_le_pw' u_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.OneStepDecrement (u_pow u_shift u_low monus_le_of)
open LeanProofs.IPRA.AnalyticNumberTheory.StepParams (ell muP clog_pos clog_bracket)
open LeanProofs.IPRA.AnalyticNumberTheory.StageAdvance (p4_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.StageInduction (Aj Amin Jst sT s_ge)
open LeanProofs.IPRA.AnalyticNumberTheory.PsiModulus (Kx Lx le_fact aJ_le psi_modulus)
open LeanProofs.IPRA.AnalyticNumberTheory.PiTheta (Pi Theta theta_le_psi theta_le_pi pi_upper pi_cheb)
open LeanProofs.IPRA.AnalyticNumberTheory.PsiTheta (psi_theta)
open LeanProofs.IPRA.AnalyticNumberTheory.PiAlg (pi_lower_alg pi_cheb_alg pi_tail_alg pi_upper_alg pow_growth)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTThresholds (Dq Q3)
open LeanProofs.IPRA.AnalyticNumberTheory.AbsDiff (absd le_absd_l le_absd_r)
open LeanProofs.IPRA.AnalyticNumberTheory.LcmUpto (Psi)
open LeanProofs.IPRA.AnalyticNumberTheory.FourthRootSum (Q4)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le cancel_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerCleared (pw_le_exp)
open LeanProofs.IPRA.Analysis.Products (fact)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The cut exponents -/

/-- `σ = ⌊ℓ/(64q)⌋`. -/
abbrev sgm (p x : PTm n) : PTm n := quo (ell x) (num 64 * succ p)

theorem p2 : Γ ⊢[PRAAx] (two : PTm n) ≐ succ (pred two) := pos_of_one_le (le_succ_self one)

/-- The growth facts of the cut exponent from `ℓ ≥ 131136 q³`. -/
theorem sgm_facts {p x : PTm n} (hl : Γ ⊢[PRAAx] le (num 131136 * Q3 p) (ell x)) :
    Γ ⊢[PRAAx] le (num 8 * (succ p * succ (ell x))) (pw two (sgm p x)) ⋏
      (le (num 16 * (succ p * succ (sgm p x)) + one) (monus (ell x) (sgm p x)) ⋏
        (le (sgm p x) (muP x) ⋏ le one (sgm p x))) := by
  have dm := div_mod_at (Γ := Γ) (x := ell x) (y := num 64 * succ p) (c := num 63 + num 64 * p)
    (by ipra_ring)
  have e := natEq (Prf.andE₁ dm)
  have r := Prf.andE₂ dm
  have hq : Γ ⊢[PRAAx] le (num 64 * succ p * (num 2048 * (succ p * succ p))) (num 64 * succ p * sgm p x) := by
    ipra_le sl hl + sl r + 64 * (𝔞 p + 1) * 𝔞 p * (𝔞 p + 2) + 1 with e
  have hs := cancel_pos (by ipra_le 64 * 𝔞 p + 63) hq
  have pg := pow_growth (c := num 512 * (succ p * succ p)) (s := sgm p x) (by ipra_le sl hs)
  have h1 : Γ ⊢[PRAAx] le one (sgm p x) := le_trans (by ipra_le 2048 * 𝔞 p * 𝔞 p + 4096 * 𝔞 p + 2047) hs
  have hsl : Γ ⊢[PRAAx] le (sgm p x) (ell x) := by
    ipra_le (64 * 𝔞 p + 63) * 𝔞 (sgm p x) + 𝔞 (rem (ell x) (num 64 * succ p)) with e
  have f := natEq (eq_add_of_le hsl)
  have d2 := div_mod_at (Γ := Γ) (x := ell x) (y := two) (c := one) (.eqRefl _)
  have e2 := natEq (Prf.andE₁ d2)
  have r2 := Prf.andE₂ d2
  have hsm2 : Γ ⊢[PRAAx] le (two * (two * sgm p x)) (two * succ (muP x)) := by
    ipra_le sl r2 + (64 * 𝔞 p + 60) * 𝔞 (sgm p x) + 𝔞 (rem (ell x) (num 64 * succ p)) + 1 with e - e2
  have hsm := mul_le_cancel (d' := one) hsm2
  refine .andI ?_ (.andI ?_ (.andI ?_ h1))
  · ipra_le sl pg + 8 * (𝔞 p + 1) * sl r with 8 * (𝔞 p + 1) * e
  · ipra_le (48 * 𝔞 p + 47) * sl h1 + 32 * 𝔞 p + 30 + 𝔞 (rem (ell x) (num 64 * succ p)) with e - f
  · ipra_le sl hsm + sl h1

/-- Prime counting at the harmonic logarithm: `|π(x) u_x − Fx| ≤ 4Fx/q`. -/
theorem pi_modulus {p x : PTm n} (hx : Γ ⊢[PRAAx] le (pw two (sT (Jst p) (Dq p))) x)
    (hl : Γ ⊢[PRAAx] le (num 131136 * Q3 p) (ell x)) :
    Γ ⊢[PRAAx] le (succ p * (fact (Lx x) * x))
        (succ p * (U x (Kx x) (fact (Lx x)) * Pi x (pairT (Kx x) (fact (Lx x)))) + num 3 * (fact (Lx x) * x)) ⋏
      le (succ p * (U x (Kx x) (fact (Lx x)) * Pi x (pairT (Kx x) (fact (Lx x)))))
        (succ p * (fact (Lx x) * x) + num 4 * (fact (Lx x) * x)) := by
  -- the exponents
  have sf := sgm_facts hl
  have hG := Prf.andE₁ sf
  have hC2 := Prf.andE₁ (Prf.andE₂ sf)
  have hσμ := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ sf))
  have hσ1 := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ sf))
  have hs1 : Γ ⊢[PRAAx] le one (sT (Jst p) (Dq p)) :=
    le_trans (by ipra_le 1048576 * (𝔞 p + 1) ^ 3 + 1599) (s_ge _ _)
  have h2x : Γ ⊢[PRAAx] le two x := le_trans (le_congr (pw_one two) (.eqRefl _) (pw_le_exp p2 hs1)) hx
  have hx1 : Γ ⊢[PRAAx] le one x := le_trans (le_succ_self one) h2x
  have br := clog_bracket h2x
  have hlt := Prf.andE₁ br
  have hle := Prf.andE₂ br
  have hlx := le_of_lt hlt
  have d2 := div_mod_at (Γ := Γ) (x := ell x) (y := two) (c := one) (.eqRefl _)
  have e2 := natEq (Prf.andE₁ d2)
  have hμl : Γ ⊢[PRAAx] le (muP x) (ell x) := by ipra_le 𝔞 (muP x) + 𝔞 (rem (ell x) two) with e2
  have em := natEq (eq_add_of_le hμl)
  have hsl := le_trans hσμ hμl
  have ew := natEq (eq_add_of_le hsl)
  -- the cut `Y = 2^{ℓ − σ}`
  have eY : Γ ⊢[PRAAx] pw two (monus (ell x) (sgm p x)) * pw two (sgm p x) ≐ pw two (ell x) :=
    (pw_add two _ _).eqSymm.eqTrans (congrAp2 powF (by apply deriveNat; ipra_simps; linear_combination -ew)
      (.eqRefl two))
  have eY1 : Γ ⊢[PRAAx] pw two (monus (ell x) (sgm p x)) * pw two (succ (sgm p x)) ≐ pw two (succ (ell x)) := by
    have a := natEq (pw_succ (Γ := Γ) two (sgm p x))
    have b := natEq (pw_succ (Γ := Γ) two (ell x))
    have c := natEq eY
    apply deriveNat; ipra_simps
    linear_combination 𝔞 (pw two (monus (ell x) (sgm p x))) * a - b + 2 * c
  have hY1 : Γ ⊢[PRAAx] le one (pw two (monus (ell x) (sgm p x))) := one_le_pw' (le_succ_self one) _
  have hYl : Γ ⊢[PRAAx] le (pw two (monus (ell x) (sgm p x))) (pw two (ell x)) := by
    have q := le_scale (pw two (monus (ell x) (sgm p x))) (one_le_pw' (Γ := Γ) (le_succ_self one) (sgm p x))
    have c := natEq eY
    ipra_le sl q with c
  have hYx := le_trans hYl hlx
  -- the cut `r = 2^{ℓ − μ + 1}`
  have hmm : Γ ⊢[PRAAx] le (muP x) (monus (ell x) (muP x)) := by
    ipra_le 𝔞 (rem (ell x) two) with e2 - em
  have hr2 : Γ ⊢[PRAAx] le (succ (ell x)) (succ (monus (ell x) (muP x)) + succ (monus (ell x) (muP x))) := by
    ipra_le sl hmm + 1 with em
  have er : Γ ⊢[PRAAx] pw two (succ (monus (ell x) (muP x)) + succ (monus (ell x) (muP x))) ≐
      pw two (succ (monus (ell x) (muP x))) * pw two (succ (monus (ell x) (muP x))) := pw_add two _ _
  have hxr : Γ ⊢[PRAAx] le x (pw two (succ (monus (ell x) (muP x))) * pw two (succ (monus (ell x) (muP x)))) :=
    le_trans hle (le_congr (.eqRefl _) er (pw_le_exp p2 hr2))
  have hrr : Γ ⊢[PRAAx] lt x (succ (pw two (succ (monus (ell x) (muP x)))) * succ (pw two (succ (monus (ell x) (muP x))))) := by
    ipra_le sl hxr + 2 * 𝔞 (pw two (succ (monus (ell x) (muP x))))
  have hμ1 := le_trans hσ1 hσμ
  have hrl : Γ ⊢[PRAAx] le (succ (monus (ell x) (muP x))) (ell x) := by ipra_le sl hμ1 with em
  have hrx := le_trans (pw_le_exp p2 hrl) hlx
  have hxL : Γ ⊢[PRAAx] lt x (pw two (succ (succ (ell x)))) := by
    have a := natEq (pw_succ (Γ := Γ) two (succ (ell x)))
    have b := one_le_pw' (Γ := Γ) (le_succ_self one) (succ (ell x))
    ipra_le sl hle + sl b with a
  -- sizes
  have hK1 : Γ ⊢[PRAAx] le one (Kx x) := by ipra_le 𝔞 x ^ 4 + 4 * 𝔞 x ^ 3 + 6 * 𝔞 x ^ 2 + 4 * 𝔞 x
  have hLf := le_fact (Γ := Γ) (Lx x)
  have hPx : Γ ⊢[PRAAx] le (Kx x * pw two (two * (two * x))) (Lx x) := by
    ipra_le (𝔞 x + 1) ^ 4 * ((𝔞 x + 1) ^ 4 + 𝔞 (pw x x))
  have h2KF : Γ ⊢[PRAAx] le (two * (Kx x * x)) (fact (Lx x)) := by
    have a := le_scale (Kx x) (show Γ ⊢[PRAAx] le (two * x) (Q4 x) by
      ipra_le 𝔞 x ^ 4 + 4 * 𝔞 x ^ 3 + 6 * 𝔞 x ^ 2 + 2 * 𝔞 x + 1)
    exact le_trans (by ipra_le sl a + (𝔞 x + 1) ^ 4 * (𝔞 (pw two (two * (two * x))) + 𝔞 (pw x x))) hLf
  have hD1 : Γ ⊢[PRAAx] le one (Dq p) := by
    ipra_le 1048576 * 𝔞 p ^ 3 + 3145728 * 𝔞 p ^ 2 + 3145728 * 𝔞 p + 1048575
  have hq1 : Γ ⊢[PRAAx] le one (succ p) := by ipra_le 𝔞 p
  have hqA : Γ ⊢[PRAAx] le (succ p * Aj (Jst p) (Dq p)) (two * Dq p) := by
    have a := le_scale (succ p) (aJ_le (Γ := Γ) p)
    ipra_le sl a + 1048576 * 𝔞 p ^ 3 + 3145728 * 𝔞 p ^ 2 + 3145726 * 𝔞 p + 1048574
  -- the psi bounds
  have pm := psi_modulus hx
  have hP : Γ ⊢[PRAAx] le (Dq p * (fact (Lx x) * x))
      (Dq p * Psi wt x (pairT (Kx x) (fact (Lx x))) + Aj (Jst p) (Dq p) * (fact (Lx x) * x)) := by
    have a := le_scale (Dq p) (le_absd_r (Γ := Γ) (Psi wt x (pairT (Kx x) (fact (Lx x)))) (fact (Lx x) * x))
    ipra_le sl a + sl pm
  have hP2 : Γ ⊢[PRAAx] le (Dq p * Psi wt x (pairT (Kx x) (fact (Lx x))))
      (Dq p * (fact (Lx x) * x) + Aj (Jst p) (Dq p) * (fact (Lx x) * x)) := by
    have a := le_scale (Dq p) (le_absd_l (Γ := Γ) (Psi wt x (pairT (Kx x) (fact (Lx x)))) (fact (Lx x) * x))
    ipra_le sl a + sl pm
  have hψ4 : Γ ⊢[PRAAx] le (Psi wt x (pairT (Kx x) (fact (Lx x)))) (num 4 * (x * fact (Lx x))) :=
    le_trans (psi_le hK1 hPx) (by ipra_le 0)
  -- the lower bound
  have hT := psi_theta (K := Kx x) (F := fact (Lx x)) (L := succ (ell x)) hrx hrr hxL
  have hTr : Γ ⊢[PRAAx] le (Theta (pw two (succ (monus (ell x) (muP x)))) (pairT (Kx x) (fact (Lx x))))
      (num 4 * (pw two (succ (monus (ell x) (muP x))) * fact (Lx x))) :=
    le_trans (theta_le_psi _ _) (le_trans (psi_le hK1 (le_trans (le_scale _ (p4_mono hrx)) hPx)) (by ipra_le 0))
  have hC1 : Γ ⊢[PRAAx] le (num 4 * (succ p * (succ (ell x) * pw two (succ (monus (ell x) (muP x)))))) x := by
    have a := le_scale (pw two (monus (ell x) (muP x))) hG
    have b := le_scale (pw two (monus (ell x) (muP x))) (pw_le_exp p2 hσμ)
    have c := natEq (pw_succ (Γ := Γ) two (monus (ell x) (muP x)))
    have d0 : Γ ⊢[PRAAx] pw two (muP x) * pw two (monus (ell x) (muP x)) ≐ pw two (ell x) :=
      (pw_add (Γ := Γ) two (muP x) (monus (ell x) (muP x))).eqSymm.eqTrans
        (congrAp2 powF (by apply deriveNat; ipra_simps; linear_combination -em) (.eqRefl two))
    have d := natEq d0
    ipra_le sl a + sl b + sl hlx with 4 * (𝔞 p + 1) * (𝔞 (ell x) + 1) * c + d
  have lower := pi_lower_alg hP hT hTr (theta_le_pi _ _ _) hqA hC1 hD1
  -- the upper bound
  have hU := pi_upper (K := Kx x) (F := fact (Lx x)) hYx
  have hmb : Γ ⊢[PRAAx] le (monus (U x (Kx x) (fact (Lx x))) (U (pw two (monus (ell x) (sgm p x))) (Kx x) (fact (Lx x))))
      (succ (sgm p x) * fact (Lx x)) :=
    monus_le_of (le_trans (u_mono _ _ (le_congr (.eqRefl _) eY1.eqSymm hle)) (u_shift _ _ hY1)) (u_mono _ _ hYx)
  have huY := u_low (K := Kx x) (F := fact (Lx x)) (monus (ell x) (sgm p x)) hK1 (by
    have a := le_scale (two * Kx x) hYx
    ipra_le sl a + sl h2KF)
  have hCh := pi_cheb (K := Kx x) (F := fact (Lx x)) hYx
  have hu : Γ ⊢[PRAAx] le (U x (Kx x) (fact (Lx x))) (succ (ell x) * fact (Lx x)) :=
    le_trans (u_mono _ _ hle) (u_pow _ _ _)
  have a := pi_cheb_alg huY hCh (theta_le_psi _ _) hψ4 (le_trans (u_mono _ _ hYx) hu)
  have b := pi_tail_alg a hC2
  have hC3 : Γ ⊢[PRAAx] le (num 4 * (succ p * (succ (pw two (monus (ell x) (sgm p x))) * succ (ell x)))) x := by
    have a := le_scale (pw two (monus (ell x) (sgm p x))) hG
    have c := natEq eY
    ipra_le sl a + sl hlx + 4 * (𝔞 p + 1) * (𝔞 (ell x) + 1) * sl hY1 with c
  have upper := pi_upper_alg hP2 hU hmb (theta_le_psi _ _) b hu hqA hC3 hq1 hD1
  exact .andI lower upper

end LeanProofs.IPRA.AnalyticNumberTheory.PiModulus
