import IPRADerivations.AnalyticNumberTheory.MobiusSummatory
import IPRADerivations.AnalyticNumberTheory.TauAbelIdentity

/-!
# The three comparison inversions (`pnt_ipra_constructive_2026-11-14`, `sb:comparison-convolution`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `selberg.tex`, proof of Lemma `sb:symmetry`:
"`𝒟τ = 2L * 𝟏`. With the finite parameter `c` … `μ * f = 2L − 2c𝟏 + 4c²ε`" for
`f = τ L − 2c τ + 4c²` (`sb:comparison-function`). Rather than proving linearity of the convolution, the summed
form `Σ_{d≤x} μ(d) B_f(x/d)` is assembled from three instances of the summed Möbius inversion
`MobiusSummatory.mobius_summatory` (`Σ_d μ(d) B_g(⌊x/d⌋) = Σ_{n≤x} g(n)`, `B_g(m) = Σ_{k≤m} (g * 𝟏)(k)`),
one for each of `g = L_w`, `g = 𝟏` and `g = ε`. This module evaluates the six finite sums those instances produce:

* `tau_bs`: `B_𝟏(m) = Σ_{k≤m} τ(k) = D(m)`;
* `conv_eps`, `eps_bs`: `(ε * 𝟏)(k) = 1` for `k ≥ 1`, hence `B_ε(m) = m`;
* `tw_bs`: `Σ_{k≤m} τ(k) L_w(k) = 2 B_{L_w}(m)` (`DivisorSwapP.tau_lw`, i.e. `𝒟τ = 2 L * 𝟏`);
* `sum_sg_one`: `Σ_{1≤n≤x} 𝟏(n) = x`; `sum_sg_eps`: `Σ_{1≤n≤x} ε(n) = 1` for `x ≥ 1`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.SymmetryInstances

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (congrSg zero_mul_l congrEqb' one_inst)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicChebyshev (wt)
open LeanProofs.IPRA.AnalyticNumberTheory.DirichletLeibniz (cvB conv cv_at DwB inst2_cvB)
open LeanProofs.IPRA.AnalyticNumberTheory.ConvolutionAssoc (cvF inst2_cvF)
open LeanProofs.IPRA.AnalyticNumberTheory.ConvSummatory (bS inst2_bS Bs)
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusSummatory (gS inst2_gS)
open LeanProofs.IPRA.AnalyticNumberTheory.TauAbelIdentity (tau_sum)
open LeanProofs.IPRA.AnalyticNumberTheory.DivisorSwapP (tau_lw)
open LeanProofs.IPRA.AnalyticNumberTheory.WeightedMangoldt (Lw)
open LeanProofs.IPRA.AnalyticNumberTheory.FactorialLambda (sum_add2)
open LeanProofs.IPRA.AnalyticNumberTheory.EulerProduct (eqb_comm')
open LeanProofs.IPRA.AnalyticNumberTheory.Multiplicative (rem_eq')
open LeanProofs.IPRA.AnalyticNumberTheory.SumPhi (sum_ones)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Shifting a sum and the empty convolution -/

/-- `Σ_{k<m+1} b(k) = b(0) + Σ_{k<m} b(k + 1)`. -/
theorem bs_shift (b : PTm 2) (m y : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF b) (succ m) y ≐ inst2 b zero y + Bs b m y :=
  sum_shift b m y

/-- `(f * g)(0) = 0`. -/
theorem conv_zero (f g : PTm 2) (y : PTm n) : Γ ⊢[PRAAx] conv f g zero y ≐ zero :=
  (sum_succ' _ _ _).eqTrans ((congrAdd (sum_zero _ _) (cv_at _ _ _ _ _)).eqTrans
    ((congrAdd (.eqRefl _) (zero_mul_l (zero_mul_l sg_zero _) _)).eqTrans (add_zero _)))

theorem shift_one'' : Syn.shift (one : PTm n) = one := by simp [Syn.shift]

/-! ## `g = 𝟏`: the divisor count -/

/-- `B_𝟏(m) = Σ_{k≤m} τ(k) = D(m)`. -/
theorem tau_bs (m y : PTm n) : Γ ⊢[PRAAx] Bs (cvF one one) m y ≐ S m m := by
  have t := natEq (tau_sum (Γ := Γ) m y)
  have s := bs_shift (Γ := Γ) (cvF one one) m y
  rw [inst2_cvF] at s
  have e := natEq s; have z := natEq (conv_zero (Γ := Γ) one one y)
  apply deriveNat; ipra_simps; linear_combination -e + t - z

/-! ## `g = ε` -/

/-- `ε(d) = [d = 1]`. -/
abbrev epsB : PTm 2 := eqb (var 0) one

theorem inst2_eps (k y : PTm n) : inst2 epsB k y = eqb k one := by simp [inst2]

/-- `[d ≥ 1][d ∣ x]`. -/
abbrev dvdB : PTm 2 := sg (var 0) * eqb (rem (var 1) (var 0)) zero

theorem inst2_dvdB (k x : PTm n) : inst2 dvdB k x = sg k * eqb (rem x k) zero := by simp [inst2]

theorem eps_pt (d a b : PTm n) :
    Γ ⊢[PRAAx] inst2 (cvB epsB one) d (pairT a b) ≐ inst2 (dB dvdB) d (pairT one a) := by
  rw [inst2_cvB, inst2_dB, inst2_eps, one_inst, inst2_dvdB]
  have e1 : Γ ⊢[PRAAx] eqb (fstT (pairT one a)) d ≐ eqb d one :=
    (congrEqb' (fst_pair _ _) (.eqRefl _)).eqTrans (eqb_comm' _ _)
  have e2 : Γ ⊢[PRAAx] eqb (rem (sndT (pairT one a)) d) zero ≐ eqb (rem a d) zero :=
    congrEqb' (congrAp2 remF (snd_pair _ _) (.eqRefl _)) (.eqRefl _)
  have e3 : Γ ⊢[PRAAx] eqb (rem (fstT (pairT a b)) d) zero ≐ eqb (rem a d) zero :=
    congrEqb' (congrAp2 remF (fst_pair _ _) (.eqRefl _)) (.eqRefl _)
  have f1 := natEq e1; have f2 := natEq e2; have f3 := natEq e3
  apply deriveNat; ipra_simps
  linear_combination 𝔞 (sg d) * 𝔞 (eqb d one) * f3 - 𝔞 (sg d) * 𝔞 (eqb d one) * f2 -
    𝔞 (sg d) * 𝔞 (eqb (rem (sndT (pairT one a)) d) zero) * f1

/-- `x mod 1 = 0`. -/
theorem rem_one (x : PTm n) : Γ ⊢[PRAAx] rem x one ≐ zero :=
  rem_eq' (congrSucc (pred_succ _).eqSymm) (q := x) (by apply deriveNat; ipra_simps; ring)
    (le_refl _)

/-- `(ε * 𝟏)(j + 1) = 1`. -/
theorem conv_eps (j y : PTm n) : Γ ⊢[PRAAx] conv epsB one (succ j) y ≐ one := by
  have h1 : Γ ⊢[PRAAx] lt one (succ (succ j)) := le_of_eq_add (d := j) (by apply deriveNat; ipra_simps; ring)
  have sd := sum_delta (Γ := Γ) dvdB (x := succ j) h1
  rw [inst2_dvdB] at sd
  have cg : Γ ⊢[PRAAx] conv epsB one (succ j) y ≐ ap2 (sumF (dB dvdB)) (succ (succ j)) (pairT one (succ j)) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_pairT, shift_pairT, shift_one'']
    exact eps_pt _ _ _
  have r1 : Γ ⊢[PRAAx] eqb (rem (succ j) one) zero ≐ one := eqb_of_eq (rem_one _)
  have s1 : Γ ⊢[PRAAx] sg (one : PTm n) ≐ one := sg_succ _
  exact cg.eqTrans (sd.eqTrans ((congrMul s1 r1).eqTrans (one_mul _)))

/-- `B_ε(m) = Σ_{k≤m} (ε * 𝟏)(k) = m`. -/
theorem eps_bs (m y : PTm n) : Γ ⊢[PRAAx] Bs (cvF epsB one) m y ≐ m := by
  refine (sum_congr_bounded _ one _ y _ (.allI (.impI ?_))).eqTrans (sum_ones _ y)
  rw [inst2_bS, inst2_cvF, one_inst]
  exact conv_eps _ _

/-! ## `g = L_w`: `𝒟τ = 2 L_w * 𝟏` summed -/

/-- `τ(k + 1) L_w(k + 1)`. -/
abbrev twB : PTm 2 := conv one one (succ (var 0)) (var 1) * Lw wt (succ (var 0)) (var 1)

theorem inst2_twB (k y : PTm n) : inst2 twB k y = conv one one (succ k) y * Lw wt (succ k) y := by
  simp [inst2]

/-- `Σ_{k≤m} τ(k) L_w(k) = 2 B_{L_w}(m)`. -/
theorem tw_bs (m y : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF twB) m y ≐ two * Bs (cvF (DwB wt one) one) m y := by
  have s := sum_add2 (Γ := Γ) (bS (cvF (DwB wt one) one)) (bS (cvF (DwB wt one) one)) twB
    (K := m) (x := y) (x' := y) (z := y) (.allI (.impI (by
      rw [inst2_twB, inst2_bS, inst2_cvF]
      have t := natEq (tau_lw (Γ := (lt (var 0) (Syn.shift m) :: Γ.map Fm.shift)) wt (y := Syn.shift y)
        (m := succ (var 0)) (congrSucc (pred_succ _).eqSymm))
      apply deriveNat; ipra_simps; linear_combination t)))
  have e := natEq s
  apply deriveNat; ipra_simps; linear_combination e

/-! ## The inverted sums for `g = 𝟏` and `g = ε` -/

/-- `Σ_{n<x+1} [n ≥ 1] = x`. -/
theorem sum_sg_one (x y : PTm n) : Γ ⊢[PRAAx] ap2 (sumF (gS one)) (succ x) y ≐ x := by
  have s := bs_shift (Γ := Γ) (gS one) x y
  rw [inst2_gS, one_inst] at s
  have t : Γ ⊢[PRAAx] Bs (gS one) x y ≐ x := by
    refine (sum_congr_bounded _ one _ y _ (.allI (.impI ?_))).eqTrans (sum_ones _ y)
    rw [inst2_bS, inst2_gS, one_inst, one_inst]
    exact (congrMul (sg_succ _) (.eqRefl _)).eqTrans (one_mul _)
  have e := natEq s; have f := natEq t; have z := natEq (sg_zero (Γ := Γ))
  apply deriveNat; ipra_simps; linear_combination e + f + z

/-- `[n ≥ 1]`, the delta body for `ε`. -/
abbrev sgB : PTm 2 := sg (var 0)

theorem inst2_sgB (k y : PTm n) : inst2 sgB k y = sg k := by simp [inst2]

/-- `Σ_{n<x+1} [n ≥ 1] ε(n) = 1` for `x ≥ 1`. -/
theorem sum_sg_eps {x : PTm n} (y : PTm n) (hx : Γ ⊢[PRAAx] le one x) :
    Γ ⊢[PRAAx] ap2 (sumF (gS epsB)) (succ x) y ≐ one := by
  have h1 : Γ ⊢[PRAAx] lt one (succ x) := (succ_monus_succ _ _).eqTrans hx
  have sd := sum_delta (Γ := Γ) sgB (x := y) h1
  rw [inst2_sgB] at sd
  refine (sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))).eqTrans (sd.eqTrans (sg_succ _))
  rw [inst2_gS, inst2_eps, inst2_dB, inst2_sgB, shift_pairT, shift_one'']
  have e1 := natEq ((congrEqb' (fst_pair (Γ := (lt (var 0) (Syn.shift (succ x)) :: Γ.map Fm.shift)) one
    (Syn.shift y)) (.eqRefl (var 0))).eqTrans (eqb_comm' _ _))
  apply deriveNat; ipra_simps; linear_combination -𝔞 (sg (var 0)) * e1

end LeanProofs.IPRA.AnalyticNumberTheory.SymmetryInstances
