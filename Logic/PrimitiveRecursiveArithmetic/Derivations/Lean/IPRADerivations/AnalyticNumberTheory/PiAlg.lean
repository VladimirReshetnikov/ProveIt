import IPRADerivations.AnalyticNumberTheory.MeshChange
import IPRADerivations.Core.Header

/-!
# The arithmetic of the prime-counting estimate (`pnt_ipra_constructive_2026-11-14`, `lem:pi-conversion`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `pnt_ipra.tex`, Lemma `lem:pi-conversion`:
"Adding the two displayed bounds to the error for `ψ` proves the claim." Over opaque terms (slack certificates
found and checked by elimination), with `D|ψ − Fx| ≤ AFx`, `qA ≤ 2D`:

* `pi_lower_alg`: `ψ ≤ θ + Lθ_r`, `θ_r ≤ 4rF`, `θ ≤ uπ` and `4qLr ≤ x` give `qFx ≤ quπ + 3Fx`;
* `pi_cheb_alg`: `wF ≤ 2u_Y + F`, `u_Y π ≤ θ + (Y + 1)u_Y`, `θ ≤ ψ ≤ 4Fx`, `u_Y ≤ TF` give
  `wFπ ≤ Fπ + 8Fx + 2(Y + 1)TF` (the Chebyshev bound `π ≤ 8x/(w − 1) + …`);
* `pi_tail_alg`: with `16q(σ + 1) + 1 ≤ w`: `16q(σ + 1)Fπ ≤ 8Fx + 2(Y + 1)TF`;
* `pi_upper_alg`: `uπ ≤ θ + mπ + (Y + 1)u`, `m ≤ (σ + 1)F`, `u ≤ TF`, `4q(Y + 1)T ≤ x` give `quπ ≤ qFx + 4Fx`.

Together: `q|π(x)u_x − Fx| ≤ 4Fx`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.PiAlg

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (cancel_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicMertens (le_scale)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerCleared (pw_le_exp)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem pi_lower_alg {D A q F x psi th thr pi u L r : PTm n}
    (hP : Γ ⊢[PRAAx] le (D * (F * x)) (D * psi + A * (F * x))) (hT : Γ ⊢[PRAAx] le psi (th + L * thr))
    (hTr : Γ ⊢[PRAAx] le thr (num 4 * (r * F))) (hTP : Γ ⊢[PRAAx] le th (u * pi))
    (hqA : Γ ⊢[PRAAx] le (q * A) (two * D)) (hC1 : Γ ⊢[PRAAx] le (num 4 * (q * (L * r))) x)
    (hD1 : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] le (q * (F * x)) (q * (u * pi) + num 3 * (F * x)) := by
  refine cancel_pos hD1 ?_
  ipra_le 𝔞 q * sl hP + 𝔞 q * 𝔞 D * sl hT + 𝔞 q * 𝔞 D * 𝔞 L * sl hTr + 𝔞 q * 𝔞 D * sl hTP +
    𝔞 F * 𝔞 x * sl hqA + 𝔞 D * 𝔞 F * sl hC1

theorem pi_cheb_alg {w F pi x Y T uY th psi : PTm n}
    (huY : Γ ⊢[PRAAx] le (w * F) (two * uY + F)) (hC : Γ ⊢[PRAAx] le (uY * pi) (th + succ Y * uY))
    (hθψ : Γ ⊢[PRAAx] le th psi) (hψ4 : Γ ⊢[PRAAx] le psi (num 4 * (x * F))) (hu : Γ ⊢[PRAAx] le uY (T * F)) :
    Γ ⊢[PRAAx] le (w * F * pi) (F * pi + num 8 * (F * x) + two * (succ Y * (T * F))) := by
  ipra_le 𝔞 pi * sl huY + 2 * sl hC + 2 * sl hθψ + 2 * sl hψ4 + 2 * (𝔞 Y + 1) * sl hu

theorem pi_tail_alg {w F pi x Y T q s : PTm n}
    (ha : Γ ⊢[PRAAx] le (w * F * pi) (F * pi + num 8 * (F * x) + two * (succ Y * (T * F))))
    (hC2 : Γ ⊢[PRAAx] le (num 16 * (q * succ s) + one) w) :
    Γ ⊢[PRAAx] le (num 16 * (q * succ s) * (F * pi)) (num 8 * (F * x) + two * (succ Y * (T * F))) := by
  ipra_le sl ha + 𝔞 F * 𝔞 pi * sl hC2

theorem pi_upper_alg {D A q F x psi th pi u m s Y T : PTm n}
    (hP2 : Γ ⊢[PRAAx] le (D * psi) (D * (F * x) + A * (F * x)))
    (hU : Γ ⊢[PRAAx] le (u * pi) (th + m * pi + succ Y * u)) (hm : Γ ⊢[PRAAx] le m (succ s * F))
    (hθψ : Γ ⊢[PRAAx] le th psi)
    (hb : Γ ⊢[PRAAx] le (num 16 * (q * succ s) * (F * pi)) (num 8 * (F * x) + two * (succ Y * (T * F))))
    (hu : Γ ⊢[PRAAx] le u (T * F)) (hqA : Γ ⊢[PRAAx] le (q * A) (two * D))
    (hC3 : Γ ⊢[PRAAx] le (num 4 * (q * (succ Y * T))) x) (hq1 : Γ ⊢[PRAAx] le one q) (hD1 : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] le (q * (u * pi)) (q * (F * x) + num 4 * (F * x)) := by
  refine cancel_pos (c := num 16 * D) (by ipra_le 16 * sl hD1 + 15) ?_
  ipra_le 16 * 𝔞 D * 𝔞 q * sl hU + 16 * 𝔞 D * 𝔞 q * 𝔞 pi * sl hm + 16 * 𝔞 D * 𝔞 q * sl hθψ + 16 * 𝔞 q * sl hP2 +
    𝔞 D * sl hb + 16 * 𝔞 D * 𝔞 q * (𝔞 Y + 1) * sl hu + 16 * 𝔞 F * 𝔞 x * sl hqA + 5 * 𝔞 D * 𝔞 F * sl hC3 +
    4 * 𝔞 D * 𝔞 F * 𝔞 T * (𝔞 Y + 1) * sl hq1 + 2 * 𝔞 D * 𝔞 F * 𝔞 T * (𝔞 Y + 1) + 19 * 𝔞 D * 𝔞 F * 𝔞 x

/-! ## Exponential growth -/

/-- `4c ≤ σ` gives `c(σ + 1) ≤ 2^σ` (from `(k + 1)² ≤ 4^k`, `ZetaFiniteContract.sq_le_pow`). -/
theorem pow_growth {c s : PTm n} (h : Γ ⊢[PRAAx] le (num 4 * c) s) : Γ ⊢[PRAAx] le (c * succ s) (pw two s) := by
  have dm := div_mod_at (Γ := Γ) (x := s) (y := two) (c := one) (.eqRefl _)
  have e := natEq (Prf.andE₁ dm)
  have r := Prf.andE₂ dm
  have h2c : Γ ⊢[PRAAx] le (two * (two * c)) (two * succ (quo s two)) := by ipra_le sl h + sl r + 1 with e
  have h2 := mul_le_cancel (d' := one) h2c
  have a := LeanProofs.IPRA.AnalyticNumberTheory.ZetaFiniteContract.sq_le_pow (Γ := Γ) (quo s two)
  have b := le_scale (succ (quo s two)) h2
  have p2 : Γ ⊢[PRAAx] (two : PTm n) ≐ succ (pred two) := LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep.pos_of_one_le (le_succ_self one)
  have hk : Γ ⊢[PRAAx] le (quo s two + quo s two) s := by ipra_le 𝔞 (rem s two) with e
  have c2 := le_congr (pw_add two _ _) (.eqRefl _) (pw_le_exp p2 hk)
  have hs : Γ ⊢[PRAAx] le (c * succ s) (c * (two * succ (quo s two))) := by
    have q := le_scale c (show Γ ⊢[PRAAx] le (succ s) (two * succ (quo s two)) by ipra_le sl r with e)
    exact q
  ipra_le sl hs + sl b + sl a + sl c2

end LeanProofs.IPRA.AnalyticNumberTheory.PiAlg
