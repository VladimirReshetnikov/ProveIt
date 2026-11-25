import IPRADerivations.Analysis.BaselQuadrature
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.LinearCombination

/-!
# The rational quarter circle on a uniform grid

Packet: `analysis/stirling_ipra`, `stirling_ipra.tex`, Section `sec:wallis` (`eq:scw`, `eq:sinc`, `eq:cinc`):
the rational parametrization `c(t) = (1 − t²)/(1 + t²)`, `s(t) = 2t/(1 + t²)`, `w(t) = 2/(1 + t²)` of the
quarter circle, sampled at `t = j/M`, `0 ≤ j ≤ M`.

Denominators are cleared by `F = L!` with `2M² ≤ L` (`M = M₀ + 1`), so that `u_j = F/(M² + j²)` is exact
(`u_eq_le`) for `j ≤ M`. The samples are the natural numbers

* `sg j = 2jM u_j = F s(j/M)`, `gm j = (M² − j²) u_j = F c(j/M)`, `om j = 2M² u_j = F w(j/M)`.

Derived, for `j ≤ M`:

* `pyth`: `gm² + sg² = F²` (`c² + s² = 1`); `om_eq`: `om = F + gm` (`w = 1 + c`);
* `gm_le`, `sg_le`: `gm ≤ F`, `sg ≤ F`; the end values `sg 0 = 0`, `gm 0 = F`, `sg M = F`, `gm M = 0`.

and for a cell `j → j + 1` (`j + 1 ≤ M`), with `T = M² + j(j + 1)`:

* `sg_step`, `gm_step`: `T (sg' − sg) = M (gm + gm')` and `T (gm − gm') = M (sg + sg')`. These are `eq:sinc`
  and `eq:cinc` in the form `s(v) − s(u) = τ (c(u) + c(v))`, `c(u) − c(v) = τ (s(u) + s(v))` with
  `τ = h/(1 + uv)`: consecutive grid points differ by the rotation whose half-angle tangent is `τ`;
* `sg_mono`, `gm_anti`: `s` increases and `c` decreases along the grid;
* `sg_inc`, `gm_inc`: `M (sg' − sg) ≤ 2F` and `M (gm − gm') ≤ 2F`, i.e. the increments are at most `2h`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.WallisGrid

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.BaselQuadrature (uq d_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Analysis.Products (fact)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

/-! ## The samples -/

/-- `F s(j/M) = 2jM u_j`. -/
def sg (j M L : PTm n) : PTm n := two * j * M * uq j M L
/-- `F c(j/M) = (M² − j²) u_j`. -/
def gm (j M L : PTm n) : PTm n := monus (M * M) (j * j) * uq j M L
/-- `F w(j/M) = 2M² u_j`. -/
def om (j M L : PTm n) : PTm n := two * (M * M) * uq j M L

@[simp] theorem subst_sg {m : ℕ} (σ : Fin n → PTm m) (j M L : PTm n) :
    Syn.subst σ (sg j M L) = sg (Syn.subst σ j) (Syn.subst σ M) (Syn.subst σ L) := by simp [sg]
@[simp] theorem subst_gm {m : ℕ} (σ : Fin n → PTm m) (j M L : PTm n) :
    Syn.subst σ (gm j M L) = gm (Syn.subst σ j) (Syn.subst σ M) (Syn.subst σ L) := by simp [gm]
@[simp] theorem subst_om {m : ℕ} (σ : Fin n → PTm m) (j M L : PTm n) :
    Syn.subst σ (om j M L) = om (Syn.subst σ j) (Syn.subst σ M) (Syn.subst σ L) := by simp [om]

/-- `L! = (M² + j²) u_j` for `j ≤ M = M₀ + 1` and `2M² ≤ L`. -/
theorem u_eq_le {j M₀ L : PTm n} (hj : Γ ⊢[PRAAx] le j (succ M₀))
    (hL : Γ ⊢[PRAAx] le (two * (succ M₀ * succ M₀)) L) :
    Γ ⊢[PRAAx] fact L ≐ (succ M₀ * succ M₀ + j * j) * uq j (succ M₀) L := by
  have hjj : Γ ⊢[PRAAx] le (j * j) (succ M₀ * succ M₀) := le_mul_mono hj hj
  have hd : Γ ⊢[PRAAx] le (succ M₀ * succ M₀ + j * j) L := by
    ipra_le sl hjj + sl hL
  have dv : Γ ⊢[PRAAx] dvd (succ M₀ * succ M₀ + j * j) (fact L) :=
    dvd_congr_left (d_pos j M₀).eqSymm
      (LeanProofs.IPRA.AnalyticNumberTheory.Primes.dvd_fact (le_congr (d_pos j M₀) (.eqRefl _) hd))
  exact LeanProofs.IPRA.DiophantineNumberTheory.Coprime.eq_of_dvd' (d_pos j M₀) dv

/-! ## One grid point -/

section point

variable {j M₀ L : PTm n}

/-- `c² + s² = 1`. -/
theorem pyth (hj : Γ ⊢[PRAAx] le j (succ M₀)) (hL : Γ ⊢[PRAAx] le (two * (succ M₀ * succ M₀)) L) :
    Γ ⊢[PRAAx] gm j (succ M₀) L * gm j (succ M₀) L + sg j (succ M₀) L * sg j (succ M₀) L ≐ fact L * fact L := by
  have ue := natEq (u_eq_le hj hL)
  have hm := natEq (eq_add_of_le (le_mul_mono hj hj))
  apply deriveNat; simp only [sg, gm, om]; ipra_simps
  have hm' : 𝔞 (monus (succ M₀ * succ M₀) (j * j)) = (𝔞 M₀ + 1) * (𝔞 M₀ + 1) - 𝔞 j * 𝔞 j := by
    linear_combination -hm
  rw [ue, hm']; ring

/-- `w = 1 + c`. -/
theorem om_eq (hj : Γ ⊢[PRAAx] le j (succ M₀)) (hL : Γ ⊢[PRAAx] le (two * (succ M₀ * succ M₀)) L) :
    Γ ⊢[PRAAx] om j (succ M₀) L ≐ fact L + gm j (succ M₀) L := by
  have ue := natEq (u_eq_le hj hL)
  have hm := natEq (eq_add_of_le (le_mul_mono hj hj))
  apply deriveNat; simp only [sg, gm, om]; ipra_simps
  have hm' : 𝔞 (monus (succ M₀ * succ M₀) (j * j)) = (𝔞 M₀ + 1) * (𝔞 M₀ + 1) - 𝔞 j * 𝔞 j := by
    linear_combination -hm
  rw [ue, hm']; ring

/-- `c ≤ 1`. -/
theorem gm_le (hj : Γ ⊢[PRAAx] le j (succ M₀)) (hL : Γ ⊢[PRAAx] le (two * (succ M₀ * succ M₀)) L) :
    Γ ⊢[PRAAx] le (gm j (succ M₀) L) (fact L) := by
  have ue := natEq (u_eq_le hj hL)
  have hm := natEq (eq_add_of_le (le_mul_mono hj hj))
  ipra_simps
  have hm' : 𝔞 (monus (succ M₀ * succ M₀) (j * j)) = (𝔞 M₀ + 1) * (𝔞 M₀ + 1) - 𝔞 j * 𝔞 j := by
    linear_combination -hm
  ipra_le 2 * (𝔞 j * 𝔞 j) * 𝔞 (uq j (succ M₀) L) using simp only [gm]; ipra_simps; rw [ue, hm']; ring

/-- `s ≤ 1`: `F − sg = (M − j)² u_j`. -/
theorem sg_le (hj : Γ ⊢[PRAAx] le j (succ M₀)) (hL : Γ ⊢[PRAAx] le (two * (succ M₀ * succ M₀)) L) :
    Γ ⊢[PRAAx] le (sg j (succ M₀) L) (fact L) := by
  have ue := natEq (u_eq_le hj hL)
  ipra_simps
  ipra_le sl hj * sl hj * 𝔞 (uq j (succ M₀) L) using simp only [sg]; ipra_simps; rw [ue]; ring

end point

/-! ## The end values -/

theorem sg_zero (M L : PTm n) : Γ ⊢[PRAAx] sg zero M L ≐ zero := by
  ipra_lc [sg]

theorem gm_top (M L : PTm n) : Γ ⊢[PRAAx] gm M M L ≐ zero := by
  have e := natEq (monus_self (Γ := Γ) (M * M))
  apply deriveNat; simp only [gm]; ipra_simps
  rw [e]; ring

theorem gm_zero {M₀ L : PTm n} (hL : Γ ⊢[PRAAx] le (two * (succ M₀ * succ M₀)) L) :
    Γ ⊢[PRAAx] gm zero (succ M₀) L ≐ fact L := by
  have ue := natEq (u_eq_le (zero_le (succ M₀)) hL)
  have hm := natEq (eq_add_of_le (le_mul_mono (zero_le (Γ := Γ) (succ M₀)) (zero_le (succ M₀))))
  apply deriveNat; simp only [gm]; ipra_simps
  have hm' : 𝔞 (monus (succ M₀ * succ M₀) (zero * zero)) = (𝔞 M₀ + 1) * (𝔞 M₀ + 1) := by
    linear_combination -hm
  rw [ue, hm']; ring

theorem sg_top {M₀ L : PTm n} (hL : Γ ⊢[PRAAx] le (two * (succ M₀ * succ M₀)) L) :
    Γ ⊢[PRAAx] sg (succ M₀) (succ M₀) L ≐ fact L := by
  have ue := natEq (u_eq_le (le_refl (succ M₀)) hL)
  apply deriveNat; simp only [sg]; ipra_simps
  rw [ue]; ring

/-! ## One cell -/

section cell

variable {j M₀ L : PTm n}

/-- `eq:sinc`: `T (s' − s) = M (c + c')` with `T = M² + j(j + 1)`. -/
theorem sg_step (hj : Γ ⊢[PRAAx] le (succ j) (succ M₀)) (hL : Γ ⊢[PRAAx] le (two * (succ M₀ * succ M₀)) L) :
    Γ ⊢[PRAAx] (succ M₀ * succ M₀ + j * succ j) * sg (succ j) (succ M₀) L ≐
      (succ M₀ * succ M₀ + j * succ j) * sg j (succ M₀) L +
        succ M₀ * (gm j (succ M₀) L + gm (succ j) (succ M₀) L) := by
  have hj0 : Γ ⊢[PRAAx] le j (succ M₀) := le_trans (le_succ_self j) hj
  have ue := natEq (u_eq_le hj0 hL); have ue1 := natEq (u_eq_le hj hL)
  have hm := natEq (eq_add_of_le (le_mul_mono hj0 hj0))
  have hm1 := natEq (eq_add_of_le (le_mul_mono hj hj))
  apply deriveNat; simp only [sg, gm]; ipra_simps
  have hm' : 𝔞 (monus (succ M₀ * succ M₀) (j * j)) = (𝔞 M₀ + 1) * (𝔞 M₀ + 1) - 𝔞 j * 𝔞 j := by
    linear_combination -hm
  have hm1' : 𝔞 (monus (succ M₀ * succ M₀) (succ j * succ j)) =
      (𝔞 M₀ + 1) * (𝔞 M₀ + 1) - (𝔞 j + 1) * (𝔞 j + 1) := by
    linear_combination -hm1
  rw [hm', hm1']
  linear_combination (𝔞 M₀ + 1) * (2 * 𝔞 j + 1) * ue - (𝔞 M₀ + 1) * (2 * 𝔞 j + 1) * ue1

/-- `eq:cinc`: `T (c − c') = M (s + s')` with `T = M² + j(j + 1)`. -/
theorem gm_step (hj : Γ ⊢[PRAAx] le (succ j) (succ M₀)) (hL : Γ ⊢[PRAAx] le (two * (succ M₀ * succ M₀)) L) :
    Γ ⊢[PRAAx] (succ M₀ * succ M₀ + j * succ j) * gm j (succ M₀) L ≐
      (succ M₀ * succ M₀ + j * succ j) * gm (succ j) (succ M₀) L +
        succ M₀ * (sg j (succ M₀) L + sg (succ j) (succ M₀) L) := by
  have hj0 : Γ ⊢[PRAAx] le j (succ M₀) := le_trans (le_succ_self j) hj
  have ue := natEq (u_eq_le hj0 hL); have ue1 := natEq (u_eq_le hj hL)
  have hm := natEq (eq_add_of_le (le_mul_mono hj0 hj0))
  have hm1 := natEq (eq_add_of_le (le_mul_mono hj hj))
  apply deriveNat; simp only [sg, gm]; ipra_simps
  have hm' : 𝔞 (monus (succ M₀ * succ M₀) (j * j)) = (𝔞 M₀ + 1) * (𝔞 M₀ + 1) - 𝔞 j * 𝔞 j := by
    linear_combination -hm
  have hm1' : 𝔞 (monus (succ M₀ * succ M₀) (succ j * succ j)) =
      (𝔞 M₀ + 1) * (𝔞 M₀ + 1) - (𝔞 j + 1) * (𝔞 j + 1) := by
    linear_combination -hm1
  rw [hm', hm1']
  linear_combination ((𝔞 M₀ + 1) * (𝔞 M₀ + 1) - 𝔞 j * (𝔞 j + 1)) * ue1 -
    ((𝔞 M₀ + 1) * (𝔞 M₀ + 1) - 𝔞 j * (𝔞 j + 1)) * ue

/-- `T = M² + j(j + 1)` is positive. -/
theorem T_pos (j M₀ : PTm n) :
    Γ ⊢[PRAAx] succ M₀ * succ M₀ + j * succ j ≐ succ (M₀ * M₀ + two * M₀ + j * succ j) := by
  ipra_ring

/-- `s` increases along the grid. -/
theorem sg_mono (hj : Γ ⊢[PRAAx] le (succ j) (succ M₀)) (hL : Γ ⊢[PRAAx] le (two * (succ M₀ * succ M₀)) L) :
    Γ ⊢[PRAAx] le (sg j (succ M₀) L) (sg (succ j) (succ M₀) L) := by
  have e := natEq (sg_step hj hL)
  refine mul_le_cancel (d' := M₀ * M₀ + two * M₀ + j * succ j)
    (le_congr (congrMul (T_pos j M₀) (.eqRefl _)) (congrMul (T_pos j M₀) (.eqRefl _)) ?_)
  ipra_le (𝔞 M₀ + 1) * (𝔞 (gm j (succ M₀) L) + 𝔞 (gm (succ j) (succ M₀) L)) with e

/-- `c` decreases along the grid. -/
theorem gm_anti (hj : Γ ⊢[PRAAx] le (succ j) (succ M₀)) (hL : Γ ⊢[PRAAx] le (two * (succ M₀ * succ M₀)) L) :
    Γ ⊢[PRAAx] le (gm (succ j) (succ M₀) L) (gm j (succ M₀) L) := by
  have e := natEq (gm_step hj hL)
  refine mul_le_cancel (d' := M₀ * M₀ + two * M₀ + j * succ j)
    (le_congr (congrMul (T_pos j M₀) (.eqRefl _)) (congrMul (T_pos j M₀) (.eqRefl _)) ?_)
  ipra_le (𝔞 M₀ + 1) * (𝔞 (sg j (succ M₀) L) + 𝔞 (sg (succ j) (succ M₀) L)) with e

/-- `s(v) − s(u) ≤ 2h`: `M (sg' − sg) ≤ 2F`. -/
theorem sg_inc (hj : Γ ⊢[PRAAx] le (succ j) (succ M₀)) (hL : Γ ⊢[PRAAx] le (two * (succ M₀ * succ M₀)) L) :
    Γ ⊢[PRAAx] le (succ M₀ * sg (succ j) (succ M₀) L) (succ M₀ * sg j (succ M₀) L + two * fact L) := by
  have hj0 : Γ ⊢[PRAAx] le j (succ M₀) := le_trans (le_succ_self j) hj
  have e := natEq (sg_step hj hL)
  have hs := sg_mono hj hL
  have hg := gm_le hj0 hL; have hg1 := gm_le hj hL
  refine mul_le_cancel (d' := M₀) ?_
  ipra_le (𝔞 M₀ + 1) * (sl hg + sl hg1) + 𝔞 j * (𝔞 j + 1) * sl hs with e

/-- `c(u) − c(v) ≤ 2h`: `M (gm − gm') ≤ 2F`. -/
theorem gm_inc (hj : Γ ⊢[PRAAx] le (succ j) (succ M₀)) (hL : Γ ⊢[PRAAx] le (two * (succ M₀ * succ M₀)) L) :
    Γ ⊢[PRAAx] le (succ M₀ * gm j (succ M₀) L) (succ M₀ * gm (succ j) (succ M₀) L + two * fact L) := by
  have hj0 : Γ ⊢[PRAAx] le j (succ M₀) := le_trans (le_succ_self j) hj
  have e := natEq (gm_step hj hL)
  have hc := gm_anti hj hL
  have hs := sg_le hj0 hL; have hs1 := sg_le hj hL
  refine mul_le_cancel (d' := M₀) ?_
  ipra_le (𝔞 M₀ + 1) * (sl hs + sl hs1) + 𝔞 j * (𝔞 j + 1) * sl hc with e

end cell

end LeanProofs.IPRA.Analysis.WallisGrid
