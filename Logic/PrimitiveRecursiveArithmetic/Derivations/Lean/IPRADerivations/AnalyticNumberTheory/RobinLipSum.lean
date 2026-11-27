import IPRADerivations.AnalyticNumberTheory.RobinLipLog

/-!
# The finitary artanh addition theorem for `LogI` (`robin_ipra_research_2026-11-19`, §"Explicit interval arithmetic")

Packet: `analytic-number-theory/robin_ipra_research_2026-11-19`, `paper/report.tex`. Item (1b) of the open list: logarithm
names of *different* arguments are additive up to an explicit error. For `x = a/b ≥ 1`, `c = c₁/c₂ ≥ 1`
(`c₁ = c₂ + k`) and every precision `K`, with `lo(·, K)` the lower name of `RobinLogInterval`:

* `lo_sub_up`:  `lo(xc, K) ≤ lo(x, K) + lo(c, K) + (c − 1)/9^K`;
* `lo_sub_low`: `lo(x, K) + lo(c, K) ≤ lo(xc, K) + (c − 1)/9^K`.

There is no "true logarithm" in iPRA. The proof is a finite Riemann-sum comparison. Partition `[1, c]` by
`t_i = u_i/(N c₂)`, `u_i = N c₂ + i k` (`i ≤ N`), and compare the steps `x t_i → x t_{i+1}` and `t_i → t_{i+1}`, which
have the same ratio. The two-sided Lipschitz bounds of `RobinLipLog` give, per step, an excess of at most
`k/u_i − k/u_{i+1} + k/(u_i 9^K)`. The invariant `RF` telescopes this, and `rs_all` proves it by induction on `i`.
At `i = N` it reads `lo(xc) ≤ lo(x) + lo(c) + (c − 1)/N + (c − 1)/9^K` (`conv`, after `lo_val`: names depend only on the
rational value). The term `(c − 1)/N` is removed by one explicit choice `N = E + 1` (`lim_le`), because the order of
rationals is decidable. Every quantity is a primitive-recursive term, and no search is unbounded.

The binary-exponent carry `e(xc) ∈ {e(x) + e(c), e(x) + e(c) + 1}` is absorbed by the Lipschitz bounds, which cross at
most one binade per step.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.RobinLipSum

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.RobinGamma (Lv Pv)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLogName (Nz Dz Lz Dz_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLipName (Rv)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLipLog (lo_lip_up lo_lip_low mul1)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLogInterval
  (eb eb_spec eb_eq Bt dt st c3 a_eq loN loD lo_mono loD_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Names depend only on the rational value -/

theorem le_of_eq' {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) : Γ ⊢[PRAAx] le a b := le_congr (.eqRefl _) h (le_refl _)

theorem lo_val {a b a' b' : PTm n} (hb : Γ ⊢[PRAAx] le one b) (hab : Γ ⊢[PRAAx] le b a)
    (hb' : Γ ⊢[PRAAx] le one b') (hab' : Γ ⊢[PRAAx] le b' a') (he : Γ ⊢[PRAAx] a * b' ≐ a' * b) (K : PTm n) :
    Γ ⊢[PRAAx] loN a b K * loD a' b' K ≐ loN a' b' K * loD a b K :=
  le_antisymm (lo_mono hb hab hb' hab' (le_of_eq' he) K) (lo_mono hb' hab' hb hab (le_of_eq' he.eqSymm) K)

/-- `lo(1, K) = 0`. -/
theorem lo_one {x : PTm n} (hx : Γ ⊢[PRAAx] le one x) (K : PTm n) : Γ ⊢[PRAAx] loN x x K ≐ zero := by
  have eP0 := natEq (pw_zero (Γ := Γ) (two : PTm n))
  have eP1 := natEq (pw_succ (Γ := Γ) (two : PTm n) zero)
  have h1 : Γ ⊢[PRAAx] le (x * pw two zero) x := by ipra_le 0 with -(𝔞 x) * eP0
  have h2 : Γ ⊢[PRAAx] lt x (x * pw two (succ zero)) := by ipra_le sl hx with 𝔞 x * eP1 + 2 * 𝔞 x * eP0
  have e0 : Γ ⊢[PRAAx] eb x x ≐ zero := eb_eq hx (le_refl x) h1 h2
  have hdt : Γ ⊢[PRAAx] dt x x ≐ zero := by
    ipra_lc -natEq (a_eq hx (le_refl x)) - 𝔞 x * natEq (congrAp2 powF e0 (.eqRefl (two : PTm n))) - 𝔞 x * eP0
  have hN : Γ ⊢[PRAAx] Nz K (dt x x) (st x x) ≐ zero :=
    (congrAp2 _ (.eqRefl _) (congrPairT hdt (.eqRefl _))).eqTrans (Nz_p0 K _)
  ipra_lc 𝔞 (Nz K one c3) * 𝔞 (Lv K zero) * 𝔞 (Pv K (st x x)) * natEq e0 + 𝔞 (Lv K zero) * 𝔞 (Pv K c3) * natEq hN

/-- A name of value `1` has numerator `0`. -/
theorem lo_zero_at {x y : PTm n} (hy : Γ ⊢[PRAAx] le one y) (he : Γ ⊢[PRAAx] x ≐ y) (K : PTm n) :
    Γ ⊢[PRAAx] loN x y K ≐ zero := by
  have hyx : Γ ⊢[PRAAx] le y x := le_congr (.eqRefl _) he.eqSymm (le_refl _)
  have v := lo_val hy hyx (le_refl one) (le_refl one) (by
    ipra_lc natEq he) K
  have o := lo_one (Γ := Γ) (le_refl one) K
  have p := loD_pos (Γ := Γ) (le_refl one) (le_refl one) K
  have w : Γ ⊢[PRAAx] loN x y K * succ (pred (loD one one K)) ≐ zero :=
    (congrMul (.eqRefl _) p.eqSymm).eqTrans (v.eqTrans ((congrMul o (.eqRefl _)).eqTrans (zero_mul _)))
  have l : Γ ⊢[PRAAx] le (loN x y K) (loN x y K * succ (pred (loD one one K))) := by
    ipra_le 𝔞 (loN x y K * pred (loD one one K))
  exact le_antisymm (le_congr (.eqRefl _) w l) (zero_le _)

/-! ## The telescoping invariant -/

abbrev uI (U k i : PTm n) : PTm n := U + i * k

/-- `X_i + Y_0 + k/u_i ≤ X_0 + Y_i + k/U + i k/(U 9^K)` with `X_i = lo(α u_i/β)`, `Y_i = lo(γ u_i/δ)`, cleared. -/
abbrev RF (i α β γ δ U k K : PTm n) : Fm PTm n :=
  le (loN (α * uI U k i) β K * loD (γ * uI U k i) δ K * loD (α * uI U k zero) β K * loD (γ * uI U k zero) δ K *
        uI U k i * U * Rv K c3 +
      loN (γ * uI U k zero) δ K * loD (α * uI U k i) β K * loD (γ * uI U k i) δ K * loD (α * uI U k zero) β K *
        uI U k i * U * Rv K c3 +
      k * loD (α * uI U k i) β K * loD (γ * uI U k i) δ K * loD (α * uI U k zero) β K * loD (γ * uI U k zero) δ K *
        U * Rv K c3)
    (loN (α * uI U k zero) β K * loD (α * uI U k i) β K * loD (γ * uI U k i) δ K * loD (γ * uI U k zero) δ K *
        uI U k i * U * Rv K c3 +
      loN (γ * uI U k i) δ K * loD (α * uI U k i) β K * loD (α * uI U k zero) β K * loD (γ * uI U k zero) δ K *
        uI U k i * U * Rv K c3 +
      k * loD (α * uI U k i) β K * loD (γ * uI U k i) δ K * loD (α * uI U k zero) β K * loD (γ * uI U k zero) δ K *
        uI U k i * Rv K c3 +
      i * k * loD (α * uI U k i) β K * loD (γ * uI U k i) δ K * loD (α * uI U k zero) β K * loD (γ * uI U k zero) δ K *
        uI U k i)

/-- The step of the invariant, as cleared-fraction algebra. -/
theorem rs_alg {Xn Xd Xn1 Xd1 Yn Yd Yn1 Yd1 Xn0 Xd0 Yn0 Yd0 U k i α β γ δ G : PTm n}
    (hM : Γ ⊢[PRAAx] Xd * Yd * (U + i * k) * α * β * (γ * γ) * (δ * δ) ≐
      succ (pred (Xd * Yd * (U + i * k) * α * β * (γ * γ) * (δ * δ))))
    (inv : Γ ⊢[PRAAx] le (Xn * Yd * Xd0 * Yd0 * (U + i * k) * U * G + Yn0 * Xd * Yd * Xd0 * (U + i * k) * U * G +
        k * Xd * Yd * Xd0 * Yd0 * U * G)
      (Xn0 * Xd * Yd * Yd0 * (U + i * k) * U * G + Yn * Xd * Xd0 * Yd0 * (U + i * k) * U * G +
        k * Xd * Yd * Xd0 * Yd0 * (U + i * k) * G + i * k * Xd * Yd * Xd0 * Yd0 * (U + i * k)))
    (tu : Γ ⊢[PRAAx] le (Xn1 * Xd * ((α * (U + i * k)) * β))
      (Xn * Xd1 * ((α * (U + i * k)) * β) + α * k * β * Xd * Xd1))
    (tl : Γ ⊢[PRAAx] le (Yn * Yd1 * ((γ * (U + succ i * k) * δ) * (γ * (U + i * k) * δ * G)) +
        γ * k * δ * Yd * Yd1 * (γ * (U + i * k) * δ * G))
      (Yn1 * Yd * ((γ * (U + succ i * k) * δ) * (γ * (U + i * k) * δ * G)) +
        γ * k * δ * Yd * Yd1 * (γ * (U + succ i * k) * δ))) :
    Γ ⊢[PRAAx] le (Xn1 * Yd1 * Xd0 * Yd0 * (U + succ i * k) * U * G + Yn0 * Xd1 * Yd1 * Xd0 * (U + succ i * k) * U * G +
        k * Xd1 * Yd1 * Xd0 * Yd0 * U * G)
      (Xn0 * Xd1 * Yd1 * Yd0 * (U + succ i * k) * U * G + Yn1 * Xd1 * Xd0 * Yd0 * (U + succ i * k) * U * G +
        k * Xd1 * Yd1 * Xd0 * Yd0 * (U + succ i * k) * G + succ i * k * Xd1 * Yd1 * Xd0 * Yd0 * (U + succ i * k)) := by
  have c : Γ ⊢[PRAAx] le (Xd * Yd * (U + i * k) * α * β * (γ * γ) * (δ * δ) *
        (Xn1 * Yd1 * Xd0 * Yd0 * (U + succ i * k) * U * G + Yn0 * Xd1 * Yd1 * Xd0 * (U + succ i * k) * U * G +
          k * Xd1 * Yd1 * Xd0 * Yd0 * U * G))
      (Xd * Yd * (U + i * k) * α * β * (γ * γ) * (δ * δ) *
        (Xn0 * Xd1 * Yd1 * Yd0 * (U + succ i * k) * U * G + Yn1 * Xd1 * Xd0 * Yd0 * (U + succ i * k) * U * G +
          k * Xd1 * Yd1 * Xd0 * Yd0 * (U + succ i * k) * G + succ i * k * Xd1 * Yd1 * Xd0 * Yd0 * (U + succ i * k))) := by
    ipra_le 𝔞 (Xd1 * Yd1 * (U + succ i * k) * α * β * (γ * γ) * (δ * δ)) * sl inv +
      𝔞 (Yd * Yd1 * Xd0 * Yd0 * (U + succ i * k) * U * G * (γ * γ) * (δ * δ)) * sl tu +
      𝔞 (Xd * Xd1 * Xd0 * Yd0 * U * α * β) * sl tl +
      𝔞 (Xd * Yd * α * β * (γ * γ) * (δ * δ) * Xd1 * Yd1 * Xd0 * Yd0 * (U + succ i * k) * k * k * i)
  exact mul_le_cancel_at hM c

theorem le_shift {a b : PTm n} (h : Γ ⊢[PRAAx] le a b) : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift a) (Syn.shift b) :=
  LeanProofs.IPRA.Order.shift_le h

theorem le_shift_one {a : PTm n} (h : Γ ⊢[PRAAx] le one a) : (Γ.map Fm.shift) ⊢[PRAAx] le one (Syn.shift a) :=
  LeanProofs.IPRA.Order.shift_one_le h

theorem le_shift_mul {a b c : PTm n} (h : Γ ⊢[PRAAx] le a (b * c)) :
    (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift a) (Syn.shift b * Syn.shift c) := by
  have b := h.shift
  simp only [Fm.shift, subst_le, PTm.subst_mul] at b
  exact b

/-- One step of the invariant from the two Lipschitz bounds. -/
theorem rs_step {i α β γ δ U k K : PTm n} (hα : Γ ⊢[PRAAx] le one α) (hγ : Γ ⊢[PRAAx] le one γ)
    (hβ : Γ ⊢[PRAAx] le one β) (hαβ : Γ ⊢[PRAAx] le β (α * U)) (hδ : Γ ⊢[PRAAx] le one δ)
    (hγδ : Γ ⊢[PRAAx] le δ (γ * U)) (hU : Γ ⊢[PRAAx] le one U) (hk : Γ ⊢[PRAAx] le k U)
    (ih : Γ ⊢[PRAAx] RF i α β γ δ U k K) : Γ ⊢[PRAAx] RF (succ i) α β γ δ U k K := by
  have hβu : Γ ⊢[PRAAx] le β (α * (U + i * k)) := by ipra_le sl hαβ + 𝔞 (α * i * k)
  have hβu1 : Γ ⊢[PRAAx] le β (α * (U + succ i * k)) := by ipra_le sl hαβ + 𝔞 (α * succ i * k)
  have hδu : Γ ⊢[PRAAx] le δ (γ * (U + i * k)) := by ipra_le sl hγδ + 𝔞 (γ * i * k)
  have hδu1 : Γ ⊢[PRAAx] le δ (γ * (U + succ i * k)) := by ipra_le sl hγδ + 𝔞 (γ * succ i * k)
  have hDX : Γ ⊢[PRAAx] (α * (U + succ i * k)) * β ≐ (α * (U + i * k)) * β + α * k * β := by ipra_ring
  have h2X : Γ ⊢[PRAAx] le ((α * (U + succ i * k)) * β) (two * ((α * (U + i * k)) * β)) := by
    ipra_le 𝔞 (α * β) * sl hk + 𝔞 (α * β * i * k)
  have hDY : Γ ⊢[PRAAx] (γ * (U + succ i * k)) * δ ≐ (γ * (U + i * k)) * δ + γ * k * δ := by ipra_ring
  have h2Y : Γ ⊢[PRAAx] le ((γ * (U + succ i * k)) * δ) (two * ((γ * (U + i * k)) * δ)) := by
    ipra_le 𝔞 (γ * δ) * sl hk + 𝔞 (γ * δ * i * k)
  have tu := lo_lip_up hβ hβu hβ hβu1 hDX h2X K
  have tl := lo_lip_low hδ hδu hδ hδu1 hDY h2Y K
  have hu : Γ ⊢[PRAAx] le one (U + i * k) := by ipra_le sl hU + 𝔞 (i * k)
  have hM : Γ ⊢[PRAAx] loD (α * (U + i * k)) β K * loD (γ * (U + i * k)) δ K * (U + i * k) * α * β * (γ * γ) * (δ * δ) ≐
      succ (pred (loD (α * (U + i * k)) β K * loD (γ * (U + i * k)) δ K * (U + i * k) * α * β * (γ * γ) * (δ * δ))) :=
    pos_mul (pos_mul (pos_mul (pos_mul (pos_mul (pos_mul (loD_pos hβ hβu K) (loD_pos hδ hδu K)) (pos_of_one_le hu))
      (pos_of_one_le hα)) (pos_of_one_le hβ)) (pos_mul (pos_of_one_le hγ) (pos_of_one_le hγ)))
      (pos_mul (pos_of_one_le hδ) (pos_of_one_le hδ))
  exact rs_alg hM ih tu tl

theorem rs_zero (α β γ δ U k K : PTm n) : Γ ⊢[PRAAx] RF zero α β γ δ U k K := by
  ipra_le 0

/-- The invariant holds for every `i`. -/
theorem rs_all {α β γ δ U k K : PTm n} (hα : Γ ⊢[PRAAx] le one α) (hγ : Γ ⊢[PRAAx] le one γ)
    (hβ : Γ ⊢[PRAAx] le one β) (hαβ : Γ ⊢[PRAAx] le β (α * U)) (hδ : Γ ⊢[PRAAx] le one δ)
    (hγδ : Γ ⊢[PRAAx] le δ (γ * U)) (hU : Γ ⊢[PRAAx] le one U) (hk : Γ ⊢[PRAAx] le k U) (N : PTm n) :
    Γ ⊢[PRAAx] RF N α β γ δ U k K := by
  have hall : Γ ⊢[PRAAx] Fm.all (RF (var 0) (Syn.shift α) (Syn.shift β) (Syn.shift γ) (Syn.shift δ) (Syn.shift U)
      (Syn.shift k) (Syn.shift K)) := by
    ipra_qfind (le_QF _ _) [subst_le, subst_ap2, subst_pairT]
    · exact rs_zero α β γ δ U k K
    · exact rs_step (le_shift_one hα).wk (le_shift_one hγ).wk (le_shift_one hβ).wk (le_shift_mul hαβ).wk
        (le_shift_one hδ).wk (le_shift_mul hγδ).wk (le_shift_one hU).wk (le_shift hk).wk Prf.hyp0
  have r := Prf.allE N hall
  simp only [subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, LeanProofs.IPRA.PTm.subst_monus,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at r
  exact r

/-! ## From the invariant at `i = N` to the four values, and `N → ∞` -/

theorem conv {Xn Xd Yn Yd Xn0 Xd0 Yn0 Yd0 u U G k N Pn Pd Qn Qd Rn Rd Sn Sd : PTm n}
    (hM : Γ ⊢[PRAAx] Xd * Yd * Xd0 * Yd0 * u ≐ succ (pred (Xd * Yd * Xd0 * Yd0 * u)))
    (inv : Γ ⊢[PRAAx] le (Xn * Yd * Xd0 * Yd0 * u * U * G + Yn0 * Xd * Yd * Xd0 * u * U * G + k * Xd * Yd * Xd0 * Yd0 * U * G)
      (Xn0 * Xd * Yd * Yd0 * u * U * G + Yn * Xd * Xd0 * Yd0 * u * U * G + k * Xd * Yd * Xd0 * Yd0 * u * G +
        N * k * Xd * Yd * Xd0 * Yd0 * u))
    (eX : Γ ⊢[PRAAx] Xn * Pd ≐ Pn * Xd) (eX0 : Γ ⊢[PRAAx] Xn0 * Qd ≐ Qn * Xd0) (eY : Γ ⊢[PRAAx] Yn * Rd ≐ Rn * Yd)
    (eY0 : Γ ⊢[PRAAx] Yn0 * Sd ≐ Sn * Yd0) :
    Γ ⊢[PRAAx] le (Pn * Sd * Qd * Rd * (U * G) + Sn * Pd * Qd * Rd * (U * G))
      (Qn * Pd * Sd * Rd * (U * G) + Rn * Pd * Sd * Qd * (U * G) + (k * G + N * k) * (Pd * Sd * Qd * Rd)) := by
  have eX := natEq eX
  have eX0 := natEq eX0
  have eY := natEq eY
  have eY0 := natEq eY0
  have c : Γ ⊢[PRAAx] le (Xd * Yd * Xd0 * Yd0 * u * (Pn * Sd * Qd * Rd * (U * G) + Sn * Pd * Qd * Rd * (U * G)))
      (Xd * Yd * Xd0 * Yd0 * u * (Qn * Pd * Sd * Rd * (U * G) + Rn * Pd * Sd * Qd * (U * G) +
        (k * G + N * k) * (Pd * Sd * Qd * Rd))) := by
    ipra_le 𝔞 (Pd * Sd * Qd * Rd) * sl inv + 𝔞 (Pd * Sd * Qd * Rd * Xd * Yd * Xd0 * Yd0 * U * G * k) with ((𝔞 G * 𝔞 Qd * 𝔞 Rd * 𝔞 Sd * 𝔞 U * 𝔞 Xd0 * 𝔞 Yd * 𝔞 Yd0 * 𝔞 u)) * eX + ((-𝔞 G * 𝔞 Pd * 𝔞 Rd * 𝔞 Sd * 𝔞 U * 𝔞 Xd * 𝔞 Yd * 𝔞 Yd0 * 𝔞 u)) * eX0 + ((-𝔞 G * 𝔞 Pd * 𝔞 Qd * 𝔞 Sd * 𝔞 U * 𝔞 Xd * 𝔞 Xd0 * 𝔞 Yd0 * 𝔞 u)) * eY + ((𝔞 G * 𝔞 Pd * 𝔞 Qd * 𝔞 Rd * 𝔞 U * 𝔞 Xd * 𝔞 Xd0 * 𝔞 Yd * 𝔞 u)) * eY0
  exact mul_le_cancel_at hM c

/-- Decidability of the order removes a vanishing error: `(E + 1) L ≤ (E + 1) R + E` gives `L ≤ R`. -/
theorem lim_le {L R E : PTm n} (h : Γ ⊢[PRAAx] le (succ E * L) (succ E * R + E)) : Γ ⊢[PRAAx] le L R := by
  refine .orE (lt_or_le R L) ?_ Prf.hyp0
  have h' : (lt R L :: Γ) ⊢[PRAAx] le (succ E * L) (succ E * R + E) := h.wk
  exact le_lt_absurd _ h' (by ipra_le 𝔞 (succ E) * sl (Prf.hyp0 : (lt R L :: Γ) ⊢[PRAAx] lt R L))

/-! ## The addition theorem -/

theorem one_le_mul {a b : PTm n} (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx] le one (a * b) := by
  have m := le_mul_mono ha hb
  ipra_le sl m

alias one_le_of_pos' := Common.one_le_of_pos

theorem G_pos (K : PTm n) : Γ ⊢[PRAAx] le one (Rv K c3) :=
  one_le_of_pos' (pw_pos' (pos_of_one_le (by ipra_le 2 : Γ ⊢[PRAAx] le one (c3 : PTm n))) (two * K))

theorem le_bc {a b c1 c2 : PTm n} (hab : Γ ⊢[PRAAx] le b a) (hc12 : Γ ⊢[PRAAx] le c2 c1) :
    Γ ⊢[PRAAx] le (b * c2) (a * c1) :=
  le_mul_mono hab hc12

/-- The upper half at an arbitrary number `N ≥ k/c₂` of steps: `lo(xc) ≤ lo(x) + lo(c) + (c − 1)/N + (c − 1)/9^K`. -/
theorem sub_up_N {a b c1 c2 k N : PTm n} (hb : Γ ⊢[PRAAx] le one b) (hab : Γ ⊢[PRAAx] le b a)
    (hc2 : Γ ⊢[PRAAx] le one c2) (hc : Γ ⊢[PRAAx] c1 ≐ c2 + k) (hN : Γ ⊢[PRAAx] le one N)
    (hkN : Γ ⊢[PRAAx] le k (N * c2)) (K : PTm n) :
    Γ ⊢[PRAAx] le (loN (a * c1) (b * c2) K * one * loD a b K * loD c1 c2 K * ((N * c2) * Rv K c3) +
        zero * loD (a * c1) (b * c2) K * loD a b K * loD c1 c2 K * ((N * c2) * Rv K c3))
      (loN a b K * loD (a * c1) (b * c2) K * one * loD c1 c2 K * ((N * c2) * Rv K c3) +
        loN c1 c2 K * loD (a * c1) (b * c2) K * one * loD a b K * ((N * c2) * Rv K c3) +
        (k * Rv K c3 + N * k) * (loD (a * c1) (b * c2) K * one * loD a b K * loD c1 c2 K)) := by
  have ec := natEq hc
  have ha1 := le_trans hb hab
  have hc12 : Γ ⊢[PRAAx] le c2 c1 := le_of_eq_add hc
  have hbc := one_le_mul hb hc2
  have hU := one_le_mul hN hc2
  have hβ := one_le_mul hb hU
  have hαβ : Γ ⊢[PRAAx] le (b * (N * c2)) (a * (N * c2)) := le_mul_mono hab (le_refl _)
  have hγδ : Γ ⊢[PRAAx] le (N * c2) (one * (N * c2)) := by ipra_le 0
  have inv := rs_all (K := K) ha1 (le_refl one) hβ hαβ hU hγδ hU hkN N
  have hβN : Γ ⊢[PRAAx] le (b * (N * c2)) (a * (N * c2 + N * k)) := by ipra_le sl hαβ + 𝔞 (a * N * k)
  have hβ0 : Γ ⊢[PRAAx] le (b * (N * c2)) (a * (N * c2 + zero * k)) := by ipra_le sl hαβ
  have hδN : Γ ⊢[PRAAx] le (N * c2) (one * (N * c2 + N * k)) := by ipra_le 𝔞 (N * k)
  have eX := lo_val hβ hβN hbc (le_bc hab hc12)
    (by ipra_lc -(𝔞 a * 𝔞 b * 𝔞 N * 𝔞 c2) * ec) K
  have eX0 := lo_val hβ hβ0 hb hab (by ipra_ring) K
  have eY := lo_val hU hδN hc2 hc12 (by ipra_lc -(𝔞 N * 𝔞 c2) * ec) K
  have eY0' := lo_zero_at (Γ := Γ) hU (by ipra_ring : Γ ⊢[PRAAx] one * (N * c2 + zero * k) ≐ N * c2) K
  have eY0 : Γ ⊢[PRAAx] loN (one * (N * c2 + zero * k)) (N * c2) K * one ≐
      zero * loD (one * (N * c2 + zero * k)) (N * c2) K :=
    (mul1 _).eqTrans (eY0'.eqTrans (zero_mul _).eqSymm)
  have hM : Γ ⊢[PRAAx] loD (a * (N * c2 + N * k)) (b * (N * c2)) K * loD (one * (N * c2 + N * k)) (N * c2) K *
      loD (a * (N * c2 + zero * k)) (b * (N * c2)) K * loD (one * (N * c2 + zero * k)) (N * c2) K * (N * c2 + N * k) ≐
      succ (pred (loD (a * (N * c2 + N * k)) (b * (N * c2)) K * loD (one * (N * c2 + N * k)) (N * c2) K *
        loD (a * (N * c2 + zero * k)) (b * (N * c2)) K * loD (one * (N * c2 + zero * k)) (N * c2) K * (N * c2 + N * k))) :=
    pos_mul (pos_mul (pos_mul (pos_mul (loD_pos hβ hβN K) (loD_pos hU hδN K)) (loD_pos hβ hβ0 K))
      (loD_pos hU (by ipra_le 0) K)) (pos_of_one_le (by ipra_le sl hU + 𝔞 (N * k)))
  exact conv hM inv eX eX0 eY eY0

/-- Item (1b), upper half: `lo(xc, K) ≤ lo(x, K) + lo(c, K) + (c − 1)/9^K` for `x = a/b ≥ 1`, `c = c₁/c₂ ≥ 1`,
`c₁ = c₂ + k`, cleared. -/
theorem lo_sub_up {a b c1 c2 k : PTm n} (hb : Γ ⊢[PRAAx] le one b) (hab : Γ ⊢[PRAAx] le b a)
    (hc2 : Γ ⊢[PRAAx] le one c2) (hc : Γ ⊢[PRAAx] c1 ≐ c2 + k) (K : PTm n) :
    Γ ⊢[PRAAx] le (loN (a * c1) (b * c2) K * loD a b K * loD c1 c2 K * (c2 * Rv K c3))
      (loN a b K * loD (a * c1) (b * c2) K * loD c1 c2 K * (c2 * Rv K c3) +
        loN c1 c2 K * loD (a * c1) (b * c2) K * loD a b K * (c2 * Rv K c3) +
        k * (loD (a * c1) (b * c2) K * loD a b K * loD c1 c2 K)) := by
  have hc12 : Γ ⊢[PRAAx] le c2 c1 := le_of_eq_add hc
  have hE1 : Γ ⊢[PRAAx] le one (Rv K c3 * (loD (a * c1) (b * c2) K * one * loD a b K * loD c1 c2 K)) :=
    one_le_mul (G_pos K) (one_le_mul (one_le_mul (one_le_mul
      (one_le_of_pos' (loD_pos (one_le_mul hb hc2) (le_bc hab hc12) K)) (le_refl _))
      (one_le_of_pos' (loD_pos hb hab K))) (one_le_of_pos' (loD_pos hc2 hc12 K)))
  have hN : Γ ⊢[PRAAx] le one (succ (k * Rv K c3 * (loD (a * c1) (b * c2) K * one * loD a b K * loD c1 c2 K))) := by
    ipra_le 𝔞 (k * Rv K c3 * (loD (a * c1) (b * c2) K * one * loD a b K * loD c1 c2 K))
  have hkN : Γ ⊢[PRAAx] le k
      (succ (k * Rv K c3 * (loD (a * c1) (b * c2) K * one * loD a b K * loD c1 c2 K)) * c2) := by
    have m := le_mul_mono (le_refl k) hE1
    ipra_le sl m + 𝔞 (succ (k * Rv K c3 * (loD (a * c1) (b * c2) K * one * loD a b K * loD c1 c2 K))) * sl hc2 + 1
  have cv := sub_up_N hb hab hc2 hc hN hkN K
  have r := lim_le (E := k * Rv K c3 * (loD (a * c1) (b * c2) K * one * loD a b K * loD c1 c2 K))
    (L := loN (a * c1) (b * c2) K * one * loD a b K * loD c1 c2 K * (c2 * Rv K c3) +
      zero * loD (a * c1) (b * c2) K * loD a b K * loD c1 c2 K * (c2 * Rv K c3))
    (R := loN a b K * loD (a * c1) (b * c2) K * one * loD c1 c2 K * (c2 * Rv K c3) +
      loN c1 c2 K * loD (a * c1) (b * c2) K * one * loD a b K * (c2 * Rv K c3) +
      k * (loD (a * c1) (b * c2) K * one * loD a b K * loD c1 c2 K)) (by ipra_le sl cv)
  ipra_le sl r

/-- The lower half at an arbitrary number of steps. -/
theorem sub_low_N {a b c1 c2 k N : PTm n} (hb : Γ ⊢[PRAAx] le one b) (hab : Γ ⊢[PRAAx] le b a)
    (hc2 : Γ ⊢[PRAAx] le one c2) (hc : Γ ⊢[PRAAx] c1 ≐ c2 + k) (hN : Γ ⊢[PRAAx] le one N)
    (hkN : Γ ⊢[PRAAx] le k (N * c2)) (K : PTm n) :
    Γ ⊢[PRAAx] le (loN c1 c2 K * loD a b K * one * loD (a * c1) (b * c2) K * ((N * c2) * Rv K c3) +
        loN a b K * loD c1 c2 K * one * loD (a * c1) (b * c2) K * ((N * c2) * Rv K c3))
      (zero * loD c1 c2 K * loD a b K * loD (a * c1) (b * c2) K * ((N * c2) * Rv K c3) +
        loN (a * c1) (b * c2) K * loD c1 c2 K * loD a b K * one * ((N * c2) * Rv K c3) +
        (k * Rv K c3 + N * k) * (loD c1 c2 K * loD a b K * one * loD (a * c1) (b * c2) K)) := by
  have ec := natEq hc
  have ha1 := le_trans hb hab
  have hc12 : Γ ⊢[PRAAx] le c2 c1 := le_of_eq_add hc
  have hbc := one_le_mul hb hc2
  have hU := one_le_mul hN hc2
  have hδ := one_le_mul hb hU
  have hγδ : Γ ⊢[PRAAx] le (b * (N * c2)) (a * (N * c2)) := le_mul_mono hab (le_refl _)
  have hαβ : Γ ⊢[PRAAx] le (N * c2) (one * (N * c2)) := by ipra_le 0
  have inv := rs_all (K := K) (le_refl one) ha1 hU hαβ hδ hγδ hU hkN N
  have hδN : Γ ⊢[PRAAx] le (b * (N * c2)) (a * (N * c2 + N * k)) := by ipra_le sl hγδ + 𝔞 (a * N * k)
  have hδ0 : Γ ⊢[PRAAx] le (b * (N * c2)) (a * (N * c2 + zero * k)) := by ipra_le sl hγδ
  have hβN : Γ ⊢[PRAAx] le (N * c2) (one * (N * c2 + N * k)) := by ipra_le 𝔞 (N * k)
  have eX := lo_val hU hβN hc2 hc12 (by ipra_lc -(𝔞 N * 𝔞 c2) * ec) K
  have eX0' := lo_zero_at (Γ := Γ) hU (by ipra_ring : Γ ⊢[PRAAx] one * (N * c2 + zero * k) ≐ N * c2) K
  have eX0 : Γ ⊢[PRAAx] loN (one * (N * c2 + zero * k)) (N * c2) K * one ≐
      zero * loD (one * (N * c2 + zero * k)) (N * c2) K :=
    (mul1 _).eqTrans (eX0'.eqTrans (zero_mul _).eqSymm)
  have eY := lo_val hδ hδN hbc (le_bc hab hc12)
    (by ipra_lc -(𝔞 a * 𝔞 b * 𝔞 N * 𝔞 c2) * ec) K
  have eY0 := lo_val hδ hδ0 hb hab (by ipra_ring) K
  have hM : Γ ⊢[PRAAx] loD (one * (N * c2 + N * k)) (N * c2) K * loD (a * (N * c2 + N * k)) (b * (N * c2)) K *
      loD (one * (N * c2 + zero * k)) (N * c2) K * loD (a * (N * c2 + zero * k)) (b * (N * c2)) K * (N * c2 + N * k) ≐
      succ (pred (loD (one * (N * c2 + N * k)) (N * c2) K * loD (a * (N * c2 + N * k)) (b * (N * c2)) K *
        loD (one * (N * c2 + zero * k)) (N * c2) K * loD (a * (N * c2 + zero * k)) (b * (N * c2)) K * (N * c2 + N * k))) :=
    pos_mul (pos_mul (pos_mul (pos_mul (loD_pos hU hβN K) (loD_pos hδ hδN K)) (loD_pos hU (by ipra_le 0) K))
      (loD_pos hδ hδ0 K)) (pos_of_one_le (by ipra_le sl hU + 𝔞 (N * k)))
  exact conv hM inv eX eX0 eY eY0

/-- Item (1b), lower half: `lo(x, K) + lo(c, K) ≤ lo(xc, K) + (c − 1)/9^K`, cleared. -/
theorem lo_sub_low {a b c1 c2 k : PTm n} (hb : Γ ⊢[PRAAx] le one b) (hab : Γ ⊢[PRAAx] le b a)
    (hc2 : Γ ⊢[PRAAx] le one c2) (hc : Γ ⊢[PRAAx] c1 ≐ c2 + k) (K : PTm n) :
    Γ ⊢[PRAAx] le (loN a b K * loD c1 c2 K * loD (a * c1) (b * c2) K * (c2 * Rv K c3) +
        loN c1 c2 K * loD a b K * loD (a * c1) (b * c2) K * (c2 * Rv K c3))
      (loN (a * c1) (b * c2) K * loD a b K * loD c1 c2 K * (c2 * Rv K c3) +
        k * (loD a b K * loD c1 c2 K * loD (a * c1) (b * c2) K)) := by
  have hc12 : Γ ⊢[PRAAx] le c2 c1 := le_of_eq_add hc
  have hE1 : Γ ⊢[PRAAx] le one (Rv K c3 * (loD c1 c2 K * loD a b K * one * loD (a * c1) (b * c2) K)) :=
    one_le_mul (G_pos K) (one_le_mul (one_le_mul (one_le_mul (one_le_of_pos' (loD_pos hc2 hc12 K))
      (one_le_of_pos' (loD_pos hb hab K))) (le_refl _))
      (one_le_of_pos' (loD_pos (one_le_mul hb hc2) (le_bc hab hc12) K)))
  have hN : Γ ⊢[PRAAx] le one (succ (k * Rv K c3 * (loD c1 c2 K * loD a b K * one * loD (a * c1) (b * c2) K))) := by
    ipra_le 𝔞 (k * Rv K c3 * (loD c1 c2 K * loD a b K * one * loD (a * c1) (b * c2) K))
  have hkN : Γ ⊢[PRAAx] le k
      (succ (k * Rv K c3 * (loD c1 c2 K * loD a b K * one * loD (a * c1) (b * c2) K)) * c2) := by
    have m := le_mul_mono (le_refl k) hE1
    ipra_le sl m + 𝔞 (succ (k * Rv K c3 * (loD c1 c2 K * loD a b K * one * loD (a * c1) (b * c2) K))) * sl hc2 + 1
  have cv := sub_low_N hb hab hc2 hc hN hkN K
  have r := lim_le (E := k * Rv K c3 * (loD c1 c2 K * loD a b K * one * loD (a * c1) (b * c2) K))
    (L := loN c1 c2 K * loD a b K * one * loD (a * c1) (b * c2) K * (c2 * Rv K c3) +
      loN a b K * loD c1 c2 K * one * loD (a * c1) (b * c2) K * (c2 * Rv K c3))
    (R := zero * loD c1 c2 K * loD a b K * loD (a * c1) (b * c2) K * (c2 * Rv K c3) +
      loN (a * c1) (b * c2) K * loD c1 c2 K * loD a b K * one * (c2 * Rv K c3) +
      k * (loD c1 c2 K * loD a b K * one * loD (a * c1) (b * c2) K)) (by ipra_le sl cv)
  ipra_le sl r

end LeanProofs.IPRA.AnalyticNumberTheory.RobinLipSum

export_ipra AnalyticNumberTheory.RobinLipSum (one_le_of_pos')
