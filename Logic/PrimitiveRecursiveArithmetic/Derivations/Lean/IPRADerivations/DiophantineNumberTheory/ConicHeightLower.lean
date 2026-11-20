import IPRADerivations.DiophantineNumberTheory.ConicLower
import IPRADerivations.DiophantineNumberTheory.SimultaneousGrid

/-!
# The lower inequality of the conic height theorem, with signs

Packet: `diophantine-number-theory/diophantine_geometry_ipra`, Theorem `thm:conic-height`, the end of the lower
inequality: "If `|s| = S`, `eq:conic-identity-s` gives `|r| S² ≤ D T_0`. ... Since `T_0 = g Ht([F])` and `g ≤ |r|`,
cancellation of the positive integer `|r|` gives `S² ≤ D Ht([F])`. Now let `x` be the primitive representative of
`Φ(T) = [MF]`. The integer vector `adj(M)x` ... Formula `eq:conic-adjugate` bounds each of its coordinates by
`2P Ht(Φ(T))`. ... `S² ≤ 2PD Ht(Φ(T)) = K Ht(Φ(T))`."

The estimate `|r s²| ≤ D T_0` is `ConicLower.lower_s` (`lower_t` for `|t| = S`); the gcd facts are `ConicGcd`.

* `sq_sign`, `prod_sign`: `s = ±S` gives `s² = S²`, and with `r = ±ρ`, `r s s = ±ρ S²`;
* `abs_exact`: `u = ±m` and `|u| ≤ X` give `m ≤ X`;
* `lower_cancel`: `ρ S² ≤ D T_0`, `T_0 = g H`, `g ≤ ρ`, `ρ ≥ 1` give `S² ≤ D H`;
* `adj_bound`: `|p_0 x_1 − p_1 x_0| ≤ 2PX` for `|p_i| ≤ P`, `|x_i| ≤ X` (the adjugate coordinates);
* `height_lower`: the assembly, `S² ≤ 2PD Ht(Φ(T)) = K Ht(Φ(T))`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.ConicHeightLower

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.PolynomialRemainder (AbsLe abs_hi abs_lo abs_add abs_mul)
open LeanProofs.IPRA.DiophantineNumberTheory.ConicHeight (abs_neg)
open LeanProofs.IPRA.DiophantineNumberTheory.SimultaneousGrid (cancel_pos)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `s = ±S` gives `s² = S²`. -/
theorem sq_sign {s : ZT n} {S : PTm n}
    (h : Γ ⊢[PRAAx] ZT.eq s (ZT.ofNat S) ⋎ ZT.eq s (-(ZT.ofNat S))) :
    Γ ⊢[PRAAx] ZT.eq (s * s) (ZT.ofNat (S * S)) := by
  refine .orE h ?_ ?_
  · have e := ZT.toZ_eq (Prf.hyp0 : (ZT.eq s (ZT.ofNat S) :: Γ) ⊢[PRAAx] _)
    refine ZT.derive ?_
    simp only [ZT.toZ_mul, ZT.toZ_ofNat, Q.mk_mul, map_mul] at e ⊢
    rw [e]
  · have e := ZT.toZ_eq (Prf.hyp0 : (ZT.eq s (-(ZT.ofNat S)) :: Γ) ⊢[PRAAx] _)
    refine ZT.derive ?_
    simp only [ZT.toZ_mul, ZT.toZ_ofNat, ZT.toZ_neg, Q.mk_mul, map_mul] at e ⊢
    rw [e]; ring

/-- `r = ±ρ`, `s² = S²` give `r s s = ±ρ S²`. -/
theorem prod_sign {r s : ZT n} {ρ S : PTm n}
    (hr : Γ ⊢[PRAAx] ZT.eq r (ZT.ofNat ρ) ⋎ ZT.eq r (-(ZT.ofNat ρ)))
    (hs : Γ ⊢[PRAAx] ZT.eq (s * s) (ZT.ofNat (S * S))) :
    Γ ⊢[PRAAx] ZT.eq (r * s * s) (ZT.ofNat (ρ * (S * S))) ⋎ ZT.eq (r * s * s) (-(ZT.ofNat (ρ * (S * S)))) := by
  have es := ZT.toZ_eq hs
  refine .orE hr ?_ ?_
  · refine .orI₁ ?_
    have e := ZT.toZ_eq (Prf.hyp0 : (ZT.eq r (ZT.ofNat ρ) :: Γ) ⊢[PRAAx] _)
    have es' := ZT.toZ_eq (hs.wk : (ZT.eq r (ZT.ofNat ρ) :: Γ) ⊢[PRAAx] _)
    refine ZT.derive ?_
    simp only [ZT.toZ_mul, ZT.toZ_ofNat, Q.mk_mul, map_mul] at e es' ⊢
    rw [_root_.mul_assoc, es', e]
  · refine .orI₂ ?_
    have e := ZT.toZ_eq (Prf.hyp0 : (ZT.eq r (-(ZT.ofNat ρ)) :: Γ) ⊢[PRAAx] _)
    have es' := ZT.toZ_eq (hs.wk : (ZT.eq r (-(ZT.ofNat ρ)) :: Γ) ⊢[PRAAx] _)
    refine ZT.derive ?_
    simp only [ZT.toZ_mul, ZT.toZ_ofNat, ZT.toZ_neg, Q.mk_mul, map_mul] at e es' ⊢
    rw [_root_.mul_assoc, es', e]; ring

/-- `u = ±m` and `|u| ≤ X` give `m ≤ X`. -/
theorem abs_exact {u : ZT n} {m X : PTm n} (h : Γ ⊢[PRAAx] ZT.eq u (ZT.ofNat m) ⋎ ZT.eq u (-(ZT.ofNat m)))
    (hab : Γ ⊢[PRAAx] AbsLe u X) : Γ ⊢[PRAAx] le m X := by
  refine .orE h ?_ ?_
  · have e := ZT.toZ_eq (Prf.hyp0 : (ZT.eq u (ZT.ofNat m) :: Γ) ⊢[PRAAx] _)
    have hi := abs_hi (hab.wk : (ZT.eq u (ZT.ofNat m) :: Γ) ⊢[PRAAx] _)
    rw [toZ_def] at e
    simp only [ZT.toZ_ofNat] at e
    ipra_le sl hi using linear_combination e
  · have e := ZT.toZ_eq (Prf.hyp0 : (ZT.eq u (-(ZT.ofNat m)) :: Γ) ⊢[PRAAx] _)
    have hl := abs_lo (hab.wk : (ZT.eq u (-(ZT.ofNat m)) :: Γ) ⊢[PRAAx] _)
    rw [toZ_def] at e
    simp only [ZT.toZ_ofNat, ZT.toZ_neg] at e
    ipra_le sl hl using linear_combination -e

/-- `ρ S² ≤ D T_0`, `T_0 = g H`, `g ≤ ρ`, `ρ ≥ 1` give `S² ≤ D H`. -/
theorem lower_cancel {ρ S D g H T0 : PTm n} (hρ : Γ ⊢[PRAAx] le one ρ)
    (hmain : Γ ⊢[PRAAx] le (ρ * (S * S)) (D * T0)) (hT : Γ ⊢[PRAAx] T0 ≐ g * H) (hg : Γ ⊢[PRAAx] le g ρ) :
    Γ ⊢[PRAAx] le (S * S) (D * H) := by
  have eT := natEq hT
  refine cancel_pos hρ ?_
  ipra_le sl hmain + 𝔟 D * 𝔟 H * sl hg using
    rw [eT]; ring

/-- The adjugate coordinate `p_0 x_1 − p_1 x_0` is at most `2PX` in absolute value. -/
theorem adj_bound {p0 p1 x0 x1 : ZT n} {P X : PTm n} (hp0 : Γ ⊢[PRAAx] AbsLe p0 P)
    (hp1 : Γ ⊢[PRAAx] AbsLe p1 P) (hx0 : Γ ⊢[PRAAx] AbsLe x0 X) (hx1 : Γ ⊢[PRAAx] AbsLe x1 X) :
    Γ ⊢[PRAAx] AbsLe (p0 * x1 + -(p1 * x0)) (P * X + P * X) :=
  abs_add (abs_mul hp0 hx1) (abs_neg (abs_mul hp1 hx0))

/-- `thm:conic-height`, the lower inequality: `S² ≤ 2PD Ht(Φ(T))`. -/
theorem height_lower {r s : ZT n} {ρ S D g H T0 P H' : PTm n}
    (hr : Γ ⊢[PRAAx] ZT.eq r (ZT.ofNat ρ) ⋎ ZT.eq r (-(ZT.ofNat ρ)))
    (hs : Γ ⊢[PRAAx] ZT.eq s (ZT.ofNat S) ⋎ ZT.eq s (-(ZT.ofNat S))) (hρ : Γ ⊢[PRAAx] le one ρ)
    (hmain : Γ ⊢[PRAAx] AbsLe (r * s * s) (D * T0)) (hT : Γ ⊢[PRAAx] T0 ≐ g * H) (hg : Γ ⊢[PRAAx] le g ρ)
    (hH : Γ ⊢[PRAAx] le H (num 2 * P * H')) :
    Γ ⊢[PRAAx] le (S * S) (num 2 * P * D * H') := by
  have h1 := lower_cancel hρ (abs_exact (prod_sign hr (sq_sign hs)) hmain) hT hg
  ipra_le sl h1 + 𝔟 D * sl hH

end LeanProofs.IPRA.DiophantineNumberTheory.ConicHeightLower
