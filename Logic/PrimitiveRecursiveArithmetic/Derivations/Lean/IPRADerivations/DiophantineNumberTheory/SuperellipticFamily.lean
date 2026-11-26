import IPRADerivations.Analysis.Inequalities.PowerGap
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.Powers
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.Header

/-!
# A uniform superelliptic family: `y^m = x^{mr} + x + 1`

Packet: `foundations/ipra_framework`, `paper/sections/07_diophantine.tex`, Theorem `dio:family` ("A uniform
superelliptic classification"): for `m ≥ 3` and `r ≥ 1` the integer points of `y^m = x^{mr} + x + 1` are
`{(−1, (−1)^r), (0, 1)}` for odd `m` and `{(−1, ±1), (0, ±1)}` for even `m`.

The derivation is uniform in both parameters: `m = j + 3` and `r = r' + 1` are terms, and `t^{mr}` is
`(t^r)^m`. An integer point is `x = t` or `x = −(t + 1)` and `y = ±s` with naturals `s, t`; since
`(−s)^m = s^m` for even `m` and `−s^m` for odd `m`, the equation becomes one of four natural-number
equations, each settled here by a power gap (`Analysis/PowerGap.strict_power_gap`: `u < v` gives
`u^{e+1} + v^e ≤ v^{e+1}`) and one slack certificate:

* `pos_branch` (`x = t ≥ 0`, `|y| = s`): `s^m = (t^r)^m + t + 1` forces `t = 0`, `s = 1`: for `t ≥ 1` and
  `T = t^r ≥ t`, `s ≤ T` gives `s^m ≤ T^m`, and `s > T` gives `s^m ≥ T^m + s^{m−1} > T^m + t + 1`;
* `neg_branch` (`x = −(t + 1)`, `|y| = s`): `s^m + (t + 1) = ((t + 1)^r)^m + 1` forces `t = 0`, `s = 1`:
  for `t ≥ 1`, `T ≥ t + 1`, `s ≥ T` gives `s^m ≥ T^m`, and `s < T` gives `T^m ≥ s^m + T^{m−1}`;
* `neg_y_nonneg_x`, `neg_y_neg_x` (odd `m`, `y = −s`): `−s^m = x^{mr} + x + 1` has no solution, since the
  right side is positive (`T^m ≥ T ≥ t + 1` for `x = −(t + 1)`);
* `point_zero`, `point_neg_one`: the listed points satisfy the equation (`1^m = 0 + 0 + 1`,
  `1^m + 1 = (1^r)^m + 1`).

So `|x|`, `|y|` are as listed, and the signs of `y` follow from the parity of `m` (and, at `x = −1`,
`y^m = (−1)^{mr}`). The helpers are `one_pw` (`1^e = 1`), `zero_pw` (`0^{e+1} = 0`) and `s_eq_one`
(`s^{e+1} = 1` gives `s = 1`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.SuperellipticFamily

open_ipra
open LeanProofs.IPRA.Analysis.PowerGap (strict_power_gap)

variable {k : ℕ} {Γ : List (Fm PTm k)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem congrPwBase {a a' : PTm k} (e : PTm k) (h : Γ ⊢[PRAAx] a ≐ a') : Γ ⊢[PRAAx] pw a e ≐ pw a' e :=
  congrAp2 _ (.eqRefl _) h

/-- `1^e = 1`. -/
theorem one_pw (e : PTm k) : Γ ⊢[PRAAx] pw one e ≐ one := by
  have hall : Γ ⊢[PRAAx] Fm.all (pw one (Syn.var 0) ≐ one) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq, subst_ap2, Syn.subst_var, Syn.inst_zero, ConciseIPRA.PTm.subst_zero,
        ConciseIPRA.PTm.subst_succ]
      exact pw_zero _
    · simp only [Fm.subst_eq, subst_ap2, Syn.subst_var, Syn.repl_zero, ConciseIPRA.PTm.subst_zero,
        ConciseIPRA.PTm.subst_succ]
      have ih : ((pw one (Syn.var 0) ≐ one) :: Γ.map Fm.shift) ⊢[PRAAx] pw one (Syn.var 0) ≐ one := Prf.hyp0
      exact (pw_succ _ _).eqTrans ((congrMul ih (.eqRefl _)).eqTrans (one_mul _))
  have h2 := Prf.allE e hall
  simpa only [Fm.subst_eq, subst_ap2, Syn.subst_var, Syn.inst_zero, ConciseIPRA.PTm.subst_zero,
    ConciseIPRA.PTm.subst_succ] using h2

/-- `0^{e+1} = 0`. -/
theorem zero_pw (e : PTm k) : Γ ⊢[PRAAx] pw zero (succ e) ≐ zero := by
  ipra_lc natEq (pw_succ (Γ := Γ) zero e)

/-- `s^{e+1} = 1` gives `s = 1`. -/
theorem s_eq_one {s e : PTm k} (h : Γ ⊢[PRAAx] pw s (succ e) ≐ one) : Γ ⊢[PRAAx] s ≐ one := by
  refine .orE (zero_or_succ s) ?_ ?_
  · have hs : ((s ≐ zero) :: Γ) ⊢[PRAAx] s ≐ zero := Prf.hyp0
    have h1 : ((s ≐ zero) :: Γ) ⊢[PRAAx] pw s (succ e) ≐ one := h.wk
    have e1 := natEq h1
    have c : ((s ≐ zero) :: Γ) ⊢[PRAAx] succ zero ≐ zero := by
      ipra_lc -e1 + natEq (pw_succ (Γ := (s ≐ zero) :: Γ) s e) + 𝔞 (pw s e) * natEq hs
    exact succ_ne_zero' _ c
  · refine .orE (zero_or_succ (pred s)) ?_ ?_
    · have hs : ((pred s ≐ zero) :: (s ≐ succ (pred s)) :: Γ) ⊢[PRAAx] s ≐ succ (pred s) := Prf.hyp1
      have hp : ((pred s ≐ zero) :: (s ≐ succ (pred s)) :: Γ) ⊢[PRAAx] pred s ≐ zero := Prf.hyp0
      exact hs.eqTrans (congrSucc hp)
    · let Δ : List (Fm PTm k) := (pred s ≐ succ (pred (pred s))) :: (s ≐ succ (pred s)) :: Γ
      have hs : Δ ⊢[PRAAx] s ≐ succ (pred s) := Prf.hyp1
      have hp : Δ ⊢[PRAAx] pred s ≐ succ (pred (pred s)) := Prf.hyp0
      have hle : Δ ⊢[PRAAx] le s (pw s (succ e)) :=
        le_congr hs.eqSymm (congrPwBase _ hs.eqSymm) (le_self_pw (pred s) e)
      have h1 : Δ ⊢[PRAAx] pw s (succ e) ≐ one := h.wk.wk
      have e1 := natEq h1
      have es := natEq hs
      have ep := natEq hp
      have c : Δ ⊢[PRAAx] le (succ one) one := by
        ipra_le sl hle + 𝔞 (pred (pred s)) using linear_combination -e1 + es + ep
      exact not_succ_le_self one _ c

section Family

variable {s t j r : PTm k}

/-- `x = t ≥ 0`: `s^m = (t^r)^m + t + 1` with `m = j + 3`, `r ≥ 1` forces `t = 0` and `s = 1`. -/
theorem pos_branch
    (h : Γ ⊢[PRAAx] pw s (succ (succ (succ j))) ≐ pw (pw t (succ r)) (succ (succ (succ j))) + t + one) :
    Γ ⊢[PRAAx] (t ≐ zero) ⋏ (s ≐ one) := by
  refine .orE (zero_or_succ t) ?_ ?_
  · let Δ : List (Fm PTm k) := (t ≐ zero) :: Γ
    have ht : Δ ⊢[PRAAx] t ≐ zero := Prf.hyp0
    have h1 : Δ ⊢[PRAAx] pw s (succ (succ (succ j))) ≐
        pw (pw t (succ r)) (succ (succ (succ j))) + t + one := h.wk
    have e := natEq h1
    have z := natEq ht
    have hsm : Δ ⊢[PRAAx] pw s (succ (succ (succ j))) ≐ one := by
      ipra_lc e + natEq (pw_succ (Γ := Δ) (pw t (succ r)) (succ (succ j))) +
        𝔞 (pw (pw t (succ r)) (succ (succ j))) * natEq (pw_succ (Γ := Δ) t r) +
        (1 + 𝔞 (pw (pw t (succ r)) (succ (succ j))) * 𝔞 (pw t r)) * z
    exact .andI ht (s_eq_one hsm)
  · let Δ : List (Fm PTm k) := (t ≐ succ (pred t)) :: Γ
    have ht : Δ ⊢[PRAAx] t ≐ succ (pred t) := Prf.hyp0
    have hT : Δ ⊢[PRAAx] le t (pw t (succ r)) :=
      le_congr ht.eqSymm (congrPwBase _ ht.eqSymm) (le_self_pw (pred t) r)
    refine .orE (lt_or_le (pw t (succ r)) s) ?_ ?_
    · let Δ₂ : List (Fm PTm k) := lt (pw t (succ r)) s :: Δ
      have hlt : Δ₂ ⊢[PRAAx] lt (pw t (succ r)) s := Prf.hyp0
      have hlt' : Δ₂ ⊢[PRAAx] le (succ (pw t (succ r))) s := hlt
      refine .orE (zero_or_succ s) ?_ ?_
      · have hs0 : ((s ≐ zero) :: Δ₂) ⊢[PRAAx] s ≐ zero := Prf.hyp0
        have hl : ((s ≐ zero) :: Δ₂) ⊢[PRAAx] le (succ (pw t (succ r))) s := hlt'.wk
        have z := natEq hs0
        have c : ((s ≐ zero) :: Δ₂) ⊢[PRAAx] le (succ zero) zero := by
          ipra_le sl hl + 𝔞 (pw t (succ r)) using linear_combination -z
        exact not_succ_le_self zero _ c
      · let Δ₃ : List (Fm PTm k) := (s ≐ succ (pred s)) :: Δ₂
        have hs : Δ₃ ⊢[PRAAx] s ≐ succ (pred s) := Prf.hyp0
        have hq : Δ₃ ⊢[PRAAx] le s (pw s (succ j)) :=
          le_congr hs.eqSymm (congrPwBase _ hs.eqSymm) (le_self_pw (pred s) j)
        have g : Δ₃ ⊢[PRAAx] le (pw (pw t (succ r)) (succ (succ (succ j))) + pw s (succ (succ j)))
            (pw s (succ (succ (succ j)))) := strict_power_gap hlt.wk (succ (succ j))
        have hl : Δ₃ ⊢[PRAAx] le (succ (pw t (succ r))) s := hlt'.wk
        have hT3 : Δ₃ ⊢[PRAAx] le t (pw t (succ r)) := hT.wk.wk
        have h3 : Δ₃ ⊢[PRAAx] pw s (succ (succ (succ j))) ≐
            pw (pw t (succ r)) (succ (succ (succ j))) + t + one := h.wk.wk.wk
        have ht3 : Δ₃ ⊢[PRAAx] t ≐ succ (pred t) := ht.wk.wk
        have e := natEq h3
        have pe := natEq (pw_succ (Γ := Δ₃) s (succ j))
        have et := natEq ht3
        have c : Δ₃ ⊢[PRAAx] le (succ zero) zero := by
          ipra_le sl g + 𝔞 s * sl hq + (𝔞 s + 1) * sl hl + (𝔞 s + 1) * sl hT3 + 𝔞 s * 𝔞 (pred t) + sl hl +
            𝔞 (pw t (succ r)) using linear_combination -e + pe + 𝔞 s * et
        exact not_succ_le_self zero _ c
    · let Δ₂ : List (Fm PTm k) := le s (pw t (succ r)) :: Δ
      have hle : Δ₂ ⊢[PRAAx] le s (pw t (succ r)) := Prf.hyp0
      have hm := pw_le_pw (succ (succ (succ j))) hle
      have h2 : Δ₂ ⊢[PRAAx] pw s (succ (succ (succ j))) ≐
          pw (pw t (succ r)) (succ (succ (succ j))) + t + one := h.wk.wk
      have e := natEq h2
      have c : Δ₂ ⊢[PRAAx] le (succ zero) zero := by
        ipra_le sl hm + 𝔞 t using linear_combination e
      exact not_succ_le_self zero _ c

/-- `x = −(t + 1)`: `s^m + (t + 1) = ((t + 1)^r)^m + 1` with `m = j + 3`, `r ≥ 1` forces `t = 0`, `s = 1`. -/
theorem neg_branch
    (h : Γ ⊢[PRAAx] pw s (succ (succ (succ j))) + succ t ≐
      pw (pw (succ t) (succ r)) (succ (succ (succ j))) + one) :
    Γ ⊢[PRAAx] (t ≐ zero) ⋏ (s ≐ one) := by
  refine .orE (zero_or_succ t) ?_ ?_
  · let Δ : List (Fm PTm k) := (t ≐ zero) :: Γ
    have ht : Δ ⊢[PRAAx] t ≐ zero := Prf.hyp0
    have eT : Δ ⊢[PRAAx] pw (succ t) (succ r) ≐ one := (congrPwBase _ (congrSucc ht)).eqTrans (one_pw _)
    have eTm : Δ ⊢[PRAAx] pw (pw (succ t) (succ r)) (succ (succ (succ j))) ≐ one :=
      (congrPwBase _ eT).eqTrans (one_pw _)
    have h1 : Δ ⊢[PRAAx] pw s (succ (succ (succ j))) + succ t ≐
        pw (pw (succ t) (succ r)) (succ (succ (succ j))) + one := h.wk
    have e := natEq h1
    have z := natEq ht
    have hsm : Δ ⊢[PRAAx] pw s (succ (succ (succ j))) ≐ one := by
      ipra_lc e - z + natEq eTm
    exact .andI ht (s_eq_one hsm)
  · let Δ : List (Fm PTm k) := (t ≐ succ (pred t)) :: Γ
    have ht : Δ ⊢[PRAAx] t ≐ succ (pred t) := Prf.hyp0
    have hT : Δ ⊢[PRAAx] le (succ t) (pw (succ t) (succ r)) := le_self_pw t r
    refine .orE (lt_or_le s (pw (succ t) (succ r))) ?_ ?_
    · let Δ₂ : List (Fm PTm k) := lt s (pw (succ t) (succ r)) :: Δ
      have hlt : Δ₂ ⊢[PRAAx] lt s (pw (succ t) (succ r)) := Prf.hyp0
      have hT2 : Δ₂ ⊢[PRAAx] le (succ t) (pw (succ t) (succ r)) := hT.wk
      refine .orE (zero_or_succ (pw (succ t) (succ r))) ?_ ?_
      · have h0 : ((pw (succ t) (succ r) ≐ zero) :: Δ₂) ⊢[PRAAx] pw (succ t) (succ r) ≐ zero := Prf.hyp0
        have hl : ((pw (succ t) (succ r) ≐ zero) :: Δ₂) ⊢[PRAAx] le (succ t) (pw (succ t) (succ r)) := hT2.wk
        have z := natEq h0
        have c : ((pw (succ t) (succ r) ≐ zero) :: Δ₂) ⊢[PRAAx] le (succ zero) zero := by
          ipra_le sl hl + 𝔞 t using linear_combination -z
        exact not_succ_le_self zero _ c
      · let Δ₃ : List (Fm PTm k) := (pw (succ t) (succ r) ≐ succ (pred (pw (succ t) (succ r)))) :: Δ₂
        have hs : Δ₃ ⊢[PRAAx] pw (succ t) (succ r) ≐ succ (pred (pw (succ t) (succ r))) := Prf.hyp0
        have hq : Δ₃ ⊢[PRAAx] le (pw (succ t) (succ r)) (pw (pw (succ t) (succ r)) (succ (succ j))) :=
          le_congr hs.eqSymm (congrPwBase _ hs.eqSymm) (le_self_pw (pred (pw (succ t) (succ r))) (succ j))
        have g : Δ₃ ⊢[PRAAx] le (pw s (succ (succ (succ j))) + pw (pw (succ t) (succ r)) (succ (succ j)))
            (pw (pw (succ t) (succ r)) (succ (succ (succ j)))) := strict_power_gap hlt.wk (succ (succ j))
        have hT3 : Δ₃ ⊢[PRAAx] le (succ t) (pw (succ t) (succ r)) := hT2.wk
        have h3 : Δ₃ ⊢[PRAAx] pw s (succ (succ (succ j))) + succ t ≐
            pw (pw (succ t) (succ r)) (succ (succ (succ j))) + one := h.wk.wk.wk
        have e := natEq h3
        have c : Δ₃ ⊢[PRAAx] le (succ zero) zero := by
          ipra_le sl g + sl hq + sl hT3 using linear_combination e
        exact not_succ_le_self zero _ c
    · let Δ₂ : List (Fm PTm k) := le (pw (succ t) (succ r)) s :: Δ
      have hle : Δ₂ ⊢[PRAAx] le (pw (succ t) (succ r)) s := Prf.hyp0
      have hm := pw_le_pw (succ (succ (succ j))) hle
      have h2 : Δ₂ ⊢[PRAAx] pw s (succ (succ (succ j))) + succ t ≐
          pw (pw (succ t) (succ r)) (succ (succ (succ j))) + one := h.wk.wk
      have ht2 : Δ₂ ⊢[PRAAx] t ≐ succ (pred t) := ht.wk
      have e := natEq h2
      have et := natEq ht2
      have c : Δ₂ ⊢[PRAAx] le (succ zero) zero := by
        ipra_le sl hm + 𝔞 (pred t) using linear_combination -e + et
      exact not_succ_le_self zero _ c

/-- Odd `m`, `y = −s`, `x = t ≥ 0`: `−s^m = x^{mr} + x + 1` is impossible. -/
theorem neg_y_nonneg_x (φ : Fm PTm k)
    (h : Γ ⊢[PRAAx] pw s (succ (succ (succ j))) + (pw (pw t (succ r)) (succ (succ (succ j))) + t + one) ≐ zero) :
    Γ ⊢[PRAAx] φ := by
  have e := natEq h
  have c : Γ ⊢[PRAAx] le (succ zero) zero := by
    ipra_le 𝔞 (pw s (succ (succ (succ j)))) + 𝔞 (pw (pw t (succ r)) (succ (succ (succ j)))) + 𝔞 t using
      linear_combination -e
  exact not_succ_le_self zero _ c

/-- Odd `m`, `y = −s`, `x = −(t + 1)`: `s^m + ((t + 1)^r)^m + 1 = t + 1` is impossible. -/
theorem neg_y_neg_x (φ : Fm PTm k)
    (h : Γ ⊢[PRAAx] pw s (succ (succ (succ j))) + pw (pw (succ t) (succ r)) (succ (succ (succ j))) + one ≐
      succ t) : Γ ⊢[PRAAx] φ := by
  have hT : Γ ⊢[PRAAx] le (succ t) (pw (succ t) (succ r)) := le_self_pw t r
  refine .orE (zero_or_succ (pw (succ t) (succ r))) ?_ ?_
  · have h0 : ((pw (succ t) (succ r) ≐ zero) :: Γ) ⊢[PRAAx] pw (succ t) (succ r) ≐ zero := Prf.hyp0
    have hl : ((pw (succ t) (succ r) ≐ zero) :: Γ) ⊢[PRAAx] le (succ t) (pw (succ t) (succ r)) := hT.wk
    have z := natEq h0
    have c : ((pw (succ t) (succ r) ≐ zero) :: Γ) ⊢[PRAAx] le (succ zero) zero := by
      ipra_le sl hl + 𝔞 t using linear_combination -z
    exact not_succ_le_self zero _ c
  · let Δ : List (Fm PTm k) := (pw (succ t) (succ r) ≐ succ (pred (pw (succ t) (succ r)))) :: Γ
    have hs : Δ ⊢[PRAAx] pw (succ t) (succ r) ≐ succ (pred (pw (succ t) (succ r))) := Prf.hyp0
    have hq : Δ ⊢[PRAAx] le (pw (succ t) (succ r)) (pw (pw (succ t) (succ r)) (succ (succ (succ j)))) :=
      le_congr hs.eqSymm (congrPwBase _ hs.eqSymm) (le_self_pw (pred (pw (succ t) (succ r))) (succ (succ j)))
    have hT1 : Δ ⊢[PRAAx] le (succ t) (pw (succ t) (succ r)) := hT.wk
    have h1 : Δ ⊢[PRAAx] pw s (succ (succ (succ j))) + pw (pw (succ t) (succ r)) (succ (succ (succ j))) + one ≐
        succ t := h.wk
    have e := natEq h1
    have c : Δ ⊢[PRAAx] le (succ zero) zero := by
      ipra_le sl hT1 + sl hq + 𝔞 (pw s (succ (succ (succ j)))) using linear_combination -e
    exact not_succ_le_self zero _ c

/-- The point `(0, 1)`: `1^m = (0^r)^m + 0 + 1`. -/
theorem point_zero : Γ ⊢[PRAAx] pw one (succ (succ (succ j))) ≐
    pw (pw zero (succ r)) (succ (succ (succ j))) + zero + one := by
  ipra_lc natEq (one_pw (Γ := Γ) (succ (succ (succ j)))) -
    natEq (congrPwBase (Γ := Γ) (succ (succ (succ j))) (zero_pw r)) - natEq (zero_pw (Γ := Γ) (succ (succ j)))

/-- The points `(−1, ±1)`: with `x = −(0 + 1)`, `1^m + 1 = (1^r)^m + 1`. -/
theorem point_neg_one : Γ ⊢[PRAAx] pw one (succ (succ (succ j))) + succ zero ≐
    pw (pw (succ zero) (succ r)) (succ (succ (succ j))) + one := by
  ipra_lc -natEq (congrPwBase (Γ := Γ) (succ (succ (succ j))) (one_pw (succ r)))

end Family

end LeanProofs.IPRA.DiophantineNumberTheory.SuperellipticFamily
