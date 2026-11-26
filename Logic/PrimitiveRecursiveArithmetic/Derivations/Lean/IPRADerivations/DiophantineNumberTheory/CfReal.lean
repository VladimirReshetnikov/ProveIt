import IPRADerivations.DiophantineNumberTheory.HurwitzLoop
import IPRADerivations.AnalyticNumberTheory.PhiLower
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.SubstCommand

/-!
# A primitive recursive continued-fraction real

Packet: `diophantine-number-theory/number_theory_ipra_2026-11-22`, `chapters/diophantine.tex`, `dio:cf-real`:

  "Fix a primitive recursive coefficient function `a(n)` with `a(0) ≥ 0` and `a(n) ≥ 1` for `n > 0`. Its
  convergents satisfy `m > n ⟹ |p_m/q_m − p_n/q_n| ≤ q_n^{−2}`. Consequently `r_k = p_{2k+2}/q_{2k+2}` is a
  primitive recursive rational name with `|r_ℓ − r_k| ≤ 2^{−2k−2}` whenever `ℓ > k`."

The coefficients are `a_0 = a'(0)` and `a_j = a'(j) + 1` for `j ≥ 1`, for an arbitrary unary primitive
recursive symbol `a'` (as in `Hurwitz`), so every admissible coefficient function is covered. The convergent
state `cv m = ⟨p_m, q_m, p_{m−1}, q_{m−1}⟩` starts at `⟨a_0, 1, 1, 0⟩` and steps by
`⟨a P + P', a Q + Q', P, Q⟩`.

* `uv k N = ⟨u_k, v_k, u_{k−1}, v_{k−1}⟩`: the same recursion from `⟨1, 0, 0, 1⟩` with the coefficients
  `a_{N+1}, a_{N+2}, …`; **`lin`**: `p_{N+k} = u_k p_N + v_k p_{N−1}`, `q_{N+k} = u_k q_N + v_k q_{N−1}`
  (and the same one row down), the matrix form of the tail `t = u_k/v_k`;
* **`det`**: `p_{m−1} q_m − p_m q_{m−1} = ±1`; **`jinv`**: `v_k ≤ u_k` (the tail is at least one);
* **`cf_bound`**: for `N ≤ M`, `|p_M q_N − p_N q_M| · q_N ≤ q_M`, that is `|p_M/q_M − p_N/q_N| ≤ q_N^{−2}`,
  as two inequalities without signs;
* **`q_pow`**: `q_{2k+2} ≥ 2^{k+1}` (from `q_{m+2} ≥ 2 q_m`, `two_step`);
* the growth bounds of `dio:continuants`: `q_zero` (`q_0 = 1`), `q_le_succ`, `q_pos`, **`q_lt_succ`**
  (`q_{m+1} < q_{m+2}`), **`two_step`**, **`q_pow_even`** (`q_{2k} ≥ 2^k`);
* **`cf_real`**: for `k ≤ l`, `|r_l − r_k| ≤ 2^{−2k−2}` for `r_k = p_{2k+2}/q_{2k+2}`, cleared of
  denominators.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.CfReal

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.DiophantineNumberTheory.HurwitzLoop (sP sQ sP' sQ' st proj_st)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The step and its algebra -/

/-- The step `⟨c P + P', c Q + Q', P, Q⟩`. -/
abbrev nx (c s : PTm n) : PTm n := st (c * sP s + sP' s) (c * sQ s + sQ' s) (sP s) (sQ s)

theorem proj_nx {c s s' : PTm n} (h : Γ ⊢[PRAAx] s' ≐ nx c s) :
    (Γ ⊢[PRAAx] sP s' ≐ c * sP s + sP' s) ∧ (Γ ⊢[PRAAx] sQ s' ≐ c * sQ s + sQ' s) ∧
      (Γ ⊢[PRAAx] sP' s' ≐ sP s) ∧ (Γ ⊢[PRAAx] sQ' s' ≐ sQ s) := by
  obtain ⟨p1, p2, p3, p4⟩ := proj_st (Γ := Γ) (c * sP s + sP' s) (c * sQ s + sQ' s) (sP s) (sQ s)
  exact ⟨(congrFst h).eqTrans p1, (congrFst (congrSnd h)).eqTrans p2,
    (congrFst (congrSnd (congrSnd h))).eqTrans p3, (congrSnd (congrSnd (congrSnd h))).eqTrans p4⟩

/-- `s` is `w` times `C`: `s = ⟨u P + v P', u Q + v Q', u' P + v' P', u' Q + v' Q'⟩` for `w = ⟨u, v, u', v'⟩`,
`C = ⟨P, Q, P', Q'⟩`. -/
def Lin4 (s C w : PTm n) : Fm PTm n :=
  ((sP s ≐ sP w * sP C + sQ w * sP' C) ⋏ (sQ s ≐ sP w * sQ C + sQ w * sQ' C)) ⋏
    ((sP' s ≐ sP' w * sP C + sQ' w * sP' C) ⋏ (sQ' s ≐ sP' w * sQ C + sQ' w * sQ' C))

ipra_subst Lin4

theorem lin4_QF (s C w : PTm n) : (Lin4 s C w).QF := by
  simp [Lin4, Fm.QF]

theorem lin_alg {c x1 x2 x3 x4 y1 y2 y3 y4 u v u' v' U V U' V' P Q P' Q' : PTm n}
    (i1 : Γ ⊢[PRAAx] x1 ≐ u * P + v * P') (i2 : Γ ⊢[PRAAx] x2 ≐ u * Q + v * Q')
    (i3 : Γ ⊢[PRAAx] x3 ≐ u' * P + v' * P') (i4 : Γ ⊢[PRAAx] x4 ≐ u' * Q + v' * Q')
    (h1 : Γ ⊢[PRAAx] y1 ≐ c * x1 + x3) (h2 : Γ ⊢[PRAAx] y2 ≐ c * x2 + x4)
    (h3 : Γ ⊢[PRAAx] y3 ≐ x1) (h4 : Γ ⊢[PRAAx] y4 ≐ x2)
    (g1 : Γ ⊢[PRAAx] U ≐ c * u + u') (g2 : Γ ⊢[PRAAx] V ≐ c * v + v')
    (g3 : Γ ⊢[PRAAx] U' ≐ u) (g4 : Γ ⊢[PRAAx] V' ≐ v) :
    Γ ⊢[PRAAx] ((y1 ≐ U * P + V * P') ⋏ (y2 ≐ U * Q + V * Q')) ⋏
      ((y3 ≐ U' * P + V' * P') ⋏ (y4 ≐ U' * Q + V' * Q')) := by
  have j1 := natEq i1; have j2 := natEq i2; have j3 := natEq i3; have j4 := natEq i4
  have e1 := natEq h1; have e2 := natEq h2; have e3 := natEq h3; have e4 := natEq h4
  have f1 := natEq g1; have f2 := natEq g2; have f3 := natEq g3; have f4 := natEq g4
  refine .andI (.andI ?_ ?_) (.andI ?_ ?_)
  · ipra_lc e1 + 𝔞 c * j1 + j3 - 𝔞 P * f1 - 𝔞 P' * f2
  · ipra_lc e2 + 𝔞 c * j2 + j4 - 𝔞 Q * f1 - 𝔞 Q' * f2
  · ipra_lc e3 + j1 - 𝔞 P * f3 - 𝔞 P' * f4
  · ipra_lc e4 + j2 - 𝔞 Q * f3 - 𝔞 Q' * f4

theorem lin_base_alg {x1 x2 x3 x4 u v u' v' P Q P' Q' : PTm n}
    (s1 : Γ ⊢[PRAAx] x1 ≐ P) (s2 : Γ ⊢[PRAAx] x2 ≐ Q) (s3 : Γ ⊢[PRAAx] x3 ≐ P') (s4 : Γ ⊢[PRAAx] x4 ≐ Q')
    (u1 : Γ ⊢[PRAAx] u ≐ one) (u2 : Γ ⊢[PRAAx] v ≐ zero) (u3 : Γ ⊢[PRAAx] u' ≐ zero)
    (u4 : Γ ⊢[PRAAx] v' ≐ one) :
    Γ ⊢[PRAAx] ((x1 ≐ u * P + v * P') ⋏ (x2 ≐ u * Q + v * Q')) ⋏
      ((x3 ≐ u' * P + v' * P') ⋏ (x4 ≐ u' * Q + v' * Q')) := by
  have t1 := natEq s1; have t2 := natEq s2; have t3 := natEq s3; have t4 := natEq s4
  have w1 := natEq u1; have w2 := natEq u2; have w3 := natEq u3; have w4 := natEq u4
  refine .andI (.andI ?_ ?_) (.andI ?_ ?_)
  · ipra_lc t1 - 𝔞 P * w1 - 𝔞 P' * w2
  · ipra_lc t2 - 𝔞 Q * w1 - 𝔞 Q' * w2
  · ipra_lc t3 - 𝔞 P * w3 - 𝔞 P' * w4
  · ipra_lc t4 - 𝔞 Q * w3 - 𝔞 Q' * w4

theorem lin_step {c s s' C w w' : PTm n} (hs : Γ ⊢[PRAAx] s' ≐ nx c s) (hw : Γ ⊢[PRAAx] w' ≐ nx c w)
    (ih : Γ ⊢[PRAAx] Lin4 s C w) : Γ ⊢[PRAAx] Lin4 s' C w' := by
  obtain ⟨h1, h2, h3, h4⟩ := proj_nx hs
  obtain ⟨g1, g2, g3, g4⟩ := proj_nx hw
  unfold Lin4 at ih ⊢
  exact lin_alg (Prf.andE₁ (Prf.andE₁ ih)) (Prf.andE₂ (Prf.andE₁ ih)) (Prf.andE₁ (Prf.andE₂ ih))
    (Prf.andE₂ (Prf.andE₂ ih)) h1 h2 h3 h4 g1 g2 g3 g4

/-- The unit determinant, with either sign. -/
def Det (s : PTm n) : Fm PTm n :=
  (sP' s * sQ s ≐ sP s * sQ' s + one) ⋎ (sP s * sQ' s ≐ sP' s * sQ s + one)

ipra_subst Det

theorem det_QF (s : PTm n) : (Det s).QF := by
  simp [Det, Fm.QF]

theorem det_pos {c P Q P' Q' P1 Q1 P1' Q1' : PTm n}
    (h1 : Γ ⊢[PRAAx] P1 ≐ c * P + P') (h2 : Γ ⊢[PRAAx] Q1 ≐ c * Q + Q') (h3 : Γ ⊢[PRAAx] P1' ≐ P)
    (h4 : Γ ⊢[PRAAx] Q1' ≐ Q) (d : Γ ⊢[PRAAx] P' * Q ≐ P * Q' + one) :
    Γ ⊢[PRAAx] P1 * Q1' ≐ P1' * Q1 + one := by
  ipra_lc 𝔞 Q1' * natEq h1 + (𝔞 c * 𝔞 P + 𝔞 P') * natEq h4 - 𝔞 Q1 * natEq h3 - 𝔞 P * natEq h2 + natEq d

theorem det_neg {c P Q P' Q' P1 Q1 P1' Q1' : PTm n}
    (h1 : Γ ⊢[PRAAx] P1 ≐ c * P + P') (h2 : Γ ⊢[PRAAx] Q1 ≐ c * Q + Q') (h3 : Γ ⊢[PRAAx] P1' ≐ P)
    (h4 : Γ ⊢[PRAAx] Q1' ≐ Q) (d : Γ ⊢[PRAAx] P * Q' ≐ P' * Q + one) :
    Γ ⊢[PRAAx] P1' * Q1 ≐ P1 * Q1' + one := by
  ipra_lc 𝔞 Q1 * natEq h3 + 𝔞 P * natEq h2 - 𝔞 Q1' * natEq h1 - (𝔞 c * 𝔞 P + 𝔞 P') * natEq h4 + natEq d

theorem det_step {c s s' : PTm n} (hs : Γ ⊢[PRAAx] s' ≐ nx c s) (hd : Γ ⊢[PRAAx] Det s) :
    Γ ⊢[PRAAx] Det s' := by
  obtain ⟨h1, h2, h3, h4⟩ := proj_nx hs
  unfold Det at hd ⊢
  refine .orE hd ?_ ?_
  · exact .orI₂ (det_pos h1.wk h2.wk h3.wk h4.wk Prf.hyp0)
  · exact .orI₁ (det_neg h1.wk h2.wk h3.wk h4.wk Prf.hyp0)

theorem det_base {P Q P' Q' : PTm n} (p2 : Γ ⊢[PRAAx] Q ≐ one) (p3 : Γ ⊢[PRAAx] P' ≐ one)
    (p4 : Γ ⊢[PRAAx] Q' ≐ zero) : Γ ⊢[PRAAx] (P' * Q ≐ P * Q' + one) ⋎ (P * Q' ≐ P' * Q + one) := by
  have f2 := natEq p2; have f3 := natEq p3; have f4 := natEq p4
  refine .orI₁ ?_
  ipra_lc 𝔞 Q * f3 + f2 - 𝔞 P * f4

/-- `v ≤ u` and `v + v' ≤ u + u'` for `w = ⟨u, v, u', v'⟩`. -/
def Jf (w : PTm n) : Fm PTm n := le (sQ w) (sP w) ⋏ le (sQ w + sQ' w) (sP w + sP' w)

ipra_subst Jf

theorem jf_QF (w : PTm n) : (Jf w).QF := by
  simp [Jf, Fm.QF, le_QF]

theorem j_alg {c0 u v u' v' U V U' V' : PTm n}
    (g1 : Γ ⊢[PRAAx] U ≐ succ c0 * u + u') (g2 : Γ ⊢[PRAAx] V ≐ succ c0 * v + v')
    (g3 : Γ ⊢[PRAAx] U' ≐ u) (g4 : Γ ⊢[PRAAx] V' ≐ v)
    (h : Γ ⊢[PRAAx] le v u ⋏ le (v + v') (u + u')) : Γ ⊢[PRAAx] le V U ⋏ le (V + V') (U + U') := by
  have h1 := Prf.andE₁ h
  have h2 := Prf.andE₂ h
  have f1 := natEq g1; have f2 := natEq g2; have f3 := natEq g3; have f4 := natEq g4
  refine .andI ?_ ?_
  · ipra_le 𝔞 c0 * sl h1 + sl h2 with f1 - f2
  · ipra_le 𝔞 c0 * sl h1 + sl h2 + sl h1 with f1 - f2 + f3 - f4

theorem j_base {u v u' v' : PTm n} (u1 : Γ ⊢[PRAAx] u ≐ one) (u2 : Γ ⊢[PRAAx] v ≐ zero)
    (u3 : Γ ⊢[PRAAx] u' ≐ zero) (u4 : Γ ⊢[PRAAx] v' ≐ one) :
    Γ ⊢[PRAAx] le v u ⋏ le (v + v') (u + u') := by
  have w1 := natEq u1; have w2 := natEq u2; have w3 := natEq u3; have w4 := natEq u4
  refine .andI ?_ ?_
  · ipra_le 1 with w1 - w2
  · ipra_le 0 with w1 + w3 - w2 - w4

/-! ## The bound, algebraically -/

theorem bound_pos {x1 x2 u v P Q P' Q' : PTm n}
    (i1 : Γ ⊢[PRAAx] x1 ≐ u * P + v * P') (i2 : Γ ⊢[PRAAx] x2 ≐ u * Q + v * Q') (hv : Γ ⊢[PRAAx] le v u)
    (d : Γ ⊢[PRAAx] P' * Q ≐ P * Q' + one) :
    Γ ⊢[PRAAx] le (x1 * Q * Q) (P * x2 * Q + x2) ⋏ le (P * x2 * Q) (x1 * Q * Q + x2) := by
  have j1 := natEq i1; have j2 := natEq i2; have x := natEq d
  refine .andI ?_ ?_
  · ipra_le 𝔞 Q * sl hv + 𝔞 v * 𝔞 Q' with 𝔞 P * 𝔞 Q * j2 + j2 - 𝔞 Q * 𝔞 Q * j1 - 𝔞 Q * 𝔞 v * x
  · ipra_le 𝔞 Q * 𝔞 v + 𝔞 x2 with 𝔞 Q * 𝔞 Q * j1 - 𝔞 P * 𝔞 Q * j2 + 𝔞 Q * 𝔞 v * x

theorem bound_neg {x1 x2 u v P Q P' Q' : PTm n}
    (i1 : Γ ⊢[PRAAx] x1 ≐ u * P + v * P') (i2 : Γ ⊢[PRAAx] x2 ≐ u * Q + v * Q') (hv : Γ ⊢[PRAAx] le v u)
    (d : Γ ⊢[PRAAx] P * Q' ≐ P' * Q + one) :
    Γ ⊢[PRAAx] le (x1 * Q * Q) (P * x2 * Q + x2) ⋏ le (P * x2 * Q) (x1 * Q * Q + x2) := by
  have j1 := natEq i1; have j2 := natEq i2; have x := natEq d
  refine .andI ?_ ?_
  · ipra_le 𝔞 Q * 𝔞 v + 𝔞 x2 with -(𝔞 Q * 𝔞 Q * j1) + 𝔞 P * 𝔞 Q * j2 + 𝔞 Q * 𝔞 v * x
  · ipra_le 𝔞 Q * sl hv + 𝔞 v * 𝔞 Q' with 𝔞 Q * 𝔞 Q * j1 - 𝔞 P * 𝔞 Q * j2 - 𝔞 Q * 𝔞 v * x + j2

theorem bound_alg {x1 x2 u v P Q P' Q' : PTm n}
    (i1 : Γ ⊢[PRAAx] x1 ≐ u * P + v * P') (i2 : Γ ⊢[PRAAx] x2 ≐ u * Q + v * Q') (hv : Γ ⊢[PRAAx] le v u)
    (d : Γ ⊢[PRAAx] (P' * Q ≐ P * Q' + one) ⋎ (P * Q' ≐ P' * Q + one)) :
    Γ ⊢[PRAAx] le (x1 * Q * Q) (P * x2 * Q + x2) ⋏ le (P * x2 * Q) (x1 * Q * Q + x2) := by
  refine .orE d ?_ ?_
  · exact bound_pos i1.wk i2.wk hv.wk Prf.hyp0
  · exact bound_neg i1.wk i2.wk hv.wk Prf.hyp0

/-- From `A Q ≤ B Q + x` and `F ≤ Q²`: `A F ≤ B F + x Q`. -/
theorem scale_alg {A B x Q F : PTm n} (hm : Γ ⊢[PRAAx] le (A * Q) (B * Q + x)) (hF : Γ ⊢[PRAAx] le F (Q * Q)) :
    Γ ⊢[PRAAx] le (A * F) (B * F + x * Q) := by
  refine .orE (lt_or_le B A) ?_ ?_
  · have hBA : (lt B A :: Γ) ⊢[PRAAx] le B A := le_of_lt Prf.hyp0
    have eA := natEq (eq_add_of_le hBA)
    have hm' : (lt B A :: Γ) ⊢[PRAAx] le (A * Q) (B * Q + x) := hm.wk
    have hMQ : (lt B A :: Γ) ⊢[PRAAx] le (monus A B * Q) x := by
      ipra_le sl hm' with 𝔞 Q * eA
    have h1 : (lt B A :: Γ) ⊢[PRAAx] le (monus A B * F) (monus A B * (Q * Q)) := le_mul_mono (le_refl _) hF.wk
    have h2 : (lt B A :: Γ) ⊢[PRAAx] le (monus A B * Q * Q) (x * Q) := le_mul_mono hMQ (le_refl Q)
    ipra_le sl h1 + sl h2 with 𝔞 F * eA
  · have hAB : (le A B :: Γ) ⊢[PRAAx] le A B := Prf.hyp0
    exact le_trans (le_mul_mono hAB (le_refl F)) (le_add_right _ _)

theorem two_alg {c0 c1 Q Q' Q1 Q1' Q2 : PTm n} (a1 : Γ ⊢[PRAAx] Q1 ≐ succ c0 * Q + Q')
    (a2 : Γ ⊢[PRAAx] Q1' ≐ Q) (b : Γ ⊢[PRAAx] Q2 ≐ succ c1 * Q1 + Q1') : Γ ⊢[PRAAx] le (two * Q) Q2 := by
  have fa1 := natEq a1; have fa2 := natEq a2; have fb := natEq b
  ipra_le 𝔞 c1 * 𝔞 Q1 + 𝔞 c0 * 𝔞 Q + 𝔞 Q' with fb + fa1 + fa2

theorem pow_base_alg {G G0 Q0 Q2 : PTm n} (g1 : Γ ⊢[PRAAx] G ≐ G0 * two) (g0 : Γ ⊢[PRAAx] G0 ≐ one)
    (h : Γ ⊢[PRAAx] le (two * Q0) Q2) (q : Γ ⊢[PRAAx] Q0 ≐ one) : Γ ⊢[PRAAx] le G Q2 := by
  have e1 := natEq g1; have e0 := natEq g0; have eq := natEq q
  ipra_le sl h with 2 * eq - e1 - 2 * e0

theorem pow_step_alg {G G' Q Q2 Q2' : PTm n} (ih : Γ ⊢[PRAAx] le G Q) (g : Γ ⊢[PRAAx] G' ≐ G * two)
    (h : Γ ⊢[PRAAx] le (two * Q) Q2) (e : Γ ⊢[PRAAx] Q2' ≐ Q2) : Γ ⊢[PRAAx] le G' Q2' := by
  have eg := natEq g; have ee := natEq e
  ipra_le 2 * sl ih + sl h with ee - eg

/-! ## The convergents -/

variable (a' : PR 1)

/-- `a_j = a'(j) + 1`, used for `j ≥ 1`. -/
abbrev co (j : PTm n) : PTm n := succ (ap1 a' j)

/-- The convergent step over `0 = j`, `1 = ⟨p_j, q_j, p_{j−1}, q_{j−1}⟩`, `2` unused. -/
abbrev cvStep : PTm 3 := nx (co a' (succ (var 0))) (var 1)

/-- `⟨p_0, q_0, p_{−1}, q_{−1}⟩ = ⟨a_0, 1, 1, 0⟩`. -/
abbrev cvInit : PTm 1 := st (ap1 a' zero) one one zero

/-- The state `⟨p_m, q_m, p_{m−1}, q_{m−1}⟩`. -/
abbrev cv (m : PTm n) : PTm n := ap2 (rec2 (cvInit a') (cvStep a')) m zero

/-- The tail step over `0 = k`, `1 = state`, `2 = N`: the coefficient `a_{N+k+1}`. -/
abbrev uvStep : PTm 3 := nx (co a' (succ (var 2 + var 0))) (var 1)

abbrev uvInit : PTm 1 := st one zero zero one

/-- `⟨u_k, v_k, u_{k−1}, v_{k−1}⟩` for the tail after index `N`. -/
abbrev uv (k N : PTm n) : PTm n := ap2 (rec2 uvInit (uvStep a')) k N

/-- The index `2k + 2`. -/
abbrev idx (k : PTm n) : PTm n := succ (succ (k + k))

variable {a'}

@[simp] theorem subst_cv {m : ℕ} (σ : Fin n → PTm m) (t : PTm n) :
    Syn.subst σ (cv a' t) = cv a' (Syn.subst σ t) := by
  simp [cv]

@[simp] theorem subst_uv {m : ℕ} (σ : Fin n → PTm m) (k N : PTm n) :
    Syn.subst σ (uv a' k N) = uv a' (Syn.subst σ k) (Syn.subst σ N) := by
  simp [uv]

theorem cv_zero : Γ ⊢[PRAAx] cv a' zero ≐ st (ap1 a' zero) one one zero := by
  have h := rec2_zero (Γ := Γ) (cvInit a') (cvStep a') zero
  first
  | simpa using h
  | exact h

theorem cv_succ (m : PTm n) : Γ ⊢[PRAAx] cv a' (succ m) ≐ nx (co a' (succ m)) (cv a' m) := by
  have h := rec2_succ (Γ := Γ) (cvInit a') (cvStep a') m zero
  have e : Syn.subst ![m, ap2 (rec2 (cvInit a') (cvStep a')) m zero, zero] (cvStep a') =
      nx (co a' (succ m)) (ap2 (rec2 (cvInit a') (cvStep a')) m zero) := by
    simp [cvStep, nx, co]
  rw [e] at h; exact h

theorem uv_zero (N : PTm n) : Γ ⊢[PRAAx] uv a' zero N ≐ st one zero zero one := by
  have h := rec2_zero (Γ := Γ) uvInit (uvStep a') N
  first
  | simpa using h
  | exact h

theorem uv_succ (k N : PTm n) : Γ ⊢[PRAAx] uv a' (succ k) N ≐ nx (co a' (succ (N + k))) (uv a' k N) := by
  have h := rec2_succ (Γ := Γ) uvInit (uvStep a') k N
  have e : Syn.subst ![k, ap2 (rec2 uvInit (uvStep a')) k N, N] (uvStep a') =
      nx (co a' (succ (N + k))) (ap2 (rec2 uvInit (uvStep a')) k N) := by
    simp [uvStep, nx, co, PTm.subst_add]
  rw [e] at h; exact h

/-! ## The tail matrix -/

theorem lin_base (N : PTm n) : Γ ⊢[PRAAx] Lin4 (cv a' (N + zero)) (cv a' N) (uv a' zero N) := by
  have e0 : Γ ⊢[PRAAx] cv a' (N + zero) ≐ cv a' N := congrAp2 _ (add_zero N) (.eqRefl _)
  obtain ⟨p1, p2, p3, p4⟩ := proj_st (Γ := Γ) one zero zero one
  have w := uv_zero (Γ := Γ) (a' := a') N
  unfold Lin4
  exact lin_base_alg (congrFst e0) (congrFst (congrSnd e0)) (congrFst (congrSnd (congrSnd e0)))
    (congrSnd (congrSnd (congrSnd e0))) ((congrFst w).eqTrans p1) ((congrFst (congrSnd w)).eqTrans p2)
    ((congrFst (congrSnd (congrSnd w))).eqTrans p3) ((congrSnd (congrSnd (congrSnd w))).eqTrans p4)

/-- **`p_{N+k} = u_k p_N + v_k p_{N−1}`, `q_{N+k} = u_k q_N + v_k q_{N−1}`**, and one row down. -/
theorem lin (N k : PTm n) : Γ ⊢[PRAAx] Lin4 (cv a' (N + k)) (cv a' N) (uv a' k N) := by
  have hall : Γ ⊢[PRAAx] Fm.all (Lin4 (cv a' (Syn.shift N + var 0)) (cv a' (Syn.shift N))
      (uv a' (var 0) (Syn.shift N))) := by
    refine PRA.qfInd _ (lin4_QF _ _ _) ?_ ?_
    · simp only [subst_Lin4, subst_cv, subst_uv, PTm.subst_add, Syn.subst_var, Syn.inst_zero,
        Syn.subst_inst_shift]
      exact lin_base N
    · simp only [subst_Lin4, subst_cv, subst_uv, PTm.subst_add, Syn.subst_var, Syn.repl_zero,
        subst_repl_shift, ConciseIPRA.PTm.subst_succ]
      exact lin_step ((congrAp2 _ (add_succ _ _) (.eqRefl _)).eqTrans (cv_succ _)) (uv_succ _ _) Prf.hyp0
  have h2 := Prf.allE k hall
  simp only [subst_Lin4, subst_cv, subst_uv, PTm.subst_add, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift] at h2
  exact h2

/-- **The unit determinant** `p_{m−1} q_m − p_m q_{m−1} = ±1`. -/
theorem det (m : PTm n) : Γ ⊢[PRAAx] Det (cv a' m) := by
  have hall : Γ ⊢[PRAAx] Fm.all (Det (cv a' (var 0))) := by
    refine PRA.qfInd _ (det_QF _) ?_ ?_
    · simp only [subst_Det, subst_cv, Syn.subst_var, Syn.inst_zero]
      obtain ⟨_, p2, p3, p4⟩ := proj_st (Γ := Γ) (ap1 a' zero) one one zero
      have w := cv_zero (Γ := Γ) (a' := a')
      unfold Det
      exact det_base ((congrFst (congrSnd w)).eqTrans p2) ((congrFst (congrSnd (congrSnd w))).eqTrans p3)
        ((congrSnd (congrSnd (congrSnd w))).eqTrans p4)
    · simp only [subst_Det, subst_cv, Syn.subst_var, Syn.repl_zero, ConciseIPRA.PTm.subst_succ]
      exact det_step (cv_succ _) Prf.hyp0
  have h2 := Prf.allE m hall
  simp only [subst_Det, subst_cv, Syn.subst_var, Syn.inst_zero] at h2
  exact h2

/-- **The tail is at least one**: `v_k ≤ u_k` (and `v_k + v_{k−1} ≤ u_k + u_{k−1}`). -/
theorem jinv (k N : PTm n) : Γ ⊢[PRAAx] Jf (uv a' k N) := by
  have hall : Γ ⊢[PRAAx] Fm.all (Jf (uv a' (var 0) (Syn.shift N))) := by
    refine PRA.qfInd _ (jf_QF _) ?_ ?_
    · simp only [subst_Jf, subst_uv, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      obtain ⟨p1, p2, p3, p4⟩ := proj_st (Γ := Γ) one zero zero one
      have w := uv_zero (Γ := Γ) (a' := a') N
      unfold Jf
      exact j_base ((congrFst w).eqTrans p1) ((congrFst (congrSnd w)).eqTrans p2)
        ((congrFst (congrSnd (congrSnd w))).eqTrans p3) ((congrSnd (congrSnd (congrSnd w))).eqTrans p4)
    · simp only [subst_Jf, subst_uv, Syn.subst_var, Syn.repl_zero, subst_repl_shift,
        ConciseIPRA.PTm.subst_succ]
      obtain ⟨g1, g2, g3, g4⟩ := proj_nx (uv_succ (Γ := (Jf (uv a' (var 0) (Syn.shift N)) :: Γ.map Fm.shift))
        (a' := a') (var 0) (Syn.shift N))
      have ih : (Jf (uv a' (var 0) (Syn.shift N)) :: Γ.map Fm.shift) ⊢[PRAAx] Jf (uv a' (var 0) (Syn.shift N)) :=
        Prf.hyp0
      unfold Jf at ih ⊢
      exact j_alg g1 g2 g3 g4 ih
  have h2 := Prf.allE k hall
  simp only [subst_Jf, subst_uv, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at h2
  exact h2

/-! ## The bounds -/

/-- **`dio:cf-real`, first part**: for `N ≤ M`, `|p_M q_N − p_N q_M| · q_N ≤ q_M`, that is
`|p_M/q_M − p_N/q_N| ≤ q_N^{−2}`, as two inequalities. -/
theorem cf_bound {N M : PTm n} (h : Γ ⊢[PRAAx] le N M) :
    Γ ⊢[PRAAx] le (sP (cv a' M) * sQ (cv a' N) * sQ (cv a' N))
        (sP (cv a' N) * sQ (cv a' M) * sQ (cv a' N) + sQ (cv a' M)) ⋏
      le (sP (cv a' N) * sQ (cv a' M) * sQ (cv a' N))
        (sP (cv a' M) * sQ (cv a' N) * sQ (cv a' N) + sQ (cv a' M)) := by
  have e : Γ ⊢[PRAAx] cv a' (N + monus M N) ≐ cv a' M := congrAp2 _ (eq_add_of_le h).eqSymm (.eqRefl _)
  have L := lin (Γ := Γ) (a' := a') N (monus M N)
  unfold Lin4 at L
  have i1 := (congrFst e).eqSymm.eqTrans (Prf.andE₁ (Prf.andE₁ L))
  have i2 := (congrFst (congrSnd e)).eqSymm.eqTrans (Prf.andE₂ (Prf.andE₁ L))
  have J := jinv (Γ := Γ) (a' := a') (monus M N) N
  unfold Jf at J
  have D := det (Γ := Γ) (a' := a') N
  unfold Det at D
  exact bound_alg i1 i2 (Prf.andE₁ J) D

theorem two_step (m : PTm n) : Γ ⊢[PRAAx] le (two * sQ (cv a' m)) (sQ (cv a' (succ (succ m)))) := by
  obtain ⟨_, b2, _, b4⟩ := proj_nx (cv_succ (Γ := Γ) (a' := a') m)
  obtain ⟨_, c2, _, _⟩ := proj_nx (cv_succ (Γ := Γ) (a' := a') (succ m))
  exact two_alg b2 b4 c2

/-- **`q_{2k+2} ≥ 2^{k+1}`.** -/
theorem q_pow (k : PTm n) : Γ ⊢[PRAAx] le (pw two (succ k)) (sQ (cv a' (idx k))) := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (pw two (succ (var 0))) (sQ (cv a' (idx (var 0))))) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [subst_le, subst_ap2, subst_cv, subst_fstT, subst_sndT, PTm.subst_add, Syn.subst_var,
        Syn.inst_zero, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
      obtain ⟨_, p2, _, _⟩ := proj_st (Γ := Γ) (ap1 a' zero) one one zero
      have q0 : Γ ⊢[PRAAx] sQ (cv a' (zero + zero)) ≐ one :=
        (congrFst (congrSnd (congrAp2 _ (add_zero zero) (.eqRefl _)))).eqTrans
          ((congrFst (congrSnd (cv_zero (a' := a')))).eqTrans p2)
      exact pow_base_alg (pw_succ two zero) (pw_zero two) (two_step (zero + zero)) q0
    · simp only [subst_le, subst_ap2, subst_cv, subst_fstT, subst_sndT, PTm.subst_add, Syn.subst_var,
        Syn.repl_zero, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
      have eI : (le (pw two (succ (var 0))) (sQ (cv a' (idx (var 0)))) :: Γ.map Fm.shift) ⊢[PRAAx]
          idx (succ (var 0)) ≐ succ (succ (idx (var 0))) := by
        ipra_ring
      exact pow_step_alg Prf.hyp0 (pw_succ two _) (two_step _)
        (congrFst (congrSnd (congrAp2 _ eI (.eqRefl _))))
  have h2 := Prf.allE k hall
  simp only [subst_le, subst_ap2, subst_cv, subst_fstT, subst_sndT, PTm.subst_add, Syn.subst_var,
    Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at h2
  exact h2

/-! ## Growth of the denominators (`dio:continuants`) -/

theorem q_zero : Γ ⊢[PRAAx] sQ (cv a' zero) ≐ one := by
  obtain ⟨_, p2, _, _⟩ := proj_st (Γ := Γ) (ap1 a' zero) one one zero
  exact (congrFst (congrSnd (cv_zero (a' := a')))).eqTrans p2

theorem mono_alg {c0 Q Q' Q1 : PTm n} (a1 : Γ ⊢[PRAAx] Q1 ≐ succ c0 * Q + Q') : Γ ⊢[PRAAx] le Q Q1 := by
  have f := natEq a1
  ipra_le 𝔞 c0 * 𝔞 Q + 𝔞 Q' with f

theorem strict_alg {c0 Q0 Q1 Q1' Q2 : PTm n} (h0 : Γ ⊢[PRAAx] le one Q0) (a1 : Γ ⊢[PRAAx] Q1' ≐ Q0)
    (b : Γ ⊢[PRAAx] Q2 ≐ succ c0 * Q1 + Q1') : Γ ⊢[PRAAx] lt Q1 Q2 := by
  have fa := natEq a1; have fb := natEq b
  ipra_le 𝔞 c0 * 𝔞 Q1 + sl h0 with fb + fa

/-- `q_m ≤ q_{m+1}`. -/
theorem q_le_succ (m : PTm n) : Γ ⊢[PRAAx] le (sQ (cv a' m)) (sQ (cv a' (succ m))) := by
  obtain ⟨_, b2, _, _⟩ := proj_nx (cv_succ (Γ := Γ) (a' := a') m)
  exact mono_alg b2

/-- `q_m ≥ 1`. -/
theorem q_pos (m : PTm n) : Γ ⊢[PRAAx] le one (sQ (cv a' m)) := by
  have hall : Γ ⊢[PRAAx] Fm.all (le one (sQ (cv a' (var 0)))) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [subst_le, subst_cv, subst_fstT, subst_sndT, Syn.subst_var, Syn.inst_zero,
        ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
      exact le_congr (.eqRefl _) (q_zero (a' := a')).eqSymm (le_refl _)
    · simp only [subst_le, subst_cv, subst_fstT, subst_sndT, Syn.subst_var, Syn.repl_zero,
        ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
      exact le_trans Prf.hyp0 (q_le_succ _)
  have h2 := Prf.allE m hall
  simp only [subst_le, subst_cv, subst_fstT, subst_sndT, Syn.subst_var, Syn.inst_zero,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at h2
  exact h2

/-- **`q_{m+1} < q_{m+2}`**: the denominators strictly increase after `q_1`. -/
theorem q_lt_succ (m : PTm n) : Γ ⊢[PRAAx] lt (sQ (cv a' (succ m))) (sQ (cv a' (succ (succ m)))) := by
  obtain ⟨_, _, _, b4⟩ := proj_nx (cv_succ (Γ := Γ) (a' := a') m)
  obtain ⟨_, c2, _, _⟩ := proj_nx (cv_succ (Γ := Γ) (a' := a') (succ m))
  exact strict_alg (q_pos m) b4 c2

/-- **`q_{2k} ≥ 2^k`.** -/
theorem q_pow_even (k : PTm n) : Γ ⊢[PRAAx] le (pw two k) (sQ (cv a' (k + k))) := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (pw two (var 0)) (sQ (cv a' (var 0 + var 0)))) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [subst_le, subst_ap2, subst_cv, subst_fstT, subst_sndT, PTm.subst_add, Syn.subst_var,
        Syn.inst_zero, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
      have q0 : Γ ⊢[PRAAx] sQ (cv a' (zero + zero)) ≐ one :=
        (congrFst (congrSnd (congrAp2 _ (add_zero zero) (.eqRefl _)))).eqTrans (q_zero (a' := a'))
      exact le_congr (pw_zero two).eqSymm q0.eqSymm (le_refl _)
    · simp only [subst_le, subst_ap2, subst_cv, subst_fstT, subst_sndT, PTm.subst_add, Syn.subst_var,
        Syn.repl_zero, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
      have eI : (le (pw two (var 0)) (sQ (cv a' (var 0 + var 0))) :: Γ.map Fm.shift) ⊢[PRAAx]
          succ (var 0) + succ (var 0) ≐ succ (succ (var 0 + var 0)) := by
        ipra_ring
      exact pow_step_alg Prf.hyp0 (pw_succ two _) (two_step _)
        (congrFst (congrSnd (congrAp2 _ eI (.eqRefl _))))
  have h2 := Prf.allE k hall
  simp only [subst_le, subst_ap2, subst_cv, subst_fstT, subst_sndT, PTm.subst_add, Syn.subst_var,
    Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at h2
  exact h2

/-- **`dio:cf-real`, the rational name**: for `k ≤ l` and `r_k = p_{2k+2}/q_{2k+2}`,
`|r_l − r_k| ≤ 2^{−2k−2}`, cleared of denominators with `F = (2^{k+1})²`. -/
theorem cf_real {k l : PTm n} (h : Γ ⊢[PRAAx] le k l) :
    Γ ⊢[PRAAx]
      le (sP (cv a' (idx l)) * sQ (cv a' (idx k)) * (pw two (succ k) * pw two (succ k)))
        (sP (cv a' (idx k)) * sQ (cv a' (idx l)) * (pw two (succ k) * pw two (succ k)) +
          sQ (cv a' (idx l)) * sQ (cv a' (idx k))) ⋏
      le (sP (cv a' (idx k)) * sQ (cv a' (idx l)) * (pw two (succ k) * pw two (succ k)))
        (sP (cv a' (idx l)) * sQ (cv a' (idx k)) * (pw two (succ k) * pw two (succ k)) +
          sQ (cv a' (idx l)) * sQ (cv a' (idx k))) := by
  have hI : Γ ⊢[PRAAx] le (idx k) (idx l) := by ipra_le 2 * sl h
  have b := cf_bound (a' := a') hI
  have hF : Γ ⊢[PRAAx] le (pw two (succ k) * pw two (succ k)) (sQ (cv a' (idx k)) * sQ (cv a' (idx k))) :=
    le_mul_mono (q_pow k) (q_pow k)
  exact .andI (scale_alg (Prf.andE₁ b) hF) (scale_alg (Prf.andE₂ b) hF)

end LeanProofs.IPRA.DiophantineNumberTheory.CfReal
