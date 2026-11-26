import IPRADerivations.AnalyticNumberTheory.RobinThreePos
import IPRADerivations.AnalyticNumberTheory.PrimorialLower
import IPRADerivations.AnalyticNumberTheory.RSA
import IPRADerivations.Geometry.HypercubeSplit
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.Header

/-!
# `ϑ(m²) ≥ m²/4` on the logarithm names (`lcm_bridge.tex`, rough Chebyshev lemma)

Packet: `analytic-number-theory/robin_ipra_research_2026-11-19`, `paper/lcm_bridge.tex`, Lemma "A rough elementary
Chebyshev lower bound": `ϑ(m²) ≥ m²/4`. Here `ϑ(P) = log ∏_{p≤P} p` is named by the lower end `lo(q, K)` of the
packet's interval `LogI` (`RobinLogInterval`) at `q = ∏_{p≤P} p = prim P` (`PrimorialLower.prim`).

* `lo2_ge`, `lo_ge`: `lo(q, K) ≥ (56/81) e(q)` for `K ≥ 2`, where `e(q) = ⌊log₂ q⌋` is the range-reduction exponent:
  `lo = e·S_K(1/3) + S_K(d/s) ≥ e·S_2(1/3)`, `S_2(1/3) = 504/729 = 56/81` (`RobinThreePos.lo_k2`, nesting);
* `eb_ge`: `b 2^E ≤ a → E ≤ e(a/b)`;
* `theta_lower`: if `m ≥ 1`, `m ≤ 2^t` and `448(m+1)t + 448 ≤ 143 m²`, then `lo(∏_{p≤m²} p, K) ≥ m²/4` for every
  `K ≥ 2`. The proof is the packet's: `2^{P−1} ≤ (P+1) P^m ∏ p` (`PrimorialLower.primorial_lower`), with
  `(P+1) P^m ≤ 2^{2t+1+2tm}`, so `e(∏ p) ≥ P − 2 − 2t(m+1)`, and `(56/81)(P − 2 − 2t(m+1)) ≥ P/4` is the side
  condition. (For `m ≥ 16` the condition holds with `t = ⌈log₂ m⌉`; that numeric discharge is separate.)

All statements are cleared cross-multiplications of natural-number terms.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.LcmBridgeTheta

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLogInterval (eb eb_spec loN loD lo_nest loD_pos dt st)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinGammaInterval (k2)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinThreePos (lo_k2)
open LeanProofs.IPRA.AnalyticNumberTheory.PrimorialLower (prim prim_pos primorial_lower)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (pw_pos')
open LeanProofs.IPRA.Geometry.HypercubeSplit (le_cancel_pos)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem two_pos : Γ ⊢[PRAAx] (two : PTm n) ≐ succ (pred two) := congrSucc (pred_succ _).eqSymm

/-! ## The lower end against the exponent -/

/-- `lo(q, 2) ≥ (56/81) e(q)`. -/
theorem lo2_ge (a b : PTm n) : Γ ⊢[PRAAx] le (num 56 * eb a b * loD a b k2) (num 81 * loN a b k2) := by
  have h := lo_k2 (Γ := Γ) a b
  refine le_of_eq_add (d := num 59049 * (num 6 * dt a b * (st a b * st a b * (st a b * st a b)) +
    two * (dt a b * dt a b * dt a b) * (st a b * st a b))) ?_
  ipra_lc 81 * natEq (Prf.andE₁ h) - 56 * 𝔞 (eb a b) * natEq (Prf.andE₂ h)

/-- `lo(q, K) ≥ (56/81) e(q)` for `K ≥ 2` and `1 ≤ b ≤ a`. -/
theorem lo_ge {a b K : PTm n} (hb : Γ ⊢[PRAAx] le one b) (hab : Γ ⊢[PRAAx] le b a) (hK : Γ ⊢[PRAAx] le k2 K) :
    Γ ⊢[PRAAx] le (num 56 * eb a b * loD a b K) (num 81 * loN a b K) := by
  have c0 := lo2_ge (Γ := Γ) a b
  have nk := lo_nest hb hab hK
  have m1 := le_mul_mono c0 (le_refl (loD a b K))
  have m2 := le_mul_mono (le_refl (num 81 : PTm n)) nk
  have m3 : Γ ⊢[PRAAx] le (num 56 * eb a b * loD a b k2 * loD a b K) (num 81 * (loN a b K * loD a b k2)) :=
    le_trans m1 (le_congr (by ipra_ring) (.eqRefl _) m2)
  refine le_cancel_pos (loD_pos hb hab k2) (le_congr ?_ ?_ m3)
  · ipra_ring
  · ipra_ring

/-- `b 2^E ≤ a → E ≤ e(a/b)`. -/
theorem eb_ge {a b E : PTm n} (hb : Γ ⊢[PRAAx] le one b) (hab : Γ ⊢[PRAAx] le b a)
    (hE : Γ ⊢[PRAAx] le (b * pw two E) a) : Γ ⊢[PRAAx] le E (eb a b) := by
  have h2 := Prf.andE₂ (eb_spec hb hab)
  refine .orE (lt_or_le (eb a b) E) ?_ Prf.hyp0
  have l : (lt (eb a b) E :: Γ) ⊢[PRAAx] le (succ (eb a b)) E := Prf.hyp0
  have p := le_mul_mono (le_refl b) (PowerCleared.pw_le_exp two_pos l)
  exact le_lt_absurd _ (le_trans p hE.wk) h2.wk

/-! ## The bound -/

/-- `ϑ(m²) ≥ m²/4` on the names: for `m ≥ 1`, `m ≤ 2^t` and `448(m+1)t + 448 ≤ 143m²`,
`m² · loD ≤ 4 · loN` at `q = ∏_{p≤m²} p` for every precision `K ≥ 2`. -/
theorem theta_lower {m t K : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (ht : Γ ⊢[PRAAx] le m (pw two t))
    (hq : Γ ⊢[PRAAx] le (num 448 * succ m * t + num 448) (num 143 * (m * m))) (hK : Γ ⊢[PRAAx] le k2 K) :
    Γ ⊢[PRAAx] le (m * m * loD (prim (m * m)) one K) (num 4 * loN (prim (m * m)) one K) := by
  have hP := Combinatorics.Binomial.pos_mul hm hm
  -- `P^m ≤ 2^{2tm}`
  have q1 : Γ ⊢[PRAAx] le (pw (m * m) m) (pw two ((t + t) * m)) := by
    have a := pw_le_pw m (le_mul_mono ht ht)
    refine le_congr (.eqRefl _) ?_ a
    exact (congrAp2 powF (.eqRefl m) (pw_add two t t).eqSymm).eqTrans (RSA.pw_mul two (t + t) m)
  -- `P + 1 ≤ 2^{2t+1}`
  have q2 : Γ ⊢[PRAAx] le (succ (m * m)) (pw two (succ (t + t))) := by
    have eP := natEq hP
    have a : Γ ⊢[PRAAx] le (succ (m * m)) (two * (m * m)) :=
      le_of_eq_add (d := pred (m * m)) (by apply deriveNat; ipra_simps; linear_combination eP)
    have b : Γ ⊢[PRAAx] le (two * (m * m)) (two * (pw two t * pw two t)) := le_mul_mono (le_refl two) (le_mul_mono ht ht)
    have c : Γ ⊢[PRAAx] two * (pw two t * pw two t) ≐ pw two (succ (t + t)) := by
      ipra_lc -natEq (pw_succ (Γ := Γ) two (t + t)) - 2 * natEq (pw_add (Γ := Γ) two t t)
    exact le_trans a (le_congr (.eqRefl _) c b)
  -- `(P + 1) P^m ≤ 2^F`, `F = 2t + 1 + 2tm`
  have q3 : Γ ⊢[PRAAx] le (succ (m * m) * pw (m * m) m) (pw two (succ (t + t) + (t + t) * m)) :=
    le_congr (.eqRefl _) (pw_add two (succ (t + t)) ((t + t) * m)).eqSymm (le_mul_mono q2 q1)
  have q4 : Γ ⊢[PRAAx] le (pw two (pred (m * m))) (pw two (succ (t + t) + (t + t) * m) * prim (m * m)) :=
    le_trans (primorial_lower hm)
      (le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono q3 (le_refl (prim (m * m)))))
  -- `F ≤ P − 1`
  have c143 : Γ ⊢[PRAAx] (num 143 : PTm n) ≐ succ (pred (num 143)) := pos_of_one_le (by ipra_le 142)
  have eP := natEq hP
  have hF : Γ ⊢[PRAAx] le (succ (t + t) + (t + t) * m) (pred (m * m)) := by
    refine le_cancel_pos c143 (le_of_eq_add (d := num 162 * (succ m * t) + num 162 +
      monus (num 143 * (m * m)) (num 448 * succ m * t + num 448)) ?_)
    ipra_lc natEq (eq_add_of_le hq) - 143 * eP
  -- `2^E ≤ ∏ p` for `E = P − 1 − F`
  have eE := eq_add_of_le hF
  have q5 : Γ ⊢[PRAAx] le (pw two (succ (t + t) + (t + t) * m) * pw two (monus (pred (m * m)) (succ (t + t) + (t + t) * m)))
      (pw two (succ (t + t) + (t + t) * m) * prim (m * m)) :=
    le_congr ((congrAp2 powF eE (.eqRefl two)).eqTrans (pw_add two _ _)) (.eqRefl _) q4
  have q6 := le_cancel_pos (pw_pos' two_pos _) q5
  have hab : Γ ⊢[PRAAx] le one (prim (m * m)) := FactorVector.one_le_pos (prim_pos _)
  have q7 := eb_ge (le_refl one) hab (le_congr (one_mul _).eqSymm (.eqRefl _) q6)
  -- `81 P ≤ 224 E ≤ 224 e`
  have hPE0 : Γ ⊢[PRAAx] le (num 81 * (m * m)) (num 224 * monus (pred (m * m)) (succ (t + t) + (t + t) * m)) := by
    refine le_of_eq_add (d := monus (num 143 * (m * m)) (num 448 * succ m * t + num 448)) ?_
    ipra_lc natEq (eq_add_of_le hq) - 224 * eP - 224 * natEq eE
  have hPE := le_trans hPE0 (le_mul_mono (le_refl (num 224 : PTm n)) q7)
  -- `81 P loD ≤ 224 e loD ≤ 4 · 81 loN`
  have lg := lo_ge (le_refl one) hab hK
  have r1 := le_mul_mono hPE (le_refl (loD (prim (m * m)) one K))
  have r2 := le_mul_mono (le_refl (num 4 : PTm n)) lg
  have r3 : Γ ⊢[PRAAx] le (num 81 * (m * m) * loD (prim (m * m)) one K) (num 4 * (num 81 * loN (prim (m * m)) one K)) :=
    le_trans r1 (le_congr (by ipra_ring) (.eqRefl _) r2)
  have c81 : Γ ⊢[PRAAx] (num 81 : PTm n) ≐ succ (pred (num 81)) := pos_of_one_le (by ipra_le 80)
  exact le_cancel_pos c81 (le_congr (by ipra_ring) (by ipra_ring) r3)

end LeanProofs.IPRA.AnalyticNumberTheory.LcmBridgeTheta
