import IPRADerivations.Probability.MedianCounts
import IPRADerivations.Geometry.HypercubeSplit
import IPRADerivations.Core.LinearCombination

/-!
# Weighted medians: the `L¹` theorem and the mean–median bound

Packet: `probability/median_ipra_constructive_proofs`, Theorem `thm:weighted-l1` (medians are
minimizers) and Theorem `thm:mean-median` (`eq:mean-median-cleared`). The data is a weight body
`w(i, p)` and a value body `x(i, p)` on `i < N`, with

  `W = ∑ w_i`,   `S = ∑ w_i x_i`,   `Q = ∑ w_i x_i²`,
  `B(t) = ∑_{x_i < t} w_i`,   `E(t) = ∑_{x_i = t} w_i`,   `A(t) = ∑_{t < x_i} w_i`,

and `m` is a weighted median when `2B(m) ≤ W` and `2A(m) ≤ W`. To compare `m` with the rational
mean `S/W` the deviation carries a scale `c`: `D_c(T) = ∑ w_i |c x_i − T|`, with
`|a − b| = (a ∸ b) + (b ∸ a)`.

* `up_below`, `up_above`, `down_above`, `down_below`: the pointwise triangle estimates for
  abstract indicator values;
* `w_partition`: `B(t) + E(t) + A(t) = W`;
* `dev_upW`, `dev_downW`: `D_c(c m) + d (B + E)(m) ≤ D_c(c m + d) + d A(m)` and, for `t ≤ c m` with
  `d = c m ∸ t`, `D_c(c m) + d (A + E)(m) ≤ D_c(t) + d B(m)`;
* `weighted_l1` (`thm:weighted-l1`, scaled): a weighted median `m` has `D_c(c m) ≤ D_c(t)` for
  every scale `c` and every `t`; `c = 1` is the theorem of the packet;
* `ad_mul`, `ad_add_le`: `|c a − c b| = c |a − b|` and `|(u + u′) − (v + v′)| ≤ |u − v| + |u′ − v′|`;
* `sum_triangle`: `|c S − T W| ≤ D_c(T)`;
* `mean_median` (`thm:mean-median`): for `W > 0`, `|S − W m|² + S² ≤ W Q`, i.e.
  `(S − W m)² ≤ W Q − S²` and `|μ − m| ≤ σ`. The chain is `W |S − W m| ≤ D_W(W m) ≤ D_W(S)`,
  Cauchy–Schwarz `D_W(S)² ≤ W ∑ w_i |W x_i − S|²` (`Expectation.second_moment`), and the variance
  identity `∑ w_i |W x_i − S|² + W S² = W² Q` (`Variance.variance_identity`).

The converse of `thm:weighted-l1` (minimizers are medians) is `Probability/MedianL1.min_median` for
unit weights; the weighted converse is not stated.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.MedianWeighted

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Algebra.CubeRootTwo (sg sg_zero sg_succ)
open LeanProofs.IPRA.AnalyticNumberTheory.Totatives (sg_lt sg_le)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Probability.Expectation (Ew Wt inst2_mul' second_moment)
open LeanProofs.IPRA.Probability.Variance (ad dvB dS Vr variance_identity)
open LeanProofs.IPRA.Probability.MedianCounts
open LeanProofs.IPRA.Geometry.HypercubeSplit (le_cancel_pos)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Pointwise estimates for abstract indicators -/

theorem up_below {X M : PTm n} (d : PTm n) {β ε α : PTm n} (h : Γ ⊢[PRAAx] le X M)
    (hs : Γ ⊢[PRAAx] β + ε ≐ one) (ha : Γ ⊢[PRAAx] α ≐ zero) :
    Γ ⊢[PRAAx] le (ad X M + d * (β + ε)) (ad X (M + d) + d * α) := by
  have h1 := natEq h; have h2 := natEq (eq_add_of_le h)
  have hle : Γ ⊢[PRAAx] le X (M + d) := le_of_eq_add (d := monus M X + d) (by
    ipra_lc h2)
  have h3 := natEq hle; have h4 := natEq (eq_add_of_le hle)
  have s := natEq hs; have a := natEq ha
  refine le_of_eq_add (d := zero) ?_
  ipra_lc h3 - h4 + h2 - h1 + 𝔞 d * a - 𝔞 d * s

theorem up_above₁ {X M : PTm n} (d : PTm n) {β ε α : PTm n} (h : Γ ⊢[PRAAx] le M X)
    (hb : Γ ⊢[PRAAx] β ≐ zero) (he : Γ ⊢[PRAAx] ε ≐ zero) (ha : Γ ⊢[PRAAx] α ≐ one)
    (hle : Γ ⊢[PRAAx] le X (M + d)) :
    Γ ⊢[PRAAx] le (ad X M + d * (β + ε)) (ad X (M + d) + d * α) := by
  have h1 := natEq h; have h2 := natEq (eq_add_of_le h)
  have b := natEq hb; have e := natEq he; have a := natEq ha
  have h3 := natEq hle; have h4 := natEq (eq_add_of_le hle)
  refine le_of_eq_add (d := monus (M + d) X + monus (M + d) X) ?_
  ipra_lc h3 + h4 + h2 - h1 + 𝔞 d * a - 𝔞 d * b - 𝔞 d * e

theorem up_above₂ {X M : PTm n} (d : PTm n) {β ε α : PTm n} (h : Γ ⊢[PRAAx] le M X)
    (hb : Γ ⊢[PRAAx] β ≐ zero) (he : Γ ⊢[PRAAx] ε ≐ zero) (ha : Γ ⊢[PRAAx] α ≐ one)
    (hge : Γ ⊢[PRAAx] le (M + d) X) :
    Γ ⊢[PRAAx] le (ad X M + d * (β + ε)) (ad X (M + d) + d * α) := by
  have h1 := natEq h; have h2 := natEq (eq_add_of_le h)
  have b := natEq hb; have e := natEq he; have a := natEq ha
  have h3 := natEq hge; have h4 := natEq (eq_add_of_le hge)
  refine le_of_eq_add (d := zero) ?_
  ipra_lc -h4 + h2 + h3 - h1 + 𝔞 d * a - 𝔞 d * b - 𝔞 d * e

/-- For `M ≤ X` with indicators `β = ε = 0`, `α = 1`:
`|X − M| + d (β + ε) ≤ |X − (M + d)| + d α`. -/
theorem up_above {X M : PTm n} (d : PTm n) {β ε α : PTm n} (h : Γ ⊢[PRAAx] le M X)
    (hb : Γ ⊢[PRAAx] β ≐ zero) (he : Γ ⊢[PRAAx] ε ≐ zero) (ha : Γ ⊢[PRAAx] α ≐ one) :
    Γ ⊢[PRAAx] le (ad X M + d * (β + ε)) (ad X (M + d) + d * α) :=
  .orE (le_total X (M + d)) (up_above₁ d h.wk hb.wk he.wk ha.wk Prf.hyp0)
    (up_above₂ d h.wk hb.wk he.wk ha.wk Prf.hyp0)

theorem down_above {X t : PTm n} (d : PTm n) {β ε α : PTm n} (h : Γ ⊢[PRAAx] le (t + d) X)
    (hs : Γ ⊢[PRAAx] α + ε ≐ one) (hb : Γ ⊢[PRAAx] β ≐ zero) :
    Γ ⊢[PRAAx] le (ad X (t + d) + d * (α + ε)) (ad X t + d * β) := by
  have h1 := natEq h; have h2 := natEq (eq_add_of_le h)
  have hle : Γ ⊢[PRAAx] le t X := le_of_eq_add (d := d + monus X (t + d)) (by
    ipra_lc h2)
  have h3 := natEq hle; have h4 := natEq (eq_add_of_le hle)
  have s := natEq hs; have b := natEq hb
  refine le_of_eq_add (d := zero) ?_
  ipra_lc -h4 + h2 + h3 - h1 + 𝔞 d * b - 𝔞 d * s

theorem down_below₁ {X t : PTm n} (d : PTm n) {β ε α : PTm n} (h : Γ ⊢[PRAAx] le X (t + d))
    (ha : Γ ⊢[PRAAx] α ≐ zero) (he : Γ ⊢[PRAAx] ε ≐ zero) (hb : Γ ⊢[PRAAx] β ≐ one)
    (hle : Γ ⊢[PRAAx] le t X) :
    Γ ⊢[PRAAx] le (ad X (t + d) + d * (α + ε)) (ad X t + d * β) := by
  have h1 := natEq h; have h2 := natEq (eq_add_of_le h)
  have a := natEq ha; have e := natEq he; have b := natEq hb
  have h3 := natEq hle; have h4 := natEq (eq_add_of_le hle)
  refine le_of_eq_add (d := monus X t + monus X t) ?_
  ipra_lc h4 + h2 + h3 - h1 + 𝔞 d * b - 𝔞 d * a - 𝔞 d * e

theorem down_below₂ {X t : PTm n} (d : PTm n) {β ε α : PTm n} (h : Γ ⊢[PRAAx] le X (t + d))
    (ha : Γ ⊢[PRAAx] α ≐ zero) (he : Γ ⊢[PRAAx] ε ≐ zero) (hb : Γ ⊢[PRAAx] β ≐ one)
    (hge : Γ ⊢[PRAAx] le X t) :
    Γ ⊢[PRAAx] le (ad X (t + d) + d * (α + ε)) (ad X t + d * β) := by
  have h1 := natEq h; have h2 := natEq (eq_add_of_le h)
  have a := natEq ha; have e := natEq he; have b := natEq hb
  have h3 := natEq hge; have h4 := natEq (eq_add_of_le hge)
  refine le_of_eq_add (d := zero) ?_
  ipra_lc -h4 + h2 + h3 - h1 + 𝔞 d * b - 𝔞 d * a - 𝔞 d * e

/-- For `X ≤ t + d` with indicators `α = ε = 0`, `β = 1`:
`|X − (t + d)| + d (α + ε) ≤ |X − t| + d β`. -/
theorem down_below {X t : PTm n} (d : PTm n) {β ε α : PTm n} (h : Γ ⊢[PRAAx] le X (t + d))
    (ha : Γ ⊢[PRAAx] α ≐ zero) (he : Γ ⊢[PRAAx] ε ≐ zero) (hb : Γ ⊢[PRAAx] β ≐ one) :
    Γ ⊢[PRAAx] le (ad X (t + d) + d * (α + ε)) (ad X t + d * β) :=
  .orE (le_total t X) (down_below₁ d h.wk ha.wk he.wk hb.wk Prf.hyp0)
    (down_below₂ d h.wk ha.wk he.wk hb.wk Prf.hyp0)

/-! ## Scaled pointwise estimates -/

/-- `|c x − c m| + d([x < m] + [x = m]) ≤ |c x − (c m + d)| + d [m < x]`. -/
theorem ptc_up (x m c d : PTm n) :
    Γ ⊢[PRAAx] le (ad (c * x) (c * m) + d * (sg (monus m x) + eqb x m))
      (ad (c * x) (c * m + d) + d * sg (monus x m)) := by
  refine .orE (lt_or_le x m) ?_ (.orE (lt_or_eq_of_le Prf.hyp0) ?_ ?_)
  · exact up_below d (le_mul_mono (le_refl c) (le_of_lt Prf.hyp0))
      ((congrAdd (sg_lt Prf.hyp0) (eqb_zero_of_lt Prf.hyp0)).eqTrans (add_zero _)) (sg_le (le_of_lt Prf.hyp0))
  · exact up_above d (le_mul_mono (le_refl c) (le_of_lt Prf.hyp0)) (sg_le (le_of_lt Prf.hyp0))
      (eqb_zero_of_gt Prf.hyp0) (sg_lt Prf.hyp0)
  · exact up_below d (le_mul_mono (le_refl c) (le_congr Prf.hyp0 (.eqRefl _) (le_refl m)))
      ((congrAdd (sg_le (le_congr (.eqRefl _) Prf.hyp0 (le_refl m))) (eqb_of_eq Prf.hyp0.eqSymm)).eqTrans
        (zero_add _))
      (sg_le (le_congr Prf.hyp0 (.eqRefl _) (le_refl m)))

theorem ptc_down_core {x m c t d : PTm n} (hM : Γ ⊢[PRAAx] c * m ≐ t + d) :
    Γ ⊢[PRAAx] le (ad (c * x) (t + d) + d * (sg (monus x m) + eqb x m)) (ad (c * x) t + d * sg (monus m x)) := by
  refine .orE (lt_or_le x m) ?_ (.orE (lt_or_eq_of_le Prf.hyp0) ?_ ?_)
  · exact down_below d (le_congr (.eqRefl _) hM.wk (le_mul_mono (le_refl c) (le_of_lt Prf.hyp0)))
      (sg_le (le_of_lt Prf.hyp0)) (eqb_zero_of_lt Prf.hyp0) (sg_lt Prf.hyp0)
  · exact down_above d (le_congr hM.wk.wk (.eqRefl _) (le_mul_mono (le_refl c) (le_of_lt Prf.hyp0)))
      ((congrAdd (sg_lt Prf.hyp0) (eqb_zero_of_gt Prf.hyp0)).eqTrans (add_zero _)) (sg_le (le_of_lt Prf.hyp0))
  · exact down_above d
      (le_congr hM.wk.wk (.eqRefl _) (le_mul_mono (le_refl c) (le_congr (.eqRefl _) Prf.hyp0 (le_refl m))))
      ((congrAdd (sg_le (le_congr Prf.hyp0 (.eqRefl _) (le_refl m))) (eqb_of_eq Prf.hyp0.eqSymm)).eqTrans
        (zero_add _))
      (sg_le (le_congr (.eqRefl _) Prf.hyp0 (le_refl m)))

/-- For `t ≤ c m` and `d = c m ∸ t`:
`|c x − c m| + d([m < x] + [x = m]) ≤ |c x − t| + d [x < m]`. -/
theorem ptc_down (x m c : PTm n) {t : PTm n} (ht : Γ ⊢[PRAAx] le t (c * m)) :
    Γ ⊢[PRAAx] le (ad (c * x) (c * m) + monus (c * m) t * (sg (monus x m) + eqb x m))
      (ad (c * x) t + monus (c * m) t * sg (monus m x)) := by
  have hM := eq_add_of_le ht
  exact le_congr (congrAdd (congrAdd (congrMonus (.eqRefl _) hM.eqSymm) (congrMonus hM.eqSymm (.eqRefl _)))
    (.eqRefl _)) (.eqRefl _) (ptc_down_core (x := x) hM)

/-! ## Absolute differences -/

theorem le_add_ad₁ {a b : PTm n} (h : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx] le a (b + ad a b) := by
  have f1 := natEq h; have f2 := natEq (eq_add_of_le h)
  refine le_of_eq_add (d := monus b a + monus b a) ?_
  ipra_lc f2 + f1

theorem le_add_ad₂ {a b : PTm n} (h : Γ ⊢[PRAAx] le b a) : Γ ⊢[PRAAx] le a (b + ad a b) := by
  have f1 := natEq h; have f2 := natEq (eq_add_of_le h)
  refine le_of_eq_add (d := zero) ?_
  ipra_lc f1 - f2

theorem le_add_ad (a b : PTm n) : Γ ⊢[PRAAx] le a (b + ad a b) :=
  .orE (le_total a b) (le_add_ad₁ Prf.hyp0) (le_add_ad₂ Prf.hyp0)

theorem ad_le_of₁ {a b c : PTm n} (h : Γ ⊢[PRAAx] le a b) (h2 : Γ ⊢[PRAAx] le b (a + c)) :
    Γ ⊢[PRAAx] le (ad a b) c := by
  have f1 := natEq h; have f2 := natEq (eq_add_of_le h); have f3 := natEq (eq_add_of_le h2)
  refine le_of_eq_add (d := monus (a + c) b) ?_
  ipra_lc f3 + f2 - f1

theorem ad_le_of₂ {a b c : PTm n} (h : Γ ⊢[PRAAx] le b a) (h1 : Γ ⊢[PRAAx] le a (b + c)) :
    Γ ⊢[PRAAx] le (ad a b) c := by
  have f1 := natEq h; have f2 := natEq (eq_add_of_le h); have f3 := natEq (eq_add_of_le h1)
  refine le_of_eq_add (d := monus (b + c) a) ?_
  ipra_lc f3 + f2 - f1

theorem ad_le_of {a b c : PTm n} (h1 : Γ ⊢[PRAAx] le a (b + c)) (h2 : Γ ⊢[PRAAx] le b (a + c)) :
    Γ ⊢[PRAAx] le (ad a b) c :=
  .orE (le_total a b) (ad_le_of₁ Prf.hyp0 h2.wk) (ad_le_of₂ Prf.hyp0 h1.wk)

/-- `|(u + u′) − (v + v′)| ≤ |u − v| + |u′ − v′|`. -/
theorem ad_add_le (u u' v v' : PTm n) : Γ ⊢[PRAAx] le (ad (u + u') (v + v')) (ad u v + ad u' v') := by
  refine ad_le_of ?_ ?_
  · exact le_congr (.eqRefl _) (by ipra_ring) (add_le_add₂ (le_add_ad u v) (le_add_ad u' v'))
  · exact le_congr (.eqRefl _) (by ipra_ring) (add_le_add₂ (le_add_ad v u) (le_add_ad v' u'))

theorem ad_mul_of_le (c : PTm n) {a b : PTm n} (h : Γ ⊢[PRAAx] le a b) :
    Γ ⊢[PRAAx] ad (c * a) (c * b) ≐ c * ad a b := by
  have hc := le_mul_mono (le_refl c) h
  ipra_lc natEq hc - natEq (eq_add_of_le hc) + 𝔞 c * natEq (eq_add_of_le h) - 𝔞 c * natEq h

/-- `|c a − c b| = c |a − b|`. -/
theorem ad_mul (c a b : PTm n) : Γ ⊢[PRAAx] ad (c * a) (c * b) ≐ c * ad a b := by
  refine .orE (le_total a b) (ad_mul_of_le c Prf.hyp0) ?_
  exact (add_comm _ _).eqTrans ((ad_mul_of_le c Prf.hyp0).eqTrans (congrMul (.eqRefl _) (add_comm _ _)))

/-! ## Weighted counts -/

section Weighted

variable (w X : PTm 2)

/-- `w(i, snd z)`. -/
abbrev wL : PTm 2 := Syn.subst ![var 0, sndT (var 1)] w

theorem wc_pt (f : PTm 2) (i t p : PTm n) :
    Γ ⊢[PRAAx] inst2 (wL w * f) i (pairT t p) ≐ inst2 w i p * inst2 f i (pairT t p) := by
  rw [inst2_mul']
  have e : inst2 (wL w) i (pairT t p) = inst2 w i (sndT (pairT t p)) := subst_data i (pairT t p) w
  rw [e]
  exact congrMul (congrInst2 w (.eqRefl _) (snd_pair _ _)) (.eqRefl _)

/-- `B(t) = ∑_{x_i < t} w_i`. -/
abbrev WB (N t p : PTm n) : PTm n := ap2 (sumF (wL w * belowB X)) N (pairT t p)
/-- `E(t) = ∑_{x_i = t} w_i`. -/
abbrev WE (N t p : PTm n) : PTm n := ap2 (sumF (wL w * equalB X)) N (pairT t p)
/-- `A(t) = ∑_{t < x_i} w_i`. -/
abbrev WA (N t p : PTm n) : PTm n := ap2 (sumF (wL w * aboveB X)) N (pairT t p)

theorem wb_pt (i t p : PTm n) :
    Γ ⊢[PRAAx] inst2 (wL w * belowB X) i (pairT t p) ≐ inst2 w i p * sg (monus t (inst2 X i p)) :=
  (wc_pt w _ i t p).eqTrans (congrMul (.eqRefl _) (below_pt X i t p))

theorem we_pt (i t p : PTm n) :
    Γ ⊢[PRAAx] inst2 (wL w * equalB X) i (pairT t p) ≐ inst2 w i p * eqb (inst2 X i p) t :=
  (wc_pt w _ i t p).eqTrans (congrMul (.eqRefl _) (equal_pt X i t p))

theorem wa_pt (i t p : PTm n) :
    Γ ⊢[PRAAx] inst2 (wL w * aboveB X) i (pairT t p) ≐ inst2 w i p * sg (monus (inst2 X i p) t) :=
  (wc_pt w _ i t p).eqTrans (congrMul (.eqRefl _) (above_pt X i t p))

theorem w_tri_pt (i t p : PTm n) :
    Γ ⊢[PRAAx] inst2 (addBody (addBody (wL w * belowB X) (wL w * equalB X)) (wL w * aboveB X)) i (pairT t p) ≐
      inst2 w i p := by
  rw [inst2_addBody, inst2_addBody]
  ipra_lc natEq (wc_pt (Γ := Γ) w (belowB X) i t p) + natEq (wc_pt (Γ := Γ) w (equalB X) i t p) +
    natEq (wc_pt (Γ := Γ) w (aboveB X) i t p) + 𝔞 (inst2 w i p) * natEq (tri_pt (Γ := Γ) X i t p)

/-- `B(t) + E(t) + A(t) = W`. -/
theorem w_partition (N t p : PTm n) : Γ ⊢[PRAAx] WB w X N t p + WE w X N t p + WA w X N t p ≐ Wt w N p := by
  have e : Γ ⊢[PRAAx] ap2 (sumF (addBody (addBody (wL w * belowB X) (wL w * equalB X)) (wL w * aboveB X))) N
      (pairT t p) ≐ ap2 (sumF w) N p := by
    refine sum_congr_bounded _ w (pairT t p) p N (.allI (.impI ?_))
    simp only [Syn.shift, subst_pairT]
    exact w_tri_pt w X _ _ _
  exact (congrAdd (sum_add (wL w * belowB X) (wL w * equalB X) N (pairT t p)) (.eqRefl _)).eqSymm.eqTrans
    ((sum_add (addBody (wL w * belowB X) (wL w * equalB X)) (wL w * aboveB X) N (pairT t p)).eqSymm.eqTrans e)

/-! ## The scaled deviation -/

/-- `w(i, snd (snd y))`. -/
abbrev wY : PTm 2 := Syn.subst ![var 0, sndT (sndT (var 1))] w

/-- `|fst y · x(i, snd (snd y)) − fst (snd y)|`, written as in `Variance.dvB`. -/
def Yb : PTm 2 :=
  monus (fstT (var 1) * Syn.subst ![var 0, sndT (sndT (var 1))] X) (fstT (sndT (var 1))) +
    monus (fstT (sndT (var 1))) (fstT (var 1) * Syn.subst ![var 0, sndT (sndT (var 1))] X)

/-- `D_c(T) = ∑_{i<N} w_i |c x_i − T|`. -/
abbrev Dw (N c T p : PTm n) : PTm n := Ew (wY w) (Yb X) N (pairT c (pairT T p))

theorem inst2_dw (i y : PTm n) :
    inst2 (wY w * Yb X) i y = inst2 w i (sndT (sndT y)) * ad (fstT y * inst2 X i (sndT (sndT y))) (fstT (sndT y)) := by
  have e : ∀ f : PTm 2, Syn.subst ![i, y] (Syn.subst ![var 0, sndT (sndT (var 1))] f) =
      Syn.subst ![i, sndT (sndT y)] f := fun f => by
    rw [Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  simp only [inst2, Yb, ad, PTm.subst_mul, PTm.subst_add, PTm.subst_monus, subst_fstT, subst_sndT, e]
  simp

theorem dw_pt (i c T p : PTm n) :
    Γ ⊢[PRAAx] inst2 (wY w * Yb X) i (pairT c (pairT T p)) ≐ inst2 w i p * ad (c * inst2 X i p) T := by
  rw [inst2_dw]
  have hA : Γ ⊢[PRAAx] fstT (pairT c (pairT T p)) ≐ c := fst_pair _ _
  have hB : Γ ⊢[PRAAx] fstT (sndT (pairT c (pairT T p))) ≐ T := (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
  have hx : Γ ⊢[PRAAx] sndT (sndT (pairT c (pairT T p))) ≐ p := (congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)
  have ht := congrMul hA (congrInst2 X (.eqRefl i) hx)
  exact congrMul (congrInst2 w (.eqRefl i) hx) (congrAdd (congrMonus ht hB) (congrMonus hB ht))

theorem congrDw (N c p : PTm n) {T T' : PTm n} (h : Γ ⊢[PRAAx] T ≐ T') : Γ ⊢[PRAAx] Dw w X N c T p ≐ Dw w X N c T' p :=
  congrAp2 (sumF (wY w * Yb X)) (.eqRefl _) (LeanProofs.IPRA.congrPairT (.eqRefl _)
    (LeanProofs.IPRA.congrPairT h (.eqRefl _)))

/-! ## The upward comparison -/

theorem upW_base (m d c p : PTm n) :
    Γ ⊢[PRAAx] le (Dw w X zero c (c * m) p + d * (WB w X zero m p + WE w X zero m p))
      (Dw w X zero c (c * m + d) p + d * WA w X zero m p) := by
  refine le_of_eq_add (d := zero) ?_
  ipra_lc natEq (sum_zero (Γ := Γ) (wY w * Yb X) (pairT c (pairT (c * m + d) p))) +
    𝔞 d * natEq (sum_zero (Γ := Γ) (wL w * aboveB X) (pairT m p)) -
    natEq (sum_zero (Γ := Γ) (wY w * Yb X) (pairT c (pairT (c * m) p))) -
    𝔞 d * natEq (sum_zero (Γ := Γ) (wL w * belowB X) (pairT m p)) -
    𝔞 d * natEq (sum_zero (Γ := Γ) (wL w * equalB X) (pairT m p))

theorem upW_step {N m d c p : PTm n}
    (ih : Γ ⊢[PRAAx] le (Dw w X N c (c * m) p + d * (WB w X N m p + WE w X N m p))
      (Dw w X N c (c * m + d) p + d * WA w X N m p)) :
    Γ ⊢[PRAAx] le (Dw w X (succ N) c (c * m) p + d * (WB w X (succ N) m p + WE w X (succ N) m p))
      (Dw w X (succ N) c (c * m + d) p + d * WA w X (succ N) m p) := by
  have sD := natEq (sum_succ' (Γ := Γ) (wY w * Yb X) N (pairT c (pairT (c * m) p)))
  have sD' := natEq (sum_succ' (Γ := Γ) (wY w * Yb X) N (pairT c (pairT (c * m + d) p)))
  have dv := natEq (dw_pt (Γ := Γ) w X N c (c * m) p); have dv' := natEq (dw_pt (Γ := Γ) w X N c (c * m + d) p)
  have bp := natEq (wb_pt (Γ := Γ) w X N m p); have ep := natEq (we_pt (Γ := Γ) w X N m p)
  refine le_congr ?_ ?_ (add_le_add₂ ih (le_mul_mono (le_refl (inst2 w N p)) (ptc_up (inst2 X N p) m c d)))
  · ipra_lc -sD - 𝔞 d * natEq (sum_succ' (Γ := Γ) (wL w * belowB X) N (pairT m p)) -
      𝔞 d * natEq (sum_succ' (Γ := Γ) (wL w * equalB X) N (pairT m p)) - dv - 𝔞 d * bp - 𝔞 d * ep
  · ipra_lc -sD' - 𝔞 d * natEq (sum_succ' (Γ := Γ) (wL w * aboveB X) N (pairT m p)) - dv' -
      𝔞 d * natEq (wa_pt (Γ := Γ) w X N m p)

/-- Variables: `0 = N`, `1 = m`, `2 = d`, `3 = c`, `4 = p`. -/
private abbrev upWF : Fm PTm 5 :=
  le (ap2 (sumF (wY w * Yb X)) (var 0) (pairT (var 3) (pairT (var 3 * var 1) (var 4))) +
      var 2 * (ap2 (sumF (wL w * belowB X)) (var 0) (pairT (var 1) (var 4)) +
        ap2 (sumF (wL w * equalB X)) (var 0) (pairT (var 1) (var 4))))
    (ap2 (sumF (wY w * Yb X)) (var 0) (pairT (var 3) (pairT (var 3 * var 1 + var 2) (var 4))) +
      var 2 * ap2 (sumF (wL w * aboveB X)) (var 0) (pairT (var 1) (var 4)))

private theorem upW₀ : ([] : List (Fm PTm 5)) ⊢[PRAAx] upWF w X := by
  refine ind _ (le_QF _ _) ?_ ?_
  · simp only [subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, Syn.subst_var, Syn.inst_zero,
      Syn.inst_one, inst_two, inst_three, inst_four, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact upW_base w X _ _ _ _
  · simp only [subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, Syn.subst_var, Syn.repl_zero,
      repl_one, repl_two, repl_three, repl_four, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact upW_step w X Prf.hyp0

/-- `D_c(c m) + d (B(m) + E(m)) ≤ D_c(c m + d) + d A(m)`. -/
theorem dev_upW (N m d c p : PTm n) :
    Γ ⊢[PRAAx] le (Dw w X N c (c * m) p + d * (WB w X N m p + WE w X N m p))
      (Dw w X N c (c * m + d) p + d * WA w X N m p) := by
  have h := inst (Γ := Γ) (upW₀ w X) (![N, m, d, c, p] : Fin 5 → PTm n)
  simpa using h

/-! ## The downward comparison -/

theorem downW_base (m t c p : PTm n) :
    Γ ⊢[PRAAx] le (Dw w X zero c (c * m) p + monus (c * m) t * (WA w X zero m p + WE w X zero m p))
      (Dw w X zero c t p + monus (c * m) t * WB w X zero m p) := by
  refine le_of_eq_add (d := zero) ?_
  ipra_lc natEq (sum_zero (Γ := Γ) (wY w * Yb X) (pairT c (pairT t p))) +
    𝔞 (monus (c * m) t) * natEq (sum_zero (Γ := Γ) (wL w * belowB X) (pairT m p)) -
    natEq (sum_zero (Γ := Γ) (wY w * Yb X) (pairT c (pairT (c * m) p))) -
    𝔞 (monus (c * m) t) * natEq (sum_zero (Γ := Γ) (wL w * aboveB X) (pairT m p)) -
    𝔞 (monus (c * m) t) * natEq (sum_zero (Γ := Γ) (wL w * equalB X) (pairT m p))

theorem downW_step {N m t c p : PTm n} (ht : Γ ⊢[PRAAx] le t (c * m))
    (ih : Γ ⊢[PRAAx] le (Dw w X N c (c * m) p + monus (c * m) t * (WA w X N m p + WE w X N m p))
      (Dw w X N c t p + monus (c * m) t * WB w X N m p)) :
    Γ ⊢[PRAAx] le (Dw w X (succ N) c (c * m) p + monus (c * m) t * (WA w X (succ N) m p + WE w X (succ N) m p))
      (Dw w X (succ N) c t p + monus (c * m) t * WB w X (succ N) m p) := by
  have sD := natEq (sum_succ' (Γ := Γ) (wY w * Yb X) N (pairT c (pairT (c * m) p)))
  have sD' := natEq (sum_succ' (Γ := Γ) (wY w * Yb X) N (pairT c (pairT t p)))
  have dv := natEq (dw_pt (Γ := Γ) w X N c (c * m) p); have dv' := natEq (dw_pt (Γ := Γ) w X N c t p)
  have bp := natEq (wb_pt (Γ := Γ) w X N m p); have ep := natEq (we_pt (Γ := Γ) w X N m p)
  refine le_congr ?_ ?_ (add_le_add₂ ih (le_mul_mono (le_refl (inst2 w N p)) (ptc_down (inst2 X N p) m c ht)))
  · ipra_lc -sD - 𝔞 (monus (c * m) t) * natEq (sum_succ' (Γ := Γ) (wL w * aboveB X) N (pairT m p)) -
      𝔞 (monus (c * m) t) * natEq (sum_succ' (Γ := Γ) (wL w * equalB X) N (pairT m p)) - dv -
      𝔞 (monus (c * m) t) * natEq (wa_pt (Γ := Γ) w X N m p) - 𝔞 (monus (c * m) t) * ep
  · ipra_lc -sD' - 𝔞 (monus (c * m) t) * natEq (sum_succ' (Γ := Γ) (wL w * belowB X) N (pairT m p)) - dv' -
      𝔞 (monus (c * m) t) * bp

/-- Variables: `0 = N`, `1 = m`, `2 = t`, `3 = c`, `4 = p`. -/
private abbrev downWF : Fm PTm 5 :=
  le (var 2) (var 3 * var 1) ⟶
    le (ap2 (sumF (wY w * Yb X)) (var 0) (pairT (var 3) (pairT (var 3 * var 1) (var 4))) +
        monus (var 3 * var 1) (var 2) * (ap2 (sumF (wL w * aboveB X)) (var 0) (pairT (var 1) (var 4)) +
          ap2 (sumF (wL w * equalB X)) (var 0) (pairT (var 1) (var 4))))
      (ap2 (sumF (wY w * Yb X)) (var 0) (pairT (var 3) (pairT (var 2) (var 4))) +
        monus (var 3 * var 1) (var 2) * ap2 (sumF (wL w * belowB X)) (var 0) (pairT (var 1) (var 4)))

private theorem downW₀ : ([] : List (Fm PTm 5)) ⊢[PRAAx] downWF w X := by
  refine ind _ ⟨le_QF _ _, le_QF _ _⟩ ?_ ?_
  · simp only [Fm.subst_imp, subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, PTm.subst_monus,
      Syn.subst_var, Syn.inst_zero, Syn.inst_one, inst_two, inst_three, inst_four, ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ]
    exact .impI (downW_base w X _ _ _ _)
  · simp only [Fm.subst_imp, subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, PTm.subst_monus,
      Syn.subst_var, Syn.repl_zero, repl_one, repl_two, repl_three, repl_four, ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ]
    exact .impI (downW_step w X Prf.hyp0 (.impE Prf.hyp1 Prf.hyp0))

/-- For `t ≤ c m` and `d = c m ∸ t`: `D_c(c m) + d (A(m) + E(m)) ≤ D_c(t) + d B(m)`. -/
theorem dev_downW (N m c p : PTm n) {t : PTm n} (ht : Γ ⊢[PRAAx] le t (c * m)) :
    Γ ⊢[PRAAx] le (Dw w X N c (c * m) p + monus (c * m) t * (WA w X N m p + WE w X N m p))
      (Dw w X N c t p + monus (c * m) t * WB w X N m p) := by
  have h := inst (Γ := Γ) (downW₀ w X) (![N, m, t, c, p] : Fin 5 → PTm n)
  simp at h
  exact .impE h ht

/-! ## Weighted medians minimize -/

/-- `m` is a weighted median: `2B(m) ≤ W` and `2A(m) ≤ W`. -/
abbrev isMedW (N m p : PTm n) : Fm PTm n := le (two * WB w X N m p) (Wt w N p) ⋏ le (two * WA w X N m p) (Wt w N p)

theorem l1W_up {N m c t p : PTm n} (hm : Γ ⊢[PRAAx] le (two * WA w X N m p) (Wt w N p))
    (h : Γ ⊢[PRAAx] le (c * m) t) : Γ ⊢[PRAAx] le (Dw w X N c (c * m) p) (Dw w X N c t p) := by
  have ineq := dev_upW (Γ := Γ) w X N m (monus t (c * m)) c p
  refine le_of_eq_add (d := monus t (c * m) * monus (Wt w N p) (two * WA w X N m p) +
    monus (Dw w X N c (c * m + monus t (c * m)) p + monus t (c * m) * WA w X N m p)
      (Dw w X N c (c * m) p + monus t (c * m) * (WB w X N m p + WE w X N m p))) ?_
  ipra_lc natEq (eq_add_of_le ineq) - natEq (congrDw (Γ := Γ) w X N c p (eq_add_of_le h).eqSymm) +
    𝔞 (monus t (c * m)) * natEq (w_partition (Γ := Γ) w X N m p) + 𝔞 (monus t (c * m)) * natEq (eq_add_of_le hm)

theorem l1W_down {N m c t p : PTm n} (hm : Γ ⊢[PRAAx] le (two * WB w X N m p) (Wt w N p))
    (h : Γ ⊢[PRAAx] le t (c * m)) : Γ ⊢[PRAAx] le (Dw w X N c (c * m) p) (Dw w X N c t p) := by
  have ineq := dev_downW (Γ := Γ) w X N m c p h
  refine le_of_eq_add (d := monus (c * m) t * monus (Wt w N p) (two * WB w X N m p) +
    monus (Dw w X N c t p + monus (c * m) t * WB w X N m p)
      (Dw w X N c (c * m) p + monus (c * m) t * (WA w X N m p + WE w X N m p))) ?_
  ipra_lc natEq (eq_add_of_le ineq) + 𝔞 (monus (c * m) t) * natEq (w_partition (Γ := Γ) w X N m p) +
    𝔞 (monus (c * m) t) * natEq (eq_add_of_le hm)

/-- `thm:weighted-l1`, scaled: a weighted median `m` has `∑ w_i |c x_i − c m| ≤ ∑ w_i |c x_i − t|`
for every `c` and `t`. -/
theorem weighted_l1 {N m p : PTm n} (hm : Γ ⊢[PRAAx] isMedW w X N m p) (c t : PTm n) :
    Γ ⊢[PRAAx] le (Dw w X N c (c * m) p) (Dw w X N c t p) :=
  .orE (le_total (c * m) t) (l1W_up w X (Prf.andE₂ hm).wk Prf.hyp0) (l1W_down w X (Prf.andE₁ hm).wk Prf.hyp0)

/-! ## The mean–median bound -/

theorem tri_base (c T p : PTm n) :
    Γ ⊢[PRAAx] le (ad (c * Ew w X zero p) (T * Wt w zero p)) (Dw w X zero c T p) := by
  have z₁ : Γ ⊢[PRAAx] c * Ew w X zero p ≐ zero := (congrMul (.eqRefl _) (sum_zero _ _)).eqTrans (mul_zero _)
  have z₂ : Γ ⊢[PRAAx] T * Wt w zero p ≐ zero := (congrMul (.eqRefl _) (sum_zero _ _)).eqTrans (mul_zero _)
  have z : Γ ⊢[PRAAx] ad (c * Ew w X zero p) (T * Wt w zero p) ≐ zero :=
    (congrAdd ((congrMonus z₁ z₂).eqTrans (zero_monus _)) ((congrMonus z₂ z₁).eqTrans (zero_monus _))).eqTrans
      (add_zero _)
  exact le_congr z.eqSymm (.eqRefl _) (zero_le _)

theorem tri_step {N c T p : PTm n}
    (ih : Γ ⊢[PRAAx] le (ad (c * Ew w X N p) (T * Wt w N p)) (Dw w X N c T p)) :
    Γ ⊢[PRAAx] le (ad (c * Ew w X (succ N) p) (T * Wt w (succ N) p)) (Dw w X (succ N) c T p) := by
  have sS := sum_succ' (Γ := Γ) (w * X) N p
  rw [inst2_mul'] at sS
  have sS' := natEq sS; have sW := natEq (sum_succ' (Γ := Γ) w N p)
  have c1 : Γ ⊢[PRAAx] c * Ew w X (succ N) p ≐ c * Ew w X N p + inst2 w N p * (c * inst2 X N p) := by
    ipra_lc 𝔞 c * sS'
  have c2 : Γ ⊢[PRAAx] T * Wt w (succ N) p ≐ T * Wt w N p + inst2 w N p * T := by
    ipra_lc 𝔞 T * sW
  have hA := congrAdd (congrMonus c1 c2) (congrMonus c2 c1)
  have DE : Γ ⊢[PRAAx] Dw w X (succ N) c T p ≐ Dw w X N c T p + inst2 w N p * ad (c * inst2 X N p) T :=
    (sum_succ' _ _ _).eqTrans (congrAdd (.eqRefl _) (dw_pt w X N c T p))
  refine le_congr hA.eqSymm DE.eqSymm (le_trans (ad_add_le _ _ _ _) (add_le_add₂ ih ?_))
  exact le_congr (.eqRefl _) (ad_mul _ _ _) (le_refl _)

/-- Variables: `0 = N`, `1 = c`, `2 = T`, `3 = p`. -/
private abbrev triF : Fm PTm 4 :=
  le (monus (var 1 * ap2 (sumF (w * X)) (var 0) (var 3)) (var 2 * ap2 (sumF w) (var 0) (var 3)) +
      monus (var 2 * ap2 (sumF w) (var 0) (var 3)) (var 1 * ap2 (sumF (w * X)) (var 0) (var 3)))
    (ap2 (sumF (wY w * Yb X)) (var 0) (pairT (var 1) (pairT (var 2) (var 3))))

private theorem tri₀ : ([] : List (Fm PTm 4)) ⊢[PRAAx] triF w X := by
  refine ind _ (le_QF _ _) ?_ ?_
  · simp only [subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, PTm.subst_monus, Syn.subst_var,
      Syn.inst_zero, Syn.inst_one, inst_two, inst_three, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact tri_base w X _ _ _
  · simp only [subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, PTm.subst_monus, Syn.subst_var,
      Syn.repl_zero, repl_one, repl_two, repl_three, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact tri_step w X Prf.hyp0

/-- `|c S − T W| ≤ ∑ w_i |c x_i − T|`. -/
theorem sum_triangle (N c T p : PTm n) :
    Γ ⊢[PRAAx] le (ad (c * Ew w X N p) (T * Wt w N p)) (Dw w X N c T p) := by
  have h := inst (Γ := Γ) (tri₀ w X) (![N, c, T, p] : Fin 4 → PTm n)
  simpa using h

theorem wt_wY (N c T p : PTm n) : Γ ⊢[PRAAx] Wt (wY w) N (pairT c (pairT T p)) ≐ Wt w N p := by
  refine sum_congr_bounded (wY w) w _ p N (.allI (.impI ?_))
  have e : ∀ (i y : PTm (n + 1)), inst2 (wY w) i y = inst2 w i (sndT (sndT y)) := fun i y => by
    simp only [inst2]; rw [Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  rw [e]
  simp only [Syn.shift, subst_pairT]
  exact congrInst2 w (.eqRefl _) ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))

/-- `thm:mean-median` (`eq:mean-median-cleared`): for a weighted median `m` and `W > 0`,
`|S − W m|² + S² ≤ W Q`, i.e. `(S − W m)² ≤ W Q − S²`. -/
theorem mean_median {N m p : PTm n} (hm : Γ ⊢[PRAAx] isMedW w X N m p)
    (hW : Γ ⊢[PRAAx] Wt w N p ≐ succ (pred (Wt w N p))) :
    Γ ⊢[PRAAx] le (ad (Ew w X N p) (Wt w N p * m) * ad (Ew w X N p) (Wt w N p * m) + Ew w X N p * Ew w X N p)
      (Wt w N p * Ew w (X * X) N p) := by
  have t1 := sum_triangle (Γ := Γ) w X N (Wt w N p) (Wt w N p * m) p
  have adm : Γ ⊢[PRAAx] ad (Wt w N p * Ew w X N p) (Wt w N p * m * Wt w N p) ≐
      Wt w N p * ad (Ew w X N p) (Wt w N p * m) :=
    (congrAdd (congrMonus (.eqRefl _) (mul_comm _ _)) (congrMonus (mul_comm _ _) (.eqRefl _))).eqTrans (ad_mul _ _ _)
  have e1 := le_trans (le_congr adm (.eqRefl _) t1) (weighted_l1 w X hm (Wt w N p) (Ew w X N p))
  have cs := second_moment (Γ := Γ) (wY w) (Yb X) N (pairT (Wt w N p) (pairT (Ew w X N p) p))
  have cs' : Γ ⊢[PRAAx] le (Dw w X N (Wt w N p) (Ew w X N p) p * Dw w X N (Wt w N p) (Ew w X N p) p)
      (Vr w X N p * Wt w N p) :=
    le_congr (.eqRefl _) (congrMul (.eqRefl _) (wt_wY w N _ _ p)) cs
  have c := le_trans (le_mul_mono e1 e1) cs'
  have big : Γ ⊢[PRAAx] le (Wt w N p * (Wt w N p * (ad (Ew w X N p) (Wt w N p * m) * ad (Ew w X N p) (Wt w N p * m) +
      Ew w X N p * Ew w X N p))) (Wt w N p * (Wt w N p * (Wt w N p * Ew w (X * X) N p))) := by
    refine le_of_eq_add (d := monus (Vr w X N p * Wt w N p)
      (Wt w N p * ad (Ew w X N p) (Wt w N p * m) * (Wt w N p * ad (Ew w X N p) (Wt w N p * m)))) ?_
    ipra_lc natEq (eq_add_of_le c) - 𝔞 (Wt w N p) * natEq (variance_identity (Γ := Γ) w X N p)
  exact le_cancel_pos hW (le_cancel_pos hW big)

end Weighted

end LeanProofs.IPRA.Probability.MedianWeighted
