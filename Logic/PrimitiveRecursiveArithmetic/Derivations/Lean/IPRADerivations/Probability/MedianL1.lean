import IPRADerivations.Probability.MedianCounts

/-!
# Balance medians minimize the absolute deviation

Packet: `probability/median_ipra_constructive_proofs`, Theorem `thm:l1` (the complete `L¹`
minimizer theorem), proved from the counts `B(t)`, `E(t)`, `A(t)` of `Probability/MedianCounts`
instead of a sorted list. For a body `x(i, p)` with `N` entries let

  `D(t) = ∑_{i<N} |x_i − t|`.

* `pt_up`, `pt_down`: the pointwise triangle estimates
  `|x − m| + d([x < m] + [x = m]) ≤ |x − (m + d)| + d [m < x]` and its mirror image;
* `dev_up`, `dev_down`: summed, `D(m) + d (B(m) + E(m)) ≤ D(m + d) + d A(m)` and
  `D(t + d) + d (A + E)(t + d) ≤ D(t) + d B(t + d)`;
* `l1_up`, `l1_down`, `median_l1`: a balance median `m` (`2B(m) ≤ N`, `2A(m) ≤ N`) has
  `D(m) ≤ D(t)` for every `t`;
* `dev_succ`, `dev_pred`: the exact unit steps `D(t + 1) + A(t) = D(t) + B(t) + E(t)` and
  `D(s) + B(s + 1) = D(s + 1) + E(s + 1) + A(s + 1)`;
* `min_median`: conversely, if `D(t) ≤ D(t + 1)` and `D(t) ≤ D(t ∸ 1)` (in particular if `t`
  minimizes `D`), then `t` is a balance median.

Together these are both directions of `thm:l1`, with the interval `[L, U]` of the packet replaced by
the balance condition (equivalent to it by `thm:middle-interval`).

The deviation is the subtraction-free `|a − b| = (a ∸ b) + (b ∸ a)` of `Probability/Variance`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.MedianL1

open_ipra
open LeanProofs.IPRA.Algebra.CubeRootTwo (sg sg_zero sg_succ)
open LeanProofs.IPRA.AnalyticNumberTheory.Totatives (sg_lt sg_le)
open LeanProofs.IPRA.Probability.Variance (ad)
open LeanProofs.IPRA.Probability.MedianCounts

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Pointwise estimates -/

theorem pt_up_below {x m : PTm n} (d : PTm n) (h : Γ ⊢[PRAAx] le x m)
    (hs : Γ ⊢[PRAAx] sg (monus m x) + eqb x m ≐ one) (ha : Γ ⊢[PRAAx] sg (monus x m) ≐ zero) :
    Γ ⊢[PRAAx] le (ad x m + d * (sg (monus m x) + eqb x m)) (ad x (m + d) + d * sg (monus x m)) :=
  MedianCounts.deviation_up_below d h hs ha

theorem pt_up_above₁ {x m : PTm n} (d : PTm n) (h : Γ ⊢[PRAAx] lt m x) (hle : Γ ⊢[PRAAx] le x (m + d)) :
    Γ ⊢[PRAAx] le (ad x m + d * (sg (monus m x) + eqb x m)) (ad x (m + d) + d * sg (monus x m)) :=
  MedianCounts.deviation_up_above₁ d (le_of_lt h) (sg_le (le_of_lt h)) (eqb_zero_of_gt h) (sg_lt h) hle

theorem pt_up_above₂ {x m : PTm n} (d : PTm n) (h : Γ ⊢[PRAAx] lt m x) (hge : Γ ⊢[PRAAx] le (m + d) x) :
    Γ ⊢[PRAAx] le (ad x m + d * (sg (monus m x) + eqb x m)) (ad x (m + d) + d * sg (monus x m)) :=
  MedianCounts.deviation_up_above₂ d (le_of_lt h) (sg_le (le_of_lt h)) (eqb_zero_of_gt h) (sg_lt h) hge

theorem pt_up_above {x m : PTm n} (d : PTm n) (h : Γ ⊢[PRAAx] lt m x) :
    Γ ⊢[PRAAx] le (ad x m + d * (sg (monus m x) + eqb x m)) (ad x (m + d) + d * sg (monus x m)) :=
  .orE (le_total x (m + d)) (pt_up_above₁ d h.wk Prf.hyp0) (pt_up_above₂ d h.wk Prf.hyp0)

/-- `|x − m| + d([x < m] + [x = m]) ≤ |x − (m + d)| + d [m < x]`. -/
theorem pt_up (x m d : PTm n) :
    Γ ⊢[PRAAx] le (ad x m + d * (sg (monus m x) + eqb x m)) (ad x (m + d) + d * sg (monus x m)) := by
  refine .orE (lt_or_le x m) ?_ (.orE (lt_or_eq_of_le Prf.hyp0) ?_ ?_)
  · exact pt_up_below d (le_of_lt Prf.hyp0)
      ((congrAdd (sg_lt Prf.hyp0) (eqb_zero_of_lt Prf.hyp0)).eqTrans (add_zero _)) (sg_le (le_of_lt Prf.hyp0))
  · exact pt_up_above d Prf.hyp0
  · exact pt_up_below d (le_congr Prf.hyp0 (.eqRefl _) (le_refl m))
      ((congrAdd (sg_le (le_congr (.eqRefl _) Prf.hyp0 (le_refl m))) (eqb_of_eq Prf.hyp0.eqSymm)).eqTrans
        (zero_add _))
      (sg_le (le_congr Prf.hyp0 (.eqRefl _) (le_refl m)))

theorem pt_down_above {x t : PTm n} (d : PTm n) (h : Γ ⊢[PRAAx] le (t + d) x)
    (hs : Γ ⊢[PRAAx] sg (monus x (t + d)) + eqb x (t + d) ≐ one) (hb : Γ ⊢[PRAAx] sg (monus (t + d) x) ≐ zero) :
    Γ ⊢[PRAAx] le (ad x (t + d) + d * (sg (monus x (t + d)) + eqb x (t + d))) (ad x t + d * sg (monus (t + d) x)) :=
  MedianCounts.deviation_down_above d h hs hb

theorem pt_down_below₁ {x t : PTm n} (d : PTm n) (h : Γ ⊢[PRAAx] lt x (t + d)) (hle : Γ ⊢[PRAAx] le t x) :
    Γ ⊢[PRAAx] le (ad x (t + d) + d * (sg (monus x (t + d)) + eqb x (t + d))) (ad x t + d * sg (monus (t + d) x)) :=
  MedianCounts.deviation_down_below₁ d (le_of_lt h) (sg_le (le_of_lt h)) (eqb_zero_of_lt h) (sg_lt h) hle

theorem pt_down_below₂ {x t : PTm n} (d : PTm n) (h : Γ ⊢[PRAAx] lt x (t + d)) (hge : Γ ⊢[PRAAx] le x t) :
    Γ ⊢[PRAAx] le (ad x (t + d) + d * (sg (monus x (t + d)) + eqb x (t + d))) (ad x t + d * sg (monus (t + d) x)) :=
  MedianCounts.deviation_down_below₂ d (le_of_lt h) (sg_le (le_of_lt h)) (eqb_zero_of_lt h) (sg_lt h) hge

theorem pt_down_below {x t : PTm n} (d : PTm n) (h : Γ ⊢[PRAAx] lt x (t + d)) :
    Γ ⊢[PRAAx] le (ad x (t + d) + d * (sg (monus x (t + d)) + eqb x (t + d))) (ad x t + d * sg (monus (t + d) x)) :=
  .orE (le_total t x) (pt_down_below₁ d h.wk Prf.hyp0) (pt_down_below₂ d h.wk Prf.hyp0)

/-- `|x − (t + d)| + d([t + d < x] + [x = t + d]) ≤ |x − t| + d [x < t + d]`. -/
theorem pt_down (x t d : PTm n) :
    Γ ⊢[PRAAx] le (ad x (t + d) + d * (sg (monus x (t + d)) + eqb x (t + d))) (ad x t + d * sg (monus (t + d) x)) := by
  refine .orE (lt_or_le x (t + d)) (pt_down_below d Prf.hyp0) (.orE (lt_or_eq_of_le Prf.hyp0) ?_ ?_)
  · exact pt_down_above d (le_of_lt Prf.hyp0)
      ((congrAdd (sg_lt Prf.hyp0) (eqb_zero_of_gt Prf.hyp0)).eqTrans (add_zero _)) (sg_le (le_of_lt Prf.hyp0))
  · exact pt_down_above d (le_congr (.eqRefl _) Prf.hyp0 (le_refl _))
      ((congrAdd (sg_le (le_congr Prf.hyp0 (.eqRefl _) (le_refl _))) (eqb_of_eq Prf.hyp0.eqSymm)).eqTrans
        (zero_add _))
      (sg_le (le_congr (.eqRefl _) Prf.hyp0 (le_refl _)))

/-! ## The deviation sum -/

section Dev

variable (X : PTm 2)

/-- `|x(i, snd z) − fst z|`. -/
def devB : PTm 2 := monus (Syn.subst ![var 0, sndT (var 1)] X) (fstT (var 1)) +
  monus (fstT (var 1)) (Syn.subst ![var 0, sndT (var 1)] X)

theorem inst2_dev (i z : PTm n) : inst2 (devB X) i z = ad (inst2 X i (sndT z)) (fstT z) := by
  simp only [inst2, devB, PTm.subst_add, PTm.subst_monus, subst_fstT, subst_data, Syn.subst_var]
  simp

theorem dev_pt (i t p : PTm n) : Γ ⊢[PRAAx] inst2 (devB X) i (pairT t p) ≐ ad (inst2 X i p) t := by
  rw [inst2_dev]
  exact congrAdd (congrMonus (congrInst2 X (.eqRefl _) (snd_pair _ _)) (fst_pair _ _))
    (congrMonus (fst_pair _ _) (congrInst2 X (.eqRefl _) (snd_pair _ _)))

/-- `D(t) = ∑_{i<N} |x_i − t|`. -/
abbrev Dv (N t p : PTm n) : PTm n := ap2 (sumF (devB X)) N (pairT t p)

theorem up_base (m d p : PTm n) :
    Γ ⊢[PRAAx] le (Dv X zero m p + d * (Bc X zero m p + Ec X zero m p)) (Dv X zero (m + d) p + d * Ac X zero m p) := by
  refine le_of_eq_add (d := zero) ?_
  ipra_lc natEq (sum_zero (Γ := Γ) (devB X) (pairT (m + d) p)) +
    𝔞 d * natEq (sum_zero (Γ := Γ) (aboveB X) (pairT m p)) - natEq (sum_zero (Γ := Γ) (devB X) (pairT m p)) -
    𝔞 d * natEq (sum_zero (Γ := Γ) (belowB X) (pairT m p)) - 𝔞 d * natEq (sum_zero (Γ := Γ) (equalB X) (pairT m p))

theorem up_step {N m d p : PTm n}
    (ih : Γ ⊢[PRAAx] le (Dv X N m p + d * (Bc X N m p + Ec X N m p)) (Dv X N (m + d) p + d * Ac X N m p)) :
    Γ ⊢[PRAAx] le (Dv X (succ N) m p + d * (Bc X (succ N) m p + Ec X (succ N) m p))
      (Dv X (succ N) (m + d) p + d * Ac X (succ N) m p) := by
  have sD := natEq (sum_succ' (Γ := Γ) (devB X) N (pairT m p))
  have sD' := natEq (sum_succ' (Γ := Γ) (devB X) N (pairT (m + d) p))
  have dv := natEq (dev_pt (Γ := Γ) X N m p); have dv' := natEq (dev_pt (Γ := Γ) X N (m + d) p)
  have bp := natEq (below_pt (Γ := Γ) X N m p); have ep := natEq (equal_pt (Γ := Γ) X N m p)
  refine le_congr ?_ ?_ (add_le_add₂ ih (pt_up (inst2 X N p) m d))
  · ipra_lc -sD - 𝔞 d * natEq (sum_succ' (Γ := Γ) (belowB X) N (pairT m p)) -
      𝔞 d * natEq (sum_succ' (Γ := Γ) (equalB X) N (pairT m p)) - dv - 𝔞 d * bp - 𝔞 d * ep
  · ipra_lc -sD' - 𝔞 d * natEq (sum_succ' (Γ := Γ) (aboveB X) N (pairT m p)) - dv' -
      𝔞 d * natEq (above_pt (Γ := Γ) X N m p)

/-- Variables: `0 = N`, `1 = m`, `2 = d`, `3 = p`. -/
private abbrev upF : Fm PTm 4 :=
  le (ap2 (sumF (devB X)) (var 0) (pairT (var 1) (var 3)) +
      var 2 * (ap2 (sumF (belowB X)) (var 0) (pairT (var 1) (var 3)) +
        ap2 (sumF (equalB X)) (var 0) (pairT (var 1) (var 3))))
    (ap2 (sumF (devB X)) (var 0) (pairT (var 1 + var 2) (var 3)) +
      var 2 * ap2 (sumF (aboveB X)) (var 0) (pairT (var 1) (var 3)))

private theorem up₀ : ([] : List (Fm PTm 4)) ⊢[PRAAx] upF X := by
  ipra_ind (le_QF _ _) [subst_le, subst_ap2, subst_pairT]
  · exact up_base X _ _ _
  · exact up_step X Prf.hyp0

/-- `D(m) + d (B(m) + E(m)) ≤ D(m + d) + d A(m)`. -/
theorem dev_up (N m d p : PTm n) :
    Γ ⊢[PRAAx] le (Dv X N m p + d * (Bc X N m p + Ec X N m p)) (Dv X N (m + d) p + d * Ac X N m p) := by
  have h := inst (Γ := Γ) (up₀ X) (![N, m, d, p] : Fin 4 → PTm n)
  simpa using h

theorem down_base (t d p : PTm n) :
    Γ ⊢[PRAAx] le (Dv X zero (t + d) p + d * (Ac X zero (t + d) p + Ec X zero (t + d) p))
      (Dv X zero t p + d * Bc X zero (t + d) p) := by
  refine le_of_eq_add (d := zero) ?_
  ipra_lc natEq (sum_zero (Γ := Γ) (devB X) (pairT t p)) +
    𝔞 d * natEq (sum_zero (Γ := Γ) (belowB X) (pairT (t + d) p)) -
    natEq (sum_zero (Γ := Γ) (devB X) (pairT (t + d) p)) -
    𝔞 d * natEq (sum_zero (Γ := Γ) (aboveB X) (pairT (t + d) p)) -
    𝔞 d * natEq (sum_zero (Γ := Γ) (equalB X) (pairT (t + d) p))

theorem down_step {N t d p : PTm n}
    (ih : Γ ⊢[PRAAx] le (Dv X N (t + d) p + d * (Ac X N (t + d) p + Ec X N (t + d) p))
      (Dv X N t p + d * Bc X N (t + d) p)) :
    Γ ⊢[PRAAx] le (Dv X (succ N) (t + d) p + d * (Ac X (succ N) (t + d) p + Ec X (succ N) (t + d) p))
      (Dv X (succ N) t p + d * Bc X (succ N) (t + d) p) := by
  have sD := natEq (sum_succ' (Γ := Γ) (devB X) N (pairT (t + d) p))
  have sD' := natEq (sum_succ' (Γ := Γ) (devB X) N (pairT t p))
  have dv := natEq (dev_pt (Γ := Γ) X N (t + d) p); have dv' := natEq (dev_pt (Γ := Γ) X N t p)
  have bp := natEq (below_pt (Γ := Γ) X N (t + d) p); have ep := natEq (equal_pt (Γ := Γ) X N (t + d) p)
  refine le_congr ?_ ?_ (add_le_add₂ ih (pt_down (inst2 X N p) t d))
  · ipra_lc -sD - 𝔞 d * natEq (sum_succ' (Γ := Γ) (aboveB X) N (pairT (t + d) p)) -
      𝔞 d * natEq (sum_succ' (Γ := Γ) (equalB X) N (pairT (t + d) p)) - dv -
      𝔞 d * natEq (above_pt (Γ := Γ) X N (t + d) p) - 𝔞 d * ep
  · ipra_lc -sD' - 𝔞 d * natEq (sum_succ' (Γ := Γ) (belowB X) N (pairT (t + d) p)) - dv' - 𝔞 d * bp

/-- Variables: `0 = N`, `1 = t`, `2 = d`, `3 = p`. -/
private abbrev downF : Fm PTm 4 :=
  le (ap2 (sumF (devB X)) (var 0) (pairT (var 1 + var 2) (var 3)) +
      var 2 * (ap2 (sumF (aboveB X)) (var 0) (pairT (var 1 + var 2) (var 3)) +
        ap2 (sumF (equalB X)) (var 0) (pairT (var 1 + var 2) (var 3))))
    (ap2 (sumF (devB X)) (var 0) (pairT (var 1) (var 3)) +
      var 2 * ap2 (sumF (belowB X)) (var 0) (pairT (var 1 + var 2) (var 3)))

private theorem down₀ : ([] : List (Fm PTm 4)) ⊢[PRAAx] downF X := by
  ipra_ind (le_QF _ _) [subst_le, subst_ap2, subst_pairT]
  · exact down_base X _ _ _
  · exact down_step X Prf.hyp0

/-- `D(t + d) + d (A + E)(t + d) ≤ D(t) + d B(t + d)`. -/
theorem dev_down (N t d p : PTm n) :
    Γ ⊢[PRAAx] le (Dv X N (t + d) p + d * (Ac X N (t + d) p + Ec X N (t + d) p))
      (Dv X N t p + d * Bc X N (t + d) p) := by
  have h := inst (Γ := Γ) (down₀ X) (![N, t, d, p] : Fin 4 → PTm n)
  simpa using h

/-! ## Medians minimize -/

theorem congrDv (N p : PTm n) {t t' : PTm n} (h : Γ ⊢[PRAAx] t ≐ t') : Γ ⊢[PRAAx] Dv X N t p ≐ Dv X N t' p :=
  congrAp2 (sumF (devB X)) (.eqRefl _) (LeanProofs.IPRA.congrPairT h (.eqRefl _))

theorem congrCount (f : PTm 2) (N p : PTm n) {t t' : PTm n} (h : Γ ⊢[PRAAx] t ≐ t') :
    Γ ⊢[PRAAx] ap2 (sumF f) N (pairT t p) ≐ ap2 (sumF f) N (pairT t' p) :=
  congrAp2 (sumF f) (.eqRefl _) (LeanProofs.IPRA.congrPairT h (.eqRefl _))

/-- If `2A(m) ≤ N` and `m ≤ t`, then `D(m) ≤ D(t)`. -/
theorem l1_up {N m t p : PTm n} (hm : Γ ⊢[PRAAx] le (two * Ac X N m p) N) (h : Γ ⊢[PRAAx] le m t) :
    Γ ⊢[PRAAx] le (Dv X N m p) (Dv X N t p) := by
  have ineq := dev_up (Γ := Γ) X N m (monus t m) p
  refine le_of_eq_add (d := monus t m * monus N (two * Ac X N m p) +
    monus (Dv X N (m + monus t m) p + monus t m * Ac X N m p)
      (Dv X N m p + monus t m * (Bc X N m p + Ec X N m p))) ?_
  ipra_lc natEq (eq_add_of_le ineq) - natEq (congrDv (Γ := Γ) X N p (eq_add_of_le h).eqSymm) +
    𝔞 (monus t m) * natEq (partition (Γ := Γ) X N m p) + 𝔞 (monus t m) * natEq (eq_add_of_le hm)

/-- If `2B(m) ≤ N` and `t ≤ m`, then `D(m) ≤ D(t)`. -/
theorem l1_down {N m t p : PTm n} (hm : Γ ⊢[PRAAx] le (two * Bc X N m p) N) (h : Γ ⊢[PRAAx] le t m) :
    Γ ⊢[PRAAx] le (Dv X N m p) (Dv X N t p) := by
  have ineq := dev_down (Γ := Γ) X N t (monus m t) p
  have hm' := (eq_add_of_le h).eqSymm
  refine le_of_eq_add (d := monus m t * monus N (two * Bc X N m p) +
    monus (Dv X N t p + monus m t * Bc X N (t + monus m t) p)
      (Dv X N (t + monus m t) p + monus m t * (Ac X N (t + monus m t) p + Ec X N (t + monus m t) p))) ?_
  ipra_lc natEq (eq_add_of_le ineq) + natEq (congrDv (Γ := Γ) X N p hm') -
    𝔞 (monus m t) * natEq (congrCount (Γ := Γ) (belowB X) N p hm') +
    𝔞 (monus m t) * natEq (congrCount (Γ := Γ) (aboveB X) N p hm') +
    𝔞 (monus m t) * natEq (congrCount (Γ := Γ) (equalB X) N p hm') +
    𝔞 (monus m t) * natEq (partition (Γ := Γ) X N m p) + 𝔞 (monus m t) * natEq (eq_add_of_le hm)

/-- `thm:l1`, medians are minimizers: a balance median `m` has `D(m) ≤ D(t)` for every `t`. -/
theorem median_l1 {N m p : PTm n} (hm : Γ ⊢[PRAAx] isMed X N m p) (t : PTm n) :
    Γ ⊢[PRAAx] le (Dv X N m p) (Dv X N t p) :=
  .orE (le_total m t) (l1_up X (Prf.andE₂ hm).wk Prf.hyp0) (l1_down X (Prf.andE₁ hm).wk Prf.hyp0)

end Dev

/-! ## Unit steps, and minimizers are medians -/

alias le_of_lt_succ' := Common.le_of_lt_succ

theorem pu_above {x t : PTm n} (h : Γ ⊢[PRAAx] lt t x) :
    Γ ⊢[PRAAx] ad x (succ t) + sg (monus x t) ≐ ad x t + (sg (monus t x) + eqb x t) := by
  have hs : Γ ⊢[PRAAx] le (succ t) x := h
  have hl := le_of_lt h
  ipra_lc natEq hs - natEq (eq_add_of_le hs) - natEq hl + natEq (eq_add_of_le hl) + natEq (sg_lt h) -
    natEq (sg_le hl) - natEq (eqb_zero_of_gt h)

theorem pu_below {x t : PTm n} (h : Γ ⊢[PRAAx] le x t) (hs : Γ ⊢[PRAAx] sg (monus t x) + eqb x t ≐ one)
    (ha : Γ ⊢[PRAAx] sg (monus x t) ≐ zero) :
    Γ ⊢[PRAAx] ad x (succ t) + sg (monus x t) ≐ ad x t + (sg (monus t x) + eqb x t) := by
  have h1 := natEq h; have h2 := natEq (eq_add_of_le h)
  have hl : Γ ⊢[PRAAx] le x (succ t) := le_of_eq_add (d := succ (monus t x)) (by
    ipra_lc h2)
  have h3 := natEq hl; have h4 := natEq (eq_add_of_le hl)
  have s' := natEq hs; have a := natEq ha
  apply deriveNat; ipra_simps
  linear_combination h3 - h4 + h2 - h1 + a - s'

/-- `|x − (t + 1)| + [t < x] = |x − t| + [x < t] + [x = t]`. -/
theorem pu (x t : PTm n) :
    Γ ⊢[PRAAx] ad x (succ t) + sg (monus x t) ≐ ad x t + (sg (monus t x) + eqb x t) := by
  refine .orE (lt_or_le t x) (pu_above Prf.hyp0) (.orE (lt_or_eq_of_le Prf.hyp0) ?_ ?_)
  · exact pu_below (le_of_lt Prf.hyp0)
      ((congrAdd (sg_lt Prf.hyp0) (eqb_zero_of_lt Prf.hyp0)).eqTrans (add_zero _)) (sg_le (le_of_lt Prf.hyp0))
  · exact pu_below (le_congr (.eqRefl _) Prf.hyp0 (le_refl _))
      ((congrAdd (sg_le (le_congr Prf.hyp0 (.eqRefl _) (le_refl _))) (eqb_of_eq Prf.hyp0)).eqTrans (zero_add _))
      (sg_le (le_congr (.eqRefl _) Prf.hyp0 (le_refl _)))

theorem pl_below {x s : PTm n} (h : Γ ⊢[PRAAx] lt x (succ s)) :
    Γ ⊢[PRAAx] ad x s + sg (monus (succ s) x) ≐ ad x (succ s) + (eqb x (succ s) + sg (monus x (succ s))) := by
  have hl := le_of_lt_succ' h; have hs := le_of_lt h
  ipra_lc natEq hl - natEq (eq_add_of_le hl) - natEq hs + natEq (eq_add_of_le hs) + natEq (sg_lt h) -
    natEq (sg_le hs) - natEq (eqb_zero_of_lt h)

theorem pl_above {x s : PTm n} (h : Γ ⊢[PRAAx] le (succ s) x)
    (hs : Γ ⊢[PRAAx] eqb x (succ s) + sg (monus x (succ s)) ≐ one) (hb : Γ ⊢[PRAAx] sg (monus (succ s) x) ≐ zero) :
    Γ ⊢[PRAAx] ad x s + sg (monus (succ s) x) ≐ ad x (succ s) + (eqb x (succ s) + sg (monus x (succ s))) := by
  have h1 := natEq h; have h2 := natEq (eq_add_of_le h)
  have hl : Γ ⊢[PRAAx] le s x := le_of_eq_add (d := succ (monus x (succ s))) (by
    ipra_lc h2)
  have h3 := natEq hl; have h4 := natEq (eq_add_of_le hl)
  have s' := natEq hs; have b := natEq hb
  apply deriveNat; ipra_simps
  linear_combination h3 - h4 + h2 - h1 + b - s'

/-- `|x − s| + [x < s + 1] = |x − (s + 1)| + [x = s + 1] + [s + 1 < x]`. -/
theorem pl (x s : PTm n) :
    Γ ⊢[PRAAx] ad x s + sg (monus (succ s) x) ≐ ad x (succ s) + (eqb x (succ s) + sg (monus x (succ s))) := by
  refine .orE (lt_or_le x (succ s)) (pl_below Prf.hyp0) (.orE (lt_or_eq_of_le Prf.hyp0) ?_ ?_)
  · exact pl_above (le_of_lt Prf.hyp0)
      ((congrAdd (eqb_zero_of_gt Prf.hyp0) (sg_lt Prf.hyp0)).eqTrans (zero_add _)) (sg_le (le_of_lt Prf.hyp0))
  · exact pl_above (le_congr (.eqRefl _) Prf.hyp0 (le_refl _))
      ((congrAdd (eqb_of_eq Prf.hyp0.eqSymm) (sg_le (le_congr Prf.hyp0 (.eqRefl _) (le_refl _)))).eqTrans
        (add_zero _))
      (sg_le (le_congr (.eqRefl _) Prf.hyp0 (le_refl _)))

section Steps

variable (X : PTm 2)

theorem uz_base (t p : PTm n) :
    Γ ⊢[PRAAx] Dv X zero (succ t) p + Ac X zero t p ≐ Dv X zero t p + (Bc X zero t p + Ec X zero t p) := by
  ipra_lc natEq (sum_zero (Γ := Γ) (devB X) (pairT (succ t) p)) + natEq (sum_zero (Γ := Γ) (aboveB X) (pairT t p)) -
    natEq (sum_zero (Γ := Γ) (devB X) (pairT t p)) - natEq (sum_zero (Γ := Γ) (belowB X) (pairT t p)) -
    natEq (sum_zero (Γ := Γ) (equalB X) (pairT t p))

theorem uz_step {N t p : PTm n}
    (ih : Γ ⊢[PRAAx] Dv X N (succ t) p + Ac X N t p ≐ Dv X N t p + (Bc X N t p + Ec X N t p)) :
    Γ ⊢[PRAAx] Dv X (succ N) (succ t) p + Ac X (succ N) t p ≐
      Dv X (succ N) t p + (Bc X (succ N) t p + Ec X (succ N) t p) := by
  have sD := natEq (sum_succ' (Γ := Γ) (devB X) N (pairT t p))
  have sD' := natEq (sum_succ' (Γ := Γ) (devB X) N (pairT (succ t) p))
  have sB := natEq (sum_succ' (Γ := Γ) (belowB X) N (pairT t p))
  have sE := natEq (sum_succ' (Γ := Γ) (equalB X) N (pairT t p))
  have sA := natEq (sum_succ' (Γ := Γ) (aboveB X) N (pairT t p))
  have dv := natEq (dev_pt (Γ := Γ) X N t p); have dv' := natEq (dev_pt (Γ := Γ) X N (succ t) p)
  have bp := natEq (below_pt (Γ := Γ) X N t p); have ep := natEq (equal_pt (Γ := Γ) X N t p)
  have ih' := natEq ih; have pw := natEq (pu (Γ := Γ) (inst2 X N p) t)
  apply deriveNat; ipra_simps
  linear_combination sD' + sA - sD - sB - sE + ih' + dv' + natEq (above_pt (Γ := Γ) X N t p) - dv - bp - ep + pw

/-- Variables: `0 = N`, `1 = t`, `2 = p`. -/
private abbrev uzF : Fm PTm 3 :=
  ap2 (sumF (devB X)) (var 0) (pairT (succ (var 1)) (var 2)) + ap2 (sumF (aboveB X)) (var 0) (pairT (var 1) (var 2)) ≐
    ap2 (sumF (devB X)) (var 0) (pairT (var 1) (var 2)) +
      (ap2 (sumF (belowB X)) (var 0) (pairT (var 1) (var 2)) + ap2 (sumF (equalB X)) (var 0) (pairT (var 1) (var 2)))

private theorem uz₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] uzF X := by
  ipra_ind [subst_ap2, subst_pairT]
  · exact uz_base X _ _
  · exact uz_step X Prf.hyp0

/-- `D(t + 1) + A(t) = D(t) + B(t) + E(t)`. -/
theorem dev_succ (N t p : PTm n) :
    Γ ⊢[PRAAx] Dv X N (succ t) p + Ac X N t p ≐ Dv X N t p + (Bc X N t p + Ec X N t p) := by
  have h := inst (Γ := Γ) (uz₀ X) (![N, t, p] : Fin 3 → PTm n)
  simpa using h

theorem lz_base (s p : PTm n) :
    Γ ⊢[PRAAx] Dv X zero s p + Bc X zero (succ s) p ≐
      Dv X zero (succ s) p + (Ec X zero (succ s) p + Ac X zero (succ s) p) := by
  ipra_lc natEq (sum_zero (Γ := Γ) (devB X) (pairT s p)) + natEq (sum_zero (Γ := Γ) (belowB X) (pairT (succ s) p)) -
    natEq (sum_zero (Γ := Γ) (devB X) (pairT (succ s) p)) - natEq (sum_zero (Γ := Γ) (equalB X) (pairT (succ s) p)) -
    natEq (sum_zero (Γ := Γ) (aboveB X) (pairT (succ s) p))

theorem lz_step {N s p : PTm n}
    (ih : Γ ⊢[PRAAx] Dv X N s p + Bc X N (succ s) p ≐ Dv X N (succ s) p + (Ec X N (succ s) p + Ac X N (succ s) p)) :
    Γ ⊢[PRAAx] Dv X (succ N) s p + Bc X (succ N) (succ s) p ≐
      Dv X (succ N) (succ s) p + (Ec X (succ N) (succ s) p + Ac X (succ N) (succ s) p) := by
  have sD := natEq (sum_succ' (Γ := Γ) (devB X) N (pairT s p))
  have sD' := natEq (sum_succ' (Γ := Γ) (devB X) N (pairT (succ s) p))
  have sB := natEq (sum_succ' (Γ := Γ) (belowB X) N (pairT (succ s) p))
  have sE := natEq (sum_succ' (Γ := Γ) (equalB X) N (pairT (succ s) p))
  have sA := natEq (sum_succ' (Γ := Γ) (aboveB X) N (pairT (succ s) p))
  have dv := natEq (dev_pt (Γ := Γ) X N s p); have dv' := natEq (dev_pt (Γ := Γ) X N (succ s) p)
  have bp := natEq (below_pt (Γ := Γ) X N (succ s) p); have ep := natEq (equal_pt (Γ := Γ) X N (succ s) p)
  have ap := natEq (above_pt (Γ := Γ) X N (succ s) p)
  have ih' := natEq ih; have pw := natEq (pl (Γ := Γ) (inst2 X N p) s)
  apply deriveNat; ipra_simps
  linear_combination sD + sB - sD' - sE - sA + ih' + dv + bp - dv' - ep - ap + pw

/-- Variables: `0 = N`, `1 = s`, `2 = p`. -/
private abbrev lzF : Fm PTm 3 :=
  ap2 (sumF (devB X)) (var 0) (pairT (var 1) (var 2)) + ap2 (sumF (belowB X)) (var 0) (pairT (succ (var 1)) (var 2)) ≐
    ap2 (sumF (devB X)) (var 0) (pairT (succ (var 1)) (var 2)) +
      (ap2 (sumF (equalB X)) (var 0) (pairT (succ (var 1)) (var 2)) +
        ap2 (sumF (aboveB X)) (var 0) (pairT (succ (var 1)) (var 2)))

private theorem lz₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] lzF X := by
  ipra_ind [subst_ap2, subst_pairT]
  · exact lz_base X _ _
  · exact lz_step X Prf.hyp0

/-- `D(s) + B(s + 1) = D(s + 1) + E(s + 1) + A(s + 1)`. -/
theorem dev_pred (N s p : PTm n) :
    Γ ⊢[PRAAx] Dv X N s p + Bc X N (succ s) p ≐ Dv X N (succ s) p + (Ec X N (succ s) p + Ac X N (succ s) p) := by
  have h := inst (Γ := Γ) (lz₀ X) (![N, s, p] : Fin 3 → PTm n)
  simpa using h

/-- `B(0) = 0`. -/
theorem below_zero (N p : PTm n) : Γ ⊢[PRAAx] Bc X N zero p ≐ zero := by
  refine sum_zero_of_all (belowB X) (pairT zero p) ?_ N
  have e : Syn.shift (pairT (zero : PTm n) p) = pairT zero (Syn.shift p) := by simp [Syn.shift]
  rw [e]
  exact .allI ((below_pt X _ _ _).eqTrans ((congrSg (zero_monus _)).eqTrans sg_zero))

theorem min_above {N t p : PTm n} (hup : Γ ⊢[PRAAx] le (Dv X N t p) (Dv X N (succ t) p)) :
    Γ ⊢[PRAAx] le (two * Ac X N t p) N := by
  refine le_of_eq_add (d := monus (Dv X N (succ t) p) (Dv X N t p)) ?_
  ipra_lc -natEq (partition (Γ := Γ) X N t p) - natEq (dev_succ (Γ := Γ) X N t p) + natEq (eq_add_of_le hup)

theorem min_below_succ {N t p : PTm n} (ht : Γ ⊢[PRAAx] t ≐ succ (pred t))
    (hdn : Γ ⊢[PRAAx] le (Dv X N t p) (Dv X N (pred t) p)) : Γ ⊢[PRAAx] le (two * Bc X N t p) N := by
  refine le_of_eq_add (d := monus (Dv X N (pred t) p) (Dv X N t p)) ?_
  ipra_lc -natEq (partition (Γ := Γ) X N t p) - natEq (dev_pred (Γ := Γ) X N (pred t) p) + natEq (eq_add_of_le hdn) -
    natEq (congrDv (Γ := Γ) X N p ht.eqSymm) + natEq (congrCount (Γ := Γ) (belowB X) N p ht.eqSymm) -
    natEq (congrCount (Γ := Γ) (equalB X) N p ht.eqSymm) - natEq (congrCount (Γ := Γ) (aboveB X) N p ht.eqSymm)

theorem min_below_zero {N t p : PTm n} (ht : Γ ⊢[PRAAx] t ≐ zero) : Γ ⊢[PRAAx] le (two * Bc X N t p) N := by
  refine le_of_eq_add (d := N) ?_
  ipra_lc -2 * natEq ((congrCount (Γ := Γ) (belowB X) N p ht).eqTrans (below_zero X N p))

/-- `thm:l1`, minimizers are medians: if `D(t) ≤ D(t + 1)` and `D(t) ≤ D(t ∸ 1)`, in particular if
`D(t) ≤ D(a)` for every `a`, then `t` is a balance median. -/
theorem min_median {N t p : PTm n} (hup : Γ ⊢[PRAAx] le (Dv X N t p) (Dv X N (succ t) p))
    (hdn : Γ ⊢[PRAAx] le (Dv X N t p) (Dv X N (pred t) p)) : Γ ⊢[PRAAx] isMed X N t p :=
  .andI (.orE (zero_or_succ t) (min_below_zero X Prf.hyp0) (min_below_succ X Prf.hyp0 hdn.wk))
    (min_above X hup)

end Steps

end LeanProofs.IPRA.Probability.MedianL1
