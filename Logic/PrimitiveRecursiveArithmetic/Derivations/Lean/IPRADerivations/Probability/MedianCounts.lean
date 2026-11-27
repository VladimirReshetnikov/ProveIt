import IPRADerivations.Core.SumOrder
import IPRADerivations.Probability.Variance
import IPRADerivations.AnalyticNumberTheory.EulerDomination

/-!
# Balance medians by counting

Packet: `probability/median_ipra_constructive_proofs` (the balance definition `eq:balance`, the
order-only part of `thm:middle-interval`, and the counting facts behind it). The data is a body
`x(i, p)` with `n` entries. For a threshold `t`,

  `B(t) = #{i < n : x_i < t}`,   `E(t) = #{i < n : x_i = t}`,   `A(t) = #{i < n : t < x_i}`,

are sums of bits, and `t` is a balance median when `2 B(t) ≤ n` and `2 A(t) ≤ n`.

* `trichotomy_bits`: `[x < t] + [x = t] + [t < x] = 1`;
* `partition`: `B(t) + E(t) + A(t) = n`, and `counts_le`: `B(t) + A(t) ≤ n`;
* `below_mono`, `above_anti`: for `t ≤ t′`, `B(t) ≤ B(t′)` and `A(t′) ≤ A(t)`;
* `med_interval`: if `t₁ ≤ t ≤ t₂` and `t₁`, `t₂` are balance medians, so is `t`: the set of
  medians is an interval, which is the order-only half of `thm:middle-interval`.

The identification of the interval with `[y_ℓ, y_u]` for sorted data, and the odd and even
formulas, are in `Probability/MedianSorted`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.MedianCounts

open_ipra
open LeanProofs.IPRA.Algebra.CubeRootTwo (sg sg_zero sg_succ)
open LeanProofs.IPRA.AnalyticNumberTheory.Totatives (sg_lt sg_le)
open LeanProofs.IPRA.AnalyticNumberTheory.EulerDomination (sg_le_one)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Probability.Expectation (le_zero_of)
open LeanProofs.IPRA.Probability.Variance (ad sum_one)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## The three bits -/

/-- `[x < t] + [x = t] + [t < x] = 1`. -/
theorem trichotomy_bits (x t : PTm n) :
    Γ ⊢[PRAAx] sg (monus t x) + eqb x t + sg (monus x t) ≐ one := by
  refine .orE (lt_or_le x t) ?_ (.orE (lt_or_eq_of_le Prf.hyp0) ?_ ?_)
  · exact (congrAdd (congrAdd (sg_lt Prf.hyp0) (eqb_zero_of_lt Prf.hyp0)) (sg_le (le_of_lt Prf.hyp0))).eqTrans
      (by ipra_ring)
  · exact (congrAdd (congrAdd (sg_le (le_of_lt Prf.hyp0)) (eqb_zero_of_gt Prf.hyp0)) (sg_lt Prf.hyp0)).eqTrans
      (by ipra_ring)
  · exact (congrAdd (congrAdd (sg_le (le_congr (.eqRefl _) Prf.hyp0 (le_refl t))) (eqb_of_eq Prf.hyp0.eqSymm))
      (sg_le (le_congr Prf.hyp0 (.eqRefl _) (le_refl t)))).eqTrans (by ipra_ring)

/-- `[x < t] ≤ [x < t′]` for `t ≤ t′`. -/
theorem below_bit_mono {x t t' : PTm n} (h : Γ ⊢[PRAAx] le t t') :
    Γ ⊢[PRAAx] le (sg (monus t x)) (sg (monus t' x)) := by
  refine .orE (lt_or_le x t) ?_ (le_zero_of (sg_le Prf.hyp0))
  exact le_congr (.eqRefl _) (sg_lt (lt_of_lt_of_le Prf.hyp0 h.wk)).eqSymm (sg_le_one _)

/-- `[t′ < x] ≤ [t < x]` for `t ≤ t′`. -/
theorem above_bit_anti {x t t' : PTm n} (h : Γ ⊢[PRAAx] le t t') :
    Γ ⊢[PRAAx] le (sg (monus x t')) (sg (monus x t)) := by
  refine .orE (lt_or_le t' x) ?_ (le_zero_of (sg_le Prf.hyp0))
  exact le_congr (.eqRefl _) (sg_lt (lt_of_le_of_lt h.wk Prf.hyp0)).eqSymm (sg_le_one _)

/-! ## The counts -/

section Counts

variable (X : PTm 2)

/-- `[x(i, snd z) < fst z]`. -/
def belowB : PTm 2 := sg (monus (fstT (var 1)) (Syn.subst ![var 0, sndT (var 1)] X))
/-- `[x(i, snd z) = fst z]`. -/
def equalB : PTm 2 := eqb (Syn.subst ![var 0, sndT (var 1)] X) (fstT (var 1))
/-- `[fst z < x(i, snd z)]`. -/
def aboveB : PTm 2 := sg (monus (Syn.subst ![var 0, sndT (var 1)] X) (fstT (var 1)))

theorem subst_data (i z : PTm n) (f : PTm 2) :
    Syn.subst ![i, z] (Syn.subst ![var 0, sndT (var 1)] f) = inst2 f i (sndT z) := by
  unfold inst2
  rw [Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp

theorem inst2_below (i z : PTm n) : inst2 (belowB X) i z = sg (monus (fstT z) (inst2 X i (sndT z))) := by
  simp only [inst2, belowB, PTm.subst_monus, subst_fstT, subst_data, ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero, Syn.subst_var]
  simp

theorem inst2_equal (i z : PTm n) : inst2 (equalB X) i z = eqb (inst2 X i (sndT z)) (fstT z) := by
  simp only [inst2, equalB, subst_eqb, subst_fstT, subst_data, Syn.subst_var]
  simp

theorem inst2_above (i z : PTm n) : inst2 (aboveB X) i z = sg (monus (inst2 X i (sndT z)) (fstT z)) := by
  simp only [inst2, aboveB, PTm.subst_monus, subst_fstT, subst_data, ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero, Syn.subst_var]
  simp

alias congrSg := Common.congrSg

theorem below_pt (i t p : PTm n) :
    Γ ⊢[PRAAx] inst2 (belowB X) i (pairT t p) ≐ sg (monus t (inst2 X i p)) := by
  rw [inst2_below]
  exact congrSg (congrMonus (fst_pair _ _) (congrInst2 X (.eqRefl _) (snd_pair _ _)))

theorem above_pt (i t p : PTm n) :
    Γ ⊢[PRAAx] inst2 (aboveB X) i (pairT t p) ≐ sg (monus (inst2 X i p) t) := by
  rw [inst2_above]
  exact congrSg (congrMonus (congrInst2 X (.eqRefl _) (snd_pair _ _)) (fst_pair _ _))

theorem equal_pt (i t p : PTm n) :
    Γ ⊢[PRAAx] inst2 (equalB X) i (pairT t p) ≐ eqb (inst2 X i p) t := by
  rw [inst2_equal]
  unfold eqb
  exact congrMonus (.eqRefl _) (congrAdd
    (congrMonus (congrInst2 X (.eqRefl _) (snd_pair _ _)) (fst_pair _ _))
    (congrMonus (fst_pair _ _) (congrInst2 X (.eqRefl _) (snd_pair _ _))))

/-- `B(t) = #{i < N : x_i < t}`. -/
abbrev Bc (N t p : PTm n) : PTm n := ap2 (sumF (belowB X)) N (pairT t p)
/-- `E(t) = #{i < N : x_i = t}`. -/
abbrev Ec (N t p : PTm n) : PTm n := ap2 (sumF (equalB X)) N (pairT t p)
/-- `A(t) = #{i < N : t < x_i}`. -/
abbrev Ac (N t p : PTm n) : PTm n := ap2 (sumF (aboveB X)) N (pairT t p)

theorem tri_pt (i t p : PTm n) :
    Γ ⊢[PRAAx] inst2 (belowB X) i (pairT t p) + inst2 (equalB X) i (pairT t p) +
      inst2 (aboveB X) i (pairT t p) ≐ one :=
  (congrAdd (congrAdd (below_pt X i t p) (equal_pt X i t p)) (above_pt X i t p)).eqTrans
    (trichotomy_bits (inst2 X i p) t)

/-- `B(t) + E(t) + A(t) = N`. -/
theorem partition (N t p : PTm n) : Γ ⊢[PRAAx] Bc X N t p + Ec X N t p + Ac X N t p ≐ N := by
  have e : Γ ⊢[PRAAx] ap2 (sumF (addBody (addBody (belowB X) (equalB X)) (aboveB X))) N (pairT t p) ≐
      ap2 (sumF (one : PTm 2)) N (pairT t p) := by
    refine sum_congr_bounded _ (one : PTm 2) (pairT t p) (pairT t p) N (.allI (.impI ?_))
    have e₁ : inst2 (one : PTm 2) (var 0 : PTm (n + 1)) (Syn.shift (pairT t p)) = one := by simp [inst2]
    rw [e₁, inst2_addBody, inst2_addBody]
    simp only [Syn.shift, subst_pairT]
    exact tri_pt X _ _ _
  exact (congrAdd (sum_add (belowB X) (equalB X) N (pairT t p)) (.eqRefl _)).eqSymm.eqTrans
    ((sum_add (addBody (belowB X) (equalB X)) (aboveB X) N (pairT t p)).eqSymm.eqTrans
      (e.eqTrans (sum_one N _)))

/-- `B(t) + A(t) ≤ N`. -/
theorem counts_le (N t p : PTm n) : Γ ⊢[PRAAx] le (Bc X N t p + Ac X N t p) N := by
  refine le_of_eq_add (d := Ec X N t p) ?_
  ipra_lc -natEq (partition (Γ := Γ) X N t p)

/-- `B(t) ≤ B(t′)` for `t ≤ t′`. -/
theorem below_mono {t t' : PTm n} (h : Γ ⊢[PRAAx] le t t') (N p : PTm n) :
    Γ ⊢[PRAAx] le (Bc X N t p) (Bc X N t' p) := by
  refine sum_le_params (belowB X) (belowB X) (pairT t p) (pairT t' p) N (.allI (.impI ?_))
  have h' : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift t) (Syn.shift t') := by
    simpa [Fm.shift, Syn.shift] using h.shift
  simp only [Syn.shift, subst_pairT] at h' ⊢
  exact le_congr (below_pt X _ _ _).eqSymm (below_pt X _ _ _).eqSymm (below_bit_mono h'.wk)

/-- `A(t′) ≤ A(t)` for `t ≤ t′`. -/
theorem above_anti {t t' : PTm n} (h : Γ ⊢[PRAAx] le t t') (N p : PTm n) :
    Γ ⊢[PRAAx] le (Ac X N t' p) (Ac X N t p) := by
  refine sum_le_params (aboveB X) (aboveB X) (pairT t' p) (pairT t p) N (.allI (.impI ?_))
  have h' : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift t) (Syn.shift t') := by
    simpa [Fm.shift, Syn.shift] using h.shift
  simp only [Syn.shift, subst_pairT] at h' ⊢
  exact le_congr (above_pt X _ _ _).eqSymm (above_pt X _ _ _).eqSymm (above_bit_anti h'.wk)

/-! ## Balance medians -/

/-- `t` is a balance median: `2 B(t) ≤ N` and `2 A(t) ≤ N`. -/
abbrev isMed (N t p : PTm n) : Fm PTm n := le (two * Bc X N t p) N ⋏ le (two * Ac X N t p) N

/-- The balance medians form an interval. -/
theorem med_interval {N t₁ t t₂ p : PTm n} (h₁ : Γ ⊢[PRAAx] le t₁ t) (h₂ : Γ ⊢[PRAAx] le t t₂)
    (m₁ : Γ ⊢[PRAAx] isMed X N t₁ p) (m₂ : Γ ⊢[PRAAx] isMed X N t₂ p) : Γ ⊢[PRAAx] isMed X N t p :=
  .andI (le_trans (le_mul_mono (le_refl two) (below_mono X h₂ N p)) (Prf.andE₁ m₂))
    (le_trans (le_mul_mono (le_refl two) (above_anti X h₁ N p)) (Prf.andE₂ m₁))

end Counts

/-! ## Pointwise absolute deviations -/

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem deviation_up_below {X M : PTm n} (d : PTm n) {β ε α : PTm n} (h : Γ ⊢[PRAAx] le X M)
    (hs : Γ ⊢[PRAAx] β + ε ≐ one) (ha : Γ ⊢[PRAAx] α ≐ zero) :
    Γ ⊢[PRAAx] le (ad X M + d * (β + ε)) (ad X (M + d) + d * α) := by
  have hle := le_trans h (le_add_right M d)
  refine le_of_eq_add (d := zero) ?_
  ipra_lc natEq hle - natEq (eq_add_of_le hle) + natEq (eq_add_of_le h) - natEq h +
    𝔞 d * (natEq ha - natEq hs)

theorem deviation_up_above₁ {X M : PTm n} (d : PTm n) {β ε α : PTm n} (h : Γ ⊢[PRAAx] le M X)
    (hb : Γ ⊢[PRAAx] β ≐ zero) (he : Γ ⊢[PRAAx] ε ≐ zero) (ha : Γ ⊢[PRAAx] α ≐ one)
    (hle : Γ ⊢[PRAAx] le X (M + d)) :
    Γ ⊢[PRAAx] le (ad X M + d * (β + ε)) (ad X (M + d) + d * α) := by
  refine le_of_eq_add (d := monus (M + d) X + monus (M + d) X) ?_
  ipra_lc natEq hle + natEq (eq_add_of_le hle) + natEq (eq_add_of_le h) - natEq h +
    𝔞 d * (natEq ha - natEq hb - natEq he)

theorem deviation_up_above₂ {X M : PTm n} (d : PTm n) {β ε α : PTm n} (h : Γ ⊢[PRAAx] le M X)
    (hb : Γ ⊢[PRAAx] β ≐ zero) (he : Γ ⊢[PRAAx] ε ≐ zero) (ha : Γ ⊢[PRAAx] α ≐ one)
    (hge : Γ ⊢[PRAAx] le (M + d) X) :
    Γ ⊢[PRAAx] le (ad X M + d * (β + ε)) (ad X (M + d) + d * α) := by
  refine le_of_eq_add (d := zero) ?_
  ipra_lc -natEq (eq_add_of_le hge) + natEq (eq_add_of_le h) + natEq hge - natEq h +
    𝔞 d * (natEq ha - natEq hb - natEq he)

theorem deviation_down_above {X t : PTm n} (d : PTm n) {β ε α : PTm n} (h : Γ ⊢[PRAAx] le (t + d) X)
    (hs : Γ ⊢[PRAAx] α + ε ≐ one) (hb : Γ ⊢[PRAAx] β ≐ zero) :
    Γ ⊢[PRAAx] le (ad X (t + d) + d * (α + ε)) (ad X t + d * β) := by
  have hle := le_trans (le_add_right t d) h
  refine le_of_eq_add (d := zero) ?_
  ipra_lc -natEq (eq_add_of_le hle) + natEq (eq_add_of_le h) + natEq hle - natEq h +
    𝔞 d * (natEq hb - natEq hs)

theorem deviation_down_below₁ {X t : PTm n} (d : PTm n) {β ε α : PTm n} (h : Γ ⊢[PRAAx] le X (t + d))
    (ha : Γ ⊢[PRAAx] α ≐ zero) (he : Γ ⊢[PRAAx] ε ≐ zero) (hb : Γ ⊢[PRAAx] β ≐ one)
    (hle : Γ ⊢[PRAAx] le t X) :
    Γ ⊢[PRAAx] le (ad X (t + d) + d * (α + ε)) (ad X t + d * β) := by
  refine le_of_eq_add (d := monus X t + monus X t) ?_
  ipra_lc natEq (eq_add_of_le hle) + natEq (eq_add_of_le h) + natEq hle - natEq h +
    𝔞 d * (natEq hb - natEq ha - natEq he)

theorem deviation_down_below₂ {X t : PTm n} (d : PTm n) {β ε α : PTm n} (h : Γ ⊢[PRAAx] le X (t + d))
    (ha : Γ ⊢[PRAAx] α ≐ zero) (he : Γ ⊢[PRAAx] ε ≐ zero) (hb : Γ ⊢[PRAAx] β ≐ one)
    (hge : Γ ⊢[PRAAx] le X t) :
    Γ ⊢[PRAAx] le (ad X (t + d) + d * (α + ε)) (ad X t + d * β) := by
  refine le_of_eq_add (d := zero) ?_
  ipra_lc -natEq (eq_add_of_le hge) + natEq (eq_add_of_le h) + natEq hge - natEq h +
    𝔞 d * (natEq hb - natEq ha - natEq he)

end LeanProofs.IPRA.Probability.MedianCounts
