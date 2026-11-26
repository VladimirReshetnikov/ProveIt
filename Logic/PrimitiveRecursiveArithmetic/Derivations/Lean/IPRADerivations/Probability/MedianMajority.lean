import IPRADerivations.Probability.Ninther
import IPRADerivations.Probability.MedianSymmetry

/-!
# The majority interval theorem

Packet: `probability/median_ipra_constructive_proofs`, Theorem `thm:majority-filter`. For a sample
`x(i, p)` of length `N` and an interval `[a, b]`, let

  `K = #{i < N : a ≤ x_i ≤ b}`.

* `in_above`, `in_below`: if `t < a` then every inlier is above `t`, so `K ≤ A(t)`; if `b < t`
  then `K ≤ B(t)`;
* `majority_interval` (`thm:majority-filter`): if `2K > N`, every balance median `t` satisfies
  `a ≤ t ≤ b`;
* `majority_value`: in particular, if more than half the entries equal `c`, every balance median
  equals `c` (the median filter removes minority corruption of a constant window).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.MedianMajority

open_ipra
open LeanProofs.IPRA.Algebra.CubeRootTwo (sg)
open LeanProofs.IPRA.AnalyticNumberTheory.Totatives (sg_lt sg_le)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Probability.MedianCounts
open LeanProofs.IPRA.Probability.MedianSymmetry (shift_pairT')
open LeanProofs.IPRA.Probability.Ninther (leb leb_one leb_zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem shift_lt' {a b : PTm n} (h : Γ ⊢[PRAAx] lt a b) : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift a) (Syn.shift b) :=
  LeanProofs.IPRA.Order.shift_lt h

/-! ## Pointwise -/

theorem prod_zero_l {u v : PTm n} (h : Γ ⊢[PRAAx] u ≐ zero) : Γ ⊢[PRAAx] u * v ≐ zero :=
  (congrMul h (.eqRefl _)).eqTrans ((mul_comm _ _).eqTrans (mul_zero _))

theorem prod_zero_r {u v : PTm n} (h : Γ ⊢[PRAAx] v ≐ zero) : Γ ⊢[PRAAx] u * v ≐ zero :=
  (congrMul (.eqRefl _) h).eqTrans (mul_zero _)

theorem prod_one {u v : PTm n} (hu : Γ ⊢[PRAAx] u ≐ one) (hv : Γ ⊢[PRAAx] v ≐ one) : Γ ⊢[PRAAx] u * v ≐ one :=
  (congrMul hu hv).eqTrans (by ipra_ring)

theorem in_above_inner {x a b t : PTm n} (h : Γ ⊢[PRAAx] lt t a) (hax : Γ ⊢[PRAAx] le a x) :
    Γ ⊢[PRAAx] le (leb a x * leb x b) (sg (monus x t)) := by
  refine .orE (lt_or_le b x) (le_congr (prod_zero_r (leb_zero Prf.hyp0)).eqSymm (.eqRefl _) (zero_le _)) ?_
  exact le_congr (prod_one (leb_one hax.wk) (leb_one Prf.hyp0)).eqSymm
    (sg_lt (lt_of_lt_of_le h.wk hax.wk)).eqSymm (le_refl _)

/-- If `t < a`, then `[a ≤ x ≤ b] ≤ [t < x]`. -/
theorem in_above_val {x a b t : PTm n} (h : Γ ⊢[PRAAx] lt t a) :
    Γ ⊢[PRAAx] le (leb a x * leb x b) (sg (monus x t)) :=
  .orE (lt_or_le x a) (le_congr (prod_zero_l (leb_zero Prf.hyp0)).eqSymm (.eqRefl _) (zero_le _))
    (in_above_inner h.wk Prf.hyp0)

theorem in_below_inner {x a b t : PTm n} (h : Γ ⊢[PRAAx] lt b t) (hxb : Γ ⊢[PRAAx] le x b) :
    Γ ⊢[PRAAx] le (leb a x * leb x b) (sg (monus t x)) := by
  refine .orE (lt_or_le x a) (le_congr (prod_zero_l (leb_zero Prf.hyp0)).eqSymm (.eqRefl _) (zero_le _)) ?_
  exact le_congr (prod_one (leb_one Prf.hyp0) (leb_one hxb.wk)).eqSymm
    (sg_lt (lt_of_le_of_lt hxb.wk h.wk)).eqSymm (le_refl _)

/-- If `b < t`, then `[a ≤ x ≤ b] ≤ [x < t]`. -/
theorem in_below_val {x a b t : PTm n} (h : Γ ⊢[PRAAx] lt b t) :
    Γ ⊢[PRAAx] le (leb a x * leb x b) (sg (monus t x)) :=
  .orE (lt_or_le b x) (le_congr (prod_zero_r (leb_zero Prf.hyp0)).eqSymm (.eqRefl _) (zero_le _))
    (in_below_inner h.wk Prf.hyp0)

/-! ## Counts -/

section Sample

variable (X : PTm 2)

/-- `[a ≤ x_i ≤ b]`, over `0 = i`, `1 = ⟨a, ⟨b, p⟩⟩`. -/
def inB : PTm 2 :=
  leb (fstT (var 1)) (Syn.subst ![var 0, sndT (sndT (var 1))] X) *
    leb (Syn.subst ![var 0, sndT (sndT (var 1))] X) (fstT (sndT (var 1)))

theorem inst2_in (i y : PTm n) :
    inst2 (inB X) i y = leb (fstT y) (inst2 X i (sndT (sndT y))) * leb (inst2 X i (sndT (sndT y))) (fstT (sndT y)) := by
  have e : ∀ f : PTm 2, Syn.subst ![i, y] (Syn.subst ![var 0, sndT (sndT (var 1))] f) =
      Syn.subst ![i, sndT (sndT y)] f := fun f => by
    rw [Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  simp only [inst2, inB, PTm.subst_mul, PTm.subst_monus, subst_fstT, subst_sndT, e]
  simp

theorem in_pt (i a b p : PTm n) :
    Γ ⊢[PRAAx] inst2 (inB X) i (pairT a (pairT b p)) ≐ leb a (inst2 X i p) * leb (inst2 X i p) b := by
  rw [inst2_in]
  have hA : Γ ⊢[PRAAx] fstT (pairT a (pairT b p)) ≐ a := fst_pair _ _
  have hB : Γ ⊢[PRAAx] fstT (sndT (pairT a (pairT b p))) ≐ b := (snd_pair _ _).fstE
  have hx : Γ ⊢[PRAAx] sndT (sndT (pairT a (pairT b p))) ≐ p := (snd_pair _ _).sndE
  have ht := congrInst2 X (.eqRefl i) hx
  exact congrMul (congrMonus (.eqRefl _) (congrSg (congrMonus hA ht)))
    (congrMonus (.eqRefl _) (congrSg (congrMonus ht hB)))

/-- `K = #{i < N : a ≤ x_i ≤ b}`. -/
abbrev Kin (N a b p : PTm n) : PTm n := ap2 (sumF (inB X)) N (pairT a (pairT b p))

theorem shift_triple (a b p : PTm n) :
    Syn.shift (pairT a (pairT b p)) = pairT (Syn.shift a) (pairT (Syn.shift b) (Syn.shift p)) := by
  simp [Syn.shift]

/-- If `t < a`, then `K ≤ A(t)`. -/
theorem in_above {N a b t p : PTm n} (h : Γ ⊢[PRAAx] lt t a) : Γ ⊢[PRAAx] le (Kin X N a b p) (Ac X N t p) := by
  refine sum_le_params (inB X) (aboveB X) _ _ N (.allI (.impI ?_))
  rw [shift_triple, shift_pairT']
  exact le_congr (in_pt X _ _ _ _).eqSymm (above_pt X _ _ _).eqSymm (in_above_val (shift_lt' h).wk)

/-- If `b < t`, then `K ≤ B(t)`. -/
theorem in_below {N a b t p : PTm n} (h : Γ ⊢[PRAAx] lt b t) : Γ ⊢[PRAAx] le (Kin X N a b p) (Bc X N t p) := by
  refine sum_le_params (inB X) (belowB X) _ _ N (.allI (.impI ?_))
  rw [shift_triple, shift_pairT']
  exact le_congr (in_pt X _ _ _ _).eqSymm (below_pt X _ _ _).eqSymm (in_below_val (shift_lt' h).wk)

/-- `thm:majority-filter`: if more than half the entries lie in `[a, b]`, every balance median lies
in `[a, b]`. -/
theorem majority_interval {N a b t p : PTm n} (hK : Γ ⊢[PRAAx] lt N (two * Kin X N a b p))
    (hm : Γ ⊢[PRAAx] isMed X N t p) : Γ ⊢[PRAAx] le a t ⋏ le t b := by
  refine .andI (.orE (lt_or_le t a) ?_ Prf.hyp0) (.orE (lt_or_le b t) ?_ Prf.hyp0)
  · exact lt_irrefl N _ (lt_of_lt_of_le hK.wk
      (le_trans (le_mul_mono (le_refl two) (in_above X Prf.hyp0)) (Prf.andE₂ hm).wk))
  · exact lt_irrefl N _ (lt_of_lt_of_le hK.wk
      (le_trans (le_mul_mono (le_refl two) (in_below X Prf.hyp0)) (Prf.andE₁ hm).wk))

/-- If more than half the entries equal `c`, every balance median equals `c`. -/
theorem majority_value {N c t p : PTm n} (hK : Γ ⊢[PRAAx] lt N (two * Kin X N c c p))
    (hm : Γ ⊢[PRAAx] isMed X N t p) : Γ ⊢[PRAAx] t ≐ c := by
  have h := majority_interval X hK hm
  exact le_antisymm (Prf.andE₂ h) (Prf.andE₁ h)

end Sample

end LeanProofs.IPRA.Probability.MedianMajority
