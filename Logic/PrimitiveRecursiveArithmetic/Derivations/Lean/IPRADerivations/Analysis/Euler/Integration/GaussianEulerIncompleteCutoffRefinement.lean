import IPRADerivations.Analysis.Euler.Integration.GaussianEulerIncompleteCutoff

/-!
# Refining the two incomplete Euler cutoff intervals

When the cutoff moves later, both old incomplete intervals rescale by
the original dyadic refinement factor. The additional pieces are exactly
the lower and upper tails of the whole Euler interval, represented on
the later denominator. The rational split point stays fixed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIncompleteCutoffRefinement

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerIncompleteCutoff (clock denominator splitPoint lowerWidth upperWidth source)
open GaussianGammaIntegralCutoffs (etaDen top)
open GaussianGammaCompactCutoffGeometry (ratio delta)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def lowerTail (k j A b : PTm n) : PTm n := b*GaussianGammaCompactCutoffGeometry.lowerWidth k j A
def upperTail (k j A R b : PTm n) : PTm n := b*GaussianGammaCompactCutoffGeometry.upperWidth k j A R

theorem denominator_refinement (k j A R b : PTm n) (hj : Γ ⊢[PRAAx] le k j) : Γ ⊢[PRAAx]
    denominator j A R b ≐ ratio k j A*denominator k A R b :=
  (congrMul (.eqRefl b) (GaussianGammaCompactCutoffGeometry.eta_den_refinement k j A R hj)).eqTrans
    (by unfold denominator; ipra_ring)

theorem point_refinement (k j A R a : PTm n) (hj : Γ ⊢[PRAAx] le k j) : Γ ⊢[PRAAx]
    splitPoint j A R a ≐ ratio k j A*splitPoint k A R a :=
  (congrMul (.eqRefl a) (GaussianGammaCompactCutoffGeometry.eta_den_refinement k j A R hj)).eqTrans
    (by unfold splitPoint; ipra_ring)

theorem tail_left_end (k j A b : PTm n) : Γ ⊢[PRAAx] b+lowerTail k j A b ≐ ratio k j A*b :=
  (by unfold lowerTail; ipra_ring : Γ ⊢[PRAAx] b+lowerTail k j A b ≐
      b*(one+GaussianGammaCompactCutoffGeometry.lowerWidth k j A)).eqTrans
    ((congrMul (.eqRefl b) (GaussianGammaCompactCutoffGeometry.lower_endpoint k j A)).eqTrans (mul_comm _ _))

theorem tail_right_end (k j A R b : PTm n) (hj : Γ ⊢[PRAAx] le k j) : Γ ⊢[PRAAx]
    denominator j A R b*top k A R+upperTail k j A R b ≐ denominator j A R b*top j A R :=
  (by unfold denominator upperTail GaussianGammaCompactCutoffGeometry.upperWidth; ipra_ring :
    Γ ⊢[PRAAx] denominator j A R b*top k A R+upperTail k j A R b ≐
      denominator j A R b*(top k A R+two*delta k j)).eqTrans
    (congrMul (.eqRefl _) (GaussianGammaCompactCutoffGeometry.top_refinement k j A R hj).eqSymm)

theorem scaled_early_lower (t k j z R B A a b : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A a b) (hk : Γ ⊢[PRAAx] le (clock t a b) k) (hj : Γ ⊢[PRAAx] le k j) :
    Γ ⊢[PRAAx] ratio k j A*b+ratio k j A*lowerWidth k A R a b ≐ splitPoint j A R a :=
  (by ipra_ring : Γ ⊢[PRAAx] ratio k j A*b+ratio k j A*lowerWidth k A R a b ≐
    ratio k j A*(b+lowerWidth k A R a b)).eqTrans
    ((congrMul (.eqRefl _) (GaussianEulerIncompleteCutoff.original_partition t k z R B A a b h hk).andE₁).eqTrans
      (point_refinement k j A R a hj).eqSymm)

theorem early_upper_endpoint (t k R A a b : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) (hA : Γ ⊢[PRAAx] le one A)
    (hk : Γ ⊢[PRAAx] le (clock t a b) k) :
    Γ ⊢[PRAAx] splitPoint k A R a+upperWidth k A R a b ≐ denominator k A R b*top k A R :=
  (eq_add_of_le (le_of_lt (GaussianEulerIncompleteCutoff.split_strict_interior t k A R a b ha hb hA hk).andE₂)).eqSymm

theorem scaled_early_upper (t k j R A a b : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) (hA : Γ ⊢[PRAAx] le one A)
    (hk : Γ ⊢[PRAAx] le (clock t a b) k) (hj : Γ ⊢[PRAAx] le k j) :
    Γ ⊢[PRAAx] splitPoint j A R a+ratio k j A*upperWidth k A R a b ≐ denominator j A R b*top k A R := by
  let q := ratio k j A
  let U := upperWidth k A R a b
  exact (congrAdd (point_refinement k j A R a hj) (.eqRefl _)).eqTrans
    ((by ipra_ring : Γ ⊢[PRAAx] q*splitPoint k A R a+q*U ≐ q*(splitPoint k A R a+U)).eqTrans
      ((congrMul (.eqRefl _) (early_upper_endpoint t k R A a b ha hb hA hk)).eqTrans
        ((by ipra_ring : Γ ⊢[PRAAx] q*(denominator k A R b*top k A R) ≐ (q*denominator k A R b)*top k A R).eqTrans
          (congrMul (denominator_refinement k j A R b hj).eqSymm (.eqRefl _)))))

theorem refined_widths (t k j z R B A a b : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A a b) (hk : Γ ⊢[PRAAx] le (clock t a b) k) (hj : Γ ⊢[PRAAx] le k j) :
    Γ ⊢[PRAAx] (lowerWidth j A R a b ≐ lowerTail k j A b+ratio k j A*lowerWidth k A R a b) ⋏
      (upperWidth j A R a b ≐ ratio k j A*upperWidth k A R a b+upperTail k j A R b) := by
  let l := lowerTail k j A b
  let u := upperTail k j A R b
  let q := ratio k j A
  let L := q*lowerWidth k A R a b
  let U := q*upperWidth k A R a b
  let x := splitPoint j A R a
  have ha := h.andE₂.andE₂.andE₁
  have hb := h.andE₂.andE₂.andE₂
  have hA := h.andE₂.andE₁
  have hj' := le_trans hk hj
  have left : Γ ⊢[PRAAx] b+(l+L) ≐ x :=
    (by ipra_ring : Γ ⊢[PRAAx] b+(l+L) ≐ (b+l)+L).eqTrans
      ((congrAdd (tail_left_end k j A b) (.eqRefl L)).eqTrans (scaled_early_lower t k j z R B A a b h hk hj))
  have right : Γ ⊢[PRAAx] x+(U+u) ≐ denominator j A R b*top j A R :=
    (by ipra_ring : Γ ⊢[PRAAx] x+(U+u) ≐ (x+U)+u).eqTrans
      ((congrAdd (scaled_early_upper t k j R A a b ha hb hA hk hj) (.eqRefl u)).eqTrans (tail_right_end k j A R b hj))
  have oldLeft := (GaussianEulerIncompleteCutoff.original_partition t j z R B A a b h hj').andE₁
  have oldRight := early_upper_endpoint t j R A a b ha hb hA hj'
  exact .andI (add_left_cancel (oldLeft.eqTrans left.eqSymm))
    (add_left_cancel (oldRight.eqTrans right.eqSymm))

theorem actual_original_incomplete_cutoff_refinement_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
      ((source (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⋏
        (le (clock (var 0) (var 7) (var 8)) (var 1) ⋏ le (var 1) (var 2))) ⟶
        ((lowerWidth (var 2) (var 6) (var 4) (var 7) (var 8) ≐ lowerTail (var 1) (var 2) (var 6) (var 8)+
          ratio (var 1) (var 2) (var 6)*lowerWidth (var 1) (var 6) (var 4) (var 7) (var 8)) ⋏
         (upperWidth (var 2) (var 6) (var 4) (var 7) (var 8) ≐
          ratio (var 1) (var 2) (var 6)*upperWidth (var 1) (var 6) (var 4) (var 7) (var 8)+
          upperTail (var 1) (var 2) (var 6) (var 4) (var 8)))) :=
  closeUniv 9 (.impI (refined_widths _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerIncompleteCutoffRefinement
