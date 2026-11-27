import IPRADerivations.Analysis.Euler.Integration.Incomplete.Cutoffs.GaussianEulerIncompleteCutoffRefinement

/-!
# Actual incomplete Euler cutoff names and their added tails

The two compact names on either side of a fixed rational time retain
their own original quadrature programs. At a later cutoff each name
splits into its earlier value and exactly the corresponding original
whole-integral tail, using checked interval rescaling and additivity.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIncompleteCutoffParts

open_ipra
open GaussianEulerIncompleteCutoff (clock denominator splitPoint lowerWidth upperWidth source)
open GaussianEulerIncompleteCutoffRefinement (lowerTail upperTail denominator_refinement point_refinement
  tail_left_end scaled_early_upper early_upper_endpoint refined_widths)
open GaussianGammaIntegralCutoffs (etaDen top top_positive)
open GaussianGammaCompactCutoffGeometry (ratio ratio_positive top_monotone)
open GaussianEulerCompactAdditivity (data nameF intervalSource name_additivity)
open GaussianGammaCompactCutoffSplit (euler_data_congr)
open GaussianGammaCompactCutoffAlignment (cross_data_congr)
open GaussianRationalHorner (positive_product)
open GaussianNameArithmetic (addF addData)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_symm cross_to_diagonal)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def lowerData (z R B k A a b : PTm n) : PTm n :=
  data z R B b (lowerWidth k A R a b) (denominator k A R b) (top k A R)
def upperData (z R B k A a b : PTm n) : PTm n :=
  data z R B (splitPoint k A R a) (upperWidth k A R a b) (denominator k A R b) (top k A R)
abbrev sumF : PR 2 := addF nameF nameF

theorem piece_sources (t k z R B A a b : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b)
    (hk : Γ ⊢[PRAAx] le (clock t a b) k) : Γ ⊢[PRAAx]
    intervalSource z R B b (lowerWidth k A R a b) (denominator k A R b) (top k A R) ⋏
      intervalSource z R B (splitPoint k A R a) (upperWidth k A R a b) (denominator k A R b) (top k A R) := by
  let x := splitPoint k A R a
  let D := denominator k A R b
  let T := top k A R
  let L := lowerWidth k A R a b
  let U := upperWidth k A R a b
  have hD := (GaussianEulerIncompleteCutoff.original_partition t k z R B A a b h hk).andE₂.andE₂.andE₁
  have ha := h.andE₂.andE₂.andE₁
  have hb := h.andE₂.andE₂.andE₂
  have hA := h.andE₂.andE₁
  have first : Γ ⊢[PRAAx] le (b+lowerWidth k A R a b) (D*T) :=
    le_trans (le_congr (.eqRefl _) (by ipra_ring : Γ ⊢[PRAAx] b+L+U ≐ b+(L+U))
      (le_add_right (b+L) U)) hD.andE₂.andE₂
  have hx : Γ ⊢[PRAAx] le one x :=
    positive_product _ _ ha (GaussianGammaIntegralCutoffs.eta_den_positive k A R)
  have last : Γ ⊢[PRAAx] le (x+upperWidth k A R a b) (D*T) :=
    le_congr (early_upper_endpoint t k R A a b ha hb hA hk).eqSymm (.eqRefl _) (le_refl _)
  exact .andI (.andI hD.andE₁ (.andI hb first)) (.andI hD.andE₁ (.andI hx last))

private theorem align (z R B a C E T S m : PTm n)
    (h : Γ ⊢[PRAAx] intervalSource z R B a C E T) (hm : Γ ⊢[PRAAx] le one m)
    (hTS : Γ ⊢[PRAAx] le T S) : Γ ⊢[PRAAx]
    crossEquivalent nameF nameF (data z R B a C E T) (data z R B (m*a) (m*C) (m*E) S) := by
  have endp := le_trans h.andE₂.andE₂
    (le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right E hTS))
  exact GaussianEulerCompactAlignment.aligned_names z R B a C E T S m
    (.andI h.andE₁ (.andI h.andE₂.andE₁ (.andI hm (.andI h.andE₂.andE₂ endp))))

private theorem add_cross (x y u v : PTm n) (h₁ : Γ ⊢[PRAAx] crossEquivalent nameF nameF x y)
    (h₂ : Γ ⊢[PRAAx] crossEquivalent nameF nameF u v) :
    Γ ⊢[PRAAx] crossEquivalent sumF sumF (addData x u) (addData y v) := by
  have h₁' := cross_symm _ _ _ _ h₁
  have h₂' := cross_symm _ _ _ _ h₂
  exact GaussianNameArithmetic.add_equivalent _ _ _ _ _ _ _ _
    (cross_trans _ _ _ _ _ _ h₁ h₁') (cross_trans _ _ _ _ _ _ h₁' h₁)
    (cross_trans _ _ _ _ _ _ h₂ h₂') (cross_trans _ _ _ _ _ _ h₂' h₂)
    (cross_to_diagonal _ _ _ _ h₁) (cross_to_diagonal _ _ _ _ h₂)

theorem original_lower_cutoff_change (t k j z R B A a b : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b)
    (hk : Γ ⊢[PRAAx] le (clock t a b) k) (hj : Γ ⊢[PRAAx] lt k j) : Γ ⊢[PRAAx]
    crossEquivalent nameF sumF (lowerData z R B j A a b)
      (addData (GaussianGammaCompactCutoffSplit.lowerData z R B k j A) (lowerData z R B k A a b)) := by
  let D := denominator j A R b
  let E := etaDen j A R
  let T := top j A R
  let m := ratio k j A
  let l := lowerTail k j A b
  let L := m*lowerWidth k A R a b
  let C := lowerWidth j A R a b
  let x := GaussianGammaCompactCutoffSplit.lowerData z R B k j A
  let y := lowerData z R B k A a b
  have hc := le_of_lt hj
  have hb := h.andE₂.andE₂.andE₂
  have old := (piece_sources t k z R B A a b h hk).andE₁
  have new := (piece_sources t j z R B A a b h (le_trans hk hc)).andE₁
  have hw := (refined_widths t k j z R B A a b h hk hc).andE₁
  have hl := positive_product _ _ hb (GaussianGammaCompactCutoffGeometry.lower_positive k j A h.andE₂.andE₁ hj)
  have hL := positive_product _ _ (ratio_positive k j A)
    (GaussianEulerIncompleteCutoff.original_partition t k z R B A a b h hk).andE₂.andE₂.andE₂.andE₁
  have all : Γ ⊢[PRAAx] GaussianEulerCompactAdditivity.source z R B b l L D T :=
    .andI (.andI new.andE₁ (.andI hb (le_congr (congrAdd (.eqRefl _) hw) (.eqRefl _) new.andE₂.andE₂))) (.andI hl hL)
  have add := name_additivity z R B b l L D T all
  have tailSource := GaussianGammaCompactCutoffSplit.lower_source z R B k j A (.andI h.andE₁ (.andI h.andE₂.andE₁ hc))
  have tail := align z R B one (GaussianGammaCompactCutoffGeometry.lowerWidth k j A) E T T b tailSource hb (le_refl _)
  have earlier := align z R B b (lowerWidth k A R a b) (denominator k A R b) (top k A R) T m
    old (ratio_positive k j A) (top_monotone k j A R hc)
  have eqWhole := euler_data_congr z R B b (l+L) D T b C D T (.eqRefl _) hw.eqSymm (.eqRefl _) (.eqRefl _)
  have eqTail := euler_data_congr (Γ := Γ) z R B (b*one) l D T b l D T (by ipra_ring) (.eqRefl _) (.eqRefl _) (.eqRefl _)
  have eqEarly := euler_data_congr z R B (m*b) L (m*denominator k A R b) T (b+l) L D T
    (tail_left_end k j A b).eqSymm (.eqRefl _) (denominator_refinement k j A R b hc).eqSymm (.eqRefl _)
  have tails := cross_data_congr nameF nameF x x (data z R B (b*one) l D T) (data z R B b l D T) (.eqRefl _) eqTail tail
  have early := cross_data_congr nameF nameF y y (data z R B (m*b) L (m*denominator k A R b) T)
    (data z R B (b+l) L D T) (.eqRefl _) eqEarly earlier
  have parts := add_cross _ _ _ _ (cross_symm _ _ _ _ tails) (cross_symm _ _ _ _ early)
  exact cross_trans _ _ _ _ _ _ (cross_data_congr _ _ _ _ _ _ eqWhole (.eqRefl _) add) parts

theorem original_upper_cutoff_change (t k j z R B A a b : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b)
    (hk : Γ ⊢[PRAAx] le (clock t a b) k) (hj : Γ ⊢[PRAAx] lt k j) : Γ ⊢[PRAAx]
    crossEquivalent nameF sumF (upperData z R B j A a b)
      (addData (upperData z R B k A a b) (GaussianGammaCompactCutoffSplit.upperData z R B k j A)) := by
  let D := denominator j A R b
  let E := etaDen j A R
  let T := top j A R
  let S := top k A R
  let m := ratio k j A
  let a₀ := splitPoint k A R a
  let a₁ := splitPoint j A R a
  let U := m*upperWidth k A R a b
  let u := upperTail k j A R b
  let C := upperWidth j A R a b
  let x := upperData z R B k A a b
  let y := GaussianGammaCompactCutoffSplit.upperData z R B k j A
  have hc := le_of_lt hj
  have hb := h.andE₂.andE₂.andE₂
  have ha := h.andE₂.andE₂.andE₁
  have hA := h.andE₂.andE₁
  have old := (piece_sources t k z R B A a b h hk).andE₂
  have new := (piece_sources t j z R B A a b h (le_trans hk hc)).andE₂
  have hw := (refined_widths t k j z R B A a b h hk hc).andE₂
  have hU := positive_product _ _ (ratio_positive k j A)
    (GaussianEulerIncompleteCutoff.original_partition t k z R B A a b h hk).andE₂.andE₂.andE₂.andE₂
  have hu := positive_product _ _ hb (GaussianGammaCompactCutoffGeometry.upper_positive k j A R hj)
  have all : Γ ⊢[PRAAx] GaussianEulerCompactAdditivity.source z R B a₁ U u D T :=
    .andI (.andI new.andE₁ (.andI new.andE₂.andE₁
      (le_congr (congrAdd (.eqRefl _) hw) (.eqRefl _) new.andE₂.andE₂))) (.andI hU hu)
  have add := name_additivity z R B a₁ U u D T all
  have tailSource := GaussianGammaCompactCutoffSplit.upper_source z R B k j A (.andI h.andE₁ (.andI hA hc))
  have tail := align z R B (E*S) (GaussianGammaCompactCutoffGeometry.upperWidth k j A R) E T T b tailSource hb (le_refl _)
  have earlier := align z R B a₀ (upperWidth k A R a b) (denominator k A R b) S T m
    old (ratio_positive k j A) (top_monotone k j A R hc)
  have eqWhole := euler_data_congr z R B a₁ (U+u) D T a₁ C D T (.eqRefl _) hw.eqSymm (.eqRefl _) (.eqRefl _)
  have eqEarly := euler_data_congr z R B (m*a₀) U (m*denominator k A R b) T a₁ U D T
    (point_refinement k j A R a hc).eqSymm (.eqRefl _) (denominator_refinement k j A R b hc).eqSymm (.eqRefl _)
  have start : Γ ⊢[PRAAx] b*(E*S) ≐ a₁+U :=
    (by unfold D denominator; ipra_ring : Γ ⊢[PRAAx] b*(E*S) ≐ D*S).eqTrans
      (scaled_early_upper t k j R A a b ha hb hA hk hc).eqSymm
  have eqTail := euler_data_congr z R B (b*(E*S)) u D T (a₁+U) u D T start (.eqRefl _) (.eqRefl _) (.eqRefl _)
  have early := cross_data_congr nameF nameF x x (data z R B (m*a₀) U (m*denominator k A R b) T)
    (data z R B a₁ U D T) (.eqRefl _) eqEarly earlier
  have tails := cross_data_congr nameF nameF y y (data z R B (b*(E*S)) u D T)
    (data z R B (a₁+U) u D T) (.eqRefl _) eqTail tail
  have parts := add_cross _ _ _ _ (cross_symm _ _ _ _ early) (cross_symm _ _ _ _ tails)
  exact cross_trans _ _ _ _ _ _ (cross_data_congr _ _ _ _ _ _ eqWhole (.eqRefl _) add) parts

theorem actual_original_incomplete_cutoff_names_change_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
      ((source (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⋏
        (le (clock (var 0) (var 7) (var 8)) (var 1) ⋏ lt (var 1) (var 2))) ⟶
        (crossEquivalent nameF sumF (lowerData (var 3) (var 4) (var 5) (var 2) (var 6) (var 7) (var 8))
          (addData (GaussianGammaCompactCutoffSplit.lowerData (var 3) (var 4) (var 5) (var 1) (var 2) (var 6))
            (lowerData (var 3) (var 4) (var 5) (var 1) (var 6) (var 7) (var 8))) ⋏
         crossEquivalent nameF sumF (upperData (var 3) (var 4) (var 5) (var 2) (var 6) (var 7) (var 8))
          (addData (upperData (var 3) (var 4) (var 5) (var 1) (var 6) (var 7) (var 8))
            (GaussianGammaCompactCutoffSplit.upperData (var 3) (var 4) (var 5) (var 1) (var 2) (var 6))))) :=
  closeUniv 9 (.impI (.andI
    (original_lower_cutoff_change _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂)
    (original_upper_cutoff_change _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianEulerIncompleteCutoffParts
