import IPRADerivations.Analysis.Gamma.Integrals.GaussianGammaCompactCutoffSplit
import IPRADerivations.Analysis.Beta.Partitions.GaussianBetaRefinedFixedCompactComparison
import IPRADerivations.Core.CertificateTactics

/-!
# Splitting an original Euler cutoff at a positive rational point

For the split point a/b, a primitive-recursive later cutoff puts the
point strictly inside the original interval. Multiplying the original
denominator by b aligns the split exactly. Both compact widths and
their agreement with the original compact name are derived in iPRA.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIncompleteCutoff

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaIntegralCutoffs (height etaDen top)
open GaussianGammaCompactQuadratureBoundary (width exact_right_endpoint)
open GaussianEulerCompactAdditivity (intervalSource nameF addedData)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameEquivalence (crossEquivalent cross_trans)
open GaussianRationalHorner (positive_product)
open GaussianExponentialReference (unit_monotone)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (num monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def clock (t a b : PTm n) : PTm n := GaussianFastValueCut.exponent (succ b) t+succ a
def denominator (k A R b : PTm n) : PTm n := b*etaDen k A R
def splitPoint (k A R a : PTm n) : PTm n := a*etaDen k A R
def lowerWidth (k A R a b : PTm n) : PTm n := monus (splitPoint k A R a) b
def upperWidth (k A R a b : PTm n) : PTm n := monus (denominator k A R b*top k A R) (splitPoint k A R a)

def source (z R B A a b : PTm n) : Fm PTm n :=
  GaussianGammaEulerCompactQuadrature.source z R B ⋏ (le one A ⋏ (le one a ⋏ le one b))

theorem clock_later (t a b : PTm n) : Γ ⊢[PRAAx] le t (clock t a b) :=
  le_trans (le_add_right _ _) (le_add_right _ _)

private theorem height_later (k A R : PTm n) : Γ ⊢[PRAAx] le k (height k A R) :=
  le_of_eq_add (d := A+GaussianGammaIntegralCutoffs.tailCoefficient R+num 10) (by unfold height; ipra_ring)

theorem split_strict_interior (t k A R a b : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) (hA : Γ ⊢[PRAAx] le one A)
    (hk : Γ ⊢[PRAAx] le (clock t a b) k) : Γ ⊢[PRAAx]
    lt b (splitPoint k A R a) ⋏ lt (splitPoint k A R a) (denominator k A R b*top k A R) := by
  let N := GaussianFastValueCut.exponent (succ b) t
  let E := etaDen k A R
  let T := top k A R
  have hN : Γ ⊢[PRAAx] le N (A*height k A R) :=
    le_trans (le_trans (le_trans (le_add_right N (succ a)) hk) (height_later k A R))
      (le_congr (by ipra_ring) (.eqRefl _) (AnalyticNumberTheory.PhiLower.le_mul_mono hA (le_refl _)))
  have bToE : Γ ⊢[PRAAx] le (succ b) E :=
    le_trans
      (le_congr (by ipra_ring) (.eqRefl _) (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl (succ b)) (unit_positive t)))
      (le_trans (GaussianFastValueCut.query_budget (succ b) t) (unit_monotone hN))
  have eToSplit : Γ ⊢[PRAAx] le E (splitPoint k A R a) :=
    le_congr (by ipra_ring) (.eqRefl _) (AnalyticNumberTheory.PhiLower.le_mul_mono ha (le_refl E))
  have heightToT : Γ ⊢[PRAAx] le (height k A R) T :=
    le_of_eq_add (d := height k A R) (by dsimp only [T, top]; ipra_ring)
  have aToT : Γ ⊢[PRAAx] le (succ a) T :=
    le_trans (le_trans (le_trans (le_add_left (succ a) N) hk) (height_later k A R)) heightToT
  have aToScaledTop : Γ ⊢[PRAAx] le (succ a) (b*T) :=
    le_trans aToT (le_congr (by ipra_ring) (.eqRefl _) (AnalyticNumberTheory.PhiLower.le_mul_mono hb (le_refl T)))
  have mul : Γ ⊢[PRAAx] le (succ a*E) ((b*T)*E) := mul_le_mul_right E aToScaledTop
  have plusOne : Γ ⊢[PRAAx] le (succ (a*E)) (succ a*E) :=
    le_congr (by ipra_ring) (by ipra_ring) (add_le_add_right (a*E) (GaussianGammaIntegralCutoffs.eta_den_positive k A R))
  exact .andI (le_trans bToE eToSplit)
    (le_trans plusOne (le_congr (.eqRefl _) (by unfold denominator; ipra_ring) mul))

theorem original_partition (t k z R B A a b : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A a b) (hk : Γ ⊢[PRAAx] le (clock t a b) k) : Γ ⊢[PRAAx]
    (b+lowerWidth k A R a b ≐ splitPoint k A R a) ⋏
      ((lowerWidth k A R a b+upperWidth k A R a b ≐ b*width k A R) ⋏
       GaussianEulerCompactAdditivity.source z R B b (lowerWidth k A R a b) (upperWidth k A R a b)
         (denominator k A R b) (top k A R)) := by
  let D := denominator k A R b
  let T := top k A R
  let L := lowerWidth k A R a b
  let U := upperWidth k A R a b
  let x := splitPoint k A R a
  let M := b*width k A R
  have hA := h.andE₂.andE₁
  have ha := h.andE₂.andE₂.andE₁
  have hb := h.andE₂.andE₂.andE₂
  have inside := split_strict_interior t k A R a b ha hb hA hk
  have left : Γ ⊢[PRAAx] b+L ≐ x := (eq_add_of_le (le_of_lt inside.andE₁)).eqSymm
  have right : Γ ⊢[PRAAx] x+U ≐ D*T := (eq_add_of_le (le_of_lt inside.andE₂)).eqSymm
  have join : Γ ⊢[PRAAx] b+(L+U) ≐ D*T :=
    (by ipra_ring : Γ ⊢[PRAAx] b+(L+U) ≐ (b+L)+U).eqTrans
      ((congrAdd left (.eqRefl U)).eqTrans right)
  have whole : Γ ⊢[PRAAx] b+M ≐ D*T :=
    (by dsimp only [M]; ipra_ring : Γ ⊢[PRAAx] b+M ≐ b*(one+width k A R)).eqTrans
      ((congrMul (.eqRefl b) (exact_right_endpoint k A R)).eqTrans (by dsimp only [D, T, denominator]; ipra_ring))
  have total : Γ ⊢[PRAAx] L+U ≐ M := by
    ipra_lc natEq (join.eqTrans whole.eqSymm)
  have disk : Γ ⊢[PRAAx] GaussianEulerExponentCompactBounds.source z R B D :=
    .andI h.andE₁.andE₁ (.andI (positive_product _ _ hb (GaussianGammaIntegralCutoffs.eta_den_positive k A R)) h.andE₁.andE₂)
  exact .andI left (.andI total
    (.andI (.andI disk (.andI hb (le_congr join.eqSymm (.eqRefl _) (le_refl _))))
      (.andI (GaussianGammaCompactCutoffGeometry.gap_positive b x inside.andE₁)
        (GaussianGammaCompactCutoffGeometry.gap_positive x (D*T) inside.andE₂))))

theorem original_compact_split (t k z R B A a b : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A a b) (hk : Γ ⊢[PRAAx] le (clock t a b) k) : Γ ⊢[PRAAx]
    crossEquivalent nameF (GaussianNameArithmetic.addF nameF nameF) (GaussianGammaEulerCompactQuadrature.data z R B k A)
      (addedData z R B b (lowerWidth k A R a b) (upperWidth k A R a b) (denominator k A R b) (top k A R)) := by
  let E := etaDen k A R
  let T := top k A R
  let W := width k A R
  have hOld := GaussianBetaRefinedFixedCompactComparison.original_interval_source z R B k A h.andE₁
  have aligned := GaussianEulerCompactAlignment.aligned_names z R B one W E T T b
    (.andI hOld.andE₁ (.andI hOld.andE₂.andE₁ (.andI h.andE₂.andE₂.andE₂
      (.andI hOld.andE₂.andE₂ hOld.andE₂.andE₂))))
  have pieces := original_partition t k z R B A a b h hk
  have eqData := GaussianGammaCompactCutoffSplit.euler_data_congr z R B
    (b*one) (b*W) (b*E) T b (lowerWidth k A R a b+upperWidth k A R a b) (denominator k A R b) T
    (by ipra_ring) pieces.andE₂.andE₁.eqSymm (.eqRefl _) (.eqRefl _)
  have rescaled := GaussianGammaCompactCutoffAlignment.cross_data_congr _ _ _ _ _ _ (.eqRefl _) eqData aligned
  exact cross_trans _ _ _ _ _ _ rescaled (GaussianEulerCompactAdditivity.name_additivity _ _ _ _ _ _ _ _ pieces.andE₂.andE₂)

theorem actual_original_euler_cutoff_split_at_rational_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      ((source (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⋏ le (clock (var 0) (var 6) (var 7)) (var 1)) ⟶
        crossEquivalent nameF (GaussianNameArithmetic.addF nameF nameF)
          (GaussianGammaEulerCompactQuadrature.data (var 2) (var 3) (var 4) (var 1) (var 5))
          (addedData (var 2) (var 3) (var 4) (var 7)
            (lowerWidth (var 1) (var 5) (var 3) (var 6) (var 7)) (upperWidth (var 1) (var 5) (var 3) (var 6) (var 7))
            (denominator (var 1) (var 5) (var 3) (var 7)) (top (var 1) (var 5) (var 3)))) :=
  closeUniv 8 (.impI (original_compact_split _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerIncompleteCutoff
