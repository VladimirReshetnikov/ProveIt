import IPRADerivations.Analysis.Euler.Integration.Incomplete.GaussianEulerIncompleteCutoffParts
import IPRADerivations.Analysis.Integration.CompactGrids.GaussianCompactMeshIndependence

/-!
# Exact opposite-radius alignment of the incomplete compact pieces

Adding the opposite radius's actual tail coefficient gives identical
heights, hence identical cutoff denominators, endpoints and widths.
Both original modulus parameters remain in the two original compact
data records. Genuine mesh-name independence compares the same Euler
evaluator on that common physical interval. No equality of the two
original meshes or observations is assumed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIncompleteRadiusAlignment

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaIntegralCutoffs (height etaDen top tailCoefficient)
open GaussianEulerIncompleteCutoff (clock denominator splitPoint lowerWidth upperWidth)
open GaussianEulerIncompleteCutoffParts (lowerData upperData piece_sources)
open GaussianEulerCompactAdditivity (intervalSource nameF data compact_input)
open GaussianEulerIntegrandName (evaluatorF fixedData)
open GaussianNameEquivalence (crossEquivalent cross_at)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalHorner (positive_product)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def cutoff (m U : PTm n) : PTm n := m+tailCoefficient U
@[simp] theorem subst_cutoff {l : ℕ} (σ : Fin n → PTm l) (m U : PTm n) :
    Syn.subst σ (cutoff m U) = cutoff (Syn.subst σ m) (Syn.subst σ U) := by simp [cutoff,tailCoefficient]

theorem cutoff_later (m U : PTm n) : Γ ⊢[PRAAx] le m (cutoff m U) := le_add_right _ _

theorem height_alignment (m A R S : PTm n) : Γ ⊢[PRAAx]
    height (cutoff m S) A R ≐ height (cutoff m R) A S := by unfold height cutoff; ipra_ring

theorem eta_alignment (m A R S : PTm n) : Γ ⊢[PRAAx]
    etaDen (cutoff m S) A R ≐ etaDen (cutoff m R) A S :=
  congrAp2 powF (congrMul (.eqRefl A) (height_alignment m A R S)) (.eqRefl two)

theorem top_alignment (m A R S : PTm n) : Γ ⊢[PRAAx]
    top (cutoff m S) A R ≐ top (cutoff m R) A S := congrMul (.eqRefl two) (height_alignment m A R S)

theorem denominator_alignment (m A R S b : PTm n) : Γ ⊢[PRAAx]
    denominator (cutoff m S) A R b ≐ denominator (cutoff m R) A S b :=
  congrMul (.eqRefl b) (eta_alignment m A R S)

theorem point_alignment (m A R S a : PTm n) : Γ ⊢[PRAAx]
    splitPoint (cutoff m S) A R a ≐ splitPoint (cutoff m R) A S a :=
  congrMul (.eqRefl a) (eta_alignment m A R S)

theorem lower_width_alignment (m A R S a b : PTm n) : Γ ⊢[PRAAx]
    lowerWidth (cutoff m S) A R a b ≐ lowerWidth (cutoff m R) A S a b :=
  congrMonus (point_alignment m A R S a) (.eqRefl b)

theorem upper_width_alignment (m A R S a b : PTm n) : Γ ⊢[PRAAx]
    upperWidth (cutoff m S) A R a b ≐ upperWidth (cutoff m R) A S a b :=
  congrMonus (congrMul (denominator_alignment m A R S b) (top_alignment m A R S)) (point_alignment m A R S a)

/-- The physical interval is unchanged; only its certified native input
radius and the resulting genuine sampled modulus are replaced. -/
theorem interval_at_radius (z R S B a C E T : PTm n)
    (hR : Γ ⊢[PRAAx] intervalSource z R B a C E T)
    (hS : Γ ⊢[PRAAx] GaussianGammaEulerCompactQuadrature.source z S B) : Γ ⊢[PRAAx]
    intervalSource z S B a C E T :=
  .andI (.andI hS.andE₁ (.andI hR.andE₁.andE₂.andE₁ hS.andE₂)) hR.andE₂

theorem compact_names (z R S B a C E T : PTm n)
    (hR : Γ ⊢[PRAAx] intervalSource z R B a C E T)
    (hS : Γ ⊢[PRAAx] intervalSource z S B a C E T) : Γ ⊢[PRAAx]
    crossEquivalent nameF nameF (data z R B a C E T) (data z S B a C E T) :=
  GaussianCompactMeshIndependence.name_independence evaluatorF a C E
    (GaussianEulerCompactModulus.lipschitz R E T) T (GaussianEulerCompactModulus.lipschitz S E T) T (fixedData z B)
    (.andI (compact_input z R B a C E T hR) (compact_input z S B a C E T hS))

theorem original_piece_names (t m z R S B A a b : PTm n)
    (hR : Γ ⊢[PRAAx] GaussianEulerIncompleteCutoff.source z R B A a b)
    (hS : Γ ⊢[PRAAx] GaussianEulerIncompleteCutoff.source z S B A a b)
    (hm : Γ ⊢[PRAAx] le (clock t a b) m) : Γ ⊢[PRAAx]
    crossEquivalent nameF nameF (lowerData z R B (cutoff m S) A a b) (lowerData z S B (cutoff m R) A a b) ⋏
    crossEquivalent nameF nameF (upperData z R B (cutoff m S) A a b) (upperData z S B (cutoff m R) A a b) := by
  let k := cutoff m S
  let D := denominator k A R b
  let T := top k A R
  let P := splitPoint k A R a
  let L := lowerWidth k A R a b
  let U := upperWidth k A R a b
  have hmR := le_trans hm (cutoff_later (Γ := Γ) m S)
  have pieces := piece_sources t k z R B A a b hR hmR
  have lowR := pieces.andE₁
  have upR := pieces.andE₂
  have lowS := interval_at_radius z R S B b L D T lowR hS.andE₁
  have upS := interval_at_radius z R S B P U D T upR hS.andE₁
  have lower := compact_names z R S B b L D T lowR lowS
  have upper := compact_names z R S B P U D T upR upS
  have lowerEq : Γ ⊢[PRAAx] data z S B b L D T ≐ lowerData z S B (cutoff m R) A a b :=
    GaussianGammaCompactCutoffSplit.euler_data_congr z S B b L D T b (lowerWidth (cutoff m R) A S a b)
      (denominator (cutoff m R) A S b) (top (cutoff m R) A S) (.eqRefl _)
      (lower_width_alignment m A R S a b) (denominator_alignment m A R S b) (top_alignment m A R S)
  have upperEq : Γ ⊢[PRAAx] data z S B P U D T ≐ upperData z S B (cutoff m R) A a b :=
    GaussianGammaCompactCutoffSplit.euler_data_congr z S B P U D T (splitPoint (cutoff m R) A S a)
      (upperWidth (cutoff m R) A S a b) (denominator (cutoff m R) A S b) (top (cutoff m R) A S)
      (point_alignment m A R S a) (upper_width_alignment m A R S a b)
      (denominator_alignment m A R S b) (top_alignment m A R S)
  exact .andI
    (GaussianGammaCompactCutoffAlignment.cross_data_congr _ _ _ _ _ _ (.eqRefl _) lowerEq lower)
    (GaussianGammaCompactCutoffAlignment.cross_data_congr _ _ _ _ _ _ (.eqRefl _) upperEq upper)

theorem original_piece_observations (p q t m z R S B A a b : PTm n)
    (hR : Γ ⊢[PRAAx] GaussianEulerIncompleteCutoff.source z R B A a b)
    (hS : Γ ⊢[PRAAx] GaussianEulerIncompleteCutoff.source z S B A a b)
    (hm : Γ ⊢[PRAAx] le (clock t a b) m) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (lowerData z R B (cutoff m S) A a b))
      (ap2 nameF q (lowerData z S B (cutoff m R) A a b)) (unit p+unit q) (unit p*unit q) ⋏
    distanceBounded (ap2 nameF p (upperData z R B (cutoff m S) A a b))
      (ap2 nameF q (upperData z S B (cutoff m R) A a b)) (unit p+unit q) (unit p*unit q) := by
  have names := original_piece_names t m z R S B A a b hR hS hm
  exact .andI (cross_at _ _ _ _ p q names.andE₁) (cross_at _ _ _ _ p q names.andE₂)

theorem actual_original_incomplete_opposite_radius_names_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    ((GaussianEulerIncompleteCutoff.source (var 2) (var 3) (var 5) (var 6) (var 7) (var 8) ⋏
      (GaussianEulerIncompleteCutoff.source (var 2) (var 4) (var 5) (var 6) (var 7) (var 8) ⋏
        le (clock (var 0) (var 7) (var 8)) (var 1))) ⟶
      (crossEquivalent nameF nameF
        (lowerData (var 2) (var 3) (var 5) (cutoff (var 1) (var 4)) (var 6) (var 7) (var 8))
        (lowerData (var 2) (var 4) (var 5) (cutoff (var 1) (var 3)) (var 6) (var 7) (var 8)) ⋏
       crossEquivalent nameF nameF
        (upperData (var 2) (var 3) (var 5) (cutoff (var 1) (var 4)) (var 6) (var 7) (var 8))
        (upperData (var 2) (var 4) (var 5) (cutoff (var 1) (var 3)) (var 6) (var 7) (var 8)))) :=
  closeUniv 9 (.impI (original_piece_names _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

theorem actual_original_incomplete_opposite_radius_observations_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
    ((GaussianEulerIncompleteCutoff.source (var 4) (var 5) (var 7) (var 8) (var 9) (var 10) ⋏
      (GaussianEulerIncompleteCutoff.source (var 4) (var 6) (var 7) (var 8) (var 9) (var 10) ⋏
        le (clock (var 2) (var 9) (var 10)) (var 3))) ⟶
      (distanceBounded (ap2 nameF (var 0) (lowerData (var 4) (var 5) (var 7) (cutoff (var 3) (var 6)) (var 8) (var 9) (var 10)))
        (ap2 nameF (var 1) (lowerData (var 4) (var 6) (var 7) (cutoff (var 3) (var 5)) (var 8) (var 9) (var 10)))
        (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1)) ⋏
       distanceBounded (ap2 nameF (var 0) (upperData (var 4) (var 5) (var 7) (cutoff (var 3) (var 6)) (var 8) (var 9) (var 10)))
        (ap2 nameF (var 1) (upperData (var 4) (var 6) (var 7) (cutoff (var 3) (var 5)) (var 8) (var 9) (var 10)))
        (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1)))) :=
  closeUniv 11 (.impI (original_piece_observations _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerIncompleteRadiusAlignment
