import IPRADerivations.Analysis.Gamma.Names.Input.GaussianEulerNamedShiftInput
import IPRADerivations.Analysis.Names.RightHalfPlane.GaussianNamedRightHalfPlaneLift
import IPRADerivations.Analysis.Gamma.EulerProducts.Convexity.GaussianGammaEulerRationalLogOrder
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRealOrderTransport

/-!
# A named input with real part above one

Subtracting the literal one from the original input name transfers the
certified bound on its real part to the C58 chart for the exponent s−1.
Adding one again gives the original argument name.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaNamedInput

open_ipra
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (addF addData add_fast)
open GaussianNameConjugation (equal_samples_cross pointwiseEqual)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (zeroF zero_fast zero_at add_associative add_zero)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianNamedRightHalfPlane (marginPoint)
open GaussianRationalHorner (qadd qzero ofGaussian_canonical)
open GaussianRationalLinearProduct (add_sub_right qadd_zero_right qadd_commutative)
open GaussianRationalMetric (qsub)
open GaussianRationalSumAlgebra (qadd_associative)
open GaussianRationalSyntheticDivision (qone qadd_congr qzero_canonical)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (f : PR 2) (x M : PTm n) : Fm PTm n :=
  pointCN f x ⋏ (le one M ⋏ realOrder constantF f (qadd qone (marginPoint M)) x)

def minusOneF (f : PR 2) : PR 2 := addF f constantF
def minusOneData (x : PTm n) : PTm n := addData x (qsub qzero qone)

def radius (f : PR 2) (x : PTm n) : PTm n :=
  GaussianNamedRightHalfPlane.radius (minusOneF f) (minusOneData x)

ipra_subst minusOneData [GaussianRationalMetric.subst_qsub]

ipra_subst radius

ipra_subst source

private theorem margin_cancel (M : PTm n) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] qadd (qadd qone (marginPoint M)) (qsub qzero qone) ≐ marginPoint M := by
  let a := marginPoint M
  let b : PTm n := qsub qzero qone
  have reorder := (qadd_congr (Γ := Γ) (qadd_commutative qone a) (.eqRefl b)).eqTrans
    (qadd_associative a qone b)
  exact reorder.eqTrans ((qadd_congr (.eqRefl a) (add_sub_right qone qzero qzero_canonical)).eqTrans
    (qadd_zero_right a (ofGaussian_canonical _ _ hM)))

theorem original_source (f : PR 2) (x M : PTm n) (h : Γ ⊢[PRAAx] source f x M) :
    Γ ⊢[PRAAx] GaussianNamedRightHalfPlane.source (minusOneF f) (minusOneData x) M := by
  let b : PTm n := qsub qzero qone
  let c := qadd qone (marginPoint M)
  have hb := constant_regular (Γ := Γ) b
  have reg : Γ ⊢[PRAAx] pointCN (minusOneF f) (minusOneData x) := add_fast f constantF x b h.andE₁ hb
  have order := GaussianGammaEulerRationalLogOrder.add_order constantF f constantF constantF c x b b
    h.andE₂.andE₂ (GaussianGammaEulerRationalLogOrder.order_refl constantF b hb)
  have exactLeft := cross_trans _ _ _ _ _ _
    (GaussianGammaEulerShift.constant_sum_cross c b)
    (GaussianGammaWeierstrassApproximant.constant_data_cross _ _ (margin_cancel M h.andE₂.andE₁))
  have cert : Γ ⊢[PRAAx] GaussianNamedRightHalfPlane.certificate (minusOneF f) (minusOneData x) M :=
    GaussianNamedRealOrderTransport.transport constantF (addF constantF constantF) (minusOneF f) (minusOneF f)
      (marginPoint M) (addData c b) (minusOneData x) (minusOneData x)
      (cross_symm _ _ _ _ exactLeft) (cross_refl _ _ reg) order
  exact .andI reg (.andI h.andE₂.andE₁ cert)

theorem lift_source (f : PR 2) (x M : PTm n) (h : Γ ⊢[PRAAx] source f x M) :
    Γ ⊢[PRAAx] GaussianNamedRightHalfPlaneLift.source (minusOneF f) (minusOneData x) M (radius f x) :=
  .andI (original_source f x M h) (le_refl _)

private theorem constant_zero_cross (x : PTm n) : Γ ⊢[PRAAx] crossEquivalent constantF zeroF (qzero : PTm n) x := by
  apply equal_samples_cross _ _ _ _ (constant_regular _) (zero_fast x)
  refine .allI ?_
  simpa only [pointwiseEqual,Syn.shift,GaussianRationalHorner.subst_qzero] using
    (constant_at (Γ := Γ.map Fm.shift) (var 0) qzero).eqTrans (zero_at (var 0) (Syn.shift x)).eqSymm

theorem original_restored (f : PR 2) (x : PTm n) (hx : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] crossEquivalent (GaussianEulerNamedShiftInput.shiftF (minusOneF f)) f
      (GaussianEulerNamedShiftInput.shiftData (minusOneData x)) x := by
  let b : PTm n := qsub qzero qone
  have hb := constant_regular (Γ := Γ) b
  have h1 := constant_regular (Γ := Γ) (qone : PTm n)
  have e := (qadd_commutative (Γ := Γ) b qone).eqTrans (add_sub_right qone qzero qzero_canonical)
  have constant := cross_trans _ _ _ _ _ _ (GaussianGammaEulerShift.constant_sum_cross b qone)
    (cross_trans _ _ _ _ _ _ (GaussianGammaWeierstrassApproximant.constant_data_cross _ _ e) (constant_zero_cross x))
  have first := add_associative f constantF constantF x b qone hx hb h1
  have collapse := GaussianNameArithmetic.add_equivalent f f (addF constantF constantF) zeroF x x (addData b qone) x
    hx hx (add_fast _ _ _ _ hb h1) (zero_fast x) (GaussianNameEquivalence.diagonal_refl _ _)
    (GaussianNameEquivalence.cross_to_diagonal _ _ _ _ constant)
  exact cross_trans _ _ _ _ _ _ first (cross_trans _ _ _ _ _ _ collapse (GaussianNameRingLaws.add_zero f x hx))

theorem actual_named_real_part_above_one_admission_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (source f (var 0) (var 1) ⟶ GaussianNamedRightHalfPlaneLift.source
        (minusOneF f) (minusOneData (var 0)) (var 1) (radius f (var 0))) :=
  closeUniv 2 (.impI (lift_source f _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaZetaNamedInput
