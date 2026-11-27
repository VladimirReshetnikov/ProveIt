import IPRADerivations.Analysis.Barnes.Vigneras.GaussianBarnesVignerasCertifiedMesh
import IPRADerivations.Analysis.Barnes.Vigneras.GaussianBarnesVignerasRefinementWrap

/-!
# Fixed positive rational endpoints of the translated refinement

Read back the projected fine observations on the real axis. The original
Gamma recurrence removes the integer translation, and rational chart
properness moves each endpoint to its fixed rational input.
-/

set_option autoImplicit false
set_option maxHeartbeats 1050000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesVignerasRefinementEndpoints

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Common (pos_of_one_le)
open LeanProofs.IPRA.DiophantineNumberTheory.DigitCode (rem_small)
open GaussianBarnesVignerasIntegerPeriod (advance data input margin period_at source)
open GaussianBarnesVignerasMesh (projection_fixed)
open GaussianBarnesVignerasMeshConstancy (mixed_close positive_chart)
open GaussianBarnesVignerasCertifiedMesh (positive_at_start)
open GaussianBarnesVignerasRefinementWrap (body numerator observationClock sample_at translation)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianDiscretePeriodicGridReadback (sample)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_triangle_same)
open GaussianRationalMetric (distanceBounded)
open GaussianSignedObservationReadback (realProjection)
open SignedDiscreteDerivativeOperators (divisor width)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "Q" => GaussianBarnesVignerasLogQuotient.nameF

def baseNumerator (x i : PTm n) : PTm n := divisor x+i*width x

theorem original_projection (f : PR 2) (t : PTm 2) (x N i : PTm n)
    (hD : Γ ⊢[PRAAx] le one (divisor x)) (hN : Γ ⊢[PRAAx] le one N) (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] realProjection (sample (body f t) x (rem i N)) ≐
      ap2 (Q f) (observationClock x) (data t (numerator x (i*width x)) (divisor x)) := by
  let A := numerator x (i*width x)
  let D := divisor x
  let r := observationClock x
  let q := ap2 (Q f) r (data t A D)
  have ha : Γ ⊢[PRAAx] le one A := by
    unfold A numerator advance
    exact le_trans (le_trans hD (le_add_right _ _)) (le_add_right _ _)
  have hs := GaussianBarnesCanonicalPositiveLogarithm.default_source A D ha hD
  have real := GaussianRealNameExponentialInjectivity.difference_sample_real _ _ r _ _
    (GaussianNamedPositiveLogarithm.real_samples f (input t A D) (margin t A D))
    (GaussianBarnesCanonicalPositiveLogarithmRealAxis.samples_axis A D _ hs)
  have read : Γ ⊢[PRAAx] sample (body f t) x (rem i N) ≐ q := by
    have atIndex := congrInst2 (body f t)
      (congrMul (rem_small (pos_of_one_le hN) hi) (.eqRefl (width x))) (.eqRefl x)
    have atChart : Γ ⊢[PRAAx] inst2 (body f t) (i*width x) x ≐ q := by
      rw [sample_at]
      exact .eqRefl q
    exact atIndex.eqTrans atChart
  have pr : Γ ⊢[PRAAx] realProjection (sample (body f t) x (rem i N)) ≐ realProjection q := by
    ipra_congr (realProjection (var 0) : PTm 1) with [read]
  exact pr.eqTrans (projection_fixed q real.andE₁ real.andE₂)

theorem endpoint_equivalence (f : PR 2) (t : PTm 2) (x i a b : PTm n)
    (hD : Γ ⊢[PRAAx] le one (divisor x)) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b)
    (hBase : Γ ⊢[PRAAx] source f t (baseNumerator x i) (divisor x))
    (hTarget : Γ ⊢[PRAAx] positive_chart f t a b)
    (hRat : Γ ⊢[PRAAx] baseNumerator x i*b ≐ a*divisor x)
    (hVal : Γ ⊢[PRAAx] crossEquivalent f f (input t (baseNumerator x i) (divisor x)) (input t a b)) :
    Γ ⊢[PRAAx] crossEquivalent (Q f) (Q f) (data t (numerator x (i*width x)) (divisor x)) (data t a b) := by
  let A := baseNumerator x i
  let D := divisor x
  have hA : Γ ⊢[PRAAx] le one A := le_trans hD (le_add_right _ _)
  have near := GaussianBarnesVignerasQuotientProperness.proper f A D a b _ _ _ _ _ _
    hA hD ha hb (positive_at_start f t A D hBase) hTarget hRat hVal
  exact cross_trans _ _ _ _ _ _ (period_at f t A D (translation x) hBase) near

theorem coarse_fraction (x N i a b : PTm n) (hD : Γ ⊢[PRAAx] divisor x ≐ N*width x)
    (h : Γ ⊢[PRAAx] (N+i)*b ≐ a*N) : Γ ⊢[PRAAx] baseNumerator x i*b ≐ a*divisor x := by
  unfold baseNumerator
  have scaled := congrMul h (.eqRefl (width x))
  ipra_lc natEq scaled + (Groth.ι (IPRA.Q.mk Γ b) - Groth.ι (IPRA.Q.mk Γ a))*natEq hD

end LeanProofs.IPRA.Analysis.GaussianBarnesVignerasRefinementEndpoints
