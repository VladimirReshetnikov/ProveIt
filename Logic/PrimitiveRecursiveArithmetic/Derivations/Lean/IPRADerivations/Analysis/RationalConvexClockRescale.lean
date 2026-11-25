import IPRADerivations.Analysis.RationalConvexEndpointBudget
import IPRADerivations.Analysis.RationalNonnegativePowers
import IPRADerivations.Core.CongruenceTactic

/-!
# The two-endpoint clock is independent of a common denominator

Enlarging the positive common scale preserves both actual endpoint
query codes. It multiplies the numerator and denominator of the
source ceiling by the same positive factor, so the returned clock
can be computed from the endpoints alone before adjoining any pair
of interior rational arguments to their common scale.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalConvexClockRescale

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open RationalCubeMidpoint (fraction fraction_represents)
open RationalConvexSecantWeights (leftPoint rightPoint margin margin_positive budget modulus)
open RationalConvexEndpointBudget (coarseBudget M localModulus)
open RationalNonnegativePowers (fraction_congr)
open GaussianDescentClockArithmetic (ceiling ceiling_lower ceiling_least subst_ceiling)
open LeanProofs.IPRA.Foundations.FiniteObservations.MetricKernel (meet meet_left meet_right)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem fraction_rescale (a D r : PTm n) (hD : Γ ⊢[PRAAx] le one D) (hr : Γ ⊢[PRAAx] le one r) :
    Γ ⊢[PRAAx] fraction (a*r) (D*r) ≐ fraction a D := by
  have h := RationalAlgebra.positive_product hD hr
  exact RationalFiniteSum.canonical_equal _ _ _ _ _ _
    (RationalNormalForm.normalize_well_formed _ _ h) (RationalNormalForm.normalize_well_formed _ _ hD)
    (fraction_represents _ _ h) (fraction_represents _ _ hD) h hD (by
      apply ZT.derive
      simp only [ZT.toZ_mul,ZT.toZ_ofNat]
      ipra_simps
      ring)

theorem left_point_rescale (D P r : PTm n) (hD : Γ ⊢[PRAAx] le one D) (hr : Γ ⊢[PRAAx] le one r) :
    Γ ⊢[PRAAx] leftPoint (D*r) (P*r) ≐ leftPoint D P :=
  (fraction_congr (.eqRefl _) (by ipra_ring)).eqTrans
    (fraction_rescale P (two*D) r (RationalAlgebra.positive_product (le_succ_self one) hD) hr)

theorem right_point_rescale (D Q r : PTm n) (hD : Γ ⊢[PRAAx] le one D) (hr : Γ ⊢[PRAAx] le one r) :
    Γ ⊢[PRAAx] rightPoint (D*r) (Q*r) ≐ rightPoint D Q :=
  (fraction_congr (by ipra_ring) (.eqRefl _)).eqTrans (fraction_rescale (Q+D) D r hD hr)

theorem meet_rescale (a b r : PTm n) : Γ ⊢[PRAAx] meet (a*r) (b*r) ≐ meet a b*r :=
  .orE (le_total a b)
    ((meet_left (mul_le_mul_right r Prf.hyp0)).eqTrans (congrMul (meet_left Prf.hyp0).eqSymm (.eqRefl _)))
    ((meet_right (mul_le_mul_right r Prf.hyp0)).eqTrans (congrMul (meet_right Prf.hyp0).eqSymm (.eqRefl _)))

theorem margin_rescale (D P r : PTm n) : Γ ⊢[PRAAx] margin (D*r) (P*r) ≐ margin D P*r := by
  have h : Γ ⊢[PRAAx] two*(D*r) ≐ (two*D)*r := by ipra_ring
  have e := Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (meet (var 0) (var 1) : PTm 2)
    (σ := ![P*r,two*(D*r)]) (σ' := ![P*r,(two*D)*r]) (fun i => by fin_cases i; exact .eqRefl _; exact h)
  have em : Γ ⊢[PRAAx] meet (P*r) (two*(D*r)) ≐ meet (P*r) ((two*D)*r) := by
    simpa [meet] using e
  exact em.eqTrans (meet_rescale P (two*D) r)

theorem ceiling_congr {a b c d : PTm n} (ha : Γ ⊢[PRAAx] a ≐ c) (hb : Γ ⊢[PRAAx] b ≐ d) :
    Γ ⊢[PRAAx] ceiling a b ≐ ceiling c d := by
  ipra_congr (ceiling (var 0) (var 1) : PTm 2) with [ha, hb]

theorem ceiling_rescale (a b r : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hr : Γ ⊢[PRAAx] le one r) :
    Γ ⊢[PRAAx] ceiling (a*r) (b*r) ≐ ceiling a b := by
  have h := RationalAlgebra.positive_product hb hr
  have lower := ceiling_lower a b hb
  have upper := ceiling_lower (a*r) (b*r) h
  exact le_antisymm (ceiling_least _ _ _ h
    (le_congr (.eqRefl _) (by ipra_ring) (mul_le_mul_right r lower)))
    (ceiling_least _ _ _ hb (RationalValueBounds.positive_cancel hr
      (le_congr (by ipra_ring) (by ipra_ring) upper)))

theorem budget_rescale (D P m r : PTm n) (hD : Γ ⊢[PRAAx] le one D) (hP : Γ ⊢[PRAAx] le one P)
    (hr : Γ ⊢[PRAAx] le one r) : Γ ⊢[PRAAx] budget (D*r) (P*r) m ≐ budget D P m :=
  (ceiling_congr (by ipra_ring) (margin_rescale D P r)).eqTrans
    (ceiling_rescale (two*D*m) (margin D P) r (margin_positive D P hD hP) hr)

theorem coarse_congr {a b c d : PTm n} (ha : Γ ⊢[PRAAx] a ≐ c) (hb : Γ ⊢[PRAAx] b ≐ d) :
    Γ ⊢[PRAAx] coarseBudget a b ≐ coarseBudget c d := by
  ipra_congr (coarseBudget (var 0) (var 1) : PTm 2) with [ha, hb]

theorem endpoint_budget_rescale (A : PR 3) (D P Q r x : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (hr : Γ ⊢[PRAAx] le one r) :
    Γ ⊢[PRAAx] M A (D*r) (P*r) (Q*r) x ≐ M A D P Q x :=
  coarse_congr (congrAp3 A (left_point_rescale D P r hD hr) (.eqRefl _) (.eqRefl _))
    (congrAp3 A (right_point_rescale D Q r hD hr) (.eqRefl _) (.eqRefl _))

theorem original_clock_rescale (A : PR 3) (D P Q k r x : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (hP : Γ ⊢[PRAAx] le one P) (hr : Γ ⊢[PRAAx] le one r) :
    Γ ⊢[PRAAx] localModulus A (D*r) (P*r) (Q*r) k x ≐ localModulus A D P Q k x :=
  congrAdd (.eqRefl k)
    ((ceiling_congr (congrMul (.eqRefl _) (endpoint_budget_rescale A D P Q r x hD hr)) (.eqRefl _)).eqTrans
      (budget_rescale D P (M A D P Q x) r hD hP hr))

theorem actual_original_convex_clock_rescale_closed (A : PR 3) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((le one (var 0) ⋏ (le one (var 1) ⋏ le one (var 4))) ⟶
      localModulus A (var 0*var 4) (var 1*var 4) (var 2*var 4) (var 3) (var 5) ≐
        localModulus A (var 0) (var 1) (var 2) (var 3) (var 5)) :=
  closeUniv 6 (.impI (original_clock_rescale A _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.RationalConvexClockRescale
