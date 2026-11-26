import IPRADerivations.Analysis.Gamma.Names.PoleFree.GaussianGammaNamedPoleFreeNegativeChartDerivative
import IPRADerivations.Analysis.Gamma.CriticalPoints.PositiveMinimum.GaussianGammaPositiveNamedCritical
import IPRADerivations.Analysis.Names.GaussianNameBranch
import IPRADerivations.Foundations.IntervalPacking

/-!
# A single derivative name on the pole-free real Gamma domain

The sign of one certified late input observation chooses the positive
Euler derivative or the derivative in the computed negative chart.
A fixed branch bit and both literal evaluation data are PR terms.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNamedRealDerivative

open_ipra
open ComplexLogarithmRemainder (re)
open GaussianCoefficientNameBounds (unit)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaNamedPoleFreeRealAdmission (snapshot negativeChart offsetF offsetData chartIndex)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans)
open GaussianNamedRightHalfPlane (numerator threshold_budget)
open GaussianSignedNameExponentialOrder (realSamples)
open LeanProofs.IPRA.Probability.MedianCounts (congrSg)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "P" => GaussianNamedPositiveDigamma.derivativeF
local notation "pd" => GaussianNamedPositiveDigamma.derivativeData
local notation "N" => GaussianGammaNamedPoleFreeNegativeChartDerivative.derivativeF
local notation "nd" => GaussianGammaNamedPoleFreeNegativeChartDerivative.derivativeData
local notation "poleSource" => GaussianGammaNamedPoleFree.source
local notation "positiveSource" => GaussianNamedGammaPositiveLower.source

def sampleReal (f : PR 2) (x E : PTm n) : ZT n := re (numerator f (snapshot E) x)

def flag (f : PR 2) (x E : PTm n) : PTm n :=
  LeanProofs.IPRA.Signum.sg (monus (sampleReal f x E).neg (sampleReal f x E).pos)

def nameF (f : PR 2) : PR 2 := GaussianNameBranch.nameF (P f) (N f)
def data (f : PR 2) (x E : PTm n) : PTm n := GaussianNameBranch.data (flag f x E) (pd x (two*E)) (nd f x E)

def positiveCase (f : PR 2) (x E : PTm n) : Fm PTm n := (flag f x E ≐ zero) ⋏ positiveSource f x (two*E)
def negativeCase (f : PR 2) (x E : PTm n) : Fm PTm n := (flag f x E ≐ one) ⋏ negativeChart f x E

theorem branch_cases (f : PR 2) (x R E : PTm n) (hf : Γ ⊢[PRAAx] poleSource f x R E)
    (hr : Γ ⊢[PRAAx] realSamples f x) : Γ ⊢[PRAAx] positiveCase f x E ⋎ negativeCase f x E := by
  let a := sampleReal f x E
  let t := snapshot E
  have late := threshold_budget (Γ := Γ) t (two*E) (le_refl _)
  have hle : Γ ⊢[PRAAx] le (two*E) (two*(two*E)) :=
    le_congr (.eqRefl _) (by unfold two; ipra_ring) (le_add_right (two*E) (two*E))
  refine .orE (lt_or_le a.pos a.neg) ?_ ?_
  · have hle : (lt a.pos a.neg :: Γ) ⊢[PRAAx] le a.pos a.neg := le_of_lt Prf.hyp0
    have sign : (lt a.pos a.neg :: Γ) ⊢[PRAAx] GaussianGammaNamedPoleFreeNegativeSnapshot.nonpositiveAt f t x :=
      le_congr (add_zero _).eqSymm (zero_add _).eqSymm hle
    exact .orI₂ (.andI (Foundations.IntervalPacking.sg_one_of_lt Prf.hyp0)
      (.andI (GaussianGammaNamedPoleFreeRealAdmission.offset_source f x R E hf.wk hr.wk sign)
        (GaussianGammaNamedPoleFreeRealAdmission.shifted_back_cross f x E hf.andE₁.wk hr.wk)))
  · have hn : (le a.neg a.pos :: Γ) ⊢[PRAAx] GaussianGammaNamedPoleFreePositiveAdmission.nonnegativeAt f t x :=
      le_congr (zero_add _).eqSymm (add_zero _).eqSymm Prf.hyp0
    exact .orI₁ (.andI ((congrSg Prf.hyp0).eqTrans LeanProofs.IPRA.Signum.sg_zero)
      (GaussianGammaNamedPoleFreePositiveAdmission.positive_source f t x R E hf.wk hr.wk hn (le_trans hle late).wk))

theorem positive_cross (f : PR 2) (x E : PTm n) (h : Γ ⊢[PRAAx] positiveCase f x E) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f) (P f) (data f x E) (pd x (two*E)) :=
  GaussianNameBranch.select_left _ _ _ _ _ h.andE₁
    (GaussianNamedPositiveDigamma.derivative_regular f x (two*E) h.andE₂)

theorem negative_cross (f : PR 2) (x E : PTm n) (h : Γ ⊢[PRAAx] negativeCase f x E) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f) (N f) (data f x E) (nd f x E) :=
  GaussianNameBranch.select_right _ _ _ _ _ h.andE₁
    (GaussianGammaNegativeIntervalNamedDerivative.name_regular (offsetF f) (offsetData f x E) (two*(two*E))
      (chartIndex f x E) (GaussianNamedEulerUnitTimeMargin.double _ _ _ h.andE₂.andE₁))

theorem name_regular (f : PR 2) (x R E : PTm n) (hf : Γ ⊢[PRAAx] poleSource f x R E)
    (hr : Γ ⊢[PRAAx] realSamples f x) : Γ ⊢[PRAAx] pointCN (nameF f) (data f x E) := by
  refine .orE (branch_cases f x R E hf hr) ?_ ?_
  · have eq := positive_cross (Γ := positiveCase f x E :: Γ) f x E Prf.hyp0
    exact cross_trans _ _ _ _ _ _ eq (cross_symm _ _ _ _ eq)
  · have eq := negative_cross (Γ := negativeCase f x E :: Γ) f x E Prf.hyp0
    exact cross_trans _ _ _ _ _ _ eq (cross_symm _ _ _ _ eq)

end LeanProofs.IPRA.Analysis.GaussianGammaNamedRealDerivative
