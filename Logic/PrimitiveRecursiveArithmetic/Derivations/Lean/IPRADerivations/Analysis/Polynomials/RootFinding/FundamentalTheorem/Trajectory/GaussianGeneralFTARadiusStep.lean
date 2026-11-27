import IPRADerivations.Analysis.Polynomials.RootFinding.FundamentalTheorem.Trajectory.GaussianGeneralFTATrajectory
import IPRADerivations.Analysis.Polynomials.RootFinding.FundamentalTheorem.Trajectory.GaussianGeneralFTAStepBound
import IPRADerivations.Analysis.FiniteOperations.FiniteProducts.GaussianGeneralProductBound

/-!
# The actual general-FTA step preserves the exact position margin

The actual product numerators and denominators give the next nonnegative
margin by their proved recurrences. The current position and residual
bounds yield the actual displacement bound; the actual trajectory update
and Euclidean triangle inequality then give the next tight margin. Its
global disk follows from the independently proved finite-product bound,
before any next residual estimate is used. All numerical data are internal.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGeneralFTARadiusStep

open_ipra
open LeanProofs.IPRA.Analysis.GaussianGeneralFTAConstants (B C K R rhoNum QNum QDen)
open LeanProofs.IPRA.Analysis.GaussianGeneralProductBound (numerator denominator)
open LeanProofs.IPRA.Analysis.GaussianGeneralFTATrajectory (trajectory polynomial precision delta)
open LeanProofs.IPRA.Analysis.GaussianGeneralPolynomialSamples (sourceInput)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (evaluate positive_product)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (bounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def margin (a : PR 3) (N h x j : PTm n) : PTm n := monus (numerator a N h x j) (denominator a N h x j)
def position (a : PR 3) (N h x j : PTm n) : Fm PTm n := bounded (trajectory a N h x j) (margin a N h x j) (denominator a N h x j)
def residual (a : PR 3) (N h x j : PTm n) : Fm PTm n :=
  bounded (evaluate (polynomial a N h x j) (trajectory a N h x j)) (B a x*pw (QNum N) j) (pw (QDen N) j)

ipra_subst margin
ipra_subst position
ipra_subst residual

theorem source_degree (a : PR 3) (N k h x : PTm n) (hSource : Γ ⊢[PRAAx] sourceInput a N k h x) : Γ ⊢[PRAAx]
    le one N := le_trans (Prf.andE₁ (Prf.andE₂ hSource)) (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ hSource)))

theorem denominator_step (a : PR 3) (N h x j : PTm n) : Γ ⊢[PRAAx]
    denominator a N h x (succ j) ≐ denominator a N h x j*pw (K N) j := GaussianGeometricProduct.denominator_succ _ _ _

theorem margin_zero (a : PR 3) (N h x : PTm n) : Γ ⊢[PRAAx] margin a N h x zero ≐ zero :=
  (congrMonus (GaussianGeometricProduct.numerator_zero _ _) (GaussianGeometricProduct.denominator_zero _ _)).eqTrans (monus_self one)

/-- This is an identity of the actual two product recursors, including
zero factors. Their independently proved v<=u removes monus truncation. -/
theorem product_margin_step (c d j : PTm n) : Γ ⊢[PRAAx]
    monus (GaussianGeometricProduct.numerator c d (succ j)) (GaussianGeometricProduct.denominator c d (succ j)) ≐
      monus (GaussianGeometricProduct.numerator c d j) (GaussianGeometricProduct.denominator c d j)*pw d j+
        GaussianGeometricProduct.numerator c d j*c*pw (PTm.pred d) j := by
  have e : Γ ⊢[PRAAx] GaussianGeometricProduct.numerator c d (succ j) ≐
      GaussianGeometricProduct.denominator c d (succ j)+
        (monus (GaussianGeometricProduct.numerator c d j) (GaussianGeometricProduct.denominator c d j)*pw d j+
          GaussianGeometricProduct.numerator c d j*c*pw (PTm.pred d) j) := by
    have u := natEq (GaussianGeometricProduct.numerator_succ (Γ := Γ) c d j)
    have v := natEq (GaussianGeometricProduct.denominator_succ (Γ := Γ) c d j)
    have gap := natEq (eq_add_of_le (GaussianGeometricProduct.denominator_le_numerator (Γ := Γ) c d j))
    apply deriveNat
    ipra_simps
    rw [u,v]
    unfold GaussianGeometricProduct.factor
    ipra_simps
    rw [gap]
    ring
  exact (congrMonus e (.eqRefl _)).eqTrans (add_monus' _ _)

theorem margin_step (a : PR 3) (N h x j : PTm n) : Γ ⊢[PRAAx]
    margin a N h x (succ j) ≐ margin a N h x j*pw (K N) j+
      numerator a N h x j*C a N h x*pw (rhoNum N) j := product_margin_step _ _ _

theorem margin_le (a : PR 3) (N h x j : PTm n) : Γ ⊢[PRAAx] le (margin a N h x j) (numerator a N h x j) :=
  GaussianMonicResidualRadius.monus_le_left _ _

theorem current_disk (a : PR 3) (N h x j : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hPosition : Γ ⊢[PRAAx] position a N h x j) : Γ ⊢[PRAAx]
    bounded (trajectory a N h x j) (numerator a N h x j) (denominator a N h x j) :=
  GaussianRationalHornerPerturbation.bounded_weaken _ _ _ _ (GaussianGeneralProductBound.denominator_positive a N h x j hN)
    (margin_le a N h x j) hPosition

theorem point_disk (a : PR 3) (N h x j : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hPosition : Γ ⊢[PRAAx] position a N h x j) : Γ ⊢[PRAAx]
    bounded (trajectory a N h x j) (R a N h x) one :=
  GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _
    (GaussianGeneralProductBound.denominator_positive a N h x j hN) (le_refl one)
    (le_congr (by ipra_ring) (mul_comm _ _)
      (le_trans (margin_le a N h x j) (GaussianGeneralProductBound.uniform_bound a N h x j hN))) hPosition

theorem displacement_bound (a : PR 3) (N k h x j : PTm n)
    (hSource : Γ ⊢[PRAAx] sourceInput a N k h x)
    (hPosition : Γ ⊢[PRAAx] position a N h x j) (hResidual : Γ ⊢[PRAAx] residual a N h x j) : Γ ⊢[PRAAx]
    bounded (delta a N h x j) (numerator a N h x j*C a N h x*pw (rhoNum N) j)
      (denominator a N h x j*pw (K N) j) := by
  have hN := source_degree a N k h x hSource
  exact GaussianGeneralFTAStepBound.displacement_bound a N k h (precision a N h x j) x (trajectory a N h x j)
    (numerator a N h x j) (denominator a N h x j) j hSource (GaussianGeneralFTATrajectory.precision_lower a N h x j)
    (GaussianGeneralProductBound.denominator_positive a N h x j hN) (GaussianGeometricProduct.denominator_le_numerator _ _ _)
    (current_disk a N h x j hN hPosition) hResidual

/-- The next position is derived before the next residual or drift is used. -/
theorem position_step (a : PR 3) (N k h x j : PTm n)
    (hSource : Γ ⊢[PRAAx] sourceInput a N k h x)
    (hPosition : Γ ⊢[PRAAx] position a N h x j) (hResidual : Γ ⊢[PRAAx] residual a N h x j) : Γ ⊢[PRAAx]
    position a N h x (succ j) := by
  have hN := source_degree a N k h x hSource
  have hv := GaussianGeneralProductBound.denominator_positive (Γ := Γ) a N h x j hN
  have hn := GaussianGeneralProductBound.denominator_positive (Γ := Γ) a N h x (succ j) hN
  have hf := RationalNonnegativePowers.denominator_positive (Γ := Γ) (K N) j (GaussianGeneralFTAConstants.K_positive N hN)
  have step := displacement_bound a N k h x j hSource hPosition hResidual
  have sum := GaussianRationalReciprocal.bounded_sum _ _ _ _ _ _ hv (positive_product _ _ hv hf) hPosition step
  have up : Γ ⊢[PRAAx]
      margin a N h x j*(denominator a N h x j*pw (K N) j)+
        (numerator a N h x j*C a N h x*pw (rhoNum N) j)*denominator a N h x j ≐
          margin a N h x (succ j)*denominator a N h x j := by
    have e := natEq (margin_step (Γ := Γ) a N h x j)
    apply deriveNat
    ipra_simps
    rw [e]
    ring
  have down : Γ ⊢[PRAAx]
      denominator a N h x j*(denominator a N h x j*pw (K N) j) ≐
        denominator a N h x (succ j)*denominator a N h x j := by
    have e := natEq (denominator_step (Γ := Γ) a N h x j)
    apply deriveNat
    ipra_simps
    rw [e]
    ring
  exact GaussianMonicResidualRadius.bounded_cancel _ _ _ _ hn hv
    (GaussianRationalReciprocal.bound_congr (GaussianGeneralFTATrajectory.trajectory_update a N h x j).eqSymm up down sum)

theorem next_disk (a : PR 3) (N k h x j : PTm n)
    (hSource : Γ ⊢[PRAAx] sourceInput a N k h x)
    (hPosition : Γ ⊢[PRAAx] position a N h x j) (hResidual : Γ ⊢[PRAAx] residual a N h x j) : Γ ⊢[PRAAx]
    bounded (trajectory a N h x (succ j)) (R a N h x) one :=
  point_disk a N h x (succ j) (source_degree a N k h x hSource) (position_step a N k h x j hSource hPosition hResidual)

theorem actual_margin_recurrence_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (margin a (var 0) (var 1) (var 2) (succ (var 3)) ≐
      margin a (var 0) (var 1) (var 2) (var 3)*pw (K (var 0)) (var 3)+
        numerator a (var 0) (var 1) (var 2) (var 3)*C a (var 0) (var 1) (var 2)*pw (rhoNum (var 0)) (var 3)) :=
  closeUniv 4 (margin_step _ _ _ _ _)

theorem actual_position_step_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (sourceInput a (var 0) (var 1) (var 2) (var 3) ⟶ position a (var 0) (var 2) (var 3) (var 4) ⟶
      residual a (var 0) (var 2) (var 3) (var 4) ⟶ position a (var 0) (var 2) (var 3) (succ (var 4))) :=
  closeUniv 5 (.impI (.impI (.impI (position_step _ _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

theorem actual_next_disk_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (sourceInput a (var 0) (var 1) (var 2) (var 3) ⟶ position a (var 0) (var 2) (var 3) (var 4) ⟶
      residual a (var 0) (var 2) (var 3) (var 4) ⟶ bounded (trajectory a (var 0) (var 2) (var 3) (succ (var 4)))
        (R a (var 0) (var 2) (var 3)) one) :=
  closeUniv 5 (.impI (.impI (.impI (next_disk _ _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianGeneralFTARadiusStep
