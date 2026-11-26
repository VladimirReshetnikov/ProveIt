import IPRADerivations.Analysis.Stirling.Binet.GaussianBinetFirstFormula
import IPRADerivations.Analysis.Stirling.Binet.StirlingBounds.GaussianBinetStirlingRemainderRate

/-!
# The actual improper Binet integral on regular right half-plane names

The proved rational first formula transfers the parameter rate of
the literal Stirling remainder to the original cofinal Laplace
sampler. Late signed-rational observations of a regular input then
give a regular name with the same controlled rational readback.
-/

set_option autoImplicit false
set_option maxHeartbeats 750000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceNamed

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetFirstFormulaDecay (laplaceData subst_laplaceData)
open GaussianBinetStirlingRemainderRate (subst_gain)
open GaussianCoefficientNameBounds (unit)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent cross_symm)
open GaussianNamedInverseRate (independentRate subst_independentRate)
open GaussianNamedRightHalfPlaneSigned (certificate denominator imagNumerator point realNumerator sign)
open GaussianRationalMetric (distanceBounded)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "J" => GaussianBinetLaplaceImproperName.nameF
local notation "S" => GaussianBinetStirlingRemainder.nameF
local notation "G" => GaussianBinetStirlingRemainderRate.gain

def pointData (z : PTm n) : PTm n :=
  laplaceData (realNumerator z) (imagNumerator z) (denominator z) (sign z)
def rationalData : PR 1 := PTm.toPR (pointData (var 0) : PTm 1)
def gain : PR 2 := PTm.toPR (G (var 0) (var 1) : PTm 2)

@[simp] theorem subst_pointData {m : ℕ} (σ : Fin n → PTm m) (z : PTm n) :
    Syn.subst σ (pointData z) = pointData (Syn.subst σ z) := by simp [pointData]

theorem rational_data_at (z : PTm n) : Γ ⊢[PRAAx] ap1 rationalData z ≐ pointData z := by
  simpa only [rationalData,ap1,subst_pointData,Syn.subst_var,Matrix.cons_val_zero] using
    toPR_eq (Γ := Γ) (pointData (var 0) : PTm 1) ![z]

theorem gain_at (R K : PTm n) : Γ ⊢[PRAAx] ap2 gain R K ≐ G R K := by
  simpa only [gain,ap2,subst_gain,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    toPR_eq (Γ := Γ) (G (var 0) (var 1) : PTm 2) ![R,K]

theorem original_variation (x y R K E D : PTm n)
    (hx : Γ ⊢[PRAAx] certificate x R K) (hy : Γ ⊢[PRAAx] certificate y R K)
    (hD : Γ ⊢[PRAAx] le one D) (small : Γ ⊢[PRAAx] le (G R K*E) D)
    (near : Γ ⊢[PRAAx] distanceBounded (point x) (point y) E D) :
    Γ ⊢[PRAAx] independentRate J J (pointData x) (pointData y) (G R K*E) D := by
  have rate := GaussianBinetStirlingRemainderRate.independent_rate x y R K E D zero hx hy hD small near
  have bx := GaussianBinetFirstFormula.equivalent (realNumerator x) (imagNumerator x) (denominator x) (sign x) zero
    hx.andE₁.andE₁
  have by' := GaussianBinetFirstFormula.equivalent (realNumerator y) (imagNumerator y) (denominator y) (sign y) zero
    hy.andE₁.andE₁
  exact GaussianNamedRateTransport.transport S S J J _ _ _ _ _ D hD rate
    (cross_symm _ _ _ _ bx) (cross_symm _ _ _ _ by')

theorem variation (x y R K E D : PTm n)
    (hx : Γ ⊢[PRAAx] certificate x R K) (hy : Γ ⊢[PRAAx] certificate y R K)
    (hD : Γ ⊢[PRAAx] le one D) (small : Γ ⊢[PRAAx] le (ap2 gain R K*E) D)
    (near : Γ ⊢[PRAAx] distanceBounded (point x) (point y) E D) :
    Γ ⊢[PRAAx] independentRate J J (ap1 rationalData x) (ap1 rationalData y) (ap2 gain R K*E) D := by
  have eq := congrMul (gain_at (Γ := Γ) R K) (.eqRefl E)
  have rate := original_variation x y R K E D hx hy hD (le_congr eq (.eqRefl _) small) near
  let φ : Fm PTm 4 := independentRate J J (var 0) (var 1) (var 2) (var 3)
  have result := Prf.eqSubst (Γ := Γ) (Ax := PRAAx) φ
    ![pointData x,pointData y,G R K*E,D] ![ap1 rationalData x,ap1 rationalData y,ap2 gain R K*E,D]
    (fun i => by
      fin_cases i
      · exact (rational_data_at x).eqSymm
      · exact (rational_data_at y).eqSymm
      · exact eq.eqSymm
      · exact .eqRefl D)
    (by simpa only [φ,subst_independentRate,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using rate)
  simpa only [φ,subst_independentRate,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using result

def rationalMap : GaussianNamedRightHalfPlaneLift.RationalMap where
  evaluator := J
  rationalData := rationalData
  gain := gain
  variation := variation

abbrev source (f : PR 2) (x M R : PTm n) : Fm PTm n := GaussianNamedRightHalfPlaneLift.source f x M R
abbrev nameF (f : PR 2) : PR 2 := GaussianNamedRightHalfPlaneLift.nameF rationalMap f
abbrev data (x M R : PTm n) : PTm n := GaussianNamedRightHalfPlaneLift.data x M R
abbrev clock (p M R : PTm n) : PTm n := GaussianNamedRightHalfPlaneLift.clock rationalMap p M R

theorem name_regular (f : PR 2) (x M R : PTm n) (h : Γ ⊢[PRAAx] source f x M R) :
    Γ ⊢[PRAAx] pointCN (nameF f) (data x M R) :=
  GaussianNamedRightHalfPlaneLift.name_regular rationalMap f x M R h

theorem proper (f g : PR 2) (x y M R : PTm n) (hx : Γ ⊢[PRAAx] source f x M R)
    (hy : Γ ⊢[PRAAx] source g y M R) (h : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF g) (data x M R) (data y M R) :=
  GaussianNamedRightHalfPlaneLift.proper rationalMap f g x y M R hx hy h

theorem late_rational_rate (f : PR 2) (s k x M R : PTm n)
    (h : Γ ⊢[PRAAx] source f x M R) (hk : Γ ⊢[PRAAx] le (clock s M R) k) :
    Γ ⊢[PRAAx] independentRate (nameF f) J (data x M R) (pointData (ap2 f k x)) one (unit s) := by
  let Z := data x M R
  let Y := ap2 f k x
  let φ := independentRate (nameF f) J (Syn.shift Z) (var 0) (Syn.shift one) (Syn.shift (unit s))
  have raw : Γ ⊢[PRAAx] independentRate (nameF f) J Z (ap1 rationalData Y) one (unit s) :=
    GaussianNamedRightHalfPlaneLift.frozen_rate rationalMap f s k x M R h hk
  simpa only [φ,subst_independentRate,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,Z,Y] using
    Prf.eqSubst1 φ (rational_data_at Y)
      (by simpa only [φ,subst_independentRate,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using raw)

theorem actual_named_Binet_Laplace_regular_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (source f (var 0) (var 1) (var 2) ⟶ pointCN (nameF f) (data (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (name_regular f _ _ _ Prf.hyp0))

theorem actual_named_Binet_Laplace_late_rational_rate_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (source f (var 0) (var 1) (var 2) ⟶ le (clock (var 3) (var 1) (var 2)) (var 4) ⟶
        independentRate (nameF f) J (data (var 0) (var 1) (var 2)) (pointData (ap2 f (var 4) (var 0)))
          one (unit (var 3))) :=
  closeUniv 5 (.impI (.impI (late_rational_rate f _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceNamed
