import IPRADerivations.Analysis.Stirling.Binet.SecondFormula.GaussianBinetSecondFormula
import IPRADerivations.Analysis.Stirling.Binet.GaussianBinetFirstFormulaNamed
import IPRADerivations.Analysis.Names.Rates.RightHalfPlane.GaussianNamedRightHalfPlaneLiftTransport

/-!
# Second Binet formula for regular right-half-plane names

The lift evaluates the original scaled Bose sampler on each late
rational sample. The rational identity transfers the Laplace spatial
modulus to this evaluator and identifies the resulting name with the
original named Stirling remainder.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianBinetSecondFormulaNamed

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianNamedRightHalfPlaneSigned (certificate denominator imagNumerator realNumerator sign)
open GaussianNamedRightHalfPlaneLiftTransport (PointAgreement transportedMap)
open GaussianBinetLaplaceNamed (source)
open GaussianCoefficientNameBounds (unit)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans)
open GaussianNamedInverseRate (independentRate subst_independentRate)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "Bose" => GaussianBinetSecondFormulaReduction.nameF
local notation "Laplace" => GaussianBinetLaplaceImproperName.nameF
local notation "LaplaceMap" => GaussianBinetLaplaceNamed.rationalMap
local notation "Stirling" => GaussianBinetStirlingRemainder.nameF
local notation "Remainder" => GaussianBinetFirstFormulaNamed.remainderF
local notation "remainderData" => GaussianBinetFirstFormulaNamed.remainderData

/-- The rational chart's denominator is an admitted reciprocal real-part
bound for the original Bose sampler. -/
def pointData (z : PTm n) : PTm n :=
  GaussianBinetSecondFormulaReduction.data (realNumerator z) (imagNumerator z) (denominator z) (sign z) (denominator z)

def rationalData : PR 1 := PTm.toPR (pointData (var 0) : PTm 1)

@[simp] theorem subst_pointData {m : ℕ} (σ : Fin n → PTm m) (z : PTm n) :
    Syn.subst σ (pointData z) = pointData (Syn.subst σ z) := by simp [pointData]

theorem rational_data_at (z : PTm n) : Γ ⊢[PRAAx] ap1 rationalData z ≐ pointData z := by
  simpa only [rationalData,ap1,subst_pointData,Syn.subst_var,Matrix.cons_val_zero] using
    toPR_eq (Γ := Γ) (pointData (var 0) : PTm 1) ![z]

theorem point_equivalent (z R K : PTm n) (h : Γ ⊢[PRAAx] certificate z R K) :
    Γ ⊢[PRAAx] crossEquivalent Laplace Bose (GaussianBinetLaplaceNamed.pointData z) (pointData z) := by
  let A := realNumerator z
  let B := imagNumerator z
  let D := denominator z
  let s := sign z
  let v := GaussianBinetStirlingRemainder.data A B D s zero
  have first := GaussianBinetFirstFormula.equivalent A B D s zero h.andE₁.andE₁
  have hz := GaussianBinetBoseImproperName.canonical_source A B D s h.andE₁.andE₁
  have second := GaussianBinetSecondFormula.equivalent A B D s D zero hz
  exact cross_trans Laplace Stirling Bose (GaussianBinetLaplaceNamed.pointData z) v (pointData z)
    (cross_symm _ _ _ _ first) second

theorem point_agreement : PointAgreement LaplaceMap Bose rationalData := by
  intro m Δ z R K hz
  let φ : Fm PTm 2 := crossEquivalent Laplace Bose (var 0) (var 1)
  have result := Prf.eqSubst (Γ := Δ) (Ax := PRAAx) φ
    ![GaussianBinetLaplaceNamed.pointData z,pointData z]
    ![ap1 GaussianBinetLaplaceNamed.rationalData z,ap1 rationalData z]
    (fun i => by
      fin_cases i
      · exact (GaussianBinetLaplaceNamed.rational_data_at z).eqSymm
      · exact (rational_data_at z).eqSymm)
    (by simpa only [φ,GaussianNameEquivalence.subst_crossEquivalent,Syn.subst_var,Matrix.cons_val_zero,
      Matrix.cons_val_one] using point_equivalent z R K hz)
  change Δ ⊢[PRAAx] crossEquivalent Laplace Bose (ap1 GaussianBinetLaplaceNamed.rationalData z) (ap1 rationalData z)
  simpa only [φ,GaussianNameEquivalence.subst_crossEquivalent,Syn.subst_var,Matrix.cons_val_zero,
    Matrix.cons_val_one] using result

def rationalMap : GaussianNamedRightHalfPlaneLift.RationalMap :=
  transportedMap LaplaceMap Bose rationalData point_agreement

abbrev nameF (f : PR 2) : PR 2 := GaussianNamedRightHalfPlaneLift.nameF rationalMap f
abbrev data (x M R : PTm n) : PTm n := GaussianNamedRightHalfPlaneLift.data x M R
abbrev clock (p M R : PTm n) : PTm n := GaussianNamedRightHalfPlaneLift.clock rationalMap p M R

theorem sample_at (f : PR 2) (p x M R : PTm n) :
    Γ ⊢[PRAAx] ap2 (nameF f) p (data x M R) ≐ ap2 Bose (succ p) (pointData (ap2 f (clock p M R) x)) :=
  (GaussianNamedRightHalfPlaneLift.sample_at rationalMap f p x M R).eqTrans
    (congrAp2 Bose (.eqRefl (succ p)) (rational_data_at (ap2 f (clock p M R) x)))

theorem name_regular (f : PR 2) (x M R : PTm n) (h : Γ ⊢[PRAAx] source f x M R) :
    Γ ⊢[PRAAx] pointCN (nameF f) (data x M R) :=
  GaussianNamedRightHalfPlaneLift.name_regular rationalMap f x M R h

theorem proper (f g : PR 2) (x y M R : PTm n)
    (hx : Γ ⊢[PRAAx] source f x M R) (hy : Γ ⊢[PRAAx] source g y M R)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF g) (data x M R) (data y M R) :=
  GaussianNamedRightHalfPlaneLift.proper rationalMap f g x y M R hx hy he

theorem late_rational_rate (f : PR 2) (s k x M R : PTm n)
    (h : Γ ⊢[PRAAx] source f x M R) (hk : Γ ⊢[PRAAx] le (clock s M R) k) :
    Γ ⊢[PRAAx] independentRate (nameF f) Bose (data x M R) (pointData (ap2 f k x)) one (unit s) := by
  let X := data x M R
  let z := ap2 f k x
  let φ := independentRate (nameF f) Bose (Syn.shift X) (var 0) (Syn.shift one) (Syn.shift (unit s))
  have rate : Γ ⊢[PRAAx] independentRate (nameF f) Bose X (ap1 rationalData z) one (unit s) :=
    GaussianNamedRightHalfPlaneLift.frozen_rate rationalMap f s k x M R h hk
  simpa only [φ,subst_independentRate,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,X,z] using
    Prf.eqSubst1 φ (rational_data_at z)
      (by simpa only [φ,subst_independentRate,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using rate)

theorem laplace_equivalent (f : PR 2) (x M R : PTm n) (h : Γ ⊢[PRAAx] source f x M R) :
    Γ ⊢[PRAAx] crossEquivalent (GaussianBinetLaplaceNamed.nameF f) (nameF f) (data x M R) (data x M R) :=
  GaussianNamedRightHalfPlaneLiftTransport.equivalent LaplaceMap Bose rationalData point_agreement f x M R h

theorem equivalent (f : PR 2) (x M R w : PTm n) (h : Γ ⊢[PRAAx] source f x M R) :
    Γ ⊢[PRAAx] crossEquivalent (Remainder f) (nameF f) (remainderData f x M R w) (data x M R) :=
  cross_trans (Remainder f) (GaussianBinetLaplaceNamed.nameF f) (nameF f) (remainderData f x M R w)
    (data x M R) (data x M R) (GaussianBinetFirstFormulaNamed.equivalent f x M R w h) (laplace_equivalent f x M R h)

theorem actual_second_Binet_formula_named_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source f (var 0) (var 1) (var 2) ⟶ crossEquivalent (Remainder f) (nameF f)
      (remainderData f (var 0) (var 1) (var 2) (var 3)) (data (var 0) (var 1) (var 2))) :=
  closeUniv 4 (.impI (equivalent f _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBinetSecondFormulaNamed
