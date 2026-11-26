import IPRADerivations.Analysis.GaussianGammaZetaMellinParameterRate
import IPRADerivations.Analysis.GaussianGammaZetaNamedChart
import IPRADerivations.Analysis.GaussianNamedRightHalfPlaneDemandComparison

/-!
# The original Mellin identity on regular half-plane input names

Each lift evaluates its own original sampler on actual late signed
rational observations of a name for s−1. Both use the same input
demand on the certified margin and disk, so the exact rational
Mellin identity gives equality of the two named lifts.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaNamedHalfPlane

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit)
open GaussianGammaZetaNamedChart (numerator denominator radius degree native_source demand
  productMap product_data_at demand_lower variation_congr)
open GaussianNamedRightHalfPlaneDemandLift (RationalMap nameF)
open GaussianNamedRightHalfPlaneDemandComparison (equal_of_rational_agreement)
open GaussianNamedRightHalfPlaneLift (source data)
open GaussianNamedRightHalfPlaneSigned (certificate point)
open GaussianNameEquivalence (crossEquivalent subst_crossEquivalent)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalMetric (distanceBounded)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "I" => GaussianGammaZetaMellinImproper.nameF
local notation "P" => GaussianGammaZetaDirichletProduct.nameF

def mellinData (q R K : PTm n) : PTm n :=
  GaussianGammaZetaMellinImproper.data (numerator q) (radius R) (denominator q) K

@[simp] theorem subst_mellinData {m : ℕ} (σ : Fin n → PTm m) (q R K : PTm n) :
    Syn.subst σ (mellinData q R K) = mellinData (Syn.subst σ q) (Syn.subst σ R) (Syn.subst σ K) := by
  simp [mellinData,radius]

def mellinDataF : PR 3 := PTm.toPR (mellinData (var 0) (var 1) (var 2) : PTm 3)

theorem mellin_data_at (q R K : PTm n) : Γ ⊢[PRAAx] ap3 mellinDataF q R K ≐ mellinData q R K := by
  simpa only [mellinDataF,ap3,subst_mellinData,Syn.subst_var,Matrix.cons_val] using
    toPR_eq (Γ := Γ) (mellinData (var 0) (var 1) (var 2) : PTm 3) ![q,R,K]

private theorem replace_data (f g : PR 2) {x y a b : PTm n}
    (left : Γ ⊢[PRAAx] x ≐ a) (right : Γ ⊢[PRAAx] y ≐ b) (h : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] crossEquivalent f g a b := by
  simpa only [subst_crossEquivalent,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    (Prf.eqSubst (Γ := Γ) (Ax := PRAAx) (crossEquivalent f g (var 0) (var 1) : Fm PTm 2)
      ![x,y] ![a,b] (fun i => by fin_cases i; exact left; exact right)
      (by simpa only [subst_crossEquivalent,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using h))

theorem mellin_variation (x y R K s : PTm n)
    (hx : Γ ⊢[PRAAx] certificate x R K) (hy : Γ ⊢[PRAAx] certificate y R K)
    (h : Γ ⊢[PRAAx] distanceBounded (point x) (point y) one (unit (ap3 demand s R K))) :
    Γ ⊢[PRAAx] independentRate I I (ap3 mellinDataF x R K) (ap3 mellinDataF y R K) one (unit s) := by
  let c := GaussianGammaZetaDirichletProductParameterRate.demand s (radius R) (degree K)
  have enough : Γ ⊢[PRAAx] le c (GaussianGammaZetaNamedChart.demandValue s R K) :=
    le_trans (le_add_right _ _) (le_add_right _ _)
  have close := demand_lower x y R K s c enough h
  have rate := GaussianGammaZetaMellinParameterRate.original_demand_rate s (numerator x) (numerator y)
    (radius R) (denominator x) (denominator y) K (native_source x R K hx) (native_source y R K hy) close
  exact variation_congr I _ _ _ _ s (mellin_data_at x R K).eqSymm (mellin_data_at y R K).eqSymm rate

def mellinMap : RationalMap where
  evaluator := I
  rationalData := mellinDataF
  demand := demand
  variation := mellin_variation

theorem rational_agreement (q R K : PTm n) (h : Γ ⊢[PRAAx] certificate q R K) :
    Γ ⊢[PRAAx] crossEquivalent I P (ap3 mellinDataF q R K) (ap3 productMap.rationalData q R K) :=
  replace_data I P (mellin_data_at q R K).eqSymm (product_data_at q R K).eqSymm
    (GaussianGammaZetaMellinIdentity.equivalent (numerator q) (radius R) (denominator q) K (native_source q R K h))

theorem original_named_identity (f : PR 2) (x M R : PTm n) (h : Γ ⊢[PRAAx] source f x M R) :
    Γ ⊢[PRAAx] crossEquivalent (nameF mellinMap f) (nameF productMap f) (data x M R) (data x M R) :=
  equal_of_rational_agreement mellinMap productMap rfl rational_agreement f x M R h

theorem actual_original_named_Gamma_zeta_Mellin_identity_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (source f (var 0) (var 1) (var 2) ⟶
        crossEquivalent (nameF mellinMap f) (nameF productMap f)
          (data (var 0) (var 1) (var 2)) (data (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (original_named_identity f _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaZetaNamedHalfPlane
