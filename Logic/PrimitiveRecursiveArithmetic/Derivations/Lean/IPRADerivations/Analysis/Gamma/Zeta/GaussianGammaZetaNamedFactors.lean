import IPRADerivations.Analysis.Gamma.Zeta.GaussianGammaZetaNamedHalfPlane
import IPRADerivations.Analysis.Gamma.Zeta.GaussianGammaZetaNamedInput
import IPRADerivations.Analysis.Names.Rates.GaussianNamedUniformRateClosure

/-!
# The original Mellin integral equals the product of the two named factors

Compare the named product and the product of the named factors at one
shared late rational observation. The rational factor bounds are
uniform on the certified margin and disk. They allow the remaining
input error to tend to zero while retaining independent output clocks.
-/

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaNamedFactors

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaZetaNamedChart (radius degree dirichletMap gammaMap productMap
  dirichletData gammaData productData dirichlet_data_at gamma_data_at product_data_at
  dirichlet_regular gamma_regular dirichlet_samples gamma_samples)
open GaussianGammaZetaNamedHalfPlane (mellinMap original_named_identity)
open GaussianNamedRightHalfPlaneDemandLift (clock nameF name_regular clock_margin)
open GaussianNamedRightHalfPlaneDemandComparison (frozen_rate)
open GaussianNamedRightHalfPlaneLift (source data late_certificate)
open GaussianNameArithmetic (multiplyF multiplyData)
open GaussianNameEquivalence (crossEquivalent cross_trans)
open GaussianNamedInverseRate (independentRate subst_independentRate)
open GaussianNamedRateComposition (compose symmetric)
open GaussianNamedUniformRateClosure (family productBudget same_denominator_product)
open GaussianRationalHorner (positive_product)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "Z" => GaussianGammaZetaDirichletCofinal.nameF
local notation "G" => GaussianGammaReciprocalInverse.gammaF
local notation "P" => GaussianGammaZetaDirichletProduct.nameF
local notation "gammaCap" => GaussianGammaZetaDirichletProductParameterRate.gammaCap
local notation "zetaCap" => GaussianGammaZetaDirichletUniformBound.cap

def factorF (f : PR 2) : PR 2 := multiplyF (nameF dirichletMap f) (nameF gammaMap f)

def factorData (f : PR 2) (x M R : PTm n) : PTm n :=
  multiplyData (nameF dirichletMap f) (nameF gammaMap f) (data x M R) (data x M R)

def budget (M R : PTm n) : PTm n :=
  one+productBudget one one (gammaCap (radius R) (degree (two*M))) (zetaCap (degree (two*M)))

@[simp] theorem subst_factorData {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (x M R : PTm n) :
    Syn.subst σ (factorData f x M R) = factorData f (Syn.subst σ x) (Syn.subst σ M) (Syn.subst σ R) := by
  simp [factorData]

@[simp] theorem subst_budget {m : ℕ} (σ : Fin n → PTm m) (M R : PTm n) :
    Syn.subst σ (budget M R) = budget (Syn.subst σ M) (Syn.subst σ R) := by
  simp [budget,productBudget,radius,degree,one,two]

private theorem rate_right_data (F H : PR 2) (x y z D N : PTm n)
    (e : Γ ⊢[PRAAx] y ≐ z) (h : Γ ⊢[PRAAx] independentRate F H x y D N) :
    Γ ⊢[PRAAx] independentRate F H x z D N := by
  let φ : Fm PTm 4 := independentRate F H (var 0) (var 1) (var 2) (var 3)
  have move := Prf.eqSubst (Γ := Γ) (Ax := PRAAx) φ ![x,y,D,N] ![x,z,D,N]
    (fun i => by
      fin_cases i
      exact .eqRefl _
      exact e
      exact .eqRefl _
      exact .eqRefl _)
  simpa only [φ,subst_independentRate,Syn.subst_var,Matrix.cons_val] using
    move (by simpa only [φ,subst_independentRate,Syn.subst_var,Matrix.cons_val] using h)

theorem product_rate (f : PR 2) (s x M R : PTm n) (h : Γ ⊢[PRAAx] source f x M R) :
    Γ ⊢[PRAAx] independentRate (nameF productMap f) (factorF f) (data x M R) (factorData f x M R)
      (budget M R) (unit s) := by
  let kz := clock dirichletMap s M R
  let kg := clock gammaMap s M R
  let kp := clock productMap s M R
  let k := kz+kg+kp
  let q := ap2 f k x
  let K := two*M
  let d := data x M R
  let Zf := nameF dirichletMap f
  let Gf := nameF gammaMap f
  let Pf := nameF productMap f
  let z := dirichletData q R K
  let g := gammaData q R K
  let p := productData q R K
  let D := unit s
  let C := productBudget one one (gammaCap (radius R) (degree K)) (zetaCap (degree K))
  have hzLate : Γ ⊢[PRAAx] le kz k := le_trans (le_add_right kz kg) (le_add_right (kz+kg) kp)
  have hgLate : Γ ⊢[PRAAx] le kg k := le_trans (le_add_left kz kg) (le_add_right (kz+kg) kp)
  have hpLate : Γ ⊢[PRAAx] le kp k := le_add_left _ _
  have cert := late_certificate f x k M R h (le_trans (clock_margin productMap s M R) hpLate)
  have positive := unit_positive (Γ := Γ) s
  have rz := rate_right_data Zf Z d _ z one D (dirichlet_data_at q R K)
    (frozen_rate dirichletMap f s k x M R h hzLate)
  have rg := rate_right_data Gf G d _ g one D (gamma_data_at q R K)
    (frozen_rate gammaMap f s k x M R h hgLate)
  have rp := rate_right_data Pf P d _ p one D (product_data_at q R K)
    (frozen_rate productMap f s k x M R h hpLate)
  have pair : Γ ⊢[PRAAx] independentRate P (factorF f) p (factorData f x M R) C D :=
    same_denominator_product Z G Zf Gf z g d d one one D _ _ positive
      (dirichlet_regular q R K cert) (gamma_regular q R K cert)
      (name_regular dirichletMap f x M R h) (name_regular gammaMap f x M R h)
      (gamma_samples q R K cert) (dirichlet_samples q R K cert)
      (symmetric Zf Z d z one D positive rz) (symmetric Gf G d g one D positive rg)
  have joined := compose Pf P (factorF f) d p (factorData f x M R) one D C D positive positive rp pair
  exact GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ (positive_product _ _ positive positive) positive
    (le_of_eq_add (d := zero) (by
      change Γ ⊢[PRAAx] (one+C)*(D*D) ≐ (one*D+C*D)*D+zero
      ipra_ring)) joined

theorem original_named_product (f : PR 2) (x M R : PTm n) (h : Γ ⊢[PRAAx] source f x M R) :
    Γ ⊢[PRAAx] crossEquivalent (nameF productMap f) (factorF f) (data x M R) (factorData f x M R) := by
  apply GaussianNamedUniformRateClosure.equivalent _ _ _ _ (budget M R)
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] source f (Syn.shift x) (Syn.shift M) (Syn.shift R) :=
    by simpa [Fm.shift,Syn.shift] using h.shift
  simpa only [family,subst_factorData,GaussianNamedRightHalfPlaneLift.subst_data,subst_budget,Syn.shift] using
    product_rate f (var 0) (Syn.shift x) (Syn.shift M) (Syn.shift R) hs

theorem original_named_mellin_product (f : PR 2) (x M R : PTm n) (h : Γ ⊢[PRAAx] source f x M R) :
    Γ ⊢[PRAAx] crossEquivalent (nameF mellinMap f) (factorF f) (data x M R) (factorData f x M R) :=
  cross_trans _ _ _ _ _ _ (original_named_identity f x M R h) (original_named_product f x M R h)

theorem actual_named_Gamma_zeta_Mellin_factorized_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (source f (var 0) (var 1) (var 2) ⟶ crossEquivalent (nameF mellinMap f) (factorF f)
        (data (var 0) (var 1) (var 2)) (factorData f (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (original_named_mellin_product f _ _ _ Prf.hyp0))

open GaussianGammaZetaNamedInput (minusOneF minusOneData)

theorem original_named_mellin_on_half_plane (f : PR 2) (x M : PTm n)
    (h : Γ ⊢[PRAAx] GaussianGammaZetaNamedInput.source f x M) :
    Γ ⊢[PRAAx] crossEquivalent (nameF mellinMap (minusOneF f)) (factorF (minusOneF f))
      (data (minusOneData x) M (GaussianGammaZetaNamedInput.radius f x))
      (factorData (minusOneF f) (minusOneData x) M (GaussianGammaZetaNamedInput.radius f x)) :=
  original_named_mellin_product (minusOneF f) (minusOneData x) M (GaussianGammaZetaNamedInput.radius f x)
    (GaussianGammaZetaNamedInput.lift_source f x M h)

theorem actual_original_named_Gamma_zeta_Mellin_Re_gt_one_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (let x := var 0
       let M := var 1
       let R := GaussianGammaZetaNamedInput.radius f x
       GaussianGammaZetaNamedInput.source f x M ⟶
         crossEquivalent (nameF mellinMap (minusOneF f)) (factorF (minusOneF f))
           (data (minusOneData x) M R) (factorData (minusOneF f) (minusOneData x) M R)) :=
  closeUniv 2 (.impI (original_named_mellin_on_half_plane f _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaZetaNamedFactors
