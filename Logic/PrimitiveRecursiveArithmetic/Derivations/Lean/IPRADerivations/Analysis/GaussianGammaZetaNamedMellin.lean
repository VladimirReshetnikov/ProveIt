import IPRADerivations.Analysis.GaussianGammaZetaNamedFactors
import IPRADerivations.Analysis.GaussianGammaZetaNamedGammaAlignment

/-!
# The Mellin identity with the original named Gamma of s

Use the primitive-recursive Mellin and cofinal Dirichlet lifts on the
actual name of the argument. The Gamma factor is the repository's
original named Gamma evaluated directly at that argument.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaNamedMellin

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaZetaNamedChart (dirichletMap gammaMap)
open GaussianGammaZetaNamedHalfPlane (mellinMap)
open GaussianGammaZetaNamedInput (source minusOneF minusOneData radius)
open GaussianNamedRightHalfPlaneDemandLift (nameF name_regular)
open GaussianNameArithmetic (multiplyF multiplyData)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "G" => GaussianNamedGamma.nameF

def inputData (f : PR 2) (x M : PTm n) : PTm n :=
  GaussianNamedRightHalfPlaneLift.data (minusOneData x) M (radius f x)

def mellinF (f : PR 2) : PR 2 := nameF mellinMap (minusOneF f)
def zetaF (f : PR 2) : PR 2 := nameF dirichletMap (minusOneF f)
def gammaZetaF (f : PR 2) : PR 2 := multiplyF (G f) (zetaF f)

def gammaZetaData (f : PR 2) (x M : PTm n) : PTm n :=
  multiplyData (G f) (zetaF f) (GaussianNamedGamma.data x M) (inputData f x M)

theorem original_named_Mellin_formula (f : PR 2) (x M : PTm n) (h : Γ ⊢[PRAAx] source f x M) :
    Γ ⊢[PRAAx] crossEquivalent (mellinF f) (gammaZetaF f) (inputData f x M) (gammaZetaData f x M) := by
  let T := minusOneF f
  let Z := zetaF f
  let d := inputData f x M
  let g := GaussianNamedGamma.data x M
  let H := nameF gammaMap T
  have chart := GaussianGammaZetaNamedInput.lift_source f x M h
  have hz := name_regular dirichletMap T (minusOneData x) M (radius f x) chart
  have hh := name_regular gammaMap T (minusOneData x) M (radius f x) chart
  have e := GaussianGammaZetaNamedGammaAlignment.equivalent_at_argument f x M h
  have hg : Γ ⊢[PRAAx] pointCN (G f) g :=
    cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ e) e
  have factors := GaussianGammaZetaNamedFactors.original_named_mellin_on_half_plane f x M h
  have replace := GaussianGammaAdjacentCutoff.multiply_cross Z Z H (G f) d d d g
    hz hz hh hg (cross_refl _ _ hz) e
  have ordered := GaussianNameRingLaws.multiply_commutative Z (G f) d g hz hg
  exact cross_trans _ _ _ _ _ _ factors (cross_trans _ _ _ _ _ _ replace ordered)

theorem actual_original_named_Gamma_zeta_Mellin_formula_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (source f (var 0) (var 1) ⟶
        crossEquivalent (mellinF f) (gammaZetaF f) (inputData f (var 0) (var 1)) (gammaZetaData f (var 0) (var 1))) :=
  closeUniv 2 (.impI (original_named_Mellin_formula f _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaZetaNamedMellin
