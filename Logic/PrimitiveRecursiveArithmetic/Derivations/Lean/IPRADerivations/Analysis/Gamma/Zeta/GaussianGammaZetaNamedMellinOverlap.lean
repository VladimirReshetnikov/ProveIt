import IPRADerivations.Analysis.Gamma.Zeta.GaussianGammaZetaNamedMellin
import IPRADerivations.Analysis.Gamma.Zeta.GaussianGammaZetaNamedDirichletOverlap

/-!
# Named Mellin values on independently certified domains

The factorized identity reduces overlap of the original Mellin samplers
to overlap of the original named Gamma and Dirichlet factors. Both
inputs may carry their own certified reciprocal real-part margins.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaNamedMellinOverlap

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerNamedShiftInput (shiftF shiftData)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaZetaNamedChart (dirichletMap)
open GaussianGammaZetaNamedInput (source minusOneF minusOneData radius)
open GaussianGammaZetaNamedMellin (mellinF zetaF inputData original_named_Mellin_formula)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNamedRightHalfPlane (marginPoint)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem gamma_source (f : PR 2) (x M : PTm n) (h : Γ ⊢[PRAAx] source f x M) :
    Γ ⊢[PRAAx] GaussianNamedRightHalfPlane.source f x M := by
  let t := minusOneF f
  let y := minusOneData x
  let m := marginPoint M
  have shifted := GaussianEulerNamedShiftInput.original_source t y M
    (GaussianGammaZetaNamedInput.original_source f x M h)
  have restored := GaussianGammaZetaNamedInput.original_restored f x h.andE₁
  have cert := GaussianNamedRealOrderTransport.transport constantF constantF (shiftF t) f m m (shiftData y) x
    (cross_refl _ _ (constant_regular m)) restored shifted.andE₂.andE₂
  exact .andI h.andE₁ (.andI h.andE₂.andE₁ cert)

theorem proper_at_argument (f g : PR 2) (x y M N : PTm n)
    (hf : Γ ⊢[PRAAx] source f x M) (hg : Γ ⊢[PRAAx] source g y N)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] crossEquivalent (mellinF f) (mellinF g) (inputData f x M) (inputData g y N) := by
  let a := GaussianNamedGamma.data x M
  let b := GaussianNamedGamma.data y N
  let u := inputData f x M
  let v := inputData g y N
  have sf := gamma_source f x M hf
  have sg := gamma_source g y N hg
  have gamma := GaussianGammaNegativeIntervalNamedTerminalDerivative.original_gamma_proper f g x y M N sf sg he
  have zeta := GaussianGammaZetaNamedDirichletOverlap.proper_at_argument f g x y M N hf hg he
  have gf := GaussianNamedGamma.name_regular f x M sf
  have gg := GaussianNamedGamma.name_regular g y N sg
  have zf := GaussianNamedRightHalfPlaneDemandLift.name_regular dirichletMap (minusOneF f) (minusOneData x) M (radius f x)
    (GaussianGammaZetaNamedInput.lift_source f x M hf)
  have zg := GaussianNamedRightHalfPlaneDemandLift.name_regular dirichletMap (minusOneF g) (minusOneData y) N (radius g y)
    (GaussianGammaZetaNamedInput.lift_source g y N hg)
  have product := GaussianGammaAdjacentCutoff.multiply_cross (GaussianNamedGamma.nameF f) (GaussianNamedGamma.nameF g)
    (zetaF f) (zetaF g) a b u v gf gg zf zg gamma zeta
  have left := original_named_Mellin_formula f x M hf
  have right := original_named_Mellin_formula g y N hg
  exact cross_trans _ _ _ _ _ _ left (cross_trans _ _ _ _ _ _ product (cross_symm _ _ _ _ right))

theorem actual_original_named_Mellin_overlap_at_argument_closed (f g : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (source f (var 0) (var 2) ⟶ source g (var 1) (var 3) ⟶
        crossEquivalent f g (var 0) (var 1) ⟶
        crossEquivalent (mellinF f) (mellinF g)
          (inputData f (var 0) (var 2)) (inputData g (var 1) (var 3))) :=
  closeUniv 4 (.impI (.impI (.impI (proper_at_argument f g _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianGammaZetaNamedMellinOverlap
