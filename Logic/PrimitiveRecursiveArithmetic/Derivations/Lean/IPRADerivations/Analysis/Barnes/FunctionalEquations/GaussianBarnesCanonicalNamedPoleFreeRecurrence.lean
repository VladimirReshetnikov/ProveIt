import IPRADerivations.Analysis.Barnes.FunctionalEquations.GaussianBarnesCanonicalNamedFunctionalEquation
import IPRADerivations.Analysis.Gamma.FunctionalEquations.GaussianGammaC7NamedInverse

/-!
# The usual Barnes functional equation on certified pole-free Gaussian names

Multiplying the cleared recurrence by the original named Gamma and
cancelling the matched reciprocal pair yields the usual formula.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNamedPoleFreeRecurrence

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalNamedDemand (source data)
open GaussianBarnesCanonicalNamedFunctionalEquation (shifted_source)
open GaussianEulerNamedShiftInput (shiftF shiftData)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (oneF one_fast multiply_associative multiply_one)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "G" => GaussianBarnesCanonicalNamed.nameF
local notation "C" => GaussianGammaC7Named.nameF
local notation "P" => GaussianGammaNamedPoleFree.nameF
local notation "pd" => GaussianGammaNamedPoleFree.data
local notation "dom" => GaussianGammaNamedPoleFree.source

abbrev resultF (f : PR 2) : PR 2 := multiplyF (G f) (P (shiftF f))

def resultData (f : PR 2) (x R E : PTm n) : PTm n :=
  multiplyData (G f) (P (shiftF f)) (data x R) (pd (shiftData x) (R+one) E)

theorem recurrence (f : PR 2) (x R E : PTm n) (h : Γ ⊢[PRAAx] source f x R)
    (hp : Γ ⊢[PRAAx] dom (shiftF f) (shiftData x) (R+one) E) : Γ ⊢[PRAAx]
    crossEquivalent (G (shiftF f)) (resultF f) (data (shiftData x) (R+one)) (resultData f x R E) := by
  let sf := shiftF f
  let sx := shiftData x
  let S := R+one
  let X := data sx S
  let Y := data x R
  let Z := pd sx S E
  let T := multiplyData (G sf) (C sf) X X
  let W := multiplyData (C sf) (P sf) X Z
  have hs := shifted_source f x R h
  have hc : Γ ⊢[PRAAx] GaussianGammaC7Named.source sf sx S := .andI hs (le_add_left one R)
  have hf := GaussianBarnesCanonicalNamed.name_regular f x R h
  have hg := GaussianBarnesCanonicalNamed.name_regular sf sx S hs
  have hC := GaussianGammaC7Named.name_regular sf sx S hc
  have hP := GaussianGammaNamedPoleFree.name_regular sf sx S E hp
  have ht := multiply_fast (G sf) (C sf) X X hg hC
  have hw := multiply_fast (C sf) (P sf) X Z hC hP
  have mul := multiply_cross (multiplyF (G sf) (C sf)) (G f) (P sf) (P sf) T Y Z Z ht hf hP hP
    (GaussianBarnesCanonicalNamedFunctionalEquation.functional_equation f x R h) (cross_refl _ _ hP)
  have assoc := multiply_associative (G sf) (C sf) (P sf) X X Z hg hC hP
  have cancel := multiply_cross (G sf) (G sf) (multiplyF (C sf) (P sf)) oneF X X W X
    hg hg hw (one_fast X) (cross_refl _ _ hg)
    (cross_trans _ _ _ _ _ _ (GaussianGammaC7NamedInverse.inverse_product sf sx S E hc hp)
      (GaussianBoundedInverseApartness.ones_equivalent sx X))
  have normalized := cross_trans _ _ _ _ _ _ assoc (cross_trans _ _ _ _ _ _ cancel (multiply_one (G sf) X hg))
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ normalized) mul

theorem actual_Barnes_named_pole_free_functional_equation_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (let x := var 0
       let R := var 1
       let E := var 2
       source f x R ⟶ dom (shiftF f) (shiftData x) (R+one) E ⟶
          crossEquivalent (G (shiftF f)) (resultF f) (data (shiftData x) (R+one)) (resultData f x R E)) :=
  closeUniv 3 (.impI (.impI (recurrence f _ _ _ Prf.hyp0.wk Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNamedPoleFreeRecurrence
