import IPRADerivations.Analysis.Barnes.FunctionalEquations.GaussianBarnesCanonicalFunctionalEquation
import IPRADerivations.Analysis.Gamma.GaussianGammaReciprocalInverse

/-!
# The original Barnes recurrence with the pole-free Gamma multiplier

On a certified pole-free chart, multiply the cleared Barnes equation
by the original Gamma name and use the checked reciprocal identity.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPoleFreeRecurrence

open_ipra
open GaussianBarnesCanonicalHead (source)
open GaussianBarnesCanonicalValue (nameF data regular)
open GaussianBarnesCanonicalShiftChart (translated_bound)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaEulerHeadLower (translated)
open GaussianGammaReciprocalInverse (gammaF gammaData gamma_product gamma_regular)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (oneF one_fast multiply_associative multiply_one)

variable {n : ℕ} {Γ : List (Fm PTm n)}

abbrev resultF : PR 2 := multiplyF nameF gammaF

def resultData (z R B d : PTm n) : PTm n :=
  multiplyData nameF gammaF (data z R B) (gammaData (translated z B one) (R+one) B d)

theorem recurrence (z R B a d : PTm n) (h : Γ ⊢[PRAAx] source z R B)
    (hg : Γ ⊢[PRAAx] GaussianGammaReciprocalInverse.source (translated z B one) (R+one) B a d) :
    Γ ⊢[PRAAx] crossEquivalent nameF resultF (data (translated z B one) (R+one) B) (resultData z R B d) := by
  let w := translated z B one
  let S := R+one
  let C := GaussianGammaC7Name.nameF
  let x := data w S B
  let y := GaussianGammaC7Name.data w S B
  let g := gammaData w S B d
  let t := multiplyData nameF C x y
  let r := multiplyData C gammaF y g
  have hx := regular w S B (.andI h.andE₁ (translated_bound z R B h.andE₂))
  have hy := GaussianGammaC7Name.name_regular w S B hg.andE₁
  have he := gamma_regular w S B a d hg
  have hw := regular z R B h
  have ht := multiply_fast nameF C x y hx hy
  have hr := multiply_fast C gammaF y g hy he
  have mul := multiply_cross (multiplyF nameF C) nameF gammaF gammaF t (data z R B) g g
    ht hw he he (GaussianBarnesCanonicalFunctionalEquation.functional_equation z R B h)
    (cross_refl _ _ he)
  have reassoc := multiply_associative nameF C gammaF x y g hx hy he
  have cancel := multiply_cross nameF nameF (multiplyF C gammaF) oneF x x r y
    hx hx hr (one_fast y) (cross_refl _ _ hx) (gamma_product w S B a d hg)
  have identity := GaussianBoundedInverseApartness.ones_equivalent (Γ := Γ) y x
  have move := multiply_cross nameF nameF oneF oneF x x y x hx hx (one_fast y) (one_fast x)
    (cross_refl _ _ hx) identity
  have normalized := cross_trans _ _ _ _ _ _ reassoc
    (cross_trans _ _ _ _ _ _ cancel (cross_trans _ _ _ _ _ _ move (multiply_one nameF x hx)))
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ normalized) mul

theorem actual_Barnes_pole_free_functional_equation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (let z := var 0
     let R := var 1
     let B := var 2
     let a := var 3
     let d := var 4
     source z R B ⟶ GaussianGammaReciprocalInverse.source (translated z B one) (R+one) B a d ⟶
       crossEquivalent nameF resultF (data (translated z B one) (R+one) B) (resultData z R B d)) :=
  closeUniv 5 (.impI (.impI (recurrence _ _ _ _ _ Prf.hyp0.wk Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPoleFreeRecurrence
