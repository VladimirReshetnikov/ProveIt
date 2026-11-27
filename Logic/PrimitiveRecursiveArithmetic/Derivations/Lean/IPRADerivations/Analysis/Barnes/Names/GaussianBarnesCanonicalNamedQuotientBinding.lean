import IPRADerivations.Analysis.Barnes.Names.GaussianBarnesCanonicalNamed
import IPRADerivations.Analysis.Names.Rates.DifferenceQuotients.GaussianNamedIncrementDifferenceQuotient
import IPRADerivations.Analysis.Names.Rates.DifferenceQuotients.GaussianNamedDifferenceQuotientProperness
import IPRADerivations.Analysis.Names.Arithmetic.GaussianBoundedInverseApartness
import IPRADerivations.Analysis.Gamma.Digamma.TwoShift.Named.GaussianGammaDigammaTwoShiftNamedSize
import IPRADerivations.Analysis.Trigonometry.Arctangent.Turns.GaussianArctangentExponentialPeriod

/-!
# The original named Barnes quotient at rational endpoints

When the endpoint and increment names represent an exact rational
Gaussian configuration, the actual named quotient agrees with the
native quotient. The theorem uses the original evaluator and the
actual named reciprocal even when the supplied names are nonconstant.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNamedQuotientBinding

open_ipra
open ComplexLogarithmRemainder (add normSq)
open GaussianBarnesCanonicalNamedDemand (source data)
open GaussianBoundedConstantProductName (constantF constant_regular)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_trans)
open GaussianRationalHorner (ofGaussian)
open GaussianRationalSyntheticDivision (qone)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "V" => GaussianBarnesCanonicalValue.nameF
local notation "vd" => GaussianBarnesCanonicalValue.data
local notation "G" => GaussianBarnesCanonicalNamed.nameF
local notation "disk" => GaussianBarnesCanonicalLogCofinal.source

def input (F H K : PR 2) (u v x a z h R S B : PTm n) : Fm PTm n :=
  (source F u R ⋏ source H v S) ⋏
    ((disk (add z h) R B ⋏ (disk z S B ⋏ le one (normSq h))) ⋏
      (GaussianNameReciprocal.input K a x ⋏
        (crossEquivalent F constantF u (ofGaussian (add z h) B) ⋏
          (crossEquivalent H constantF v (ofGaussian z B) ⋏ crossEquivalent K constantF x (ofGaussian h B)))))

def nameF (F H K : PR 2) : PR 2 :=
  GaussianNamedIncrementDifferenceQuotient.nameF (G F) (G H) K

def quotientData (F H K : PR 2) (u v x a R S : PTm n) : PTm n :=
  GaussianNamedIncrementDifferenceQuotient.data (G F) (G H) K (data u R) (data v S) x a

theorem inverse_binding (K : PR 2) (x a h B : PTm n)
    (hk : Γ ⊢[PRAAx] GaussianNameReciprocal.input K a x)
    (he : Γ ⊢[PRAAx] crossEquivalent K constantF x (ofGaussian h B))
    (hs : Γ ⊢[PRAAx] GaussianNamedDifferenceQuotient.separated h B) : Γ ⊢[PRAAx]
    crossEquivalent (GaussianNameReciprocal.nameF K) constantF (GaussianNameReciprocal.nameData a x)
      (GaussianNamedDifferenceQuotient.inverse h B) := by
  let δ := ofGaussian h B
  let c := GaussianNamedDifferenceQuotient.inverse h B
  have direct := (GaussianRationalPowerAlgebra.qmul_commutative δ c).eqTrans
    (GaussianNamedDifferenceQuotient.actual_inverse h B hs)
  have exactInverse := GaussianGammaDigammaTwoShiftNamedSize.constant_product δ c qone direct
  have factored := GaussianGammaAdjacentCutoff.multiply_cross K constantF constantF constantF x δ c c
    hk.andE₁ (constant_regular δ) (constant_regular c) (constant_regular c) he
    (cross_refl _ _ (constant_regular c))
  have one := GaussianArctangentExponentialPeriod.constant_one_cross (Γ := Γ) x
  exact GaussianBoundedInverseApartness.reciprocal_matches_inverse K constantF a x c hk.andE₁
    (constant_regular c) hk.andE₂ (cross_trans _ _ _ _ _ _ factored (cross_trans _ _ _ _ _ _ exactInverse one))

theorem binding (F H K : PR 2) (u v x a z h R S B : PTm n)
    (hs : Γ ⊢[PRAAx] input F H K u v x a z h R S B) :
    Γ ⊢[PRAAx] crossEquivalent (nameF F H K) (GaussianNamedDifferenceQuotient.nameF V V)
      (quotientData F H K u v x a R S) (GaussianNamedDifferenceQuotient.data V V (vd (add z h) R B) (vd z S B) h B) := by
  have hu := hs.andE₁.andE₁
  have hv := hs.andE₁.andE₂
  have hplus := hs.andE₂.andE₁.andE₁
  have hbase := hs.andE₂.andE₁.andE₂.andE₁
  have hk := hs.andE₂.andE₂.andE₁
  have sep : Γ ⊢[PRAAx] GaussianNamedDifferenceQuotient.separated h B := .andI hbase.andE₁ hs.andE₂.andE₁.andE₂.andE₂
  have g₁ := GaussianBarnesCanonicalNamed.name_regular F u R hu
  have g₀ := GaussianBarnesCanonicalNamed.name_regular H v S hv
  have v₁ := GaussianBarnesCanonicalValue.regular (add z h) R B hplus
  have v₀ := GaussianBarnesCanonicalValue.regular z S B hbase
  have e₁ := GaussianBarnesCanonicalNamed.bind F u (add z h) R B hu hplus hs.andE₂.andE₂.andE₂.andE₁
  have e₀ := GaussianBarnesCanonicalNamed.bind H v z S B hv hbase hs.andE₂.andE₂.andE₂.andE₂.andE₁
  have numerator := GaussianNamedDifferenceQuotientProperness.difference_proper (G F) V (G H) V
    (data u R) (vd (add z h) R B) (data v S) (vd z S B) g₁ v₁ g₀ v₀ e₁ e₀
  have step := inverse_binding K x a h B hk hs.andE₂.andE₂.andE₂.andE₂.andE₂ sep
  exact GaussianGammaAdjacentCutoff.multiply_cross (GaussianNameReciprocal.nameF K) constantF
    (GaussianNamedDifference.nameF (G F) (G H)) (GaussianNamedDifference.nameF V V) _ _ _ _
    (GaussianNameReciprocal.name_fast K a x hk.andE₁ hk.andE₂) (constant_regular _)
    (GaussianNamedDifference.name_regular _ _ _ _ g₁ g₀) (GaussianNamedDifference.name_regular _ _ _ _ v₁ v₀)
    step numerator

theorem actual_named_Barnes_rational_quotient_binding_closed (F H K : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
      (let u := var 0
       let v := var 1
       let x := var 2
       let a := var 3
       let z := var 4
       let h := var 5
       let R := var 6
       let S := var 7
       let B := var 8
       input F H K u v x a z h R S B ⟶
         crossEquivalent (nameF F H K) (GaussianNamedDifferenceQuotient.nameF V V)
           (quotientData F H K u v x a R S) (GaussianNamedDifferenceQuotient.data V V (vd (add z h) R B) (vd z S B) h B)) :=
  closeUniv 9 (.impI (binding F H K _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNamedQuotientBinding
