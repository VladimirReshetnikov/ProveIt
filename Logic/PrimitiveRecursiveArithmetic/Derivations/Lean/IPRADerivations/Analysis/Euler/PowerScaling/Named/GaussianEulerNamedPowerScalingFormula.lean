import IPRADerivations.Analysis.Euler.PowerScaling.Named.GaussianEulerNamedPowerScalingParameter

/-!
# The actual Gamma-side formula for positive named scaling parameters

The formula is the ordinary product of the named positive reciprocal,
the original exponential of -(z/r) log(c), and the original Gamma
sampler at the certified right-half-plane name z/r.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerNamedPowerScalingFormula

open_ipra
open GaussianEulerNamedPowerScalingParameter (named_half_plane)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameRingLaws (negativeF negativeData negative_fast)
open GaussianEuclideanDistanceName (pointCN)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (F G : PR 2) (z R B A x E T y H J : PTm n) : Fm PTm n :=
  GaussianEulerNamedPowerScalingParameter.source G z R B A y H J ⋏
    GaussianNamedPositiveLogarithm.source F x E T

abbrev exponentF (F G : PR 2) : PR 2 :=
  negativeF (multiplyF (GaussianEulerNamedPowerScalingParameter.nameF G) (GaussianNamedPositiveLogarithm.nameF F))

def exponentData (F G : PR 2) (z R B x E y H : PTm n) : PTm n :=
  negativeData (multiplyData (GaussianEulerNamedPowerScalingParameter.nameF G) (GaussianNamedPositiveLogarithm.nameF F)
    (GaussianEulerNamedPowerScalingParameter.data z R B y H) (GaussianNamedPositiveLogarithm.data x E))

abbrev powerF (F G : PR 2) : PR 2 := GaussianRadiusExponentialName.nameF (exponentF F G)
def powerData (F G : PR 2) (z R B x E y H : PTm n) : PTm n :=
  GaussianGammaFiniteApproximantName.exponentialInputData (exponentF F G) (exponentData F G z R B x E y H)

abbrev gammaF (G : PR 2) : PR 2 := GaussianNamedGamma.nameF (GaussianEulerNamedPowerScalingParameter.nameF G)
def gammaData (z R B A y H J : PTm n) : PTm n :=
  GaussianNamedGamma.data (GaussianEulerNamedPowerScalingParameter.data z R B y H) (J*A)

abbrev nameF (F G : PR 2) : PR 2 :=
  multiplyF (GaussianNamedPositiveReciprocal.nameF G) (multiplyF (powerF F G) (gammaF G))
def data (F G : PR 2) (z R B A x E y H J : PTm n) : PTm n :=
  multiplyData (GaussianNamedPositiveReciprocal.nameF G) (multiplyF (powerF F G) (gammaF G))
    (GaussianNamedPositiveReciprocal.data y H)
    (multiplyData (powerF F G) (gammaF G) (powerData F G z R B x E y H) (gammaData z R B A y H J))

theorem name_regular (F G : PR 2) (z R B A x E T y H J : PTm n)
    (hs : Γ ⊢[PRAAx] source F G z R B A x E T y H J) :
    Γ ⊢[PRAAx] pointCN (nameF F G) (data F G z R B A x E y H J) := by
  let P := GaussianEulerNamedPowerScalingParameter.nameF G
  let L := GaussianNamedPositiveLogarithm.nameF F
  let a := GaussianEulerNamedPowerScalingParameter.data z R B y H
  let b := GaussianNamedPositiveLogarithm.data x E
  let expInput := exponentData F G z R B x E y H
  have hHalf := named_half_plane G z R B A y H J hs.andE₁
  have hLog := GaussianNamedPositiveLogarithm.name_regular F x E T hs.andE₂
  have hExp : Γ ⊢[PRAAx] pointCN (exponentF F G) expInput :=
    negative_fast (multiplyF P L) (multiplyData P L a b) (multiply_fast P L a b hHalf.andE₁ hLog)
  have hRadius := GaussianGammaFiniteApproximantName.exponential_input (exponentF F G) expInput hExp
  have power := GaussianRadiusExponentialName.name_regular (exponentF F G) _ expInput hRadius
  have gamma := GaussianNamedGamma.name_regular P a (J*A) hHalf
  have inverse := GaussianNamedPositiveReciprocal.name_regular G y H J hs.andE₁.andE₂.andE₂
  exact multiply_fast _ _ _ _ inverse (multiply_fast _ _ _ _ power gamma)

theorem actual_named_Gamma_power_scaling_formula_regular_closed (F G : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
      (source F G (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) ⟶
        pointCN (nameF F G) (data F G (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 7) (var 8) (var 9))) :=
  closeUniv 10 (.impI (name_regular F G _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerNamedPowerScalingFormula
