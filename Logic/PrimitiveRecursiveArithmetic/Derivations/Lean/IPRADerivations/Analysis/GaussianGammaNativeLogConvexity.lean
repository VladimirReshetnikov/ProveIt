import IPRADerivations.Analysis.GaussianGammaNativeLogConvexityCore
import IPRADerivations.Analysis.GaussianGammaEulerRationalLogConvergence
import IPRADerivations.Analysis.GaussianNamedRateRadius

/-!
# Weighted log convexity of the original positive rational Gamma names

Use the certified cofinal rates of the three original inverse Euler
approximants. A common cutoff and rate coefficient suffice for the
finite weighted comparison to hold at the native limits.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaNativeLogConvexity

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaEulerRationalHeadConvexity (weight barycenter)
open GaussianGammaEulerRationalLogConvergence (actual_rate rateCoefficient)
open GaussianGammaEulerRationalLogMargin (cutoff cutoff_positive denominator_positive)
open GaussianGammaEulerInverseConvergence (coefficientDenominator)
open GaussianGammaNativeLogConvexityCore (familyRate nativeCenterData nativeWeightedData weighted_convexity_of_family_rates)
open GaussianNameArithmetic (addF)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianNaturalScaleProductName (productF)
open GaussianRationalHorner (positive_product)
open GaussianStirlingGammaLogarithm (source logGammaF logGammaData)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "G" => productF logGammaF

theorem family_rate (a b K C : PTm n) (hs : Γ ⊢[PRAAx] source a b)
    (hK : Γ ⊢[PRAAx] le (cutoff a b) K) (hC : Γ ⊢[PRAAx] le (rateCoefficient a b) C) :
    Γ ⊢[PRAAx] familyRate a b K C := by
  refine .allI (.impI ?_)
  let sh (t : PTm n) := Syn.shift t
  let Δ := le (sh K) (var 0) :: Γ.map Fm.shift
  let a' := sh a
  let b' := sh b
  let N : PTm (n+1) := var 0
  let L := GaussianGammaReciprocalInverse.lambdaNumerator a' one
  let D := coefficientDenominator a' one N
  have sa : Δ ⊢[PRAAx] source a' b' := by simpa [Δ,Fm.shift,Syn.shift,sh,a',b'] using hs.shift.wk
  have ka : Δ ⊢[PRAAx] le (cutoff a' b') (sh K) := by
    simpa [Δ,Fm.shift,Syn.shift,sh,a',b'] using hK.shift.wk
  have ca : Δ ⊢[PRAAx] le (rateCoefficient a' b') (sh C) := by
    simpa [Δ,Fm.shift,Syn.shift,sh,a',b'] using hC.shift.wk
  have inp : Δ ⊢[PRAAx] GaussianGammaEulerRationalLogMargin.source N a' b' :=
    .andI sa (le_trans ka Prf.hyp0)
  have hi := cutoff_positive N a' b' inp
  have lp : Δ ⊢[PRAAx] le one L :=
    GaussianPolynomialPerturbation.power_positive _ _ (le_refl one)
  have grow : Δ ⊢[PRAAx] le N D :=
    le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right N (positive_product _ _ lp lp))
  have h := LeanProofs.IPRA.AnalyticNumberTheory.PhiLower.le_mul_mono ca grow
  exact GaussianNamedRateRadius.weaken GaussianGammaEulerRationalLog.nameF logGammaF
    (GaussianGammaEulerRationalLog.data N a' b') (logGammaData a' b') (rateCoefficient a' b') D (sh C) N
    (denominator_positive N a' b' inp) hi h (actual_rate N a' b' inp)

theorem weighted_convexity (a d b r s : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hd : Γ ⊢[PRAAx] le one d) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] realOrder G (addF G G) (nativeCenterData a d b r s) (nativeWeightedData a d b r s) := by
  let z := barycenter a d r s
  let w := weight r s*b
  let K := cutoff a b+cutoff d b+cutoff z w
  let C := rateCoefficient a b+rateCoefficient d b+rateCoefficient z w
  have hz : Γ ⊢[PRAAx] source z w :=
    .andI (le_trans (positive_product _ _ (zero_lt_succ r) ha) (le_add_right _ _))
      (positive_product _ _ (zero_lt_succ (r+s)) hb)
  apply weighted_convexity_of_family_rates a d b r s K C ha hd hb
  · exact family_rate a b K C (.andI ha hb)
      (le_trans (le_add_right _ _) (le_add_right _ _)) (le_trans (le_add_right _ _) (le_add_right _ _))
  · exact family_rate d b K C (.andI hd hb)
      (le_trans (le_add_left _ _) (le_add_right _ _)) (le_trans (le_add_left _ _) (le_add_right _ _))
  · exact family_rate z w K C hz (le_add_left _ _) (le_add_left _ _)

theorem actual_positive_rational_log_Gamma_convexity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((le one (var 0) ⋏ (le one (var 1) ⋏ le one (var 2))) ⟶ realOrder G (addF G G)
      (nativeCenterData (var 0) (var 1) (var 2) (var 3) (var 4))
      (nativeWeightedData (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (weighted_convexity _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaNativeLogConvexity
