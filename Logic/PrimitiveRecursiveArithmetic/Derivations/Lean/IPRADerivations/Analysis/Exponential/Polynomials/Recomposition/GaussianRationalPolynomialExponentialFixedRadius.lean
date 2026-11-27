import IPRADerivations.Analysis.Exponential.Polynomials.Recomposition.GaussianRationalPolynomialExponentialDilation
import IPRADerivations.Analysis.RationalArithmetic.Directions.GaussianRationalTravelScaling

/-!
# Exponential recomposition at a positive rational radius

Normalize the original Gaussian rational input by the certified radius A/D.
The proof keeps the original exponential data and original recomposition
value at that input. Its error uses the normalized displacement DH/(AB)
and the coefficient mass weighted at A/D.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalPolynomialExponentialFixedRadius

open_ipra
open GaussianDominantPairAlgebra (radiusPoint radius_bounded)
open GaussianEuclideanDistanceName (fraction)
open GaussianGammaCanonicalExponent (constantF)
open GaussianNamedInverseRate (independentRate subst_independentRate)
open GaussianRationalHorner (canonical qmul qzero positive_product)
open GaussianRationalMetric (bounded)
open GaussianRationalPolynomialDilation (weightedNorm)
open GaussianRationalPolynomialExponentialRecomposition (nameF data value numerator denominator subst_data subst_value)
open GaussianRationalTravelScaling (ratio)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open RationalArgmin (rationalLE)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem normalized_bound (w A D H B : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (hB : Γ ⊢[PRAAx] le one B) (hw : Γ ⊢[PRAAx] bounded w H B) : Γ ⊢[PRAAx]
    bounded (ratio A D w) (D*H) (A*B) :=
  GaussianRationalReciprocal.bounded_product (radiusPoint D A) w D A H B hA hB (radius_bounded D A hA) hw

theorem normalized_roundtrip (w A D : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (hD : Γ ⊢[PRAAx] le one D) (hCan : Γ ⊢[PRAAx] canonical w) : Γ ⊢[PRAAx]
    qmul (radiusPoint A D) (ratio A D w) ≐ w :=
  GaussianRationalInvertibleNorm.qmul_roundtrip (radiusPoint A D) (radiusPoint D A) w
    ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
      (GaussianRationalTravelScaling.inverse_radius A D hA hD)) hCan

private theorem query_rate_congr (C N m u w E K : PTm n)
    (he : Γ ⊢[PRAAx] u ≐ w) (h : Γ ⊢[PRAAx] independentRate nameF constantF (data C u) (value C N m u) E K) :
    Γ ⊢[PRAAx] independentRate nameF constantF (data C w) (value C N m w) E K := by
  simpa only [subst_independentRate,subst_data,subst_value,Syn.subst_var,Matrix.cons_val] using
    Prf.eqSubst (independentRate nameF constantF (data (var 0) (var 1))
      (value (var 0) (var 2) (var 3) (var 1)) (var 4) (var 5) : Fm PTm 6)
      ![C,u,N,m,E,K] ![C,w,N,m,E,K]
      (fun i => by
        fin_cases i
        · exact .eqRefl _
        · exact he
        · exact .eqRefl _
        · exact .eqRefl _
        · exact .eqRefl _
        · exact .eqRefl _)
      (by simpa only [subst_independentRate,subst_data,subst_value,Syn.subst_var,Matrix.cons_val] using h)

theorem fixed_radius_rate (C N m w A D H B L : PTm n)
    (hC : Γ ⊢[PRAAx] length C ≐ succ N) (hZero : Γ ⊢[PRAAx] entry C N ≐ qzero)
    (hm : Γ ⊢[PRAAx] le m (m*N))
    (hA : Γ ⊢[PRAAx] le one A) (hD : Γ ⊢[PRAAx] le one D) (hB : Γ ⊢[PRAAx] le one B)
    (hHB : Γ ⊢[PRAAx] le (D*H) (A*B)) (hSmall : Γ ⊢[PRAAx] le (two*(L*(D*H))) (A*B))
    (hMass : Γ ⊢[PRAAx] rationalLE (weightedNorm C N (radiusPoint A D)) (fraction L one))
    (hCan : Γ ⊢[PRAAx] canonical w) (hw : Γ ⊢[PRAAx] bounded w H B) : Γ ⊢[PRAAx]
    independentRate nameF constantF (data C w) (value C N m w)
      (numerator m L (pw (num 3) L) (D*H)) (denominator m (A*B)) := by
  let z := ratio A D w
  let u := qmul (radiusPoint A D) z
  let E := numerator m L (pw (num 3) L) (D*H)
  let K := denominator m (A*B)
  exact query_rate_congr C N m u w E K (normalized_roundtrip w A D hA hD hCan)
    (GaussianRationalPolynomialExponentialDilation.uniform_rate C N m (radiusPoint A D) z (D*H) (A*B) L
      hC hZero hm (positive_product A B hA hB) hHB hSmall hMass (normalized_bound w A D H B hA hB hw))

end LeanProofs.IPRA.Analysis.GaussianRationalPolynomialExponentialFixedRadius
