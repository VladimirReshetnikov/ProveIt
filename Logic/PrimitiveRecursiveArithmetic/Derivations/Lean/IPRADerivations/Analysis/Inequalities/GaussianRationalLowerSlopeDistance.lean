import IPRADerivations.Analysis.Beta.Endpoints.GaussianBetaRowMonomialReference
import IPRADerivations.Analysis.Gamma.Digamma.ElementaryBounds.GaussianGammaDigammaHarmonicCells
import IPRADerivations.Analysis.Integration.Partitions.GaussianRationalSignedPanelTailDistance
import IPRADerivations.Analysis.Exponential.PositiveAxis.GaussianNamedPositiveExponentialOrder
import IPRADerivations.Analysis.Stirling.Expansions.GaussianStirlingOddCoefficients

/-!
# Recover a rational input distance from a lower scalar slope

An observed lower comparison with the exact input gap, scaled by
a positive numerical divisor, bounds the input distance by the
observed output distance and the allowed scalar comparison error.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalLowerSlopeDistance

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianNamedPositiveExponentialOrder (scalar_coordinate_distance)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_radius_mono)
open GaussianRationalHorner (positive_product qadd)
open GaussianRationalMetric (distanceBounded)
open RationalGaussianEmbedding (scalarZero scalar_zero_represents)
open RationalValueBounds (upper upper_congr upper_mono upper_of_radius upper_triangle)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def margin (a b c d M : PTm n) : PTm n := fraction (monus (b*c) (d*a)) (M*b*d)

private theorem cleared (W B C D : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] upper (fstT (fraction W B)) scalarZero C D) :
    Γ ⊢[PRAAx] le (D*W) (C*B) := by
  let l := ZT.ofNat (D*one)*ZT.ofNat W
  let r := ZT.ofNat (D*B)*ZT.ofNat zero+ZT.ofNat (C*B*one)
  have signed : Γ ⊢[PRAAx] zle l r :=
    RationalUpperRepresentation.upper_from_representations _ _ B one C D _ _
      (GaussianGammaDigammaHarmonicCells.point_fraction_represents W B hB) (scalar_zero_represents one) h
  have e := zle_toZ signed
  apply le_of_eq_add (d := PolynomialBisection.slack l r)
  apply deriveNat
  simp only [l,r,PolynomialBisection.slack,ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat] at e ⊢
  ipra_simps
  linear_combination -e

theorem input_distance (a b c d M u v H A D : PTm n)
    (hb : Γ ⊢[PRAAx] le one b) (hd : Γ ⊢[PRAAx] le one d) (hM : Γ ⊢[PRAAx] le one M)
    (hD : Γ ⊢[PRAAx] le one D) (horder : Γ ⊢[PRAAx] le (d*a) (b*c))
    (hgap : Γ ⊢[PRAAx] upper (fstT (qadd u (margin a b c d M))) (fstT v) A D)
    (hobs : Γ ⊢[PRAAx] distanceBounded u v H D) :
    Γ ⊢[PRAAx] distanceBounded (fraction a b) (fraction c d) (M*(A+H)) D := by
  let w := monus (b*c) (d*a)
  let e := M*b*d
  have den := positive_product _ _ hb hd
  have he := positive_product _ _ (positive_product _ _ hM hb) hd
  have back := upper_of_radius _ _ _ _ (scalar_coordinate_distance v u H D hD (distance_symmetric _ _ _ _ hD hobs))
  have amount := upper_mono _ _ _ _ (A+H) D (positive_product _ _ hD hD)
    (upper_triangle _ _ _ _ _ _ _ hgap back) (le_of_eq_add (d := zero) (by ipra_ring))
  have gap0 : Γ ⊢[PRAAx] upper (fstT (fraction w e)) scalarZero (A+H) D :=
    upper_congr (.eqRefl _) RationalGaussianRealPart.real_zero (.eqRefl _) (.eqRefl _)
      (GaussianRationalSignedPanelTailDistance.real_add_cancel u (margin a b c d M) _ _ amount)
  have scale := cleared w e (A+H) D he gap0
  have gap_eq : Γ ⊢[PRAAx] (b*d)*(c*b) ≐ (b*d)*(a*d)+w*d*b := by
    apply deriveNat
    have delta := natEq (eq_add_of_le horder)
    dsimp only [w]
    ipra_simps
    linear_combination (Groth.ι (Q.mk Γ b)*Groth.ι (Q.mk Γ d))*delta
  have raw := GaussianBetaRowMonomialReference.fraction_gap_distance c d a b w (b*d) hd hb den gap_eq
  have exactGap := distance_congr (GaussianStirlingOddCoefficients.fraction_embed c d hd)
    (GaussianStirlingOddCoefficients.fraction_embed a b hb) (.eqRefl _) (.eqRefl _) raw
  exact distance_radius_mono _ _ _ _ _ _ den hD (le_congr (by ipra_ring) (by dsimp only [e]; ipra_ring) scale)
    (distance_symmetric _ _ _ _ den exactGap)

theorem actual_rational_input_distance_from_lower_slope_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (((le one (var 1) ⋏ le one (var 3)) ⋏ (le one (var 4) ⋏ le one (var 9))) ⟶
      (le (var 3*var 0) (var 1*var 2) ⋏
        upper (fstT (qadd (var 5) (margin (var 0) (var 1) (var 2) (var 3) (var 4)))) (fstT (var 6)) (var 8) (var 9)) ⟶
      distanceBounded (var 5) (var 6) (var 7) (var 9) ⟶
      distanceBounded (fraction (var 0) (var 1)) (fraction (var 2) (var 3)) (var 4*(var 8+var 7)) (var 9)) :=
  closeUniv 10 (.impI (.impI (.impI (input_distance _ _ _ _ _ _ _ _ _ _
    Prf.hyp0.wk.wk.andE₁.andE₁ Prf.hyp0.wk.wk.andE₁.andE₂
    Prf.hyp0.wk.wk.andE₂.andE₁ Prf.hyp0.wk.wk.andE₂.andE₂ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianRationalLowerSlopeDistance
