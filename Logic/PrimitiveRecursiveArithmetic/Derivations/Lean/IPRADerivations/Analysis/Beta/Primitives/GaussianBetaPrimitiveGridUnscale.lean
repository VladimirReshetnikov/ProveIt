import IPRADerivations.Analysis.Beta.Primitives.GaussianBetaPrimitiveCompactGridAccuracy
import IPRADerivations.Analysis.Beta.Endpoints.GaussianBetaUpperEndpointInverse
import IPRADerivations.Analysis.Gamma.EulerProducts.Factorials.GaussianGammaFactorialValues

/-!
# Dyadic error for the original unscaled beta quadrature

The degree used to scale the primitive endpoint difference cancels the
reciprocal degree in the exact telescoped sum. A computed increase in
the dyadic demand pays for the degree in the norm estimate, yielding a
bound for the original weighted beta quadrature itself.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaPrimitiveGridUnscale

open_ipra
open GaussianRationalHorner (qmul qmul_canonical)
open GaussianRationalSyntheticDivision (qone qmul_congr)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianRationalMetric (qsub distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianNamedNaturalScale (natural_point_bound)
open GaussianRationalRoundedPower (multiplication_difference)
open GaussianReciprocalHorner (qmul_associative qmul_one_right)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianBetaPrimitiveGridTelescope (gridEndpoint quadratureScaled)
open GaussianBetaKernelGridComparison (evaluatorF sampleDataBeta)
open GaussianBetaPrimitiveCompactGridAccuracy (source cells precisionAt original_grid_dyadic_accuracy_at)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianGammaEulerShiftLimit (reciprocalPoint)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def quadrature (p z B a C E M N : PTm n) : PTm n :=
  GaussianCompactRiemannName.quadrature evaluatorF p M a C E (sampleDataBeta z B N)
def scaledEndpoint (i p z B a C E M N : PTm n) : PTm n :=
  qmul (naturalPoint N) (gridEndpoint i p z B a C E M N)
def demand (t N : PTm n) : PTm n := GaussianFastValueCut.exponent N t

private theorem fraction_one (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] fraction one N ≐ reciprocalPoint N :=
  (GaussianPositiveRationalLogarithm.fraction_product one N hN).eqSymm.eqTrans
    ((qmul_congr GaussianGammaFactorialValues.natural_one (.eqRefl _)).eqTrans
      ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
        (qmul_one_right _ (GaussianRationalHorner.ofGaussian_canonical _ _ hN))))

theorem quadrature_unscale (p z B a C E M N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] qmul (naturalPoint N) (quadratureScaled p z B a C E M N) ≐ quadrature p z B a C E M N := by
  let Q := quadrature p z B a C E M N
  have right : Γ ⊢[PRAAx] GaussianRationalHorner.canonical Q := by
    unfold Q quadrature GaussianCompactRiemannName.quadrature
    exact qmul_canonical _ _
  have inv : Γ ⊢[PRAAx] qmul (naturalPoint N) (fraction one N) ≐ qone :=
    (qmul_congr (.eqRefl _) (fraction_one N hN)).eqTrans
      (GaussianBetaUpperEndpointInverse.natural_reciprocal_one N hN)
  exact (qmul_associative (naturalPoint N) (fraction one N) Q).eqSymm.eqTrans
    ((qmul_congr inv (.eqRefl _)).eqTrans
      ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans (qmul_one_right _ right)))

theorem original_dyadic_accuracy (t p z R B A a C E T M N : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A a C E T N)
    (hm : Γ ⊢[PRAAx] le (cells (demand t N) z R B C E T N) M)
    (hp : Γ ⊢[PRAAx] le (precisionAt (demand t N) z B N M) p) :
    Γ ⊢[PRAAx] distanceBounded
      (qsub (scaledEndpoint M p z B a C E M N) (scaledEndpoint zero p z B a C E M N))
      (quadrature p z B a C E M N) one (unit t) := by
  let τ := demand t N
  let S := naturalPoint N
  let X := gridEndpoint M p z B a C E M N
  let Y := gridEndpoint zero p z B a C E M N
  let Q := quadratureScaled p z B a C E M N
  have hτ := unit_positive (Γ := Γ) τ
  have raw := original_grid_dyadic_accuracy_at τ p z R B A a C E T M N h hm hp
  have product := GaussianRationalReciprocal.bounded_product S (qsub (qsub X Y) Q) N one one (unit τ)
    (le_refl one) hτ (natural_point_bound N) raw
  have scaled : Γ ⊢[PRAAx] distanceBounded (qmul S (qsub X Y)) (qmul S Q) N (unit τ) :=
    GaussianRationalReciprocal.bound_congr (multiplication_difference S (qsub X Y) Q).eqSymm
      (by ipra_ring) (one_mul _) product
  have cmp : Γ ⊢[PRAAx] le (N*unit t) (one*unit τ) :=
    le_congr (.eqRefl _) (one_mul _).eqSymm (GaussianFastValueCut.query_budget N t)
  exact distance_congr (multiplication_difference S X Y).eqSymm
    (quadrature_unscale p z B a C E M N h.andE₂.andE₂.andE₁) (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ hτ (unit_positive t) cmp scaled)

theorem original_unscaled_beta_quadrature_dyadic_accuracy_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 12
    ((source (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 11) ⋏
      le (cells (demand (var 0) (var 11)) (var 2) (var 3) (var 4) (var 7) (var 8) (var 9) (var 11)) (var 10) ⋏
      le (precisionAt (demand (var 0) (var 11)) (var 2) (var 4) (var 11) (var 10)) (var 1)) ⟶
      distanceBounded
        (qsub (scaledEndpoint (var 10) (var 1) (var 2) (var 4) (var 6) (var 7) (var 8) (var 10) (var 11))
          (scaledEndpoint zero (var 1) (var 2) (var 4) (var 6) (var 7) (var 8) (var 10) (var 11)))
        (quadrature (var 1) (var 2) (var 4) (var 6) (var 7) (var 8) (var 10) (var 11)) one (unit (var 0))) :=
  closeUniv 12 (.impI (original_dyadic_accuracy _ _ _ _ _ _ _ _ _ _ _ _
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBetaPrimitiveGridUnscale
