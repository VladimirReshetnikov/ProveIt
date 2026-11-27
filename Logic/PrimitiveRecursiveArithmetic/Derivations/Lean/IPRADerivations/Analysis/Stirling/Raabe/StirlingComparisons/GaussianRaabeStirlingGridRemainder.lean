import IPRADerivations.Analysis.Stirling.Raabe.StirlingComparisons.GaussianRaabeStirlingRemainder
import IPRADerivations.Analysis.Stirling.Raabe.StirlingComparisons.GaussianRaabeStirlingMesh
import IPRADerivations.Analysis.Stirling.Raabe.UnitPanels.GaussianRaabeUnitGridRecurrence

/-!
# The original Stirling remainder on a distant Raabe unit grid
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianRaabeStirlingGridRemainder

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (quadrature sampleBody sampleData sample_body_at)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRaabeStirlingRemainder (constantSample model)
open GaussianRaabeUnitGridRecurrence (logGammaEvaluator log_gamma_at)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalNaturalScale (natScale_as_product)
open GaussianRationalQuadratureDifference (differenceBody difference_body_at weighted_difference)
open GaussianRationalRiemannRefinement (leftSum constantBody constant_entry constant_sum termsDistance)
open GaussianRationalSyntheticDivision (qmul_congr qsub_congr qone)
open GaussianStirlingOddCoefficients (fraction_equal fraction_product)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)
local notation "F" => GaussianRaabeStirlingMesh.evaluator

def cost (N A D : PTm n) : PTm n := num 18+two*((A+D)*N)
def numerator (p N A D : PTm n) : PTm n := two*D*unit p+cost N A D*A
def denominator (p A : PTm n) : PTm n := A*unit p

ipra_subst cost [two, one]

ipra_subst numerator [two, one]

ipra_subst denominator

private theorem unit_constant (p N D w : PTm n) (hN : Γ ⊢[PRAAx] le one N) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] leftSum constantBody N (constantSample p w) D D ≐ constantSample p w := by
  let c := constantSample p w
  have hc : Γ ⊢[PRAAx] GaussianRationalHorner.canonical c :=
    GaussianNameArithmetic.multiply_canonical _ _ _ _ p
  have sum := (constant_sum (Γ := Γ) c N).eqTrans (natScale_as_product N c)
  have pair : Γ ⊢[PRAAx] qmul (fraction one N) (fraction N one) ≐ qone :=
    (fraction_product one N N one hN (le_refl one)).eqTrans
      ((fraction_equal (one*N) (N*one) one one
        (positive_product _ _ hN (le_refl one)) (le_refl one) (by ipra_ring)).eqTrans
          ((GaussianEulerDecayFactorBounds.fraction_is_radius_point one one (le_refl one)).eqTrans
            GaussianDominantPairAlgebra.radius_one))
  exact (qmul_congr (GaussianRaabeCenteredMesh.unit_weight N D hN hD) sum).eqTrans
    ((GaussianReciprocalHorner.qmul_associative (fraction one N) (fraction N one) c).eqSymm.eqTrans
      ((qmul_congr pair (.eqRefl c)).eqTrans (GaussianPolynomialDeterminantTerms.one_mul_canonical c hc)))

private theorem row_budget (U A D a d C : PTm n)
    (mass : Γ ⊢[PRAAx] le (d*A) (D*a)) (clock : Γ ⊢[PRAAx] le (num 18+two*a) C) :
    Γ ⊢[PRAAx] le ((two*d*U+(num 18+two*a)*a)*(A*U)) ((two*D*U+C*A)*(a*U)) := by
  ipra_le 𝔞(two*U*U)*sl mass+𝔞(A*a*U)*sl clock

private theorem cell_error (i p N A D w : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hD : Γ ⊢[PRAAx] le one D) (hDA : Γ ⊢[PRAAx] le D A)
    (hi : Γ ⊢[PRAAx] le i N) :
    Γ ⊢[PRAAx] distanceBounded
      (inst2 (differenceBody (sampleBody logGammaEvaluator) (sampleBody F)) i
        (pairT (sampleData p N A D D zero) (sampleData p N A D D zero)))
      (constantSample p w) (numerator p N A D) (denominator p A) := by
  let a := A*N+D*i
  let d := D*N
  let U := unit p
  let x := sampleData p N A D D zero
  have hd : Γ ⊢[PRAAx] le one d := positive_product _ _ hD hN
  have hda : Γ ⊢[PRAAx] le d a := le_trans (mul_le_mul_right N hDA) (le_add_right (A*N) (D*i))
  have hA := le_trans hD hDA
  have ha := le_trans hd hda
  have hU := unit_positive (Γ := Γ) p
  have mass : Γ ⊢[PRAAx] le (d*A) (D*a) := by
    dsimp only [a,d]
    ipra_le 𝔞(D)*𝔞(D)*𝔞(i)
  have cap : Γ ⊢[PRAAx] le a ((A+D)*N) :=
    le_congr (.eqRefl _) (by ipra_ring)
      (add_le_add₂ (le_refl (A*N)) (le_mul_mono (le_refl D) hi))
  have late : Γ ⊢[PRAAx] le (num 18+two*a) (cost N A D) :=
    add_le_add₂ (le_refl (num 18)) (le_mul_mono (le_refl two) cap)
  have original := GaussianRaabeStirlingRemainder.sample_error p a d w hd hda
  let g := ap2 GaussianStirlingGammaLogarithm.logGammaF p (GaussianStirlingGammaLogarithm.logGammaData a d)
  let v := GaussianRaabeStirlingCell.elementary p a d
  let c := constantSample p w
  have budget : Γ ⊢[PRAAx] le (GaussianRaabeStirlingRemainder.numerator p a d*denominator p A)
      (numerator p N A D*GaussianRaabeStirlingRemainder.denominator p a) :=
    row_budget U A D a d (cost N A D) mass late
  have target : Γ ⊢[PRAAx] distanceBounded g (model p a d w) (numerator p N A D) (denominator p A) :=
    distance_radius_mono g (model p a d w) (GaussianRaabeStirlingRemainder.numerator p a d)
      (GaussianRaabeStirlingRemainder.denominator p a) (numerator p N A D) (denominator p A)
      (positive_product _ _ ha hU) (positive_product _ _ hA hU) budget original
  have subtracted : Γ ⊢[PRAAx] distanceBounded (qsub g v) c (numerator p N A D) (denominator p A) :=
    GaussianRationalReciprocal.bound_congr (GaussianRationalInverseQuadraticAlgebra.subtract_sum g v c).eqSymm
      (.eqRefl (numerator p N A D)) (.eqRefl (denominator p A)) target
  have a₁ := (sample_body_at (Γ := Γ) logGammaEvaluator i p N A D D zero).eqTrans (log_gamma_at p a d zero)
  have a₂ := (sample_body_at (Γ := Γ) F i p N A D D zero).eqTrans
    (GaussianRaabeStirlingMesh.evaluator_at p a d zero)
  have read : Γ ⊢[PRAAx] inst2 (differenceBody (sampleBody logGammaEvaluator) (sampleBody F)) i (pairT x x) ≐ qsub g v :=
    (difference_body_at (Γ := Γ) (sampleBody logGammaEvaluator) (sampleBody F) i x x).eqTrans (qsub_congr a₁ a₂)
  exact distance_congr read.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) subtracted

theorem quadrature_error (p N A D w : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hD : Γ ⊢[PRAAx] le one D) (hDA : Γ ⊢[PRAAx] le D A) :
    Γ ⊢[PRAAx] distanceBounded
      (qsub (quadrature logGammaEvaluator p N A D D zero) (quadrature F p N A D D zero))
      (constantSample p w) (numerator p N A D) (denominator p A) := by
  let f := sampleBody logGammaEvaluator
  let g := sampleBody F
  let x := sampleData p N A D D zero
  let c := constantSample p w
  let V := numerator p N A D
  let B := denominator p A
  have rows : Γ ⊢[PRAAx] termsDistance (differenceBody f g) constantBody N (pairT x x) c V B := by
    refine .allI (.impI ?_)
    let s (t : PTm n) := Syn.shift t
    let Δ := lt (var 0) (s N)::Γ.map Fm.shift
    have sn : Δ ⊢[PRAAx] le one (s N) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hN.shift.wk
    have sd : Δ ⊢[PRAAx] le one (s D) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hD.shift.wk
    have sa : Δ ⊢[PRAAx] le (s D) (s A) := by simpa [Δ,s,Fm.shift,Syn.shift] using hDA.shift.wk
    have i : Δ ⊢[PRAAx] le (var 0) (s N) := le_of_lt Prf.hyp0
    simpa only [Δ,s,f,g,x,c,V,B,Syn.shift,subst_pairT,GaussianCompactRiemannName.subst_sampleData,
      ConciseIPRA.PTm.subst_zero,constant_entry,GaussianRaabeStirlingRemainder.subst_constantSample,subst_numerator,
      subst_denominator] using cell_error (var 0) (s p) (s N) (s A) (s D) (s w) sn sd sa i
  have hb : Γ ⊢[PRAAx] le one B := positive_product _ _ (le_trans hD hDA) (unit_positive p)
  have raw := GaussianCompactScalarMajorant.common_mesh_distance (differenceBody f g) constantBody
    N (pairT x x) c D D V B hN hD hb rows
  have old := distance_congr (weighted_difference f g N x x D D).eqSymm (unit_constant p N D w hN hD)
    (.eqRefl _) (.eqRefl _) raw
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hD hb) hb
    (by change Γ ⊢[PRAAx] le ((D*V)*B) (V*(D*B)); exact le_of_eq_add (d := zero) (by ipra_ring)) old

end LeanProofs.IPRA.Analysis.GaussianRaabeStirlingGridRemainder
