import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.Arctangent.GaussianBinetArctangentQuadratureBound
import IPRADerivations.Analysis.Stirling.Binet.WeightedIntegrals.GaussianBinetReciprocalRows
import IPRADerivations.Analysis.Stirling.Binet.Laplace.Strips.GaussianBinetLaplaceStripCutoff
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianCompactScalarMajorant

/-!
# The linear term of the original Binet arctangent sampler

The exact resolvent differs from one over the argument by a product
with two powers of the time tag. The actual compact quadrature
multiplies the uniform row bound by the interval width. The
resulting cubic error holds at every observation clock.
-/

set_option autoImplicit false
set_option maxHeartbeats 710000

namespace LeanProofs.IPRA.Analysis.GaussianBinetArctangentLinearApproximation

open_ipra
open GaussianBinetArctangentQuadrature (evaluatorF fixedData nameF data evaluator_at)
open GaussianBinetArctangentResolvent (polynomial value)
open GaussianCompactRiemannName (grid sampleBody sampleData sample_body_at quadrature mesh mesh_positive precision)
open GaussianLogGammaEulerHead (argument)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalCoefficientScaling (qmul_add)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)
open GaussianRationalFiniteSum (sum)
open GaussianRationalHorner (canonical qadd qmul qmul_canonical ofGaussian_canonical positive_product)
open GaussianRationalLowerBounds (name_lower inverse_bound)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalReciprocal (reciprocal reciprocal_identity reciprocal_canonical bound_congr bounded_product)
open GaussianRationalRiemannRefinement (termsDistance constantBody constant_entry constant_sum weight weight_repetition)
open GaussianRationalSyntheticDivision (qone qadd_congr qmul_congr qadd_sub_cancel qsub_congr)
open GaussianReciprocalHorner (qmul_associative qmul_one_right)
open GaussianRightHalfPlaneLogarithm (source)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def cube (u : PTm n) : PTm n := u*u*u
def linear (X Y D sign A B : PTm n) : PTm n := qmul (fraction A B) (reciprocal (argument X Y D sign))

ipra_subst cube
ipra_subst linear [GaussianLogGammaEulerRepresentation.subst_argument]

private theorem right_distribute (a b c : PTm n) :
    Γ ⊢[PRAAx] qadd (qmul a c) (qmul b c) ≐ qmul (qadd a b) c :=
  (qadd_congr (qmul_commutative a c) (qmul_commutative b c)).eqTrans
    ((qmul_add c a b).eqSymm.eqTrans (qmul_commutative c (qadd a b)))

private theorem correction (z w : PTm n) (hz : Γ ⊢[PRAAx] canonical z)
    (hzI : Γ ⊢[PRAAx] qmul z (reciprocal z) ≐ qone)
    (hpI : Γ ⊢[PRAAx] qmul (qadd (qmul z z) w) (reciprocal (qadd (qmul z z) w)) ≐ qone) :
    Γ ⊢[PRAAx] qsub (reciprocal z) (qmul z (reciprocal (qadd (qmul z z) w))) ≐
      qmul (qmul (reciprocal z) w) (reciprocal (qadd (qmul z z) w)) := by
  let P := qadd (qmul z z) w
  let I := reciprocal z
  let J := reciprocal P
  let V := qmul z J
  let W := qmul I w
  let E := qmul W J
  have iz : Γ ⊢[PRAAx] qmul I (qmul z z) ≐ z :=
    (qmul_associative I z z).eqSymm.eqTrans
      ((qmul_congr ((qmul_commutative I z).eqTrans hzI) (.eqRefl z)).eqTrans
        ((qmul_commutative qone z).eqTrans (qmul_one_right z hz)))
  have balance : Γ ⊢[PRAAx] qadd z W ≐ qmul I P :=
    (qadd_congr iz.eqSymm (.eqRefl W)).eqTrans (qmul_add I (qmul z z) w).eqSymm
  have combined : Γ ⊢[PRAAx] qadd V E ≐ I :=
    (right_distribute z W J).eqTrans
      ((qmul_congr balance (.eqRefl J)).eqTrans
        ((qmul_associative I P J).eqTrans
          ((qmul_congr (.eqRefl I) hpI).eqTrans (qmul_one_right I (reciprocal_canonical z)))))
  exact (qsub_congr combined.eqSymm (.eqRefl V)).eqTrans (qadd_sub_cancel V E (qmul_canonical _ _))

theorem resolvent_error (X Y D sign a b A B : PTm n) (hz : Γ ⊢[PRAAx] source X D sign)
    (hb : Γ ⊢[PRAAx] le one b) (hB : Γ ⊢[PRAAx] le one B)
    (ht : Γ ⊢[PRAAx] bounded (fraction a b) A B) :
    Γ ⊢[PRAAx] distanceBounded (value X Y D sign a b) (reciprocal (argument X Y D sign))
      (cube D*(A*A)) (cube X*(B*B)) := by
  let Z := argument X Y D sign
  let P := polynomial X Y D sign a b
  let t := fraction a b
  have hX := hz.andE₁.andE₁
  have hD := hz.andE₂
  have hX2 := positive_product _ _ hX hX
  have hD2 := positive_product _ _ hD hD
  have hzL := GaussianBinetReciprocalRows.real_part_lower X Y D sign hz
  have hpL := GaussianBinetArctangentResolvent.polynomial_lower X Y D sign a b hD hb
  have hzI := reciprocal_identity Z (GaussianNameReciprocal.lower_norm_positive Z D hD (name_lower Z X D hX hD hzL))
  have hpI := reciprocal_identity P
    (GaussianNameReciprocal.lower_norm_positive P (D*D) hD2 (name_lower P (X*X) (D*D) hX2 hD2 hpL))
  have raw := bounded_product _ _ _ _ _ _ hB hB ht ht
  have first := bounded_product _ _ _ _ _ _ hX (positive_product _ _ hB hB) (inverse_bound Z X D hX hD hzL) raw
  have last := bounded_product _ _ _ _ _ _ (positive_product _ _ hX (positive_product _ _ hB hB)) hX2 first
    (inverse_bound P (X*X) (D*D) hX2 hD2 hpL)
  have e := correction Z (qmul t t) (ofGaussian_canonical _ _ hD) hzI hpI
  have hden := positive_product _ _ (positive_product _ _ hX2 hX) (positive_product _ _ hB hB)
  exact distance_symmetric _ _ _ _ hden
    (bound_congr e.eqSymm (by unfold cube; ipra_ring) (by unfold cube; ipra_ring) last)

private theorem tag_bound (i M A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hM : Γ ⊢[PRAAx] le one M)
    (hi : Γ ⊢[PRAAx] le i M) :
    Γ ⊢[PRAAx] bounded (fraction (GaussianBinetLaplaceStrip.tagNumerator (grid i M (B+zero) A B))
      (sndT (grid i M (B+zero) A B))) A B := by
  have hb := positive_product _ _ hB hM
  have enc := GaussianBinetLaplaceStripCutoff.grid_tag (Γ := Γ) i M zero A B
  have num := enc.andE₁.eqTrans (by ipra_ring : Γ ⊢[PRAAx] zero*M+A*i ≐ A*i)
  have eq := GaussianCompactRiemannName.fraction_congr _ _ _ _ num enc.andE₂
  have bound := bound_congr (GaussianEulerDecayFactorBounds.fraction_is_radius_point (A*i) (B*M) hb).eqSymm
    (.eqRefl _) (.eqRefl _) (GaussianDominantPairAlgebra.radius_bounded (A*i) (B*M) hb)
  apply bound_congr eq.eqSymm (.eqRefl _) (.eqRefl _)
  apply GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ hb hB ?_ bound
  exact le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (A*B) hi)

private theorem constant_integral (q M A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] GaussianRationalRiemannRefinement.leftSum constantBody M q A B ≐ qmul (fraction A B) q := by
  let W := weight A B M
  let N := GaussianRationalNaturalScale.naturalPoint M
  have em : Γ ⊢[PRAAx] W ≐ weight A B (M*one) :=
    GaussianCompactRiemannName.fraction_congr _ _ _ _ (.eqRefl A) (congrMul (.eqRefl B) (by ipra_ring : Γ ⊢[PRAAx] M ≐ M*one))
  have e1 : Γ ⊢[PRAAx] weight A B one ≐ fraction A B :=
    GaussianCompactRiemannName.fraction_congr _ _ _ _ (.eqRefl A) (by ipra_ring)
  have read := (constant_sum (Γ := Γ) q M).eqTrans (GaussianRationalNaturalScale.natScale_as_product M q)
  exact (qmul_congr (.eqRefl W) read).eqTrans
    ((qmul_associative W N q).eqSymm.eqTrans
      (qmul_congr ((qmul_congr em (.eqRefl N)).eqTrans
        ((weight_repetition A B M one hB hM (le_refl one)).eqTrans e1)) (.eqRefl q)))

theorem quadrature_error (p M X Y D sign A B : PTm n) (hz : Γ ⊢[PRAAx] source X D sign)
    (hB : Γ ⊢[PRAAx] le one B) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] distanceBounded (quadrature evaluatorF p M (B+zero) A B (fixedData X Y D sign))
      (linear X Y D sign A B) (cube (A*D)) (cube (B*X)) := by
  let f := sampleBody evaluatorF
  let q := reciprocal (argument X Y D sign)
  let d := sampleData p M (B+zero) A B (fixedData X Y D sign)
  let U := cube D*(A*A)
  let V := cube X*(B*B)
  have rows : Γ ⊢[PRAAx] termsDistance f constantBody M d q U V := by
    refine .allI (.impI ?_)
    let s (v : PTm n) := Syn.shift v
    let Δ := lt (var 0) (s M)::Γ.map Fm.shift
    let t := grid (var 0) (s M) (s B+zero) (s A) (s B)
    have zs : Δ ⊢[PRAAx] source (s X) (s D) (s sign) := by
      simpa [s,Δ,Fm.shift,Syn.shift,source,GaussianRightHalfPlaneArgument.source] using hz.shift.wk
    have bs : Δ ⊢[PRAAx] le one (s B) := by simpa [s,Δ,Fm.shift,Syn.shift,one] using hB.shift.wk
    have ms : Δ ⊢[PRAAx] le one (s M) := by simpa [s,Δ,Fm.shift,Syn.shift,one] using hM.shift.wk
    have hi : Δ ⊢[PRAAx] le (var 0) (s M) := le_of_lt Prf.hyp0
    have read := (sample_body_at (Γ := Δ) evaluatorF (var 0) (s p) (s M) (s B+zero) (s A) (s B)
      (fixedData (s X) (s Y) (s D) (s sign))).eqTrans (evaluator_at (s p) t (s X) (s Y) (s D) (s sign))
    have ht := tag_bound (var 0) (s M) (s A) (s B) bs ms hi
    have hb := le_congr (.eqRefl _) (GaussianBinetLaplaceStripCutoff.grid_tag (Γ := Δ) (var 0) (s M) zero (s A) (s B)).andE₂.eqSymm
      (positive_product _ _ bs ms)
    have err := resolvent_error (s X) (s Y) (s D) (s sign) (GaussianBinetLaplaceStrip.tagNumerator t) (sndT t)
      (s A) (s B) zs hb bs ht
    rw [constant_entry]
    simpa only [f,q,d,U,V,Syn.shift,s,Δ,GaussianCompactRiemannName.subst_sampleData,
      GaussianBinetArctangentQuadrature.subst_fixedData,subst_cube,GaussianLogGammaEulerRepresentation.subst_argument,
      GaussianRationalReciprocal.subst_reciprocal,PTm.subst_add,PTm.subst_mul,ConciseIPRA.PTm.subst_zero] using
      distance_congr read.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) err
  have hX := hz.andE₁.andE₁
  have hV := positive_product _ _ (positive_product _ _ (positive_product _ _ hX hX) hX) (positive_product _ _ hB hB)
  exact distance_congr (.eqRefl _) (constant_integral q M A B hB hM)
    (by dsimp only [U,cube]; ipra_ring) (by dsimp only [V,cube]; ipra_ring)
    (GaussianCompactScalarMajorant.common_mesh_distance f constantBody M d q A B U V hM hB hV rows)

theorem name_error (p X Y D sign A B : PTm n) (hz : Γ ⊢[PRAAx] source X D sign) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data X Y D sign A B)) (linear X Y D sign A B)
      (cube (A*D)) (cube (B*X)) :=
  distance_congr (GaussianCompactRiemannName.name_at evaluatorF p (B+zero) A B (D*D) A (fixedData X Y D sign)).eqSymm
    (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (quadrature_error (precision p A) (mesh p (D*D) A) X Y D sign A B hz hB (mesh_positive p (D*D) A))

theorem divided_error (p X Y D sign A B : PTm n) (hz : Γ ⊢[PRAAx] source X D sign)
    (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] distanceBounded
      (qmul (fraction B A) (ap2 nameF p (data X Y D sign A B))) (reciprocal (argument X Y D sign))
      ((A*A)*cube D) ((B*B)*cube X) := by
  let W := fraction B A
  let Z := argument X Y D sign
  let I := reciprocal Z
  let L := linear X Y D sign A B
  let V := ap2 nameF p (data X Y D sign A B)
  let E := cube (B*X)
  have hX := hz.andE₁.andE₁
  have hBX := positive_product _ _ hB hX
  have hE : Γ ⊢[PRAAx] le one E := positive_product _ _ (positive_product _ _ hBX hBX) hBX
  have wBound := bound_congr (GaussianEulerDecayFactorBounds.fraction_is_radius_point B A hA).eqSymm
    (.eqRefl _) (.eqRefl _) (GaussianDominantPairAlgebra.radius_bounded B A hA)
  have scaled := bounded_product W (qsub V L) B A (cube (A*D)) E hA hE wBound (name_error p X Y D sign A B hz hB)
  have e : Γ ⊢[PRAAx] qmul W L ≐ I :=
    (qmul_associative W (fraction A B) I).eqSymm.eqTrans
      ((qmul_congr (GaussianGammaHalfEulerSquare.inverse_fraction B A hB hA) (.eqRefl I)).eqTrans
        ((qmul_commutative qone I).eqTrans (qmul_one_right I (reciprocal_canonical Z))))
  have raw := distance_congr (.eqRefl _) e (.eqRefl _) (.eqRefl _)
    (bound_congr (GaussianRationalRoundedPower.multiplication_difference W V L).eqSymm (.eqRefl _) (.eqRefl _) scaled)
  apply distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hA hE)
    (positive_product _ _ (positive_product _ _ hB hB) (positive_product _ _ (positive_product _ _ hX hX) hX)) ?_ raw
  exact le_of_eq_add (d := zero) (by dsimp only [E,cube]; ipra_ring)

theorem actual_Binet_arctangent_linear_approximation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    ((source (var 1) (var 3) (var 4) ⋏ le one (var 6)) ⟶
      distanceBounded (ap2 nameF (var 0) (data (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)))
        (linear (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
        (cube (var 5*var 3)) (cube (var 6*var 1))) :=
  closeUniv 7 (.impI (name_error _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem actual_Binet_divided_arctangent_near_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    ((source (var 1) (var 3) (var 4) ⋏ (le one (var 5) ⋏ le one (var 6))) ⟶
      distanceBounded (qmul (fraction (var 6) (var 5)) (ap2 nameF (var 0)
        (data (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))))
        (reciprocal (argument (var 1) (var 2) (var 3) (var 4)))
        ((var 5*var 5)*cube (var 3)) ((var 6*var 6)*cube (var 1))) :=
  closeUniv 7 (.impI (divided_error _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBinetArctangentLinearApproximation
