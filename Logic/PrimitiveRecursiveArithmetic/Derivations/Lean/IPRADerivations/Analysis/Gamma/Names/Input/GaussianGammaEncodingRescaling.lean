import IPRADerivations.Analysis.Gamma.Names.Input.GaussianGammaInputProperness
import IPRADerivations.Analysis.Gamma.EulerProducts.Approximants.GaussianGammaEulerApproximationName
import IPRADerivations.Analysis.Exponential.IntegerPowers.GaussianRobinMeshExponential
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Recurrence.GaussianGammaRepeatedShift
import IPRADerivations.Analysis.Gamma.Names.PoleFree.Regularity.GaussianGammaRadiusOverlap

/-!
# Positive encoding rescaling of the original Gamma reciprocal

Canonical input fractions and the original finite Euler head respect
(z,B) -> (E*z,E*B). The actual original Q_N data are literally equal.
The SAME computed cofinal Euler cutoff and its checked C10 name then
transport this equality to the original C7 names. In particular every
positive encoding of one has the original normalized value P(1)=1.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaEncodingRescaling

open_ipra
open GaussianRationalHorner (ofGaussian positive_product)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr)
open GaussianGammaCanonicalExponent (source constantF)
open GaussianGammaFiniteApproximantName (qF qData logF logExponentF exponentialInputData)
open GaussianGammaEulerHead (factor head head_zero head_succ)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_symm)
open ComplexLogarithmRemainder (scale oneCode)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem fraction_rescale (z B E : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hE : Γ ⊢[PRAAx] le one E) : Γ ⊢[PRAAx]
    ofGaussian (scale E z) (E*B) ≐ ofGaussian z B := by
  have hEB : Γ ⊢[PRAAx] le one (E*B) := positive_product E B hE hB
  have represented : Γ ⊢[PRAAx] GaussianRationalHorner.represents (ofGaussian z B) (scale E z) (E*B) :=
    GaussianRationalSyntheticDivision.rescale_to (ofGaussian z B) z B E (E*B)
      (GaussianRationalHorner.ofGaussian_represents z B hB) (mul_comm B E)
  exact GaussianRationalHorner.canonical_unique (ofGaussian (scale E z) (E*B)) (ofGaussian z B) (scale E z) (E*B)
    (GaussianRationalHorner.ofGaussian_canonical (scale E z) (E*B) hEB)
    (GaussianRationalHorner.ofGaussian_canonical z B hB) hEB
    (GaussianRationalHorner.ofGaussian_represents (scale E z) (E*B) hEB) represented

theorem fraction_denominator_congr (z B C : PTm n) (e : Γ ⊢[PRAAx] B ≐ C) : Γ ⊢[PRAAx]
    ofGaussian z B ≐ ofGaussian z C := by
  ipra_congr (ofGaussian (var 0) (var 1) : PTm 2) with [.eqRefl z, e]

theorem factor_rescale (z B E i : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hE : Γ ⊢[PRAAx] le one E) : Γ ⊢[PRAAx]
    factor i (scale E z) (E*B) ≐ factor i z B :=
  qadd_congr (.eqRefl _) ((fraction_denominator_congr (scale E z) ((E*B)*succ i) (E*(B*succ i)) (by ipra_ring)).eqTrans
    (fraction_rescale z (B*succ i) E (positive_product _ _ hB (zero_lt_succ i)) hE))

def headLaw (z B E N : PTm n) : Fm PTm n := head (scale E z) (E*B) N ≐ head z B N
ipra_subst headLaw

theorem head_rescale (z B E N : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hE : Γ ⊢[PRAAx] le one E) : Γ ⊢[PRAAx] headLaw z B E N := by
  have bs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using hB.shift
  have es : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift E) := by simpa [Fm.shift,Syn.shift] using hE.shift
  have hall : Γ ⊢[PRAAx] .all (headLaw (Syn.shift z) (Syn.shift B) (Syn.shift E) (var 0)) := by
    ipra_qfind [subst_headLaw]
    · exact (head_zero _ _ (positive_product _ _ hE hB)).eqTrans
        ((fraction_rescale z B E hB hE).eqTrans (head_zero z B hB).eqSymm)
    · exact (head_succ _ _ _).eqTrans ((qmul_congr Prf.hyp0 (factor_rescale _ _ _ _ bs.wk es.wk)).eqTrans (head_succ _ _ _).eqSymm)
  simpa only [subst_headLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using hall.allE N

theorem returned_head_rescale (z B E N : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hE : Γ ⊢[PRAAx] le one E) : Γ ⊢[PRAAx]
    GaussianGammaEulerHead.run (scale E z) (E*B) N ≐ GaussianGammaEulerHead.run z B N :=
  (GaussianGammaEulerHead.program_at _ _ _).eqTrans ((head_rescale z B E N hB hE).eqTrans (GaussianGammaEulerHead.program_at _ _ _).eqSymm)

/-- This is the literal original Q data with its actual head and canonical
input fraction exposed as two scalar parameters. -/
def qParameters (H q N : PTm n) : PTm n := GaussianNameArithmetic.multiplyData constantF
  (GaussianRadiusExponentialName.nameF logExponentF) H
  (exponentialInputData logExponentF (GaussianNameArithmetic.multiplyData logF constantF N (GaussianRationalMetric.qnegative q)))
ipra_subst qParameters [exponentialInputData]

theorem q_parameters_at (z B N : PTm n) : Γ ⊢[PRAAx]
    qData z B N ≐ qParameters (GaussianGammaEulerHead.run z B N) (ofGaussian z B) N := .eqRefl _

theorem bound_data_congr (f : PR 2) {x y : PTm n} (e : Γ ⊢[PRAAx] x ≐ y) : Γ ⊢[PRAAx]
    GaussianNameBounds.U f x ≐ GaussianNameBounds.U f y := by
  ipra_congr (GaussianNameBounds.U f (var 0) : PTm 1) with [e]

theorem multiply_data_congr (f g : PR 2) {x y u v : PTm n} (ex : Γ ⊢[PRAAx] x ≐ u) (ey : Γ ⊢[PRAAx] y ≐ v) : Γ ⊢[PRAAx]
    GaussianNameArithmetic.multiplyData f g x y ≐ GaussianNameArithmetic.multiplyData f g u v :=
  congrPairT (congrAdd (bound_data_congr f ex) (bound_data_congr g ey)) (congrPairT ex ey)

theorem exponential_data_congr (f : PR 2) {x y : PTm n} (e : Γ ⊢[PRAAx] x ≐ y) : Γ ⊢[PRAAx]
    exponentialInputData f x ≐ exponentialInputData f y := congrPairT (bound_data_congr f e) e

theorem q_parameters_congr {H G q r N : PTm n} (hH : Γ ⊢[PRAAx] H ≐ G) (hq : Γ ⊢[PRAAx] q ≐ r) : Γ ⊢[PRAAx]
    qParameters H q N ≐ qParameters G r N :=
  multiply_data_congr constantF (GaussianRadiusExponentialName.nameF logExponentF) hH
    (exponential_data_congr logExponentF (multiply_data_congr logF constantF (.eqRefl N)
      (GaussianInverseBinomialRows.negative_congr hq)))

theorem q_data_rescale (z B E N : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hE : Γ ⊢[PRAAx] le one E) : Γ ⊢[PRAAx]
    qData (scale E z) (E*B) N ≐ qData z B N :=
  (q_parameters_at _ _ _).eqTrans ((q_parameters_congr (returned_head_rescale z B E N hB hE)
    (fraction_rescale z B E hB hE)).eqTrans (q_parameters_at _ _ _).eqSymm)

theorem rescaled_source (z R B E : PTm n) (h : Γ ⊢[PRAAx] source z R B) (hE : Γ ⊢[PRAAx] le one E) : Γ ⊢[PRAAx]
    source (scale E z) R (E*B) :=
  .andI h.andE₁ (.andI (positive_product _ _ hE h.andE₂.andE₁)
    (le_congr (.eqRefl _) (by ipra_ring) (ComplexLogarithmRemainder.bounded_scale E h.andE₂.andE₂)))

theorem cofinal_sample_rescale (p z R B E : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hE : Γ ⊢[PRAAx] le one E) : Γ ⊢[PRAAx]
    GaussianGammaEulerApproximationName.sample p (scale E z) R (E*B) ≐ GaussianGammaEulerApproximationName.sample p z R B :=
  (GaussianGammaEulerApproximationName.sample_at _ _ _ _).eqTrans
    ((congrAp2 qF (.eqRefl _) (q_data_rescale z B E (GaussianGammaEulerApproximationName.cutoff p R) hB hE)).eqTrans
      (GaussianGammaEulerApproximationName.sample_at _ _ _ _).eqSymm)

theorem cofinal_rescale (z R B E : PTm n) (h : Γ ⊢[PRAAx] source z R B) (hE : Γ ⊢[PRAAx] le one E) : Γ ⊢[PRAAx]
    crossEquivalent GaussianGammaEulerApproximationName.nameF GaussianGammaEulerApproximationName.nameF
      (GaussianGammaEulerApproximationName.data (scale E z) R (E*B)) (GaussianGammaEulerApproximationName.data z R B) := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _
    (GaussianGammaEulerApproximationName.name_regular _ _ _ (rescaled_source z R B E h hE))
    (GaussianGammaEulerApproximationName.name_regular z R B h)
  refine .allI ?_
  have bs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using h.andE₂.andE₁.shift
  have es : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift E) := by simpa [Fm.shift,Syn.shift] using hE.shift
  simpa only [GaussianNameConjugation.pointwiseEqual,Syn.shift,GaussianGammaEulerApproximationName.sample,
    GaussianGammaEulerApproximationName.subst_data,ComplexLogarithmRemainder.subst_scale,PTm.subst_mul] using
    cofinal_sample_rescale (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift E) bs es

/-- Genuine input encoding rescaling for the SAME original C7 name. -/
theorem original_C7_rescale (z R B E : PTm n) (h : Γ ⊢[PRAAx] source z R B) (hE : Γ ⊢[PRAAx] le one E) : Γ ⊢[PRAAx]
    crossEquivalent GaussianGammaC7Name.nameF GaussianGammaC7Name.nameF
      (GaussianGammaC7Name.data (scale E z) R (E*B)) (GaussianGammaC7Name.data z R B) :=
  cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (GaussianGammaEulerApproximationName.named_equivalence _ _ _ (rescaled_source z R B E h hE)))
    (cross_trans _ _ _ _ _ _ (cofinal_rescale z R B E h hE) (GaussianGammaEulerApproximationName.named_equivalence z R B h))
theorem encoded_one_source (B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx] source (scale B oneCode) one B :=
  .andI (le_refl one) (.andI hB (le_congr (.eqRefl _) (by ipra_ring)
    (ComplexLogarithmRemainder.bounded_scale B GaussianGammaNormalization.unit_source.andE₂.andE₂)))

theorem original_encoded_one (B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    crossEquivalent GaussianGammaC7Name.nameF GaussianNameRingLaws.oneF (GaussianGammaC7Name.data (scale B oneCode) one B) zero := by
  have here := encoded_one_source B hB
  have scaled := rescaled_source oneCode one one B GaussianGammaNormalization.unit_source hB
  have denom : Γ ⊢[PRAAx] B ≐ B*one := by ipra_ring
  have dataEq := GaussianGammaRepeatedShift.C7_data_congr (Γ := Γ) (.eqRefl (scale B oneCode)) (.eqRefl one) denom
  have reindex := GaussianGammaInputProperness.code_data_cross GaussianGammaC7Name.nameF _ _
    (GaussianGammaC7Name.name_regular _ _ _ here) (GaussianGammaC7Name.name_regular _ _ _ scaled) dataEq
  exact cross_trans _ _ _ _ _ _ reindex
    (cross_trans _ _ _ _ _ _ (original_C7_rescale oneCode one one B GaussianGammaNormalization.unit_source hB)
      GaussianRobinMeshExponential.C20_P_one)

theorem encoded_one_radius_source (R B : PTm n) (hR : Γ ⊢[PRAAx] le one R) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    source (scale B oneCode) R B :=
  .andI hR (.andI hB (ComplexLogarithmRemainder.bounded_mono (encoded_one_source B hB).andE₂.andE₂
    (mul_le_mul_right B hR)))

/-- Every original radius containing one and every positive native encoding
of one have the SAME original normalized P value. -/
theorem original_encoded_one_at_radius (R B : PTm n) (hR : Γ ⊢[PRAAx] le one R) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    crossEquivalent GaussianGammaC7Name.nameF GaussianNameRingLaws.oneF (GaussianGammaC7Name.data (scale B oneCode) R B) zero :=
  cross_trans _ _ _ _ _ _
    (GaussianGammaRadiusOverlap.original_P_overlap (scale B oneCode) R one B
      (encoded_one_radius_source R B hR hB) (encoded_one_source B hB)) (original_encoded_one B hB)

theorem one_constant_cross : Γ ⊢[PRAAx] crossEquivalent GaussianNameRingLaws.oneF constantF (zero : PTm n) GaussianRationalSyntheticDivision.qone :=
  GaussianNameEquivalence.cross_symm _ _ _ _ (GaussianNameRingLaws.constant_one_cross zero)

theorem original_encoded_one_constant (R B : PTm n) (hR : Γ ⊢[PRAAx] le one R) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    crossEquivalent GaussianGammaC7Name.nameF constantF (GaussianGammaC7Name.data (scale B oneCode) R B) GaussianRationalSyntheticDivision.qone :=
  cross_trans _ _ _ _ _ _ (original_encoded_one_at_radius R B hR hB) one_constant_cross
/-- Actual independent rescaled/original observations and canonical input fraction. -/
def output (p q z R B E : PTm n) : PTm n := pairT (GaussianGammaC7Name.sample p (scale E z) R (E*B))
  (pairT (GaussianGammaC7Name.sample q z R B) (ofGaussian z B))
def outputF : PR 6 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
def run (p q z R B E : PTm n) : PTm n := PTm.app outputF ![p,q,z,R,B,E]
ipra_subst output
ipra_subst run

theorem program_at (p q z R B E : PTm n) : Γ ⊢[PRAAx] run p q z R B E ≐ output p q z R B E := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) ![p,q,z,R,B,E]
theorem returned_rescaled (p q z R B E : PTm n) : Γ ⊢[PRAAx]
    fstT (run p q z R B E) ≐ GaussianGammaC7Name.sample p (scale E z) R (E*B) :=
  (program_at p q z R B E).fstE
theorem returned_original (p q z R B E : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run p q z R B E)) ≐ GaussianGammaC7Name.sample q z R B :=
  (program_at p q z R B E).sndE.fstE
theorem returned_fraction (p q z R B E : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (run p q z R B E)) ≐ ofGaussian z B :=
  (program_at p q z R B E).sndE.sndE
theorem returned_distance (p q z R B E : PTm n) (h : Γ ⊢[PRAAx] source z R B) (hE : Γ ⊢[PRAAx] le one E) : Γ ⊢[PRAAx]
    GaussianRationalMetric.distanceBounded (fstT (run p q z R B E)) (fstT (sndT (run p q z R B E)))
      (GaussianCoefficientNameBounds.unit p+GaussianCoefficientNameBounds.unit q)
      (GaussianCoefficientNameBounds.unit p*GaussianCoefficientNameBounds.unit q) :=
  GaussianRationalDistanceOrder.distance_congr (returned_rescaled p q z R B E).eqSymm (returned_original p q z R B E).eqSymm
    (.eqRefl _) (.eqRefl _) (GaussianNameEquivalence.cross_at _ _ _ _ p q (original_C7_rescale z R B E h hE))

theorem original_canonical_fraction_rescaling_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((le one (var 1) ⋏ le one (var 2)) ⟶ ofGaussian (scale (var 2) (var 0)) (var 2*var 1) ≐ ofGaussian (var 0) (var 1)) :=
  closeUniv 3 (.impI (fraction_rescale _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))
theorem actual_original_Euler_head_rescaling_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((le one (var 1) ⋏ le one (var 2)) ⟶ headLaw (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (head_rescale _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))
theorem actual_original_Q_data_rescaling_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((le one (var 1) ⋏ le one (var 2)) ⟶ qData (scale (var 2) (var 0)) (var 2*var 1) (var 3) ≐ qData (var 0) (var 1) (var 3)) :=
  closeUniv 4 (.impI (q_data_rescale _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))
theorem original_C7_input_encoding_rescaling_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((source (var 0) (var 1) (var 2) ⋏ le one (var 3)) ⟶ crossEquivalent GaussianGammaC7Name.nameF GaussianGammaC7Name.nameF
      (GaussianGammaC7Name.data (scale (var 3) (var 0)) (var 1) (var 3*var 2)) (GaussianGammaC7Name.data (var 0) (var 1) (var 2))) :=
  closeUniv 4 (.impI (original_C7_rescale _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))
theorem original_P_one_every_positive_encoding_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((le one (var 0) ⋏ le one (var 1)) ⟶ crossEquivalent GaussianGammaC7Name.nameF constantF
      (GaussianGammaC7Name.data (scale (var 1) oneCode) (var 0) (var 1)) GaussianRationalSyntheticDivision.qone) :=
  closeUniv 2 (.impI (original_encoded_one_constant _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))
theorem actual_original_encoding_rescale_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (program_at _ _ _ _ _ _)
theorem actual_returned_original_encoding_rescale_distance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((source (var 2) (var 3) (var 4) ⋏ le one (var 5)) ⟶ GaussianRationalMetric.distanceBounded
      (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)))
      (fstT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))))
      (GaussianCoefficientNameBounds.unit (var 0)+GaussianCoefficientNameBounds.unit (var 1))
      (GaussianCoefficientNameBounds.unit (var 0)*GaussianCoefficientNameBounds.unit (var 1))) :=
  closeUniv 6 (.impI (returned_distance _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))


end LeanProofs.IPRA.Analysis.GaussianGammaEncodingRescaling
