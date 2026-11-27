import IPRADerivations.Analysis.Gamma.EulerProducts.Approximants.Continuity.GaussianGammaFiniteValueProperness
import IPRADerivations.Analysis.Names.Arithmetic.GaussianNameConjugation
import IPRADerivations.Analysis.Gamma.EulerProducts.Weierstrass.GaussianGammaWeierstrassLimit
import IPRADerivations.Analysis.Gamma.FunctionalEquations.ReciprocalGamma.GaussianGammaReciprocalInverse

/-!
# Original Gamma names respect native input values at the same denominator

The original finite literal samples are proved equal before transporting
both actual independent normalizers. The same C11 cutoff then supplies
properness of the SAME original C7 reciprocal. Original pole guards
transfer by native norm equality, and actual reciprocal uniqueness
supplies properness of the SAME original Gamma program and anchor data.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaInputProperness

open_ipra
open GaussianRootAlgebra (equal)
open GaussianGammaFiniteValueProperness (fraction_equal source_equal literal_prefix_equal)
open GaussianGammaCanonicalExponent (source constantF gammaF)
open GaussianGammaWeierstrassApproximant (positiveExponentF positiveExponentData positiveExpF positiveExpData
  positive_exp_regular literalF literalData literal_regular)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianEuclideanDistanceName (pointCN)
open GaussianRationalMetric (distanceBounded)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem code_data_cross (f : PR 2) (x y : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN f y)
    (e : Γ ⊢[PRAAx] x ≐ y) : Γ ⊢[PRAAx] crossEquivalent f f x y := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _ hf hg
  refine .allI ?_
  have es : Γ.map Fm.shift ⊢[PRAAx] Syn.shift x ≐ Syn.shift y := by simpa [Fm.shift,Syn.shift] using e.shift
  simpa only [GaussianNameConjugation.pointwiseEqual,Syn.shift] using congrAp2 f (.eqRefl (var 0)) es

theorem raw_sample_equal (p z w R B N : PTm n) (hB : Γ ⊢[PRAAx] le one B) (h : Γ ⊢[PRAAx] equal z w) : Γ ⊢[PRAAx]
    ap2 GaussianGammaWeierstrassFiniteName.rawF p (GaussianGammaWeierstrassFiniteName.data z R B N) ≐
      ap2 GaussianGammaWeierstrassFiniteName.rawF p (GaussianGammaWeierstrassFiniteName.data w R B N) :=
  (GaussianGammaWeierstrassFiniteName.raw_at p z R B N).eqTrans
    ((literal_prefix_equal z w B
      (GaussianScalarExponentialProductTail.rectangleCutoff (GaussianGammaWeierstrassFactors.width R N) p) N hB h).eqTrans
      (GaussianGammaWeierstrassFiniteName.raw_at p w R B N).eqSymm)

theorem finite_name_proper (z w R B N : PTm n) (hz : Γ ⊢[PRAAx] source z R B) (h : Γ ⊢[PRAAx] equal z w) : Γ ⊢[PRAAx]
    crossEquivalent GaussianGammaWeierstrassFiniteName.nameF GaussianGammaWeierstrassFiniteName.nameF
      (GaussianGammaWeierstrassFiniteName.nameData z R B N) (GaussianGammaWeierstrassFiniteName.nameData w R B N) := by
  have diag : Γ ⊢[PRAAx] GaussianValueNormalizerExtensionality.rawDiagonal GaussianGammaWeierstrassFiniteName.rawF
      GaussianGammaWeierstrassFiniteName.rawF (GaussianGammaWeierstrassFiniteName.data z R B N)
      (GaussianGammaWeierstrassFiniteName.data w R B N) zero := by
    refine .allI ?_
    have bs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using hz.andE₂.andE₁.shift
    have es : Γ.map Fm.shift ⊢[PRAAx] equal (Syn.shift z) (Syn.shift w) := by simpa [Fm.shift,Syn.shift] using h.shift
    have e := raw_sample_equal (var 0) (Syn.shift z) (Syn.shift w) (Syn.shift R) (Syn.shift B) (Syn.shift N) bs es
    have d := GaussianNameConjugation.equal_distance _ _ (unit (var 0)) (unit_positive _) e
    simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,Syn.shift,GaussianGammaWeierstrassFiniteName.subst_data,
      ConciseIPRA.PTm.subst_zero] using d
  exact GaussianValueNormalizerExtensionality.normalized_names_equivalent _ _ _ _ _ _ zero
    (GaussianGammaWeierstrassFiniteName.raw_regular z R B N hz)
    (GaussianGammaWeierstrassFiniteName.raw_regular w R B N (source_equal z w R B hz h)) diag

def positiveData (q : PTm n) : PTm n := GaussianGammaFiniteApproximantName.exponentialInputData positiveExponentF
  (GaussianNameArithmetic.multiplyData gammaF constantF zero q)
ipra_subst positiveData [GaussianGammaFiniteApproximantName.exponentialInputData]

theorem positive_exp_data_equal (z w B : PTm n) (hB : Γ ⊢[PRAAx] le one B) (h : Γ ⊢[PRAAx] equal z w) : Γ ⊢[PRAAx]
    positiveExpData z B ≐ positiveExpData w B := by
  change Γ ⊢[PRAAx] positiveData (GaussianRationalHorner.ofGaussian z B) ≐ positiveData (GaussianRationalHorner.ofGaussian w B)
  ipra_congr (positiveData (var 0) : PTm 1) with [fraction_equal z w B hB h]

theorem positive_exp_proper (z w B : PTm n) (hB : Γ ⊢[PRAAx] le one B) (h : Γ ⊢[PRAAx] equal z w) : Γ ⊢[PRAAx]
    crossEquivalent positiveExpF positiveExpF (positiveExpData z B) (positiveExpData w B) :=
  code_data_cross _ _ _ (positive_exp_regular z B) (positive_exp_regular w B) (positive_exp_data_equal z w B hB h)

theorem literal_proper (z w R B N : PTm n) (hz : Γ ⊢[PRAAx] source z R B) (h : Γ ⊢[PRAAx] equal z w) : Γ ⊢[PRAAx]
    crossEquivalent literalF literalF (literalData z R B N) (literalData w R B N) :=
  GaussianGammaAdjacentCutoff.multiply_cross GaussianGammaWeierstrassFiniteName.nameF GaussianGammaWeierstrassFiniteName.nameF
    positiveExpF positiveExpF (GaussianGammaWeierstrassFiniteName.nameData z R B N)
    (GaussianGammaWeierstrassFiniteName.nameData w R B N) (positiveExpData z B) (positiveExpData w B)
    (GaussianGammaWeierstrassFiniteName.name_regular z R B N hz)
    (GaussianGammaWeierstrassFiniteName.name_regular w R B N (source_equal z w R B hz h))
    (positive_exp_regular z B) (positive_exp_regular w B) (finite_name_proper z w R B N hz h)
    (positive_exp_proper z w B hz.andE₂.andE₁ h)

theorem cofinal_proper_at (p z w R B : PTm n) (hz : Γ ⊢[PRAAx] source z R B) (h : Γ ⊢[PRAAx] equal z w) : Γ ⊢[PRAAx]
    distanceBounded (GaussianGammaWeierstrassLimit.sample p z R B) (GaussianGammaWeierstrassLimit.sample p w R B) one (unit p) := by
  let N := GaussianGammaWeierstrassLimit.cutoff p R
  have raw := GaussianNameEquivalence.cross_at _ _ _ _ (succ p) (succ p) (literal_proper z w R B N hz h)
  have budget : Γ ⊢[PRAAx] le ((unit (succ p)+unit (succ p))*unit p) (one*(unit (succ p)*unit (succ p))) := by
    refine le_of_eq_add (d := zero) ?_
    have e := natEq (pw_succ (Γ := Γ) two p)
    apply deriveNat; unfold unit; ipra_simps; rw [e]; ring
  have small : Γ ⊢[PRAAx] distanceBounded (ap2 literalF (succ p) (literalData z R B N))
      (ap2 literalF (succ p) (literalData w R B N)) one (unit p) :=
    GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ _ _
      (GaussianRationalHorner.positive_product _ _ (unit_positive _) (unit_positive _)) (unit_positive _) budget raw
  exact GaussianRationalDistanceOrder.distance_congr (GaussianGammaWeierstrassLimit.sample_at p z R B).eqSymm
    (GaussianGammaWeierstrassLimit.sample_at p w R B).eqSymm (.eqRefl _) (.eqRefl _) small

theorem cofinal_proper (z w R B : PTm n) (hz : Γ ⊢[PRAAx] source z R B) (h : Γ ⊢[PRAAx] equal z w) : Γ ⊢[PRAAx]
    crossEquivalent GaussianGammaWeierstrassLimit.nameF GaussianGammaWeierstrassLimit.nameF
      (GaussianGammaWeierstrassConvergence.data z R B) (GaussianGammaWeierstrassConvergence.data w R B) := by
  apply GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ one (GaussianGammaWeierstrassLimit.limit_regular z R B hz)
    (GaussianGammaWeierstrassLimit.limit_regular w R B (source_equal z w R B hz h))
  refine .allI ?_
  have zs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using hz.shift
  have es : Γ.map Fm.shift ⊢[PRAAx] equal (Syn.shift z) (Syn.shift w) := by simpa [Fm.shift,Syn.shift] using h.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,GaussianGammaWeierstrassLimit.sample,Syn.shift,
    GaussianGammaWeierstrassConvergence.subst_data,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    cofinal_proper_at (var 0) (Syn.shift z) (Syn.shift w) (Syn.shift R) (Syn.shift B) zs es

/-- Original C7 names, with SAME B,R but independently computed data and
normalizer clocks, represent the same value under native input equality. -/
theorem original_C7_proper (z w R B : PTm n) (hz : Γ ⊢[PRAAx] source z R B) (h : Γ ⊢[PRAAx] equal z w) : Γ ⊢[PRAAx]
    crossEquivalent GaussianGammaC7Name.nameF GaussianGammaC7Name.nameF (GaussianGammaC7Name.data z R B) (GaussianGammaC7Name.data w R B) :=
  cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (GaussianGammaWeierstrassLimit.limit_equivalence z R B hz))
    (cross_trans _ _ _ _ _ _ (cofinal_proper z w R B hz h)
      (GaussianGammaWeierstrassLimit.limit_equivalence w R B (source_equal z w R B hz h)))

theorem translated_equal (z w B k : PTm n) (h : Γ ⊢[PRAAx] equal z w) : Γ ⊢[PRAAx]
    equal (GaussianGammaEulerHeadLower.translated z B k) (GaussianGammaEulerHeadLower.translated w B k) :=
  GaussianRootAlgebra.add_equal h (GaussianRootAlgebra.equal_refl _)

theorem pole_at_equal (z w B a d k : PTm n) (hz : Γ ⊢[PRAAx] GaussianGammaEulerHeadLower.poleAt z B a d k)
    (h : Γ ⊢[PRAAx] equal z w) : Γ ⊢[PRAAx] GaussianGammaEulerHeadLower.poleAt w B a d k :=
  le_congr (.eqRefl _) (congrMul (.eqRefl _) (GaussianRootAlgebra.normSq_equal (translated_equal z w B k h))) hz

theorem pole_guard_equal (z w B a d N : PTm n) (hz : Γ ⊢[PRAAx] GaussianGammaEulerHeadLower.poleGuard z B a d N)
    (h : Γ ⊢[PRAAx] equal z w) : Γ ⊢[PRAAx] GaussianGammaEulerHeadLower.poleGuard w B a d N := by
  refine .allI (.impI ?_)
  have zs : Γ.map Fm.shift ⊢[PRAAx] GaussianGammaEulerHeadLower.poleGuard (Syn.shift z) (Syn.shift B) (Syn.shift a) (Syn.shift d) (Syn.shift N) := by
    simpa [Fm.shift,Syn.shift] using hz.shift
  have es : Γ.map Fm.shift ⊢[PRAAx] equal (Syn.shift z) (Syn.shift w) := by simpa [Fm.shift,Syn.shift] using h.shift
  have old := GaussianGammaEulerHeadLower.pole_at (Syn.shift z) (Syn.shift B) (Syn.shift a) (Syn.shift d) (Syn.shift N)
    (var 0) zs.wk Prf.hyp0
  simpa only [GaussianGammaEulerHeadLower.poleGuard,Syn.shift] using
    pole_at_equal (Syn.shift z) (Syn.shift w) (Syn.shift B) (Syn.shift a) (Syn.shift d) (var 0) old es.wk

theorem gamma_source_equal (z w R B a d : PTm n) (hz : Γ ⊢[PRAAx] GaussianGammaReciprocalInverse.source z R B a d)
    (h : Γ ⊢[PRAAx] equal z w) : Γ ⊢[PRAAx] GaussianGammaReciprocalInverse.source w R B a d :=
  .andI (source_equal z w R B hz.andE₁ h) (.andI hz.andE₂.andE₁ (.andI hz.andE₂.andE₂.andE₁
    (pole_guard_equal z w B a d (two*R) hz.andE₂.andE₂.andE₂ h)))

/-- The candidate original Gamma(z) is proved to invert original P(w).
Both original data and the target's independent anchor remain intact. -/
theorem inverse_product_proper (z w R B a d : PTm n) (hz : Γ ⊢[PRAAx] GaussianGammaReciprocalInverse.source z R B a d)
    (h : Γ ⊢[PRAAx] equal z w) : Γ ⊢[PRAAx]
    crossEquivalent (GaussianNameArithmetic.multiplyF GaussianGammaC7Name.nameF GaussianGammaReciprocalInverse.gammaF)
      GaussianNameRingLaws.oneF
      (GaussianNameArithmetic.multiplyData GaussianGammaC7Name.nameF GaussianGammaReciprocalInverse.gammaF
        (GaussianGammaC7Name.data w R B) (GaussianGammaReciprocalInverse.gammaData z R B d))
      (GaussianGammaC7Name.data w R B) := by
  let P := GaussianGammaC7Name.nameF
  let G := GaussianGammaReciprocalInverse.gammaF
  let Z := GaussianGammaC7Name.data z R B
  let W := GaussianGammaC7Name.data w R B
  let X := GaussianGammaReciprocalInverse.gammaData z R B d
  have hp := GaussianGammaC7Name.name_regular z R B hz.andE₁
  have hw := GaussianGammaC7Name.name_regular w R B (source_equal z w R B hz.andE₁ h)
  have hg := GaussianGammaReciprocalInverse.gamma_regular z R B a d hz
  have replace := GaussianGammaAdjacentCutoff.multiply_cross P P G G Z W X X hp hw hg hg
    (original_C7_proper z w R B hz.andE₁ h) (cross_refl _ _ hg)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ replace)
    (cross_trans _ _ _ _ _ _ (GaussianGammaReciprocalInverse.gamma_product z R B a d hz)
      (GaussianBoundedInverseApartness.ones_equivalent Z W))

/-- Native value input properness of the SAME original Gamma program.
No equality of distinct raw input codes or returned samples is assumed. -/
theorem original_Gamma_proper (z w R B a d : PTm n) (hz : Γ ⊢[PRAAx] GaussianGammaReciprocalInverse.source z R B a d)
    (h : Γ ⊢[PRAAx] equal z w) : Γ ⊢[PRAAx]
    crossEquivalent GaussianGammaReciprocalInverse.gammaF GaussianGammaReciprocalInverse.gammaF
      (GaussianGammaReciprocalInverse.gammaData z R B d) (GaussianGammaReciprocalInverse.gammaData w R B d) := by
  have target := (GaussianGammaReciprocalInverse.original_gamma_inverse w R B a d (gamma_source_equal z w R B a d hz h)).andE₁
  exact cross_symm _ _ _ _ (GaussianBoundedInverseApartness.reciprocal_matches_inverse
    GaussianGammaC7Name.nameF GaussianGammaReciprocalInverse.gammaF (GaussianGammaReciprocalInverse.gammaHeight w R B d)
    (GaussianGammaC7Name.data w R B) (GaussianGammaReciprocalInverse.gammaData z R B d) target.andE₁
    (GaussianGammaReciprocalInverse.gamma_regular z R B a d hz) target.andE₂ (inverse_product_proper z w R B a d hz h))


/-- Original C7 and Gamma observations at independent precisions retain
both raw native codes, the same B,R, and the original separation d. -/
def output (p q z w R B d : PTm n) : PTm n := pairT (GaussianGammaC7Name.sample p z R B)
  (pairT (GaussianGammaC7Name.sample q w R B)
    (pairT (ap2 GaussianGammaReciprocalInverse.gammaF p (GaussianGammaReciprocalInverse.gammaData z R B d))
      (ap2 GaussianGammaReciprocalInverse.gammaF q (GaussianGammaReciprocalInverse.gammaData w R B d))))
def outputF : PR 7 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
def run (p q z w R B d : PTm n) : PTm n := PTm.app outputF ![p,q,z,w,R,B,d]
ipra_subst output [GaussianGammaReciprocalInverse.gammaData, GaussianGammaReciprocalInverse.gammaHeight]
ipra_subst run

theorem program_at (p q z w R B d : PTm n) : Γ ⊢[PRAAx] run p q z w R B d ≐ output p q z w R B d := by
  simpa [run,outputF] using
    toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) : PTm 7) ![p,q,z,w,R,B,d]
theorem returned_P_left (p q z w R B d : PTm n) : Γ ⊢[PRAAx] fstT (run p q z w R B d) ≐ GaussianGammaC7Name.sample p z R B :=
  (program_at p q z w R B d).fstE
theorem returned_P_right (p q z w R B d : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run p q z w R B d)) ≐ GaussianGammaC7Name.sample q w R B :=
  ((congrFst (congrSnd (program_at p q z w R B d))).eqTrans (congrFst (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_Gamma_left (p q z w R B d : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (run p q z w R B d))) ≐ ap2 GaussianGammaReciprocalInverse.gammaF p (GaussianGammaReciprocalInverse.gammaData z R B d) :=
  (((congrFst (congrSnd (congrSnd (program_at p q z w R B d)))).eqTrans (congrFst (congrSnd (snd_pair _ _)))).eqTrans
    (congrFst (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_Gamma_right (p q z w R B d : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (sndT (run p q z w R B d))) ≐ ap2 GaussianGammaReciprocalInverse.gammaF q (GaussianGammaReciprocalInverse.gammaData w R B d) :=
  (((congrSnd (congrSnd (congrSnd (program_at p q z w R B d)))).eqTrans (congrSnd (congrSnd (snd_pair _ _)))).eqTrans
    (congrSnd (snd_pair _ _))).eqTrans (snd_pair _ _)
theorem returned_P_distance (p q z w R B d : PTm n) (hz : Γ ⊢[PRAAx] source z R B) (h : Γ ⊢[PRAAx] equal z w) : Γ ⊢[PRAAx]
    distanceBounded (fstT (run p q z w R B d)) (fstT (sndT (run p q z w R B d))) (unit p+unit q) (unit p*unit q) :=
  GaussianRationalDistanceOrder.distance_congr (returned_P_left p q z w R B d).eqSymm (returned_P_right p q z w R B d).eqSymm
    (.eqRefl _) (.eqRefl _) (GaussianNameEquivalence.cross_at _ _ _ _ p q (original_C7_proper z w R B hz h))
theorem returned_Gamma_distance (p q z w R B a d : PTm n) (hz : Γ ⊢[PRAAx] GaussianGammaReciprocalInverse.source z R B a d)
    (h : Γ ⊢[PRAAx] equal z w) : Γ ⊢[PRAAx]
    distanceBounded (fstT (sndT (sndT (run p q z w R B d)))) (sndT (sndT (sndT (run p q z w R B d)))) (unit p+unit q) (unit p*unit q) :=
  GaussianRationalDistanceOrder.distance_congr (returned_Gamma_left p q z w R B d).eqSymm (returned_Gamma_right p q z w R B d).eqSymm
    (.eqRefl _) (.eqRefl _) (GaussianNameEquivalence.cross_at _ _ _ _ p q (original_Gamma_proper z w R B a d hz h))

theorem actual_original_finite_names_native_proper_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 2) (var 3) ⟶ equal (var 0) (var 1) ⟶
      crossEquivalent GaussianGammaWeierstrassFiniteName.nameF GaussianGammaWeierstrassFiniteName.nameF
        (GaussianGammaWeierstrassFiniteName.nameData (var 0) (var 2) (var 3) (var 4))
        (GaussianGammaWeierstrassFiniteName.nameData (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (.impI (finite_name_proper _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem original_literal_C5_native_input_proper_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 2) (var 3) ⟶ equal (var 0) (var 1) ⟶
      crossEquivalent literalF literalF (literalData (var 0) (var 2) (var 3) (var 4)) (literalData (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (.impI (literal_proper _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem original_C7_native_input_proper_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 2) (var 3) ⟶ equal (var 0) (var 1) ⟶
      crossEquivalent GaussianGammaC7Name.nameF GaussianGammaC7Name.nameF
        (GaussianGammaC7Name.data (var 0) (var 2) (var 3)) (GaussianGammaC7Name.data (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (.impI (original_C7_proper _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem original_Gamma_domain_native_input_proper_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (GaussianGammaReciprocalInverse.source (var 0) (var 2) (var 3) (var 4) (var 5) ⟶ equal (var 0) (var 1) ⟶
      GaussianGammaReciprocalInverse.source (var 1) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (.impI (.impI (gamma_source_equal _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem original_Gamma_native_input_proper_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (GaussianGammaReciprocalInverse.source (var 0) (var 2) (var 3) (var 4) (var 5) ⟶ equal (var 0) (var 1) ⟶
      crossEquivalent GaussianGammaReciprocalInverse.gammaF GaussianGammaReciprocalInverse.gammaF
        (GaussianGammaReciprocalInverse.gammaData (var 0) (var 2) (var 3) (var 5))
        (GaussianGammaReciprocalInverse.gammaData (var 1) (var 2) (var 3) (var 5))) :=
  closeUniv 6 (.impI (.impI (original_Gamma_proper _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_original_native_properness_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ≐
      output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) := closeUniv 7 (program_at _ _ _ _ _ _ _)

theorem actual_returned_original_native_properness_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (GaussianGammaReciprocalInverse.source (var 2) (var 4) (var 5) (var 6) (var 7) ⟶ equal (var 2) (var 3) ⟶
      distanceBounded (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 7)))
        (fstT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 7)))) (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1)) ⋏
      distanceBounded (fstT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 7)))))
        (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 7))))) (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 8 (.impI (.impI (.andI (returned_P_distance _ _ _ _ _ _ _ Prf.hyp1.andE₁ Prf.hyp0)
    (returned_Gamma_distance _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianGammaInputProperness
