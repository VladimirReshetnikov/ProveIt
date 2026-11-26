import IPRADerivations.Analysis.Names.GaussianNameConjugation
import IPRADerivations.Analysis.Gamma.EulerProducts.Approximants.GaussianGammaFiniteConjugation
import IPRADerivations.Analysis.Gamma.EulerProducts.Weierstrass.GaussianGammaWeierstrassLimit
import IPRADerivations.Analysis.Exponential.Names.GaussianExponentialRadiusIndependence

/-!
# Conjugation of the original named Gamma reciprocal

The literal C5 finite product commutes with conjugation through its
actual regularized name. The C11 cofinal sampler uses the same numerical
cutoff at both conjugate inputs, and transports this law to the original
C7 name. Each independently computed normalization and radius is retained.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaNameConjugation

open_ipra
open GaussianRationalConjugation (point point_congr)
open GaussianRationalReciprocal (conjugate)
open GaussianGammaCanonicalExponent (source gammaF gamma_regular constantF constant_at constant_regular)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_trans cross_symm)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaWeierstrassApproximant (positiveExponentF positiveExponentData positiveExpF positiveExpData literalF literalData
  positive_exponent_regular positive_exp_regular literal_regular)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalMetric (distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem raw_sample_covariance (p z R B N : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    point (ap2 GaussianGammaWeierstrassFiniteName.rawF p (GaussianGammaWeierstrassFiniteName.data z R B N)) ≐
      ap2 GaussianGammaWeierstrassFiniteName.rawF p (GaussianGammaWeierstrassFiniteName.data (conjugate z) R B N) :=
  (point_congr (GaussianGammaWeierstrassFiniteName.raw_at p z R B N)).eqTrans
    ((GaussianGammaFiniteConjugation.literal_prefix_conjugate z B
      (GaussianScalarExponentialProductTail.rectangleCutoff (GaussianGammaWeierstrassFactors.width R N) p) N hB).eqTrans
      (GaussianGammaWeierstrassFiniteName.raw_at p (conjugate z) R B N).eqSymm)

theorem raw_covariance (z R B N : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    GaussianNameConjugation.covariance GaussianGammaWeierstrassFiniteName.rawF GaussianGammaWeierstrassFiniteName.rawF
      (GaussianGammaWeierstrassFiniteName.data z R B N) (GaussianGammaWeierstrassFiniteName.data (conjugate z) R B N) := by
  refine .allI ?_
  have bs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using hB.shift
  simpa only [GaussianNameConjugation.covariance,Syn.shift,GaussianGammaWeierstrassFiniteName.subst_data,
    GaussianRationalReciprocal.subst_conjugate] using
    raw_sample_covariance (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift N) bs

theorem finite_name_conjugate (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    crossEquivalent (GaussianNameConjugation.nameF GaussianGammaWeierstrassFiniteName.nameF) GaussianGammaWeierstrassFiniteName.nameF
      (GaussianGammaWeierstrassFiniteName.nameData z R B N) (GaussianGammaWeierstrassFiniteName.nameData (conjugate z) R B N) :=
  GaussianNameConjugation.normalized_transport _ _ _ _ _ _
    (GaussianGammaWeierstrassFiniteName.raw_regular z R B N h)
    (GaussianGammaWeierstrassFiniteName.raw_regular (conjugate z) R B N (GaussianGammaFiniteConjugation.source_conjugate z R B h))
    (raw_covariance z R B N h.andE₂.andE₁)

theorem constant_sample_conjugate (p q r : PTm n) (e : Γ ⊢[PRAAx] point q ≐ r) : Γ ⊢[PRAAx]
    ap2 (GaussianNameConjugation.nameF constantF) p q ≐ ap2 constantF p r :=
  (GaussianNameConjugation.sample_at _ p q).eqTrans
    ((point_congr (constant_at p q)).eqTrans (e.eqTrans (constant_at p r).eqSymm))

theorem constant_name_conjugate (q r : PTm n) (e : Γ ⊢[PRAAx] point q ≐ r) : Γ ⊢[PRAAx]
    crossEquivalent (GaussianNameConjugation.nameF constantF) constantF q r := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _
    (GaussianNameConjugation.regular _ _ (constant_regular q)) (constant_regular r)
  refine .allI ?_
  have es : Γ.map Fm.shift ⊢[PRAAx] point (Syn.shift q) ≐ Syn.shift r := by
    simpa [Fm.shift,Syn.shift] using e.shift
  simpa only [GaussianNameConjugation.pointwiseEqual,Syn.shift] using
    constant_sample_conjugate (var 0) (Syn.shift q) (Syn.shift r) es

theorem positive_exponent_conjugate (z B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    crossEquivalent (GaussianNameConjugation.nameF positiveExponentF) positiveExponentF
      (positiveExponentData z B) (positiveExponentData (conjugate z) B) := by
  let q := GaussianRationalHorner.ofGaussian z B
  let r := GaussianRationalHorner.ofGaussian (conjugate z) B
  have hg := gamma_regular (Γ := Γ) (n := n)
  have hq := constant_regular (Γ := Γ) q
  have hr := constant_regular (Γ := Γ) r
  have first := GaussianNameConjugation.multiply_cross gammaF constantF zero q hg hq
  have second := GaussianGammaAdjacentCutoff.multiply_cross (GaussianNameConjugation.nameF gammaF) gammaF
    (GaussianNameConjugation.nameF constantF) constantF zero zero q r
    (GaussianNameConjugation.regular _ _ hg) hg (GaussianNameConjugation.regular _ _ hq) hr
    (GaussianNameConjugation.embedded_cross_fixed GammaEulerConstantName.gammaF zero hg)
    (constant_name_conjugate q r (GaussianRationalConjugation.of_gaussian z B hB))
  exact cross_trans _ _ _ _ _ _ first second

theorem positive_exp_conjugate (z B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    crossEquivalent (GaussianNameConjugation.nameF positiveExpF) positiveExpF
      (positiveExpData z B) (positiveExpData (conjugate z) B) := by
  let x := positiveExponentData z B
  let y := positiveExponentData (conjugate z) B
  let U := GaussianNameBounds.U positiveExponentF x
  let V := GaussianNameBounds.U positiveExponentF y
  have hx := GaussianGammaFiniteApproximantName.exponential_input (Γ := Γ) positiveExponentF x (positive_exponent_regular z B)
  have hy := GaussianGammaFiniteApproximantName.exponential_input (Γ := Γ) positiveExponentF y (positive_exponent_regular (conjugate z) B)
  have first := GaussianNameConjugation.exponential_cross positiveExponentF U x hx
  have second := GaussianExponentialRadiusIndependence.independent_radii_proper (GaussianNameConjugation.nameF positiveExponentF)
    positiveExponentF U V x y (GaussianNameConjugation.exponential_input positiveExponentF U x hx) hy
    (positive_exponent_conjugate z B hB)
  exact cross_trans _ _ _ _ _ _ first second

theorem literal_conjugate (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    crossEquivalent (GaussianNameConjugation.nameF literalF) literalF
      (literalData z R B N) (literalData (conjugate z) R B N) := by
  have hs := GaussianGammaFiniteConjugation.source_conjugate z R B h
  have hf := GaussianGammaWeierstrassFiniteName.name_regular z R B N h
  have hg := GaussianGammaWeierstrassFiniteName.name_regular (conjugate z) R B N hs
  have hx := positive_exp_regular (Γ := Γ) z B
  have hy := positive_exp_regular (Γ := Γ) (conjugate z) B
  have first := GaussianNameConjugation.multiply_cross GaussianGammaWeierstrassFiniteName.nameF positiveExpF
    (GaussianGammaWeierstrassFiniteName.nameData z R B N) (positiveExpData z B) hf hx
  have second := GaussianGammaAdjacentCutoff.multiply_cross
    (GaussianNameConjugation.nameF GaussianGammaWeierstrassFiniteName.nameF) GaussianGammaWeierstrassFiniteName.nameF
    (GaussianNameConjugation.nameF positiveExpF) positiveExpF
    (GaussianGammaWeierstrassFiniteName.nameData z R B N) (GaussianGammaWeierstrassFiniteName.nameData (conjugate z) R B N)
    (positiveExpData z B) (positiveExpData (conjugate z) B)
    (GaussianNameConjugation.regular _ _ hf) hg (GaussianNameConjugation.regular _ _ hx) hy
    (finite_name_conjugate z R B N h) (positive_exp_conjugate z B h.andE₂.andE₁)
  exact cross_trans _ _ _ _ _ _ first second


theorem cofinal_conjugate_at (p z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    distanceBounded
      (ap2 (GaussianNameConjugation.nameF GaussianGammaWeierstrassLimit.nameF) p (GaussianGammaWeierstrassConvergence.data z R B))
      (GaussianGammaWeierstrassLimit.sample p (conjugate z) R B) one (unit p) := by
  let N := GaussianGammaWeierstrassLimit.cutoff p R
  let X := literalData z R B N
  let Y := literalData (conjugate z) R B N
  have raw := GaussianNameEquivalence.cross_at (Γ := Γ) _ _ _ _ (succ p) (succ p) (literal_conjugate z R B N h)
  have budget : Γ ⊢[PRAAx] le ((unit (succ p)+unit (succ p))*unit p)
      (one*(unit (succ p)*unit (succ p))) := by
    refine le_of_eq_add (d := zero) ?_
    have e := natEq (pw_succ (Γ := Γ) two p)
    apply deriveNat; unfold unit; ipra_simps; rw [e]; ring
  have small : Γ ⊢[PRAAx] distanceBounded
      (ap2 (GaussianNameConjugation.nameF literalF) (succ p) X) (ap2 literalF (succ p) Y) one (unit p) :=
    GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ _ _
      (GaussianRationalHorner.positive_product _ _ (unit_positive _) (unit_positive _)) (unit_positive _) budget raw
  have left : Γ ⊢[PRAAx]
      ap2 (GaussianNameConjugation.nameF GaussianGammaWeierstrassLimit.nameF) p (GaussianGammaWeierstrassConvergence.data z R B) ≐
        ap2 (GaussianNameConjugation.nameF literalF) (succ p) X :=
    (GaussianNameConjugation.sample_at _ p _).eqTrans
      ((point_congr (GaussianGammaWeierstrassLimit.sample_at p z R B)).eqTrans
        (GaussianNameConjugation.sample_at literalF (succ p) X).eqSymm)
  have right : Γ ⊢[PRAAx] GaussianGammaWeierstrassLimit.sample p (conjugate z) R B ≐ ap2 literalF (succ p) Y :=
    GaussianGammaWeierstrassLimit.sample_at p (conjugate z) R B
  exact GaussianRationalDistanceOrder.distance_congr left.eqSymm right.eqSymm (.eqRefl _) (.eqRefl _) small

theorem cofinal_conjugate (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    crossEquivalent (GaussianNameConjugation.nameF GaussianGammaWeierstrassLimit.nameF) GaussianGammaWeierstrassLimit.nameF
      (GaussianGammaWeierstrassConvergence.data z R B) (GaussianGammaWeierstrassConvergence.data (conjugate z) R B) := by
  apply GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ one
    (GaussianNameConjugation.regular _ _ (GaussianGammaWeierstrassLimit.limit_regular z R B h))
    (GaussianGammaWeierstrassLimit.limit_regular (conjugate z) R B (GaussianGammaFiniteConjugation.source_conjugate z R B h))
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using h.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,Syn.shift,GaussianGammaWeierstrassLimit.sample,
    GaussianGammaWeierstrassConvergence.subst_data,GaussianRationalReciprocal.subst_conjugate,
    one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    cofinal_conjugate_at (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) hs

/-- The original C7 reciprocal commutes with conjugation, including its
zeros. Both finite normalizers and the C11 cofinal program are actual. -/
theorem original_reciprocal_conjugate (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    crossEquivalent (GaussianNameConjugation.nameF GaussianGammaC7Name.nameF) GaussianGammaC7Name.nameF
      (GaussianGammaC7Name.data z R B) (GaussianGammaC7Name.data (conjugate z) R B) := by
  have original := GaussianNameConjugation.conjugate_cross _ _ _ _ (GaussianGammaWeierstrassLimit.limit_equivalence z R B h)
  have target := GaussianGammaWeierstrassLimit.limit_equivalence (conjugate z) R B (GaussianGammaFiniteConjugation.source_conjugate z R B h)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ original)
    (cross_trans _ _ _ _ _ _ (cofinal_conjugate z R B h) target)


/-- The returned pair keeps independent observation precisions. -/
def output (p q z R B : PTm n) : PTm n :=
  pairT (ap2 (GaussianNameConjugation.nameF GaussianGammaC7Name.nameF) p (GaussianGammaC7Name.data z R B))
    (GaussianGammaC7Name.sample q (conjugate z) R B)
def outputF : PR 5 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4))
def run (p q z R B : PTm n) : PTm n := PTm.app outputF ![p,q,z,R,B]
ipra_subst output
ipra_subst run

theorem program_at (p q z R B : PTm n) : Γ ⊢[PRAAx] run p q z R B ≐ output p q z R B := by
  simpa only [run,outputF,subst_output,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] using
    toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![p,q,z,R,B]

theorem returned_conjugate (p q z R B : PTm n) : Γ ⊢[PRAAx]
    fstT (run p q z R B) ≐ ap2 (GaussianNameConjugation.nameF GaussianGammaC7Name.nameF) p (GaussianGammaC7Name.data z R B) :=
  (program_at p q z R B).fstE
theorem returned_original (p q z R B : PTm n) : Γ ⊢[PRAAx]
    sndT (run p q z R B) ≐ GaussianGammaC7Name.sample q (conjugate z) R B :=
  (program_at p q z R B).sndE
theorem returned_distance (p q z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    distanceBounded (fstT (run p q z R B)) (sndT (run p q z R B)) (unit p+unit q) (unit p*unit q) :=
  GaussianRationalDistanceOrder.distance_congr (returned_conjugate p q z R B).eqSymm (returned_original p q z R B).eqSymm
    (.eqRefl _) (.eqRefl _) (GaussianNameEquivalence.cross_at _ _ _ _ p q (original_reciprocal_conjugate z R B h))

theorem actual_original_raw_finite_conjugation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 3) ⟶
      point (ap2 GaussianGammaWeierstrassFiniteName.rawF (var 0) (GaussianGammaWeierstrassFiniteName.data (var 1) (var 2) (var 3) (var 4))) ≐
        ap2 GaussianGammaWeierstrassFiniteName.rawF (var 0) (GaussianGammaWeierstrassFiniteName.data (conjugate (var 1)) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (raw_sample_covariance _ _ _ _ _ Prf.hyp0))

theorem actual_finite_product_name_conjugation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) ⟶
      crossEquivalent (GaussianNameConjugation.nameF GaussianGammaWeierstrassFiniteName.nameF) GaussianGammaWeierstrassFiniteName.nameF
        (GaussianGammaWeierstrassFiniteName.nameData (var 0) (var 1) (var 2) (var 3))
        (GaussianGammaWeierstrassFiniteName.nameData (conjugate (var 0)) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (finite_name_conjugate _ _ _ _ Prf.hyp0))

theorem actual_euler_exponent_conjugation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 1) ⟶ crossEquivalent (GaussianNameConjugation.nameF positiveExponentF) positiveExponentF
      (positiveExponentData (var 0) (var 1)) (positiveExponentData (conjugate (var 0)) (var 1))) :=
  closeUniv 2 (.impI (positive_exponent_conjugate _ _ Prf.hyp0))

theorem actual_euler_exponential_conjugation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 1) ⟶ crossEquivalent (GaussianNameConjugation.nameF positiveExpF) positiveExpF
      (positiveExpData (var 0) (var 1)) (positiveExpData (conjugate (var 0)) (var 1))) :=
  closeUniv 2 (.impI (positive_exp_conjugate _ _ Prf.hyp0))

theorem original_literal_C5_conjugation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) ⟶ crossEquivalent (GaussianNameConjugation.nameF literalF) literalF
      (literalData (var 0) (var 1) (var 2) (var 3)) (literalData (conjugate (var 0)) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (literal_conjugate _ _ _ _ Prf.hyp0))

theorem original_C11_conjugation_observation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 1) (var 2) (var 3) ⟶ distanceBounded
      (ap2 (GaussianNameConjugation.nameF GaussianGammaWeierstrassLimit.nameF) (var 0)
        (GaussianGammaWeierstrassConvergence.data (var 1) (var 2) (var 3)))
      (GaussianGammaWeierstrassLimit.sample (var 0) (conjugate (var 1)) (var 2) (var 3)) one (unit (var 0))) :=
  closeUniv 4 (.impI (cofinal_conjugate_at _ _ _ _ Prf.hyp0))

theorem original_C11_conjugation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 0) (var 1) (var 2) ⟶
      crossEquivalent (GaussianNameConjugation.nameF GaussianGammaWeierstrassLimit.nameF) GaussianGammaWeierstrassLimit.nameF
        (GaussianGammaWeierstrassConvergence.data (var 0) (var 1) (var 2))
        (GaussianGammaWeierstrassConvergence.data (conjugate (var 0)) (var 1) (var 2))) :=
  closeUniv 3 (.impI (cofinal_conjugate _ _ _ Prf.hyp0))

theorem original_C26_reciprocal_conjugation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 0) (var 1) (var 2) ⟶
      crossEquivalent (GaussianNameConjugation.nameF GaussianGammaC7Name.nameF) GaussianGammaC7Name.nameF
        (GaussianGammaC7Name.data (var 0) (var 1) (var 2)) (GaussianGammaC7Name.data (conjugate (var 0)) (var 1) (var 2))) :=
  closeUniv 3 (.impI (original_reciprocal_conjugate _ _ _ Prf.hyp0))

theorem actual_returned_C26_observations_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 2) (var 3) (var 4) ⟶
      distanceBounded (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4)))
        (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))) (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 5 (.impI (returned_distance _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaNameConjugation
