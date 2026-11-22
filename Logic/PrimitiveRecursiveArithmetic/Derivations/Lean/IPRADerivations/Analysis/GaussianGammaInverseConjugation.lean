import IPRADerivations.Analysis.GaussianGammaNameConjugation
import IPRADerivations.Analysis.GaussianGammaReciprocalInverse

/-!
# Original Gamma conjugation on its actual pole-guard domain

The same cleared pole separation is preserved by conjugation. The
actual C7 product with the original Gamma reciprocal algorithm is then
conjugated using named multiplication. The already checked actual
reciprocal uniqueness theorem identifies the original Gamma name at
the conjugate input, retaining its independently computed anchor height.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaInverseConjugation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalConjugation (point point_congr)
open GaussianRationalReciprocal (conjugate)
open GaussianGammaEulerHeadLower (translated poleAt poleGuard)
open GaussianGammaReciprocalInverse (source gammaF gammaData gammaHeight gamma_regular gamma_product original_gamma_inverse)
open GaussianNameArithmetic (multiplyF multiplyData)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (oneF one_at one_fast)
open GaussianCoefficientNameBounds (unit)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem translated_conjugate (z B k : PTm n) : Γ ⊢[PRAAx]
    GaussianRootAlgebra.equal (translated (conjugate z) B k) (conjugate (translated z B k)) := by
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [translated,GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add,
      GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one,
      GaussianRationalReciprocal.re_conjugate,GaussianRationalReciprocal.im_conjugate]
  all_goals ring

theorem translated_norm (z B k : PTm n) : Γ ⊢[PRAAx]
    ComplexLogarithmRemainder.normSq (translated (conjugate z) B k) ≐ ComplexLogarithmRemainder.normSq (translated z B k) :=
  (GaussianRootAlgebra.normSq_equal (translated_conjugate z B k)).eqTrans (GaussianRationalReciprocal.norm_conjugate _)

theorem pole_at_conjugate (z B a d k : PTm n) (h : Γ ⊢[PRAAx] poleAt z B a d k) : Γ ⊢[PRAAx]
    poleAt (conjugate z) B a d k :=
  le_congr (.eqRefl _) (congrMul (.eqRefl _) (translated_norm z B k)).eqSymm h

theorem pole_guard_conjugate (z B a d N : PTm n) (h : Γ ⊢[PRAAx] poleGuard z B a d N) : Γ ⊢[PRAAx]
    poleGuard (conjugate z) B a d N := by
  refine .allI (.impI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] poleGuard (Syn.shift z) (Syn.shift B) (Syn.shift a) (Syn.shift d) (Syn.shift N) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  have old := GaussianGammaEulerHeadLower.pole_at (Syn.shift z) (Syn.shift B) (Syn.shift a) (Syn.shift d) (Syn.shift N)
    (var 0) hs.wk Prf.hyp0
  simpa only [poleGuard,Syn.shift,GaussianRationalReciprocal.subst_conjugate] using
    pole_at_conjugate (Syn.shift z) (Syn.shift B) (Syn.shift a) (Syn.shift d) (var 0) old

theorem source_conjugate (z R B a d : PTm n) (h : Γ ⊢[PRAAx] source z R B a d) : Γ ⊢[PRAAx]
    source (conjugate z) R B a d :=
  .andI (GaussianGammaFiniteConjugation.source_conjugate z R B h.andE₁)
    (.andI h.andE₂.andE₁ (.andI h.andE₂.andE₂.andE₁
      (pole_guard_conjugate z B a d (two*R) h.andE₂.andE₂.andE₂)))

theorem one_sample_fixed (p x : PTm n) : Γ ⊢[PRAAx]
    ap2 (GaussianNameConjugation.nameF oneF) p x ≐ ap2 oneF p x :=
  (GaussianNameConjugation.sample_at _ p x).eqTrans
    ((point_congr (one_at p x)).eqTrans ((GaussianRationalConjugation.point_one).eqTrans (one_at p x).eqSymm))

theorem one_name_fixed (x : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent (GaussianNameConjugation.nameF oneF) oneF x x := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _ (GaussianNameConjugation.regular _ _ (one_fast x)) (one_fast x)
  refine .allI ?_
  simpa only [GaussianNameConjugation.pointwiseEqual,Syn.shift] using
    one_sample_fixed (Γ := Γ.map Fm.shift) (var 0) (Syn.shift x)

/-- The original P at the conjugate input multiplies the conjugated
original Gamma name to one. No inverse output law is supplied. -/
theorem conjugated_inverse_product (z R B a d : PTm n) (h : Γ ⊢[PRAAx] source z R B a d) : Γ ⊢[PRAAx]
    crossEquivalent (multiplyF GaussianGammaC7Name.nameF (GaussianNameConjugation.nameF gammaF)) oneF
      (multiplyData GaussianGammaC7Name.nameF (GaussianNameConjugation.nameF gammaF)
        (GaussianGammaC7Name.data (conjugate z) R B) (gammaData z R B d))
      (GaussianGammaC7Name.data (conjugate z) R B) := by
  let P := GaussianGammaC7Name.nameF
  let x := GaussianGammaC7Name.data z R B
  let x' := GaussianGammaC7Name.data (conjugate z) R B
  let y := gammaData z R B d
  have hp : Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN P x := GaussianGammaC7Name.name_regular z R B h.andE₁
  have hq : Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN P x' :=
    GaussianGammaC7Name.name_regular (conjugate z) R B (source_conjugate z R B a d h).andE₁
  have hg := gamma_regular z R B a d h
  have chp := GaussianNameConjugation.regular P x hp
  have chg := GaussianNameConjugation.regular gammaF y hg
  have product := GaussianNameConjugation.conjugate_cross _ _ _ _ (gamma_product z R B a d h)
  have expand := GaussianNameConjugation.multiply_cross P gammaF x y hp hg
  have replace := GaussianGammaAdjacentCutoff.multiply_cross
    (GaussianNameConjugation.nameF P) P (GaussianNameConjugation.nameF gammaF) (GaussianNameConjugation.nameF gammaF)
    x x' y y chp hq chg chg (GaussianGammaNameConjugation.original_reciprocal_conjugate z R B h.andE₁)
    (cross_refl _ _ chg)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ replace)
    (cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ expand)
      (cross_trans _ _ _ _ _ _ product
        (cross_trans _ _ _ _ _ _ (one_name_fixed x) (GaussianBoundedInverseApartness.ones_equivalent x x'))))

/-- Original C26 for the actual Gamma program, with the SAME original
pole guard and independently recomputed reciprocal anchor at the target. -/
theorem original_gamma_conjugate (z R B a d : PTm n) (h : Γ ⊢[PRAAx] source z R B a d) : Γ ⊢[PRAAx]
    crossEquivalent (GaussianNameConjugation.nameF gammaF) gammaF
      (gammaData z R B d) (gammaData (conjugate z) R B d) := by
  have hs := source_conjugate z R B a d h
  have target := (original_gamma_inverse (conjugate z) R B a d hs).andE₁
  exact cross_symm _ _ _ _ (GaussianBoundedInverseApartness.reciprocal_matches_inverse
    GaussianGammaC7Name.nameF (GaussianNameConjugation.nameF gammaF) (gammaHeight (conjugate z) R B d)
    (GaussianGammaC7Name.data (conjugate z) R B) (gammaData z R B d) target.andE₁
    (GaussianNameConjugation.regular _ _ (gamma_regular z R B a d h)) target.andE₂
    (conjugated_inverse_product z R B a d h))


@[simp] theorem subst_original_gamma_data {l : ℕ} (σ : Fin n → PTm l) (z R B d : PTm n) :
    Syn.subst σ (gammaData z R B d) = gammaData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ d) := by
  simp [gammaData,gammaHeight]

/-- The pole-separation numerator a belongs to the proof domain; the
original Gamma sampler itself uses the original data z,R,B,d. -/
def output (p q z R B d : PTm n) : PTm n :=
  pairT (ap2 (GaussianNameConjugation.nameF gammaF) p (gammaData z R B d))
    (ap2 gammaF q (gammaData (conjugate z) R B d))
def outputF : PR 6 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
def run (p q z R B d : PTm n) : PTm n := PTm.app outputF ![p,q,z,R,B,d]
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (p q z R B d : PTm n) :
    Syn.subst σ (output p q z R B d) = output (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ z)
      (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ d) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (p q z R B d : PTm n) :
    Syn.subst σ (run p q z R B d) = run (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ z)
      (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ d) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem program_at (p q z R B d : PTm n) : Γ ⊢[PRAAx] run p q z R B d ≐ output p q z R B d := by
  simpa [run,outputF,subst_output] using
    toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) ![p,q,z,R,B,d]

theorem returned_conjugate (p q z R B d : PTm n) : Γ ⊢[PRAAx]
    fstT (run p q z R B d) ≐ ap2 (GaussianNameConjugation.nameF gammaF) p (gammaData z R B d) :=
  (congrFst (program_at p q z R B d)).eqTrans (fst_pair _ _)
theorem returned_original (p q z R B d : PTm n) : Γ ⊢[PRAAx]
    sndT (run p q z R B d) ≐ ap2 gammaF q (gammaData (conjugate z) R B d) :=
  (congrSnd (program_at p q z R B d)).eqTrans (snd_pair _ _)
theorem returned_distance (p q z R B a d : PTm n) (h : Γ ⊢[PRAAx] source z R B a d) : Γ ⊢[PRAAx]
    GaussianRationalMetric.distanceBounded (fstT (run p q z R B d)) (sndT (run p q z R B d)) (unit p+unit q) (unit p*unit q) :=
  GaussianRationalDistanceOrder.distance_congr (returned_conjugate p q z R B d).eqSymm (returned_original p q z R B d).eqSymm
    (.eqRefl _) (.eqRefl _) (GaussianNameEquivalence.cross_at _ _ _ _ p q (original_gamma_conjugate z R B a d h))

theorem actual_original_pole_guard_conjugation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (poleGuard (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ poleGuard (conjugate (var 0)) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (.impI (pole_guard_conjugate _ _ _ _ _ Prf.hyp0))

theorem original_gamma_pole_domain_conjugation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ source (conjugate (var 0)) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (.impI (source_conjugate _ _ _ _ _ Prf.hyp0))

theorem actual_original_conjugate_gamma_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      crossEquivalent (multiplyF GaussianGammaC7Name.nameF (GaussianNameConjugation.nameF gammaF)) oneF
        (multiplyData GaussianGammaC7Name.nameF (GaussianNameConjugation.nameF gammaF)
          (GaussianGammaC7Name.data (conjugate (var 0)) (var 1) (var 2)) (gammaData (var 0) (var 1) (var 2) (var 4)))
        (GaussianGammaC7Name.data (conjugate (var 0)) (var 1) (var 2))) :=
  closeUniv 5 (.impI (conjugated_inverse_product _ _ _ _ _ Prf.hyp0))

theorem original_C26_gamma_conjugation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      crossEquivalent (GaussianNameConjugation.nameF gammaF) gammaF
        (gammaData (var 0) (var 1) (var 2) (var 4)) (gammaData (conjugate (var 0)) (var 1) (var 2) (var 4))) :=
  closeUniv 5 (.impI (original_gamma_conjugate _ _ _ _ _ Prf.hyp0))

theorem actual_original_C26_gamma_observations_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (source (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      GaussianRationalMetric.distanceBounded (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 6)))
        (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 6))) (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 7 (.impI (returned_distance _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaInverseConjugation
