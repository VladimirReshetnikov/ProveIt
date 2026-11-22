import IPRADerivations.Analysis.GaussianGammaPerturbationExponent
import IPRADerivations.Analysis.GaussianGammaFoldedApproximantBalance
import IPRADerivations.Analysis.GaussianGammaCutoffIndependence
import IPRADerivations.Analysis.GaussianGammaC9Bound
import IPRADerivations.Analysis.GaussianNamedSmallPerturbationTransport

/-!
# The quantitative C10 Euler convergence estimate

The two actual folded C8 product identities give the Euler name as
the original fixed-cutoff reciprocal name times the exponential of
the perturbation. This factorization uses only multiplication.
The exactly bounded representative of the perturbation supplies
the numerical constant in C10, with the usual independent observation
errors at the two requested precisions.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaEulerConvergence

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast multiply_equivalent)
open GaussianNameEquivalence (crossEquivalent cross_to_diagonal cross_trans cross_symm diagonal_refl)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaFoldedApproximantBalance (tail_factor_identity euler_factor_identity exponential_product_equivalent
  tailExpF tailExpData tailProductF tailProductData correctionExpF correctionExpData eulerProductF eulerProductData)
open GaussianGammaFoldedExponentBalance (correctionF correctionData correction_fast)
open GaussianGammaFiniteApproximantName (pF pData p_regular qF qData exponentialInputData exponential_input)
open GaussianGammaPerturbationExponent (deltaF deltaData delta_regular delta_envelope numerator slack tail_plus_delta)
open GaussianNamedSmallPerturbationTransport (prefactorSamples correctionSamples budgetNumerator budgetDenominator)
open GaussianRationalMetric (distanceBounded)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def deltaExpF : PR 2 := GaussianRadiusExponentialName.nameF deltaF
def deltaExpData (z R B N : PTm n) : PTm n := exponentialInputData deltaF (deltaData z R B N)

theorem euler_product_at_cutoff (z R B N : PTm n)
    (h : Γ ⊢[PRAAx] GaussianGammaCanonicalTailName.source z R B N) :
    Γ ⊢[PRAAx] crossEquivalent qF (multiplyF GaussianGammaCutoffName.nameF deltaExpF)
      (qData z B N) (multiplyData GaussianGammaCutoffName.nameF deltaExpF
        (GaussianGammaCutoffName.data z R B N) (deltaExpData z R B N)) := by
  let P := pData z B N
  let T := tailExpData z R B N
  let D := deltaExpData z R B N
  let C := correctionExpData z B N
  let X := GaussianGammaCutoffName.data z R B N
  let H := GaussianGammaCutoffName.nameF
  let E := deltaExpF
  let J := GaussianGammaCanonicalTailName.pointF
  let Y := GaussianGammaCanonicalTailName.data z R B N
  have pn : Γ ⊢[PRAAx] pointCN pF P := p_regular z B N
  have hn : Γ ⊢[PRAAx] pointCN H X := GaussianGammaCutoffName.name_regular z R B N h
  have jt := exponential_input J Y (GaussianGammaCanonicalTailName.name_regular z R B N h)
  have jd := exponential_input deltaF (deltaData z R B N) (delta_regular z R B N h)
  have jc := exponential_input correctionF (correctionData z B N) (correction_fast z B N h.andE₂.andE₁)
  have tn : Γ ⊢[PRAAx] pointCN tailExpF T := GaussianRadiusExponentialName.name_regular _ _ _ jt
  have dn : Γ ⊢[PRAAx] pointCN E D := GaussianRadiusExponentialName.name_regular _ _ _ jd
  have cn : Γ ⊢[PRAAx] pointCN correctionExpF C := GaussianRadiusExponentialName.name_regular _ _ _ jc
  have ex : Γ ⊢[PRAAx] crossEquivalent (multiplyF tailExpF E) correctionExpF (multiplyData tailExpF E T D) C :=
    exponential_product_equivalent J deltaF correctionF _ _ _ Y (deltaData z R B N) (correctionData z B N)
      jt jd jc (tail_plus_delta z R B N h)
  have ht := multiply_equivalent H tailProductF E E X (tailProductData z R B N) D D hn
    (multiply_fast pF tailExpF P T pn tn) dn dn
    (cross_to_diagonal _ _ _ _ (tail_factor_identity z R B N h)) (diagonal_refl E D)
  have ha := GaussianNameRingLaws.multiply_associative pF tailExpF E P T D pn tn dn
  have hm := multiply_equivalent pF pF (multiplyF tailExpF E) correctionExpF P P (multiplyData tailExpF E T D) C
    pn pn (multiply_fast tailExpF E T D tn dn) cn (diagonal_refl pF P) (cross_to_diagonal _ _ _ _ ex)
  have he := cross_trans _ _ _ _ _ _ ht (cross_trans _ _ _ _ _ _ ha hm)
  exact cross_trans _ _ _ _ _ _ (euler_factor_identity z B N h.andE₂.andE₁) (cross_symm _ _ _ _ he)

def source (z R B N : PTm n) : Fm PTm n :=
  GaussianGammaCanonicalExponent.source z R B ⋏ (le (two*R) N ⋏ le (numerator R) N)

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (z R B N : PTm n) :
    (source z R B N).subst σ = source (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) := by
  simp [source]

theorem local_source (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] GaussianGammaCanonicalTailName.source z R B N :=
  .andI h.andE₁.andE₂.andE₁
    (.andI (le_trans (GaussianGammaCanonicalExponent.tail_source z R B h.andE₁).andE₂.andE₁ h.andE₂.andE₁)
      (.andI h.andE₁.andE₂.andE₂ h.andE₂.andE₁))

def exactF : PR 2 := GaussianExactDiskShrinking.nameF deltaF
def exactData (z R B N : PTm n) : PTm n :=
  GaussianExactDiskShrinking.data (deltaData z R B N) (numerator R) N (slack z R B N)
def smallExpF : PR 2 := GaussianUnitDiskExponentialName.nameF exactF
def smallExpData (z R B N : PTm n) : PTm n := exactData z R B N

theorem small_exp (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] pointCN smallExpF (smallExpData z R B N) ⋏
      correctionSamples smallExpF (smallExpData z R B N) (numerator R) N := by
  have s := local_source z R B N h
  simpa only [smallExpF, smallExpData, exactF, exactData, correctionSamples,
    GaussianExponentialSmallPerturbation.nearOneSamples, GaussianUnitDiskExponentialName.sample] using
    GaussianExactDiskShrinking.exponential_near_one deltaF (deltaData z R B N) (numerator R) N (slack z R B N)
      s.andE₂.andE₁ h.andE₂.andE₂ (delta_regular z R B N s) (delta_envelope z R B N s)

theorem euler_actual_product (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] crossEquivalent qF (multiplyF GaussianGammaC7Name.nameF smallExpF) (qData z B N)
      (multiplyData GaussianGammaC7Name.nameF smallExpF (GaussianGammaC7Name.data z R B) (smallExpData z R B N)) := by
  let X := GaussianGammaCutoffName.data z R B N
  let H := GaussianGammaCutoffName.nameF
  let Y := GaussianGammaC7Name.data z R B
  let K := GaussianGammaC7Name.nameF
  let D := deltaExpData z R B N
  let U := smallExpData z R B N
  let dt := deltaData z R B N
  have s := local_source z R B N h
  have inp := exponential_input deltaF dt (delta_regular z R B N s)
  have he : Γ ⊢[PRAAx] crossEquivalent deltaExpF smallExpF D U :=
    GaussianExactDiskExponential.original_exp_equiv_shrunk_unit deltaF _ dt (numerator R) N (slack z R B N)
      inp s.andE₂.andE₁ h.andE₂.andE₂ (delta_envelope z R B N s)
  have hc := GaussianGammaCutoffIndependence.original_C7_cutoff_equivalent z R B N h.andE₁ h.andE₂.andE₁
  have a := multiply_equivalent H K deltaExpF smallExpF X Y D U
    (GaussianGammaCutoffName.name_regular z R B N s) (GaussianGammaC7Name.name_regular z R B h.andE₁)
    (GaussianRadiusExponentialName.name_regular _ _ _ inp) (small_exp z R B N h).andE₁
    (cross_to_diagonal _ _ _ _ (cross_symm _ _ _ _ hc)) (cross_to_diagonal _ _ _ _ he)
  exact cross_trans _ _ _ _ _ _ (euler_product_at_cutoff z R B N s) a

theorem reciprocal_prefactor (z R B : PTm n) (h : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source z R B) :
    Γ ⊢[PRAAx] prefactorSamples GaussianGammaC7Name.nameF (GaussianGammaC7Name.data z R B)
      (GaussianGammaC9Bound.majorant R) := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] GaussianGammaCanonicalExponent.source (Syn.shift z) (Syn.shift R) (Syn.shift B) := by
    simpa only [Fm.shift, Syn.shift, GaussianGammaCanonicalExponent.subst_source] using h.shift
  simpa only [prefactorSamples, Syn.shift, GaussianGammaC7Name.subst_data, GaussianGammaC9Bound.subst_majorant,
    GaussianGammaC7Name.sample] using
    Prf.andI (GaussianGammaC7Name.sample_canonical (Γ := Γ.map Fm.shift) (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B))
      (GaussianGammaC9Bound.reciprocal_sample_bound (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) hs)

theorem observation_error (p q z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 qF p (qData z B N)) (GaussianGammaC7Name.sample q z R B)
      (budgetNumerator p q (numerator R) N (GaussianGammaC9Bound.majorant R)) (budgetDenominator p q N) :=
  GaussianNamedSmallPerturbationTransport.independent_error GaussianGammaC7Name.nameF smallExpF qF
    (GaussianGammaC7Name.data z R B) (smallExpData z R B N) (qData z B N)
    (GaussianGammaC9Bound.majorant R) (numerator R) N p q
    (local_source z R B N h).andE₂.andE₁ (GaussianGammaC7Name.name_regular z R B h.andE₁)
    (reciprocal_prefactor z R B h.andE₁) (small_exp z R B N h).andE₂ (euler_actual_product z R B N h)

theorem original_euler_C10_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 2) (var 3) (var 4) (var 5) ⟶
      distanceBounded (ap2 qF (var 0) (qData (var 2) (var 4) (var 5)))
        (GaussianGammaC7Name.sample (var 1) (var 2) (var 3) (var 4))
        (budgetNumerator (var 0) (var 1) (numerator (var 3)) (var 5) (GaussianGammaC9Bound.majorant (var 3)))
        (budgetDenominator (var 0) (var 1) (var 5))) :=
  closeUniv 6 (.impI (observation_error _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaEulerConvergence
