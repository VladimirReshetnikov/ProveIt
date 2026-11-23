import IPRADerivations.Analysis.GaussianEulerExponentialSubstitutionIntegrand
import IPRADerivations.Analysis.GaussianNameRingLaws

/-!
# The actual named-input kernel exp((z/B)u-exp(u))

All nested exponentials and arithmetic use their original normalization
and computed-radius programs. Every regular input name is accepted;
realness is a separate possible restriction. At the original positive
rational logarithm, the checked exp(log(t))=t identity identifies this
kernel with the original exponential pullback, at independent queries.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerExponentialSubstitutionNamedKernel

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaCanonicalExponent (constantF constant_regular constant_at)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast addF addData add_fast)
open GaussianNameRingLaws (negativeF negativeData negative_fast)
open GaussianGammaFiniteApproximantName (exponentialInputData exponential_input)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_trans cross_symm cross_to_diagonal cross_at)
open GaussianEuclideanDistanceName (pointCN)
open GaussianRationalHorner (ofGaussian qadd qmul qzero)
open GaussianRationalMetric (qsub qnegative distanceBounded)
open GaussianCoefficientNameBounds (unit)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

abbrev innerF (f : PR 2) : PR 2 := GaussianRadiusExponentialName.nameF f
def innerData (f : PR 2) (x : PTm n) : PTm n := exponentialInputData f x
abbrev linearF (f : PR 2) : PR 2 := multiplyF constantF f
def linearData (f : PR 2) (z B x : PTm n) : PTm n := multiplyData constantF f (ofGaussian z B) x
abbrev exponentF (f : PR 2) : PR 2 := addF (linearF f) (negativeF (innerF f))
def exponentData (f : PR 2) (z B x : PTm n) : PTm n := addData (linearData f z B x) (negativeData (innerData f x))
def radius (f : PR 2) (z B x : PTm n) : PTm n := GaussianNameBounds.U (exponentF f) (exponentData f z B x)
abbrev nameF (f : PR 2) : PR 2 := GaussianRadiusExponentialName.nameF (exponentF f)
def data (f : PR 2) (z B x : PTm n) : PTm n := GaussianRadiusExponentialName.data (radius f z B x) (exponentData f z B x)

@[simp] theorem subst_innerData {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (x : PTm n) :
    Syn.subst σ (innerData f x) = innerData f (Syn.subst σ x) := by simp [innerData,exponentialInputData]
@[simp] theorem subst_linearData {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (z B x : PTm n) :
    Syn.subst σ (linearData f z B x) = linearData f (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ x) := by simp [linearData]
@[simp] theorem subst_exponentData {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (z B x : PTm n) :
    Syn.subst σ (exponentData f z B x) = exponentData f (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ x) := by simp [exponentData]
@[simp] theorem subst_radius {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (z B x : PTm n) :
    Syn.subst σ (radius f z B x) = radius f (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ x) := by simp [radius]
@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (z B x : PTm n) :
    Syn.subst σ (data f z B x) = data f (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ x) := by simp [data]

theorem inner_regular (f : PR 2) (x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) : Γ ⊢[PRAAx] pointCN (innerF f) (innerData f x) :=
  GaussianRadiusExponentialName.name_regular f _ x (exponential_input f x hf)

theorem linear_regular (f : PR 2) (z B x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) : Γ ⊢[PRAAx] pointCN (linearF f) (linearData f z B x) :=
  multiply_fast constantF f _ _ (constant_regular _) hf

theorem exponent_regular (f : PR 2) (z B x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) : Γ ⊢[PRAAx] pointCN (exponentF f) (exponentData f z B x) :=
  add_fast _ _ _ _ (linear_regular f z B x hf) (negative_fast (innerF f) _ (inner_regular f x hf))

theorem original_input (f : PR 2) (z B x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) : Γ ⊢[PRAAx]
    GaussianRadiusExponentialName.input (exponentF f) (radius f z B x) (exponentData f z B x) :=
  exponential_input (exponentF f) _ (exponent_regular f z B x hf)

theorem name_regular (f : PR 2) (z B x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) : Γ ⊢[PRAAx] pointCN (nameF f) (data f z B x) :=
  GaussianRadiusExponentialName.name_regular _ _ _ (original_input f z B x hf)

theorem linear_at (f : PR 2) (p z B x : PTm n) : Γ ⊢[PRAAx]
    ap2 (linearF f) p (linearData f z B x) ≐ qmul (ofGaussian z B)
      (ap2 f (GaussianFastValueCut.exponent (GaussianNameArithmetic.multiplyModulus constantF f (ofGaussian z B) x) p) x) :=
  (GaussianNameArithmetic.multiply_at constantF f _ _ p).eqTrans
    ((GaussianNameArithmetic.recode_congr (GaussianRationalSyntheticDivision.qmul_congr (constant_at _ _) (.eqRefl _))).eqTrans
      (GaussianExponentialReference.recode_fixed _ (GaussianRationalHorner.qmul_canonical _ _)))

theorem exponent_at (f : PR 2) (p z B x : PTm n) : Γ ⊢[PRAAx]
    ap2 (exponentF f) p (exponentData f z B x) ≐ GaussianFastValueCut.recode (qadd
      (ap2 (linearF f) (GaussianFastValueCut.exponent two p) (linearData f z B x))
      (ap2 (negativeF (innerF f)) (GaussianFastValueCut.exponent two p) (negativeData (innerData f x)))) :=
  GaussianNameArithmetic.add_at _ _ _ _ p

theorem inner_proper (f g : PR 2) (x y : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y) : Γ ⊢[PRAAx] crossEquivalent (innerF f) (innerF g) (innerData f x) (innerData g y) :=
  GaussianExponentialRadiusIndependence.independent_radii_proper f g _ _ x y (exponential_input f x hf) (exponential_input g y hg) he

theorem exponent_proper (f g : PR 2) (z B x y : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y) : Γ ⊢[PRAAx]
    crossEquivalent (exponentF f) (exponentF g) (exponentData f z B x) (exponentData g z B y) := by
  have l := GaussianGammaAdjacentCutoff.multiply_cross constantF constantF f g (ofGaussian z B) (ofGaussian z B) x y
    (constant_regular _) (constant_regular _) hf hg (cross_refl _ _ (constant_regular _)) he
  have e := inner_proper f g x y hf hg he
  have neg := GaussianNameRingLaws.negative_equivalent (innerF f) (innerF g) (innerData f x) (innerData g y)
    (inner_regular f x hf) (inner_regular g y hg) (cross_to_diagonal _ _ _ _ e)
  exact GaussianNameArithmetic.add_equivalent (linearF f) (linearF g) (negativeF (innerF f)) (negativeF (innerF g))
    _ _ _ _ (linear_regular f z B x hf) (linear_regular g z B y hg)
    (negative_fast _ _ (inner_regular f x hf)) (negative_fast _ _ (inner_regular g y hg))
    (cross_to_diagonal _ _ _ _ l) (cross_to_diagonal _ _ _ _ neg)

theorem name_proper (f g : PR 2) (z B x y : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y) : Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF g) (data f z B x) (data g z B y) :=
  GaussianExponentialRadiusIndependence.independent_radii_proper (exponentF f) (exponentF g) _ _ _ _
    (original_input f z B x hf) (original_input g z B y hg) (exponent_proper f g z B x y hf hg he)

private theorem negative_constant_at (p q : PTm n) : Γ ⊢[PRAAx]
    ap2 (negativeF constantF) p (negativeData q) ≐ qnegative q := by
  have e : Γ ⊢[PRAAx] qsub qzero (ap2 constantF (GaussianFastValueCut.exponent (one+one) p) q) ≐ qnegative q :=
    (GaussianRationalSyntheticDivision.qsub_congr (.eqRefl _) (constant_at _ _)).eqTrans
      (GaussianRationalSyntheticDivision.qzero_add _ (GaussianRationalMetric.qnegative_canonical q))
  exact (GaussianNameRingLaws.negative_at constantF q p).eqTrans
    ((GaussianNameArithmetic.recode_congr e).eqTrans (GaussianExponentialReference.recode_fixed _ (GaussianRationalMetric.qnegative_canonical q)))

private theorem negative_constant_cross (q : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent (negativeF constantF) constantF (negativeData q) (qnegative q) := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _ (negative_fast constantF q (constant_regular _)) (constant_regular _)
  refine .allI ?_
  simpa only [GaussianNameConjugation.pointwiseEqual,GaussianNameRingLaws.subst_negativeData,GaussianRationalMetric.subst_qnegative,Syn.shift] using
    (negative_constant_at (Γ := Γ.map Fm.shift) (var 0) (Syn.shift q)).eqTrans (constant_at _ _).eqSymm

theorem original_logarithm_exponent (z B a b : PTm n) (h : Γ ⊢[PRAAx] GaussianEulerIntegrandName.source z B a b) : Γ ⊢[PRAAx]
    crossEquivalent (exponentF GaussianPositiveRationalLogarithm.logF) GaussianEulerExponentialSubstitutionIntegrand.exponentF
      (exponentData GaussianPositiveRationalLogarithm.logF z B (GaussianPositiveRationalLogarithm.data a b))
      (GaussianEulerExponentialSubstitutionIntegrand.exponentData z B a b) := by
  let f := GaussianPositiveRationalLogarithm.logF
  let x := GaussianPositiveRationalLogarithm.data a b
  let q := GaussianPositiveRationalLogarithm.fraction a b
  have hf := GaussianPositiveRationalLogarithm.name_regular a b h.andE₂
  have hi := inner_regular f x hf
  have hc := constant_regular (Γ := Γ) q
  have ne := GaussianNameRingLaws.negative_equivalent (innerF f) constantF (innerData f x) q hi hc
    (cross_to_diagonal _ _ _ _ (GaussianPositiveRationalLogarithm.exponential_fraction a b h.andE₂))
  have negative := cross_trans _ _ _ _ _ _ ne (negative_constant_cross q)
  have linear := linear_regular f z B x hf
  exact GaussianNameArithmetic.add_equivalent (linearF f) (linearF f) (negativeF (innerF f)) constantF
    (linearData f z B x) (linearData f z B x) (negativeData (innerData f x)) (GaussianEulerIntegrandName.decayPoint a b)
    linear linear (negative_fast _ _ hi) (constant_regular _) (cross_to_diagonal _ _ _ _ (cross_refl _ _ linear))
    (cross_to_diagonal _ _ _ _ negative)

theorem original_at_log (z B a b : PTm n) (h : Γ ⊢[PRAAx] GaussianEulerIntegrandName.source z B a b) : Γ ⊢[PRAAx]
    crossEquivalent (nameF GaussianPositiveRationalLogarithm.logF) GaussianEulerExponentialSubstitutionIntegrand.exponentialF
      (data GaussianPositiveRationalLogarithm.logF z B (GaussianPositiveRationalLogarithm.data a b))
      (GaussianEulerExponentialSubstitutionIntegrand.data z B a b) :=
  GaussianExponentialRadiusIndependence.independent_radii_proper _ _ _ _ _ _
    (original_input GaussianPositiveRationalLogarithm.logF z B (GaussianPositiveRationalLogarithm.data a b)
      (GaussianPositiveRationalLogarithm.name_regular a b h.andE₂))
    (GaussianEulerExponentialSubstitutionIntegrand.exponential_input z B a b h) (original_logarithm_exponent z B a b h)

theorem original_log_observations (p q z B a b : PTm n) (h : Γ ⊢[PRAAx] GaussianEulerIntegrandName.source z B a b) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (nameF GaussianPositiveRationalLogarithm.logF) p
      (data GaussianPositiveRationalLogarithm.logF z B (GaussianPositiveRationalLogarithm.data a b)))
      (ap2 GaussianEulerExponentialSubstitutionIntegrand.exponentialF q (GaussianEulerExponentialSubstitutionIntegrand.data z B a b))
      (unit p+unit q) (unit p*unit q) := cross_at _ _ _ _ p q (original_at_log z B a b h)

theorem original_pullback (z B a b : PTm n) (h : Γ ⊢[PRAAx] GaussianEulerIntegrandName.source z B a b) : Γ ⊢[PRAAx]
    crossEquivalent (nameF GaussianPositiveRationalLogarithm.logF) GaussianEulerExponentialSubstitutionIntegrand.productF
      (data GaussianPositiveRationalLogarithm.logF z B (GaussianPositiveRationalLogarithm.data a b))
      (GaussianEulerExponentialSubstitutionIntegrand.productData z B a b) :=
  cross_trans _ _ _ _ _ _ (original_at_log z B a b h) (cross_symm _ _ _ _ (GaussianEulerExponentialSubstitutionIntegrand.original_pullback z B a b h))

theorem actual_named_exponential_substitution_kernel_regular_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (pointCN f (var 2) ⟶ pointCN (nameF f) (data f (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (name_regular f _ _ _ Prf.hyp0))

theorem actual_original_logarithm_exponential_substitution_kernel_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (GaussianEulerIntegrandName.source (var 0) (var 1) (var 2) (var 3) ⟶
      crossEquivalent (nameF GaussianPositiveRationalLogarithm.logF) GaussianEulerExponentialSubstitutionIntegrand.exponentialF
        (data GaussianPositiveRationalLogarithm.logF (var 0) (var 1) (GaussianPositiveRationalLogarithm.data (var 2) (var 3)))
        (GaussianEulerExponentialSubstitutionIntegrand.data (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (original_at_log _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerExponentialSubstitutionNamedKernel
