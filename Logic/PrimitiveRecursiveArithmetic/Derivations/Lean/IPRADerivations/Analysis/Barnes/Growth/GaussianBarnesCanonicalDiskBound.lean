import IPRADerivations.Analysis.Barnes.CanonicalProducts.GaussianBarnesCanonicalValue

/-!
# A disk bound for the original fixed Barnes prefix

The actual sampled prefactor uses a radius computed from two zeroth
observations. Bound both observations uniformly before passing to the
prefactor, and retain the same bound through the fixed finite head.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDiskBound

open_ipra
open GaussianRationalPowerDifference (bounded_sum_one)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogSchedule (initial)
open GaussianBarnesCanonicalPrefactor
open GaussianCoefficientNameBounds (bounded_radius_mono_one)
open GaussianEuclideanDistanceName (fraction_represents)
open GaussianGammaCanonicalExponent (constantF constant_at gammaF gamma_regular)
open GaussianGeneralFTAConstants (ceilL1 l1_natural_representation)
open GaussianNameArithmetic (addF addData add_at multiplyF multiplyData multiply_at multiplyModulus)
open GaussianNameBounds (U sample_bound)
open GaussianRationalHorner (ofGaussian ofGaussian_represents qmul)
open GaussianRationalMetric (bounded bounded_of_cleared comparison_to_cleared qnegative_represents)
open RationalIntegerNormalization (positivePart)
open RationalSupMetric (numeratorOf denominatorOf)
open GaussianRationalReciprocal (bound_congr bounded_product bounded_product_one bounded_sum)
open GaussianRadiusExponentialLipschitzRate (factor)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem add_bound (f g : PR 2) (x y p A B : PTm n)
    (hf : ∀ s : PTm n, Γ ⊢[PRAAx] bounded (ap2 f s x) A one)
    (hg : ∀ s : PTm n, Γ ⊢[PRAAx] bounded (ap2 g s y) B one) :
    Γ ⊢[PRAAx] bounded (ap2 (addF f g) p (addData x y)) (A+B) one := by
  let s := GaussianFastValueCut.exponent two p
  exact bound_congr (add_at f g x y p).eqSymm (.eqRefl _) (.eqRefl _)
    ((GaussianFastValueCut.recode_bound_iff _ _ one (le_refl one)).iffMpr
      (bounded_sum_one (hf s) (hg s)))

private theorem multiply_bound (f g : PR 2) (x y p A B : PTm n)
    (hf : ∀ s : PTm n, Γ ⊢[PRAAx] bounded (ap2 f s x) A one)
    (hg : ∀ s : PTm n, Γ ⊢[PRAAx] bounded (ap2 g s y) B one) :
    Γ ⊢[PRAAx] bounded (ap2 (multiplyF f g) p (multiplyData f g x y)) (A*B) one := by
  let s := GaussianFastValueCut.exponent (multiplyModulus f g x y) p
  have raw := bounded_product _ _ A one B one (le_refl one) (le_refl one) (hf s) (hg s)
  exact bound_congr (multiply_at f g x y p).eqSymm (.eqRefl _) (.eqRefl _)
    ((GaussianFastValueCut.recode_bound_iff _ _ one (le_refl one)).iffMpr
      (bound_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) raw))

private theorem constant_bound (x p A : PTm n) (h : Γ ⊢[PRAAx] bounded x A one) :
    Γ ⊢[PRAAx] bounded (ap2 constantF p x) A one :=
  bound_congr (constant_at p x).eqSymm (.eqRefl _) (.eqRefl _) h

private theorem U_le (f : PR 2) (x C : PTm n) (h : Γ ⊢[PRAAx] bounded (ap2 f zero x) C one) :
    Γ ⊢[PRAAx] le (U f x) (two*C+two) := by
  let q := ap2 f zero x
  let A := positivePart (numeratorOf (GaussianRationalL1.qL1 q))
  let B := denominatorOf (GaussianRationalL1.qL1 q)
  have hb : Γ ⊢[PRAAx] le one B := RationalArgmin.denominator_positive _
  have hl := GaussianRationalL1Algebra.qL1_of_bounded q C one (le_refl one) h
  have cle := comparison_to_cleared _ _ A (two*C) B one (l1_natural_representation q)
    (fraction_represents _ _ (le_refl one)) hl
  have ceil : Γ ⊢[PRAAx] le (ceilL1 q) (two*C) :=
    GaussianDescentClockArithmetic.ceiling_least A B (two*C) hb
      (le_congr (one_mul A) (mul_comm _ _) cle)
  exact add_le_add_right two ceil

private theorem fraction_bound (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] bounded (ofGaussian z B) R one :=
  bounded_of_cleared _ _ _ _ _ h.andE₁ (le_refl one) (ofGaussian_represents _ _ h.andE₁)
    (le_congr (by ipra_ring) (by ipra_ring) h.andE₂)

private def L (R : PTm n) : PTm n := R*U GaussianStirlingConstant.nameF (GaussianStirlingConstant.nameData zero)
private def C (R : PTm n) : PTm n := R+(R*R)*(one+U gammaF zero)
def prefactorRadius (R : PTm n) : PTm n := (two*L R+two)+(two*C R+two)
def prefactorBound (R : PTm n) : PTm n := factor (prefactorRadius R)*factor (prefactorRadius R)

@[simp] theorem subst_prefactorBound {m : ℕ} (σ : Fin n → PTm m) (R : PTm n) :
    Syn.subst σ (prefactorBound R) = prefactorBound (Syn.subst σ R) := by
  simp [prefactorBound,prefactorRadius,L,C,one,two,GaussianStirlingConstant.nameData]

private theorem linear_bound (p z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] bounded (ap2 linearF p (linearData z B)) (L R) one :=
  multiply_bound _ _ _ _ p R _ (fun s => constant_bound _ s _ (fraction_bound z R B h))
    (fun s => sample_bound _ _ s (GaussianStirlingConstant.name_regular zero))

private theorem correction_bound (p z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] bounded (ap2 correctionF p (correctionData z B)) (C R) one := by
  let a := ofGaussian z B
  have ha : Γ ⊢[PRAAx] bounded a R one := fraction_bound z R B h
  have hs : Γ ⊢[PRAAx] bounded (qmul a a) (R*R) one :=
    bounded_product_one ha ha
  have qc : ∀ s : PTm n, Γ ⊢[PRAAx] bounded (ap2 quadraticCoefficientF s quadraticCoefficientData)
      (one+U gammaF zero) one := fun s =>
    add_bound _ _ _ _ s one _ (fun t => bound_congr (GaussianNameRingLaws.one_at t zero).eqSymm
      (.eqRefl _) (.eqRefl _) GaussianRationalReciprocal.qone_bounded)
      (fun t => sample_bound gammaF zero t gamma_regular)
  have q : ∀ s : PTm n, Γ ⊢[PRAAx] bounded (ap2 quadraticF s (quadraticData z B)) ((R*R)*(one+U gammaF zero)) one :=
    fun s => multiply_bound _ _ _ _ s _ _ (fun t => constant_bound _ t _ hs) qc
  have poly : ∀ s : PTm n, Γ ⊢[PRAAx] bounded (ap2 polynomialF s (polynomialData z B)) (C R) one :=
    fun s => add_bound _ _ _ _ s _ _ (fun t => constant_bound _ t _ ha) q
  have half : Γ ⊢[PRAAx] bounded negativeHalf one one := by
    let v : PTm n := ComplexLogarithmRemainder.scale one ComplexLogarithmRemainder.oneCode
    have rep := qnegative_represents _ v two (ofGaussian_represents (Γ := Γ) v two (le_succ_self one))
    have norm := (ComplexLogarithmRemainder.normSq_neg (Γ := Γ) v).eqTrans
      ((ComplexLogarithmRemainder.normSq_scale one ComplexLogarithmRemainder.oneCode).eqTrans
        (congrMul (.eqRefl _) ComplexLogarithmRemainder.normSq_one))
    have normEq : Γ ⊢[PRAAx] ComplexLogarithmRemainder.normSq (ComplexLogarithmRemainder.neg v) ≐ one :=
      norm.eqTrans (by ipra_ring)
    exact bounded_of_cleared _ _ _ _ _ (le_succ_self one) (le_refl one) rep
      (le_congr (congrMul (.eqRefl _) normEq).eqSymm (.eqRefl _)
        (le_of_eq_add (d := num 3) (by ipra_ring)))
  exact bound_congr (.eqRefl _) (one_mul _) (.eqRefl _)
    (multiply_bound _ _ _ _ p one (C R) (fun s => constant_bound _ s _ half) poly)

theorem radius_le (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] le (radius z B) (prefactorRadius R) :=
  add_le_add₂ (U_le linearF _ _ (linear_bound zero z R B h))
    (U_le correctionF _ _ (correction_bound zero z R B h))

private theorem exponential_bound (f : PR 2) (x r R p : PTm n)
    (h : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input f r x) (hr : Γ ⊢[PRAAx] le r R) :
    Γ ⊢[PRAAx] bounded (ap2 (GaussianRadiusExponentialName.nameF f) p
      (GaussianRadiusExponentialName.data r x)) (factor R) one := by
  let v := GaussianRadiusExponentialName.query f r p x
  have base := GaussianPositiveExponentialMajorant.disk_bound v r (GaussianRadiusExponentialName.index r p)
    (GaussianRadiusExponentialName.query_bound f r x p h)
  have leF : Γ ⊢[PRAAx] le (factor r) (factor R) :=
    GaussianFactorBudget.power_monotone_length (num 3) r R (le_trans (le_succ_self one) (le_succ_self two)) hr
  exact bound_congr (GaussianRadiusExponentialName.sample_at f r p x).eqSymm (.eqRefl _) (.eqRefl _)
    (bounded_radius_mono_one leF base)

theorem prefactor_sample_bound (p z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] bounded (ap2 nameF p (data z B)) (prefactorBound R) one :=
  multiply_bound _ _ _ _ p _ _
    (fun s => exponential_bound _ _ _ _ s (linear_input z B) (radius_le z R B h))
    (fun s => exponential_bound _ _ _ _ s (correction_input z B) (radius_le z R B h))

def prefixBound (R : PTm n) : PTm n :=
  prefactorBound R*GaussianBarnesCanonicalHead.cap R zero (initial R)

theorem prefix_sample_bound (p z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    bounded (ap2 GaussianBarnesCanonicalValue.prefixF p (GaussianBarnesCanonicalValue.prefixData z R B))
      (prefixBound R) one :=
  multiply_bound _ _ _ _ p _ _ (fun s => prefactor_sample_bound s z R B h)
    (fun s => GaussianBarnesCanonicalHead.sample_bound s z R B zero (initial R) h)

theorem prefix_U_le (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    le (U GaussianBarnesCanonicalValue.prefixF (GaussianBarnesCanonicalValue.prefixData z R B))
      (two*prefixBound R+two) :=
  U_le _ _ _ (prefix_sample_bound zero z R B h)

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDiskBound
