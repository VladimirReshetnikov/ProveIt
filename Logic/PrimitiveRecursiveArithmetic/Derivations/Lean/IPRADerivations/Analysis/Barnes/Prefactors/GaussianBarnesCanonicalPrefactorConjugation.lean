import IPRADerivations.Analysis.Barnes.Prefactors.GaussianBarnesCanonicalPrefactor
import IPRADerivations.Analysis.Gamma.GaussianGammaNameConjugation
import IPRADerivations.Analysis.Gamma.FunctionalEquations.GaussianNamedGammaHalfShift

/-!
# Conjugation of the original Barnes prefactor

The Stirling constant and the Euler–Mascheroni constant retain their
original real names. The two original exponentials retain their
separately computed radii at a rational input and its conjugate.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPrefactorConjugation

open_ipra
open GaussianBarnesCanonicalPrefactor
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular gammaF gamma_regular)
open GaussianGammaNameConjugation (constant_name_conjugate)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_trans)
open GaussianNameRingLaws (oneF one_at one_fast)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalConjugation (point point_congr point_embed point_mul point_one of_gaussian)
open GaussianRationalHorner (canonical ofGaussian ofGaussian_canonical qmul)
open GaussianRationalReciprocal (conjugate)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianSignedNameExponentialOrder (realSamples real_sample_at)
open RationalGaussianEmbedding (axis canonical_axis_roundtrip)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "Conj" => GaussianNameConjugation.nameF
local notation "Exp" => GaussianRadiusExponentialName.nameF
local notation "expData" => GaussianRadiusExponentialName.data
local notation "S" => GaussianStirlingConstant.nameF
local notation "stirlingData" => GaussianStirlingConstant.nameData

private theorem real_point_fixed (q : PTm n) (h : Γ ⊢[PRAAx] canonical q) (hr : Γ ⊢[PRAAx] axis q) :
    Γ ⊢[PRAAx] point q ≐ q :=
  let e := canonical_axis_roundtrip q h hr
  (point_congr e.eqSymm).eqTrans ((point_embed _).eqTrans e)

private theorem real_name_fixed (f : PR 2) (x : PTm n)
    (h : Γ ⊢[PRAAx] pointCN f x) (hr : Γ ⊢[PRAAx] realSamples f x) :
    Γ ⊢[PRAAx] crossEquivalent (Conj f) f x x := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _ (GaussianNameConjugation.regular _ _ h) h
  refine .allI ?_
  let X := Syn.shift x
  let p : PTm (n+1) := var 0
  let Δ := Γ.map Fm.shift
  have rs : Δ ⊢[PRAAx] realSamples f X := by simpa [Fm.shift,Syn.shift,Δ,X] using hr.shift
  have s := real_sample_at f X p rs
  exact (GaussianNameConjugation.sample_at f p X).eqTrans (real_point_fixed _ s.andE₁ s.andE₂)

private theorem product_conjugate (f g : PR 2) (x y u v : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hf' : Γ ⊢[PRAAx] pointCN f y)
    (hg : Γ ⊢[PRAAx] pointCN g u) (hg' : Γ ⊢[PRAAx] pointCN g v)
    (ef : Γ ⊢[PRAAx] crossEquivalent (Conj f) f x y)
    (eg : Γ ⊢[PRAAx] crossEquivalent (Conj g) g u v) : Γ ⊢[PRAAx]
    crossEquivalent (Conj (multiplyF f g)) (multiplyF f g) (multiplyData f g x u) (multiplyData f g y v) :=
  cross_trans _ _ _ _ _ _ (GaussianNameConjugation.multiply_cross f g x u hf hg)
    (GaussianGammaAdjacentCutoff.multiply_cross (Conj f) f (Conj g) g x y u v
      (GaussianNameConjugation.regular _ _ hf) hf' (GaussianNameConjugation.regular _ _ hg) hg' ef eg)

private theorem sum_conjugate (f g : PR 2) (x y u v : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hf' : Γ ⊢[PRAAx] pointCN f y)
    (hg : Γ ⊢[PRAAx] pointCN g u) (hg' : Γ ⊢[PRAAx] pointCN g v)
    (ef : Γ ⊢[PRAAx] crossEquivalent (Conj f) f x y)
    (eg : Γ ⊢[PRAAx] crossEquivalent (Conj g) g u v) : Γ ⊢[PRAAx]
    crossEquivalent (Conj (addF f g)) (addF f g) (addData x u) (addData y v) :=
  cross_trans _ _ _ _ _ _ (GaussianNameConjugation.add_cross f g x u hf hg)
    (GaussianNamedGammaHalfShift.add_cross (Conj f) f (Conj g) g x y u v
      (GaussianNameConjugation.regular _ _ hf) hf' (GaussianNameConjugation.regular _ _ hg) hg' ef eg)

private theorem exponential_conjugate (f : PR 2) (R T x y : PTm n)
    (hf : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input f R x)
    (hf' : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input f T y)
    (e : Γ ⊢[PRAAx] crossEquivalent (Conj f) f x y) : Γ ⊢[PRAAx]
    crossEquivalent (Conj (Exp f)) (Exp f) (expData R x) (expData T y) :=
  cross_trans _ _ _ _ _ _ (GaussianNameConjugation.exponential_cross f R x hf)
    (GaussianExponentialRadiusIndependence.independent_radii_proper (Conj f) f R T x y
      (GaussianNameConjugation.exponential_input f R x hf) hf' e)

theorem stirling_constant_fixed (x : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent (Conj S) S (stirlingData x) (stirlingData x) :=
  real_name_fixed S (stirlingData x) (GaussianStirlingConstant.name_regular x) (GaussianStirlingConstant.name_real x)

private theorem one_fixed (x : PTm n) : Γ ⊢[PRAAx] crossEquivalent (Conj oneF) oneF x x := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _
    (GaussianNameConjugation.regular _ _ (one_fast x)) (one_fast x)
  refine .allI ?_
  have e := one_at (Γ := Γ.map Fm.shift) (var 0) (Syn.shift x)
  exact (GaussianNameConjugation.sample_at oneF _ _).eqTrans
    ((point_congr e).eqTrans (point_one.eqTrans e.eqSymm))

theorem quadratic_coefficient_fixed : Γ ⊢[PRAAx] crossEquivalent (Conj quadraticCoefficientF) quadraticCoefficientF
    (quadraticCoefficientData : PTm n) quadraticCoefficientData :=
  sum_conjugate oneF gammaF zero zero zero zero (one_fast zero) (one_fast zero) gamma_regular gamma_regular
    (one_fixed zero) (GaussianNameConjugation.embedded_cross_fixed GammaEulerConstantName.gammaF zero gamma_regular)

theorem linear_cross (z B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    crossEquivalent (Conj linearF) linearF (linearData z B) (linearData (conjugate z) B) :=
  product_conjugate constantF S (ofGaussian z B) (ofGaussian (conjugate z) B) (stirlingData zero) (stirlingData zero)
    (constant_regular _) (constant_regular _) (GaussianStirlingConstant.name_regular zero)
    (GaussianStirlingConstant.name_regular zero) (constant_name_conjugate _ _ (of_gaussian z B hB))
    (stirling_constant_fixed zero)

private theorem quadratic_regular (z B : PTm n) : Γ ⊢[PRAAx] pointCN quadraticF (quadraticData z B) :=
  multiply_fast constantF quadraticCoefficientF _ _ (constant_regular _) quadratic_coefficient_regular

private theorem polynomial_regular (z B : PTm n) : Γ ⊢[PRAAx] pointCN polynomialF (polynomialData z B) :=
  add_fast constantF quadraticF _ _ (constant_regular _) (quadratic_regular z B)

theorem correction_cross (z B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    crossEquivalent (Conj correctionF) correctionF (correctionData z B) (correctionData (conjugate z) B) := by
  let w := conjugate z
  let q := ofGaussian z B
  let r := ofGaussian w B
  have e := of_gaussian z B hB
  have square := (point_mul q q).eqTrans (qmul_congr e e)
  have quad := product_conjugate constantF quadraticCoefficientF (qmul q q) (qmul r r)
    quadraticCoefficientData quadraticCoefficientData (constant_regular _) (constant_regular _)
    quadratic_coefficient_regular quadratic_coefficient_regular (constant_name_conjugate _ _ square)
    quadratic_coefficient_fixed
  have poly := sum_conjugate constantF quadraticF q r (quadraticData z B) (quadraticData w B)
    (constant_regular _) (constant_regular _) (quadratic_regular z B) (quadratic_regular w B)
    (constant_name_conjugate q r e) quad
  have half : Γ ⊢[PRAAx] point (negativeHalf : PTm n) ≐ negativeHalf :=
    real_point_fixed negativeHalf (GaussianRationalMetric.qnegative_canonical _)
      (RationalGaussianEmbedding.axis_negative _ (GaussianStirlingNames.fraction_axis one two (le_succ_self one)))
  exact product_conjugate constantF polynomialF negativeHalf negativeHalf (polynomialData z B) (polynomialData w B)
    (constant_regular _) (constant_regular _) (polynomial_regular z B) (polynomial_regular w B)
    (constant_name_conjugate _ _ half) poly

theorem prefactor_cross (z B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    crossEquivalent (Conj nameF) nameF (data z B) (data (conjugate z) B) := by
  let w := conjugate z
  let R := radius z B
  let T := radius w B
  let x := linearData z B
  let y := linearData w B
  let u := correctionData z B
  let v := correctionData w B
  have hx := linear_input (Γ := Γ) z B
  have hy := linear_input (Γ := Γ) w B
  have hu := correction_input (Γ := Γ) z B
  have hv := correction_input (Γ := Γ) w B
  exact product_conjugate (Exp linearF) (Exp correctionF) (expData R x) (expData T y) (expData R u) (expData T v)
    (GaussianRadiusExponentialName.name_regular _ _ _ hx) (GaussianRadiusExponentialName.name_regular _ _ _ hy)
    (GaussianRadiusExponentialName.name_regular _ _ _ hu) (GaussianRadiusExponentialName.name_regular _ _ _ hv)
    (exponential_conjugate linearF R T x y hx hy (linear_cross z B hB))
    (exponential_conjugate correctionF R T u v hu hv (correction_cross z B hB))

theorem actual_Barnes_canonical_prefactor_conjugation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 1) ⟶ crossEquivalent (Conj nameF) nameF (data (var 0) (var 1)) (data (conjugate (var 0)) (var 1))) :=
  closeUniv 2 (.impI (prefactor_cross _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPrefactorConjugation
