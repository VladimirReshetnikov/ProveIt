import IPRADerivations.Analysis.Gamma.EulerProducts.Exponents.GaussianGammaFoldedQBound
import IPRADerivations.Analysis.Gamma.GaussianGammaReciprocalInverse

/-!
# The original finite Euler reciprocal with the SAME C13 constant

The head_(2R) reciprocal is multiplied by the actual exponential of
negative corrected fixed Euler exponent. Exact factorization of the
original Q_N proves the inverse product, including every actual clock.
The C12 head lower bound and exact A disk give the SAME C13 lambda as
for the original C7 inverse. The actual named reciprocal frontend is
then licensed by the checked bounded-inverse apartness construction.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaEulerReciprocalInverse

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaFixedEulerExponent (correctedF correctedData corrected_exponential_input)
open GaussianGammaFoldedQBound (factoredF factoredData)
open GaussianGammaFiniteApproximantName (qF qData q_regular)
open GaussianGammaReciprocalInverse (lambdaNumerator lambdaDenominator lambda_positive headInverse inverse_pairs constant_inverse)
open GaussianGammaCanonicalExponentBound (numericalRadius)
open GaussianGammaC9Bound (exponentialMajorant)
open GaussianNameRingLaws (negativeF negativeData oneF)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_trans cross_to_diagonal)
open GaussianEuclideanDistanceName (pointCN)
open GaussianExponentialSmallPerturbation (smallSamples)
open GaussianRationalMetric (bounded)
open GaussianRationalHorner (positive_product)
open GaussianRationalReciprocal (bound_congr bounded_product)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (z R B a d N : PTm n) : Fm PTm n := GaussianGammaReciprocalInverse.source z R B a d ⋏ le (two*R) N
@[simp] theorem subst_source {l : ℕ} (σ : Fin n → PTm l) (z R B a d N : PTm n) :
    (source z R B a d N).subst σ = source (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
      (Syn.subst σ a) (Syn.subst σ d) (Syn.subst σ N) := by simp [source]

theorem folded_source (z R B a d N : PTm n) (h : Γ ⊢[PRAAx] source z R B a d N) :
    Γ ⊢[PRAAx] GaussianGammaFoldedMajorantExponent.input z R B N := .andI h.andE₁.andE₁ h.andE₂

def negExpF : PR 2 := GaussianRadiusExponentialName.nameF (negativeF correctedF)
def negExpData (z R B N : PTm n) : PTm n := GaussianRadiusExponentialName.data (numericalRadius R) (negativeData (correctedData z R B N))
def inverseF : PR 2 := multiplyF constantF negExpF
def inverseData (z R B N : PTm n) : PTm n := multiplyData constantF negExpF (headInverse z R B) (negExpData z R B N)
@[simp] theorem subst_negExpData {l : ℕ} (σ : Fin n → PTm l) (z R B N : PTm n) :
    Syn.subst σ (negExpData z R B N) = negExpData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) := by simp [negExpData]
@[simp] theorem subst_inverseData {l : ℕ} (σ : Fin n → PTm l) (z R B N : PTm n) :
    Syn.subst σ (inverseData z R B N) = inverseData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) := by
  simp [inverseData,headInverse]

theorem negative_exponential_regular (z R B N : PTm n) (h : Γ ⊢[PRAAx] GaussianGammaFoldedMajorantExponent.input z R B N) :
    Γ ⊢[PRAAx] pointCN negExpF (negExpData z R B N) :=
  GaussianRadiusExponentialName.name_regular _ _ _ (GaussianExponentialInverse.negative_input _ _ _ (corrected_exponential_input z R B N h))
theorem negative_exponential_bound (p z R B N : PTm n) (h : Γ ⊢[PRAAx] GaussianGammaFoldedMajorantExponent.input z R B N) :
    Γ ⊢[PRAAx] bounded (ap2 negExpF p (negExpData z R B N)) (exponentialMajorant R) one := by
  let G := negativeF correctedF
  let T := numericalRadius R
  let X := negativeData (correctedData z R B N)
  have ng := GaussianExponentialInverse.negative_input _ _ _ (corrected_exponential_input z R B N h)
  exact bound_congr (GaussianRadiusExponentialName.sample_at G T p X).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianPositiveExponentialMajorant.disk_bound _ T _ (GaussianRadiusExponentialName.query_bound G T X p ng))
theorem inverse_regular (z R B N : PTm n) (h : Γ ⊢[PRAAx] GaussianGammaFoldedMajorantExponent.input z R B N) :
    Γ ⊢[PRAAx] pointCN inverseF (inverseData z R B N) :=
  multiply_fast _ _ _ _ (constant_regular _) (negative_exponential_regular z R B N h)

theorem inverse_sample_bound (p z R B a d N : PTm n) (h : Γ ⊢[PRAAx] source z R B a d N) :
    Γ ⊢[PRAAx] bounded (ap2 inverseF p (inverseData z R B N)) (lambdaDenominator R d) (lambdaNumerator R a) := by
  let U := headInverse z R B
  let V := negExpData z R B N
  let t := GaussianFastValueCut.exponent (GaussianNameArithmetic.multiplyModulus constantF negExpF U V) p
  have src := h.andE₁
  have hs := GaussianGammaEulerHeadLower.returned_inverse_bound z B a d (two*R)
    src.andE₁.andE₂.andE₁ src.andE₂.andE₁ src.andE₂.andE₂.andE₁ src.andE₂.andE₂.andE₂
  have e := (GaussianNameArithmetic.multiply_at (Γ := Γ) constantF negExpF U V p).eqTrans
    (GaussianNameArithmetic.recode_congr (GaussianRationalSyntheticDivision.qmul_congr (constant_at t U) (.eqRefl _)))
  have den := (lambda_positive R a d src.andE₂.andE₁ src.andE₂.andE₂.andE₁).andE₁
  exact bound_congr e.eqSymm (.eqRefl _) (.eqRefl _)
    ((GaussianFastValueCut.recode_bound_iff _ _ _ den).iffMpr
      (bound_congr (.eqRefl _) (.eqRefl _) (by ipra_ring)
        (bounded_product _ _ _ _ _ _ den (le_refl _) hs (negative_exponential_bound t z R B N (folded_source z R B a d N h)))))

theorem inverse_disk (z R B a d N : PTm n) (h : Γ ⊢[PRAAx] source z R B a d N) :
    Γ ⊢[PRAAx] smallSamples inverseF (inverseData z R B N) (lambdaDenominator R d) (lambdaNumerator R a) := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift a) (Syn.shift d) (Syn.shift N) := by
    simpa only [Fm.shift,Syn.shift,subst_source] using h.shift
  simpa only [smallSamples,Syn.shift,subst_inverseData,GaussianGammaReciprocalInverse.subst_lambdaNumerator,
    GaussianGammaReciprocalInverse.subst_lambdaDenominator] using
    inverse_sample_bound (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift a) (Syn.shift d) (Syn.shift N) hs

theorem exponential_pair (z R B N ref : PTm n) (h : Γ ⊢[PRAAx] GaussianGammaFoldedMajorantExponent.input z R B N) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF GaussianGammaFoldedQBound.exponentialF negExpF) oneF
      (multiplyData GaussianGammaFoldedQBound.exponentialF negExpF (GaussianGammaFoldedQBound.exponentialData z R B N)
        (negExpData z R B N)) ref :=
  cross_trans _ _ _ _ _ _ (GaussianExponentialInverse.exponential_inverse correctedF (numericalRadius R)
    (correctedData z R B N) (corrected_exponential_input z R B N h))
    (GaussianBoundedInverseApartness.ones_equivalent (correctedData z R B N) ref)

theorem inverse_product (z R B a d N : PTm n) (h : Γ ⊢[PRAAx] source z R B a d N) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF qF inverseF) oneF
      (multiplyData qF inverseF (qData z B N) (inverseData z R B N)) (qData z B N) := by
  have qsrc := folded_source z R B a d N h
  have src := h.andE₁
  have hn := (GaussianGammaFoldedMajorantExponent.tail_source z R B N qsrc).andE₂.andE₁
  have invCN := inverse_regular z R B N qsrc
  have first := GaussianGammaAdjacentCutoff.multiply_cross qF factoredF inverseF inverseF _ _ _ _
    (q_regular z B N hn) (GaussianGammaFoldedQBound.factored_regular z R B N qsrc) invCN invCN
    (GaussianGammaFoldedQBound.original_Q_factored z R B N qsrc) (cross_refl _ _ invCN)
  have pair := inverse_pairs constantF GaussianGammaFoldedQBound.exponentialF constantF negExpF
    (GaussianGammaEulerHead.run z B (two*R)) (GaussianGammaFoldedQBound.exponentialData z R B N)
    (headInverse z R B) (negExpData z R B N) (qData z B N)
    (constant_regular _) (GaussianGammaFoldedQBound.exponential_regular z R B N qsrc)
    (constant_regular _) (negative_exponential_regular z R B N qsrc)
    (constant_inverse _ _ _ (GaussianGammaEulerHeadLower.returned_inverse_identity z B a d (two*R)
      src.andE₁.andE₂.andE₁ src.andE₂.andE₁ src.andE₂.andE₂.andE₁ src.andE₂.andE₂.andE₂))
    (exponential_pair z R B N _ qsrc)
  exact cross_trans _ _ _ _ _ _ first pair

def eulerHeight (z R B d N : PTm n) : PTm n := GaussianBoundedInverseApartness.height qF inverseF
  (qData z B N) (inverseData z R B N) (lambdaDenominator R d)
def eulerF : PR 2 := GaussianNameReciprocal.nameF qF
def eulerData (z R B d N : PTm n) : PTm n := GaussianNameReciprocal.nameData (eulerHeight z R B d N) (qData z B N)

theorem original_euler_inverse (z R B a d N : PTm n) (h : Γ ⊢[PRAAx] source z R B a d N) :
    Γ ⊢[PRAAx] GaussianNameReciprocal.input qF (eulerHeight z R B d N) (qData z B N) ⋏
      crossEquivalent eulerF inverseF (eulerData z R B d N) (inverseData z R B N) := by
  have src := h.andE₁
  have qsrc := folded_source z R B a d N h
  have l := lambda_positive R a d src.andE₂.andE₁ src.andE₂.andE₂.andE₁
  exact GaussianBoundedInverseApartness.bounded_inverse_correct _ _ _ _ _ _ l.andE₂ l.andE₁
    (q_regular z B N (GaussianGammaFoldedMajorantExponent.tail_source z R B N qsrc).andE₂.andE₁)
    (inverse_regular z R B N qsrc) (inverse_disk z R B a d N h) (inverse_product z R B a d N h)

theorem euler_regular (z R B a d N : PTm n) (h : Γ ⊢[PRAAx] source z R B a d N) :
    Γ ⊢[PRAAx] pointCN eulerF (eulerData z R B d N) := by
  have hi := (original_euler_inverse z R B a d N h).andE₁
  exact GaussianNameReciprocal.name_fast _ _ _ hi.andE₁ hi.andE₂

theorem euler_product (z R B a d N : PTm n) (h : Γ ⊢[PRAAx] source z R B a d N) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF qF eulerF) oneF
      (multiplyData qF eulerF (qData z B N) (eulerData z R B d N)) (qData z B N) := by
  have hi := (original_euler_inverse z R B a d N h).andE₁
  exact GaussianNameReciprocal.product_one _ _ _ hi.andE₁ hi.andE₂

theorem original_Q_C14_bounded_inverse_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶ pointCN inverseF (inverseData (var 0) (var 1) (var 2) (var 5)) ⋏
      (smallSamples inverseF (inverseData (var 0) (var 1) (var 2) (var 5)) (lambdaDenominator (var 1) (var 4)) (lambdaNumerator (var 1) (var 3)) ⋏
        crossEquivalent (multiplyF qF inverseF) oneF
          (multiplyData qF inverseF (qData (var 0) (var 2) (var 5)) (inverseData (var 0) (var 1) (var 2) (var 5)))
          (qData (var 0) (var 2) (var 5)))) :=
  closeUniv 6 (.impI (.andI (inverse_regular _ _ _ _ (folded_source _ _ _ _ _ _ Prf.hyp0))
    (.andI (inverse_disk _ _ _ _ _ _ Prf.hyp0) (inverse_product _ _ _ _ _ _ Prf.hyp0))))
theorem original_pole_free_euler_inverse_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      GaussianNameReciprocal.input qF (eulerHeight (var 0) (var 1) (var 2) (var 4) (var 5)) (qData (var 0) (var 2) (var 5)) ⋏
        crossEquivalent eulerF inverseF (eulerData (var 0) (var 1) (var 2) (var 4) (var 5)) (inverseData (var 0) (var 1) (var 2) (var 5))) :=
  closeUniv 6 (.impI (original_euler_inverse _ _ _ _ _ _ Prf.hyp0))
theorem original_pole_free_euler_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶ pointCN eulerF (eulerData (var 0) (var 1) (var 2) (var 4) (var 5))) :=
  closeUniv 6 (.impI (euler_regular _ _ _ _ _ _ Prf.hyp0))
theorem original_pole_free_euler_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶ crossEquivalent (multiplyF qF eulerF) oneF
      (multiplyData qF eulerF (qData (var 0) (var 2) (var 5)) (eulerData (var 0) (var 1) (var 2) (var 4) (var 5)))
      (qData (var 0) (var 2) (var 5))) := closeUniv 6 (.impI (euler_product _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaEulerReciprocalInverse
