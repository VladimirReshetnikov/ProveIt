import IPRADerivations.Analysis.Barnes.Prefactors.GaussianBarnesCanonicalPrefactor
import IPRADerivations.Analysis.Exponential.Names.GaussianExponentialInverseSamples
import IPRADerivations.Analysis.Gamma.FunctionalEquations.ReciprocalGamma.GaussianGammaAdjacentCutoff

/-!
# The original Barnes prefactor is apart from zero

The actual exponential of the negated combined exponent supplies an
inverse for the literal prefactor. The checked bound on that inverse
gives a concrete apartness certificate for the original prefactor name.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPrefactorInverse

open_ipra
open GaussianBarnesCanonicalPrefactor (linearF linearData correctionF correctionData radius
  nameF data combinedF combinedData combined regular linear_input correction_input)
open GaussianEuclideanDistanceName (pointCN)
open GaussianExponentialInverse (negative_input exponential_inverse)
open GaussianExponentialInverseSamples (disk disk_positive sample_disk)
open GaussianExponentialSmallPerturbation (smallSamples)
open GaussianNameArithmetic (addF addData multiplyF multiplyData)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_trans)
open GaussianNameRingLaws (negativeF negativeData oneF)
open GaussianRationalMetric (bounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def exponentF : PR 2 := addF linearF correctionF
def exponentData (z B : PTm n) : PTm n := addData (linearData z B) (correctionData z B)
def exponentRadius (z B : PTm n) : PTm n := radius z B+radius z B

def inverseF : PR 2 := GaussianRadiusExponentialName.nameF (negativeF exponentF)
def inverseData (z B : PTm n) : PTm n :=
  GaussianRadiusExponentialName.data (exponentRadius z B) (negativeData (exponentData z B))

def productF : PR 2 := multiplyF nameF inverseF
def productData (z B : PTm n) : PTm n := multiplyData nameF inverseF (data z B) (inverseData z B)

def inverseBound (z B : PTm n) : PTm n := disk (exponentRadius z B)
def height (z B : PTm n) : PTm n :=
  GaussianBoundedInverseApartness.height nameF inverseF (data z B) (inverseData z B) (inverseBound z B)

@[simp] theorem subst_inverseData {m : ℕ} (σ : Fin n → PTm m) (z B : PTm n) :
    Syn.subst σ (inverseData z B) = inverseData (Syn.subst σ z) (Syn.subst σ B) := by
  simp [inverseData,exponentRadius,exponentData,GaussianBarnesCanonicalPrefactor.radius,linearData,correctionData,
    GaussianBarnesCanonicalPrefactor.polynomialData,GaussianBarnesCanonicalPrefactor.quadraticData,
    GaussianBarnesCanonicalPrefactor.quadraticCoefficientData,GaussianBarnesCanonicalPrefactor.negativeHalf,one,two]

@[simp] theorem subst_inverseBound {m : ℕ} (σ : Fin n → PTm m) (z B : PTm n) :
    Syn.subst σ (inverseBound z B) = inverseBound (Syn.subst σ z) (Syn.subst σ B) := by
  simp [inverseBound,exponentRadius,GaussianBarnesCanonicalPrefactor.radius,linearData,correctionData,
    GaussianBarnesCanonicalPrefactor.polynomialData,GaussianBarnesCanonicalPrefactor.quadraticData,
    GaussianBarnesCanonicalPrefactor.quadraticCoefficientData,GaussianBarnesCanonicalPrefactor.negativeHalf,one,two]

theorem exponent_input (z B : PTm n) :
    Γ ⊢[PRAAx] GaussianRadiusExponentialName.input exponentF (exponentRadius z B) (exponentData z B) :=
  GaussianExponentialReference.add_input _ _ _ _ _ (linear_input z B) (correction_input z B)

theorem inverse_input (z B : PTm n) : Γ ⊢[PRAAx]
    GaussianRadiusExponentialName.input (negativeF exponentF) (exponentRadius z B) (negativeData (exponentData z B)) :=
  negative_input _ _ _ (exponent_input z B)

theorem inverse_regular (z B : PTm n) : Γ ⊢[PRAAx] pointCN inverseF (inverseData z B) :=
  GaussianRadiusExponentialName.name_regular _ _ _ (inverse_input z B)

theorem inverse_sample_bound (p z B : PTm n) :
    Γ ⊢[PRAAx] bounded (ap2 inverseF p (inverseData z B)) (inverseBound z B) one :=
  sample_disk _ _ p _ (inverse_input z B)

theorem inverse_samples (z B : PTm n) : Γ ⊢[PRAAx] smallSamples inverseF (inverseData z B) (inverseBound z B) one := by
  refine .allI ?_
  simpa only [smallSamples,subst_inverseData,subst_inverseBound,Syn.shift,one,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    inverse_sample_bound (Γ := Γ.map Fm.shift) (var 0) (Syn.shift z) (Syn.shift B)

theorem inverse_identity (z B : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent productF oneF (productData z B) (data z B) := by
  have split := GaussianGammaAdjacentCutoff.multiply_cross (Γ := Γ) nameF combinedF inverseF inverseF
    (data z B) (combinedData z B) (inverseData z B) (inverseData z B)
    (regular z B) (GaussianRadiusExponentialName.name_regular _ _ _ (exponent_input z B))
    (inverse_regular z B) (inverse_regular z B) (combined z B) (cross_refl _ _ (inverse_regular z B))
  have unitProduct := exponential_inverse (Γ := Γ) exponentF (exponentRadius z B) (exponentData z B) (exponent_input z B)
  exact cross_trans _ _ _ _ _ _ split (cross_trans _ _ _ _ _ _ unitProduct
    (GaussianBoundedInverseApartness.ones_equivalent (exponentData z B) (data z B)))

theorem apart (z B : PTm n) : Γ ⊢[PRAAx] GaussianNameReciprocal.apart nameF (height z B) (data z B) :=
  GaussianBoundedInverseApartness.anchor_apart nameF inverseF _ _ _ (disk_positive (exponentRadius z B))
    (regular z B) (inverse_regular z B) (inverse_samples z B) (inverse_identity z B)

theorem actual_Barnes_canonical_prefactor_apart_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (GaussianNameReciprocal.apart nameF (height (var 0) (var 1)) (data (var 0) (var 1)) ⋏
      crossEquivalent productF oneF (productData (var 0) (var 1)) (data (var 0) (var 1))) :=
  closeUniv 2 (.andI (apart _ _) (inverse_identity _ _))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPrefactorInverse
