import IPRADerivations.Analysis.Beta.Endpoints.GaussianBetaUpperEndpointInverse

/-!
# A certified original finite Euler reciprocal at every positive degree

The original Q_N observation program is unchanged. The existing reciprocal
program is also unchanged; its numerical apartness height is obtained
from the actual beta endpoint inverse and its computed zeroth-sample disk.
This is valid at every N>=1 in the right half-plane. The old fixed-2R
height agrees as a named value on its proved domain; pointwise equality
of different reciprocal clocks is not claimed. Exact sample readback
shows the original Q_N query used at every input and precision.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianBetaAllDegreeEulerInverse

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaFiniteApproximantName (qF qData q_regular)
open GaussianBetaUpperEndpointName (name_regular)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans)
open GaussianEuclideanDistanceName (pointCN)
open GaussianRationalMetric (bounded)
open GaussianExponentialSmallPerturbation (smallSamples)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

abbrev endpointF : PR 2 := GaussianBetaUpperEndpointName.nameF
abbrev nameF : PR 2 := GaussianGammaEulerReciprocalInverse.eulerF
def endpointData (z B N : PTm n) : PTm n := GaussianBetaUpperEndpointName.data z B one N
def radius (z B N : PTm n) : PTm n := GaussianNameBounds.U endpointF (endpointData z B N)
def height (z B N : PTm n) : PTm n := GaussianBoundedInverseApartness.height qF endpointF
  (qData z B N) (endpointData z B N) (radius z B N)
def data (z B N : PTm n) : PTm n := GaussianNameReciprocal.nameData (height z B N) (qData z B N)
def source (z R B A N : PTm n) : Fm PTm n := GaussianEulerLowerPowerCoefficients.source z R B A ⋏ le one N
def query (p z B N : PTm n) : PTm n := GaussianFastValueCut.exponent (GaussianNameReciprocal.modulus (height z B N)) p+
  GaussianNameReciprocal.anchor (height z B N)
@[simp] theorem subst_endpointData {m : ℕ} (σ : Fin n → PTm m) (z B N : PTm n) :
    Syn.subst σ (endpointData z B N) = endpointData (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) := by simp [endpointData,one]
@[simp] theorem subst_radius {m : ℕ} (σ : Fin n → PTm m) (z B N : PTm n) :
    Syn.subst σ (radius z B N) = radius (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) := by simp [radius]
@[simp] theorem subst_original_head {m : ℕ} (σ : Fin n → PTm m) (z B N : PTm n) :
    Syn.subst σ (GaussianGammaEulerHead.run z B N) =
      GaussianGammaEulerHead.run (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) := by
  change PTm.app GaussianGammaEulerHead.headF (fun i => Syn.subst σ (![z,B,N] i)) =
    PTm.app GaussianGammaEulerHead.headF ![Syn.subst σ z,Syn.subst σ B,Syn.subst σ N]
  congr 1
  funext i
  fin_cases i <;> rfl
@[simp] theorem subst_height {m : ℕ} (σ : Fin n → PTm m) (z B N : PTm n) :
    Syn.subst σ (height z B N) = height (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) := by
  simp [height,GaussianGammaFiniteApproximantName.qData,GaussianGammaFiniteApproximantName.approximantData,
    GaussianGammaFiniteApproximantName.exponentialInputData,GaussianGammaFiniteApproximantName.logExponentData]
@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (z B N : PTm n) :
    Syn.subst σ (data z B N) = data (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) := by
  simp [data,GaussianGammaFiniteApproximantName.qData,GaussianGammaFiniteApproximantName.approximantData,
    GaussianGammaFiniteApproximantName.exponentialInputData,GaussianGammaFiniteApproximantName.logExponentData]
@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (z R B A N : PTm n) :
    (source z R B A N).subst σ = source (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ A) (Syn.subst σ N) := by simp [source]
@[simp] theorem subst_query {m : ℕ} (σ : Fin n → PTm m) (p z B N : PTm n) :
    Syn.subst σ (query p z B N) = query (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) := by
  simp [query,GaussianNameReciprocal.modulus,GaussianNameReciprocal.anchor]

theorem endpoint_regular (z R B A N : PTm n) (h : Γ ⊢[PRAAx] source z R B A N) : Γ ⊢[PRAAx]
    pointCN endpointF (endpointData z B N) := name_regular z B one N h.andE₁.andE₂.andE₁.andE₁ (le_refl one) h.andE₂

theorem endpoint_disk (z R B A N : PTm n) (h : Γ ⊢[PRAAx] source z R B A N) : Γ ⊢[PRAAx]
    smallSamples endpointF (endpointData z B N) (radius z B N) one := by
  simpa only [smallSamples,GaussianRootApproximationWitness.pointBounds,radius,Syn.shift,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    GaussianNameBounds.all_samples_bounded endpointF (endpointData z B N) (endpoint_regular z R B A N h)

/-- Constructive apartness and inverse equality for every positive N. -/
theorem original_inverse (z R B A N : PTm n) (h : Γ ⊢[PRAAx] source z R B A N) : Γ ⊢[PRAAx]
    GaussianNameReciprocal.input qF (height z B N) (qData z B N) ⋏
      crossEquivalent nameF endpointF (data z B N) (endpointData z B N) :=
  GaussianBoundedInverseApartness.bounded_inverse_correct qF endpointF (qData z B N) (endpointData z B N)
    (radius z B N) one (GaussianNameBounds.U_positive _ _) (le_refl one)
    (q_regular z B N h.andE₂) (endpoint_regular z R B A N h) (endpoint_disk z R B A N h)
    (GaussianBetaUpperEndpointInverse.original_upper_product z R B A one N h.andE₁ (le_refl one) h.andE₂)

/-- Every positive encoding of the upper time N gives this same
certified reciprocal, including the original grid endpoint encoding. -/
theorem original_upper_inverse (z R B A b N : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A N) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    crossEquivalent endpointF nameF (GaussianBetaUpperEndpointName.data z B b N) (data z B N) := by
  have input := (original_inverse z R B A N h).andE₁
  exact cross_symm _ _ _ _
    (GaussianBoundedInverseApartness.reciprocal_matches_inverse qF endpointF _ _ _
      (q_regular z B N h.andE₂)
      (GaussianBetaUpperEndpointName.name_regular z B b N h.andE₁.andE₂.andE₁.andE₁ hb h.andE₂)
      input.andE₂ (GaussianBetaUpperEndpointInverse.original_upper_product z R B A b N h.andE₁ hb h.andE₂))

theorem name_regular (z R B A N : PTm n) (h : Γ ⊢[PRAAx] source z R B A N) : Γ ⊢[PRAAx]
    pointCN nameF (data z B N) := by
  have input := (original_inverse z R B A N h).andE₁
  exact GaussianNameReciprocal.name_fast qF _ _ input.andE₁ input.andE₂

theorem original_product (z R B A N : PTm n) (h : Γ ⊢[PRAAx] source z R B A N) : Γ ⊢[PRAAx]
    crossEquivalent (GaussianNameArithmetic.multiplyF qF nameF) GaussianNameRingLaws.oneF
      (GaussianNameArithmetic.multiplyData qF nameF (qData z B N) (data z B N)) (qData z B N) := by
  have input := (original_inverse z R B A N h).andE₁
  exact GaussianNameReciprocal.product_one qF _ _ input.andE₁ input.andE₂

/-- Same old reciprocal producer and same finite Q_N program, with the
new checked numerical apartness certificate and its literal query. -/
theorem sample_literal (p z B N : PTm n) : Γ ⊢[PRAAx]
    ap2 nameF p (data z B N) ≐ GaussianFastValueCut.recode
      (GaussianRationalReciprocal.reciprocal (ap2 qF (query p z B N) (qData z B N))) :=
  (GaussianFastValueCut.name_at (GaussianNameReciprocal.rawF qF) (GaussianNameReciprocal.modulus (height z B N))
    (GaussianNameReciprocal.rawData (height z B N) (qData z B N)) p).eqTrans
      (GaussianNameArithmetic.recode_congr (GaussianNameReciprocal.raw_at qF (height z B N) (qData z B N)
        (GaussianFastValueCut.exponent (GaussianNameReciprocal.modulus (height z B N)) p)))

theorem original_endpoint_observations (p q z R B A N : PTm n) (h : Γ ⊢[PRAAx] source z R B A N) : Γ ⊢[PRAAx]
    GaussianRationalMetric.distanceBounded (ap2 nameF p (data z B N)) (ap2 endpointF q (endpointData z B N))
      (GaussianCoefficientNameBounds.unit p+GaussianCoefficientNameBounds.unit q)
      (GaussianCoefficientNameBounds.unit p*GaussianCoefficientNameBounds.unit q) :=
  GaussianNameEquivalence.cross_at _ _ _ _ p q (original_inverse z R B A N h).andE₂

/-- Agreement with the previously published finite Euler data on its
original certified domain; different query codes are not identified. -/
theorem original_compatible (z R B A N : PTm n) (h : Γ ⊢[PRAAx] source z R B A N)
    (hR : Γ ⊢[PRAAx] le one R) (hCut : Γ ⊢[PRAAx] le (two*R) N) : Γ ⊢[PRAAx]
    crossEquivalent nameF GaussianGammaEulerReciprocalInverse.eulerF (data z B N)
      (GaussianGammaEulerReciprocalInverse.eulerData z R B A N) :=
  cross_trans _ _ _ _ _ _ (original_inverse z R B A N h).andE₂
    (GaussianBetaUpperEndpointInverse.original_upper_inverse z R B A one N h.andE₁ hR (le_refl one) h.andE₂ hCut)

def dataF : PR 3 := PTm.toPR (data (var 0) (var 1) (var 2))
def sampleF : PR 4 := PTm.toPR (ap2 nameF (var 0) (data (var 1) (var 2) (var 3)))
theorem data_at (z B N : PTm n) : Γ ⊢[PRAAx] ap3 dataF z B N ≐ data z B N := by
  simpa [dataF,ap3] using toPR_eq (Γ := Γ) (data (var 0) (var 1) (var 2) : PTm 3) ![z,B,N]
theorem program_at (p z B N : PTm n) : Γ ⊢[PRAAx] PTm.app sampleF ![p,z,B,N] ≐ ap2 nameF p (data z B N) := by
  simpa [sampleF] using toPR_eq (Γ := Γ) (ap2 nameF (var 0) (data (var 1) (var 2) (var 3)) : PTm 4) ![p,z,B,N]

theorem original_all_positive_degrees_finite_Euler_inverse_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      GaussianNameReciprocal.input qF (height (var 0) (var 2) (var 4)) (qData (var 0) (var 2) (var 4)) ⋏
        crossEquivalent nameF endpointF (data (var 0) (var 2) (var 4)) (endpointData (var 0) (var 2) (var 4))) :=
  closeUniv 5 (.impI (original_inverse _ _ _ _ _ Prf.hyp0))
theorem literal_all_degree_original_finite_sampler_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (ap2 nameF (var 0) (data (var 1) (var 2) (var 3)) ≐ GaussianFastValueCut.recode
      (GaussianRationalReciprocal.reciprocal (ap2 qF (query (var 0) (var 1) (var 2) (var 3)) (qData (var 1) (var 2) (var 3))))) :=
  closeUniv 4 (sample_literal _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianBetaAllDegreeEulerInverse
