import IPRADerivations.Analysis.Gamma.GaussianGammaFoldedExponentBalance
import IPRADerivations.Analysis.Geometry.GaussianExactDiskShrinking

/-!
# The exact Euler-constant correction disk

The two original C2 scalar inequalities supply an absolute bound on each
common-mesh difference. Multiplication by the original rational input and
the verified retiming error give a numerical envelope for the actual
correction name. The exact-disk construction removes its dyadic slack.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaEulerCorrectionDisk

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qmul ofGaussian positive_product)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalReciprocal (bounded_product bounded_sum bound_congr)
open GaussianGammaCanonicalExponent (gammaF gamma_sample_at)
open GaussianGammaLogHarmonicName (fixedF)
open GaussianGammaFoldedExponentBalance (correctionF correctionData correctionBudget correctionCore
  correction_error correction_fast subst_correctionData)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianFastValueCut (rawEnvelope)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem scalar_difference_radius (p N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] RationalValueBounds.radius (GammaEulerConstantName.fixedSample p N)
      (GammaEulerConstantName.gammaSample p zero) (unit p+two*N) (N*unit p) := by
  let U := GammaEulerConstantName.unit p
  let a := GammaEulerConstantName.fixedSample p N
  let b := GammaEulerConstantName.gammaSample p zero
  have h := GammaEulerConstantName.C2_samples N p p zero hN
  have up := GammaEulerConstantName.unit_positive (Γ := Γ) p
  have pp := positive_product _ _ up up
  have tp := positive_product _ _ (positive_product _ _ hN up) up
  apply RationalValueBounds.radius_of_upper a b
  · exact RationalValueBounds.upper_mono a b _ _ _ _ tp h.andE₂
      (le_of_eq_add (d := zero) (by unfold unit GammaEulerConstantName.unit; ipra_ring))
  · exact RationalValueBounds.upper_mono b a _ _ _ _ pp h.andE₁
      (le_of_eq_add (d := U*U*U) (by unfold U unit GammaEulerConstantName.unit; ipra_ring))

theorem embedded_difference_bound (p N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] bounded (qsub (ap2 fixedF p N) (ap2 gammaF p zero))
      (unit p+two*N) (N*unit p) :=
  distance_congr
    (RationalGaussianNameEmbedding.sample_at GammaEulerConstantName.fixedF p N).eqSymm
    (gamma_sample_at p).eqSymm (.eqRefl _) (.eqRefl _)
    (RationalGaussianNameEmbedding.distance_from_radius _ _ _ _
      (positive_product _ _ hN (unit_positive p)) (scalar_difference_radius p N hN))

def source (z R B N : PTm n) : Fm PTm n :=
  le one N ⋏ (le one B ⋏ ComplexLogarithmRemainder.bounded z (R*B))

def slack (z R B N : PTm n) : PTm n := two*R+correctionBudget z B N

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (z R B N : PTm n) :
    (source z R B N).subst σ = source (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) := by
  simp [source]
@[simp] theorem subst_slack {m : ℕ} (σ : Fin n → PTm m) (z R B N : PTm n) :
    Syn.subst σ (slack z R B N) = slack (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) := by
  simp [slack]

theorem core_bound (p z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] bounded (correctionCore p z B N) (R*unit p+(two*R)*N) (N*unit p) := by
  exact bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring)
    (bounded_product _ _ _ _ _ _ (positive_product _ _ h.andE₁ (unit_positive p)) (le_refl one)
      (embedded_difference_bound p N h.andE₁)
      (GaussianGammaEulerHead.fraction_disk z R B h.andE₂.andE₁ h.andE₂.andE₂))

theorem correction_bound (p z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] bounded (ap2 correctionF p (correctionData z B N))
      (R*unit p+slack z R B N*N) (N*unit p) := by
  let q := ap2 correctionF p (correctionData z B N)
  let c := correctionCore p z B N
  let U := unit p
  let D := N*U
  let A := R*U+(two*R)*N
  let S := correctionBudget z B N
  have dpos := positive_product _ _ h.andE₁ (unit_positive p)
  have core := core_bound p z R B N h
  have error := correction_error p z B N h.andE₁
  have wider : Γ ⊢[PRAAx] bounded (qsub q c) (S*N) D :=
    GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ (unit_positive p) dpos
      (le_of_eq_add (d := zero) (by unfold D; ipra_ring)) error
  have sum := GaussianRationalPowerDifference.bounded_sum_same c (qsub q c) A (S*N) D dpos core wider
  have hc : Γ ⊢[PRAAx] GaussianRationalHorner.canonical q :=
    GaussianNameArithmetic.multiply_canonical _ _ _ _ p
  exact bound_congr (GaussianRationalLinearProduct.add_sub_right c q hc) (by unfold slack A S; ipra_ring)
    (.eqRefl _) sum

theorem correction_envelope (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] rawEnvelope correctionF (correctionData z B N) R N (slack z R B N) := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift N) := by
    simpa only [Fm.shift, Syn.shift, subst_source] using h.shift
  simpa only [rawEnvelope, unit, Syn.shift, subst_correctionData, subst_slack] using
    correction_bound (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift N) hs

def exactF : PR 2 := GaussianExactDiskShrinking.nameF correctionF
def exactData (z R B N : PTm n) : PTm n :=
  GaussianExactDiskShrinking.data (correctionData z B N) R N (slack z R B N)

theorem exact_correction_disk (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] pointCN exactF (exactData z R B N) ⋏
      (crossEquivalent exactF correctionF (exactData z R B N) (correctionData z B N) ⋏
        GaussianExponentialSmallPerturbation.smallSamples exactF (exactData z R B N) R N) :=
  GaussianExactDiskShrinking.correct _ _ _ _ _ h.andE₁ (correction_fast z B N h.andE₁) (correction_envelope z R B N h)

theorem original_euler_correction_envelope_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) (var 3) ⟶
      rawEnvelope correctionF (correctionData (var 0) (var 2) (var 3)) (var 1) (var 3)
        (slack (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (correction_envelope _ _ _ _ Prf.hyp0))

theorem original_euler_correction_exact_disk_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) (var 3) ⟶
      (pointCN exactF (exactData (var 0) (var 1) (var 2) (var 3)) ⋏
        (crossEquivalent exactF correctionF (exactData (var 0) (var 1) (var 2) (var 3))
            (correctionData (var 0) (var 2) (var 3)) ⋏
          GaussianExponentialSmallPerturbation.smallSamples exactF (exactData (var 0) (var 1) (var 2) (var 3))
            (var 1) (var 3)))) :=
  closeUniv 4 (.impI (exact_correction_disk _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaEulerCorrectionDisk
