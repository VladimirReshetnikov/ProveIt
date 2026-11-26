import IPRADerivations.Analysis.Series.Harmonic.RationalHarmonicIntervalProduct
import IPRADerivations.Analysis.Euler.HarmonicLogarithms.GaussianHarmonicLogarithmName

/-!
# Product identity for the actual ordered harmonic logarithm name

The true finite harmonic product rectangle is evaluated at the exact
original mesh shared by all three names. Its 2/Q error and the actual
normalized addition error give a five-unit diagonal envelope. The
genuine original name regularities remove this envelope at a computed
finite gap query. No logarithm product identity is supplied as input.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianHarmonicLogarithmProduct

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianHarmonicLogarithmName (nameF data sample observation sample_at name_regular clock)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same distance_symmetric)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameEquivalence (crossEquivalent)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (a b c d : PTm n) : Fm PTm n := GaussianPositiveRationalLogarithm.source a b ⋏ GaussianPositiveRationalLogarithm.source c d
def addedF : PR 2 := GaussianNameArithmetic.addF nameF nameF
def addedData (a b c d : PTm n) : PTm n := GaussianNameArithmetic.addData (data a b) (data c d)
def mesh (p : PTm n) : PTm n := GammaEulerConstantName.mesh (clock p)
@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (a b c d : PTm n) :
    (source a b c d).subst σ = source (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ c) (Syn.subst σ d) := by simp [source]
@[simp] theorem subst_addedData {m : ℕ} (σ : Fin n → PTm m) (a b c d : PTm n) :
    Syn.subst σ (addedData a b c d) = addedData (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ c) (Syn.subst σ d) := by simp [addedData]
@[simp] theorem subst_mesh {m : ℕ} (σ : Fin n → PTm m) (p : PTm n) : Syn.subst σ (mesh p) = mesh (Syn.subst σ p) := by
  simp [mesh,GammaEulerConstantName.mesh,GammaEulerConstantName.unit]

theorem product_source (a b c d : PTm n) (h : Γ ⊢[PRAAx] source a b c d) : Γ ⊢[PRAAx]
    GaussianPositiveRationalLogarithm.source (a*c) (b*d) :=
  .andI (RationalAlgebra.positive_product h.andE₁.andE₁ h.andE₂.andE₁)
    (RationalAlgebra.positive_product h.andE₁.andE₂ h.andE₂.andE₂)

theorem mesh_later (p : PTm n) : Γ ⊢[PRAAx] le (unit p) (mesh p) := by
  have grow := GaussianExponentialReference.unit_monotone (Γ := Γ) (le_add_right p (num 9))
  have four : Γ ⊢[PRAAx] le one (num 4 : PTm n) := le_trans (le_succ_self one) (le_trans (le_succ_self two) (le_succ_self (num 3)))
  exact le_trans grow (le_congr (one_mul _ ) (.eqRefl _) (AnalyticNumberTheory.PhiLower.le_mul_mono four (le_refl (unit (clock p)))))

theorem finite_samples (p a b c d : PTm n) (h : Γ ⊢[PRAAx] source a b c d) : Γ ⊢[PRAAx]
    distanceBounded (sample p (a*c) (b*d)) (GaussianRationalHorner.qadd (sample p a b) (sample p c d)) two (unit p) := by
  have hQ := le_trans (unit_positive (Γ := Γ) p) (mesh_later p)
  have raw := RationalHarmonicIntervalProduct.finite_product_error a b c d (mesh p)
    h.andE₁.andE₁ h.andE₁.andE₂ h.andE₂.andE₁ h.andE₂.andE₂ hQ
  have old := distance_congr (sample_at p (a*c) (b*d)).eqSymm
    (GaussianRationalSyntheticDivision.qadd_congr (sample_at p a b) (sample_at p c d)).eqSymm (.eqRefl _) (.eqRefl _) raw
  exact distance_radius_mono _ _ _ _ two (unit p) hQ (unit_positive p)
    (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl two) (mesh_later p)) old

theorem diagonal_error (p a b c d : PTm n) (h : Γ ⊢[PRAAx] source a b c d) : Γ ⊢[PRAAx]
    distanceBounded (sample p (a*c) (b*d)) (ap2 addedF p (addedData a b c d)) (num 5) (unit p) := by
  have correction := GaussianNameRingLaws.add_sample_error nameF nameF (data a b) (data c d) p
    (name_regular a b h.andE₁) (name_regular c d h.andE₂)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold GaussianNameRingLaws.three; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p) (finite_samples p a b c d h)
      (distance_symmetric _ _ _ _ (unit_positive p) correction))

theorem logarithm_product (a b c d : PTm n) (h : Γ ⊢[PRAAx] source a b c d) : Γ ⊢[PRAAx]
    crossEquivalent nameF addedF (data (a*c) (b*d)) (addedData a b c d) := by
  apply GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (num 5)
    (name_regular _ _ (product_source a b c d h))
    (GaussianNameArithmetic.add_fast nameF nameF (data a b) (data c d) (name_regular a b h.andE₁) (name_regular c d h.andE₂))
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift a) (Syn.shift b) (Syn.shift c) (Syn.shift d) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  simpa [GaussianValueNormalizerExtensionality.rawDiagonal,Syn.shift,addedF,addedData,sample] using
    diagonal_error (var 0) (Syn.shift a) (Syn.shift b) (Syn.shift c) (Syn.shift d) hs

theorem actual_ordered_harmonic_logarithm_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) (var 3) ⟶ crossEquivalent nameF addedF
      (data (var 0*var 2) (var 1*var 3)) (addedData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (logarithm_product _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianHarmonicLogarithmProduct
