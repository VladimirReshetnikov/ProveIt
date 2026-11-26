import IPRADerivations.Analysis.Gamma.Digamma.NegativeAxis.GaussianGammaNegativeIntervalNamedDigammaUniqueness
import IPRADerivations.Analysis.Gamma.NegativeAxis.Input.GaussianGammaNegativeIntervalRationalProperness
import IPRADerivations.Analysis.Gamma.NegativeAxis.Input.GaussianGammaNegativeIntervalNamedInputRetiming

/-!
# The actual negative critical location is the unique named zero

The decoded sample of the computed offset represents the exact selected
rational, including its original unreduced denominator. The original
grid residual binds the extended shifted digamma to zero at that
offset. The lower slope rules out any other certified zero.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedDigammaRoot

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaNegativeCriticalCorrection (guard)
open GaussianGammaNegativeCriticalEndpoints (mesh mesh_minimum)
open GaussianGammaNegativeCriticalGrid (denominator)
open GaussianGammaNegativeCriticalLocation (fractionLocationF lower lower_guard denominator_positive)
open GaussianGammaNegativeCriticalLocationComparison (datum_congr)
open GaussianGammaNegativeCriticalLocationResidual (original_residual_at residualCost)
open GaussianGammaNegativeCriticalRescale (original_rescale)
open GaussianGammaNegativeCriticalSlope (coefficient)
open GaussianGammaNegativeIntervalNamedDigamma (source nameF data subst_data name_regular frozenData original_frozen_rate)
open GaussianGammaNegativeIntervalNamedDigammaUniqueness (zeros_equal)
open GaussianGammaNegativeIntervalNamedInput (root_source)
open GaussianGammaNegativeIntervalNamedInputRetiming (orderedWindow retimed_source)
open GaussianGammaNegativeIntervalRationalProperness (root_guard root_cross_products)
open GaussianGammaRealValues (cross_right_data)
open GaussianNameEquivalence (crossEquivalent cross_at cross_symm cross_trans)
open GaussianNameRingLaws (zeroF zero_at zero_fast)
open GaussianNamedInverseRate (diagonal_rate)
open GaussianNamedPositiveLateLogSource (retimedF retimedData original_cross)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (positive_product qzero)
open GaussianRationalMetric (distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "F" => GaussianGammaNegativeCriticalEndpoints.nameF
local notation "d" => GaussianGammaNegativeCriticalEndpoints.nameData
local notation "rootF" => nameF fractionLocationF

def rootCost (N : PTm n) : PTm n := coefficient N (mesh N)+residualCost N+num 5

ipra_subst rootCost

theorem original_rational_cross (a b c B N : PTm n)
    (ha : Γ ⊢[PRAAx] guard a b) (hc : Γ ⊢[PRAAx] guard c B)
    (h : Γ ⊢[PRAAx] B*a ≐ b*c) :
    Γ ⊢[PRAAx] crossEquivalent F F (d a b N) (d c B N) := by
  have hb := le_trans ha.andE₁ (le_of_lt ha.andE₂)
  have hB := le_trans hc.andE₁ (le_of_lt hc.andE₂)
  have left := cross_symm _ _ _ _ (original_rescale a b N B ha hB)
  have right := original_rescale c B N b hc hb
  have e : Γ ⊢[PRAAx] d (B*a) (B*b) N ≐ d (b*c) (b*B) N := datum_congr h (mul_comm _ _)
  exact cross_trans _ _ _ _ _ _ (cross_right_data e left) right

theorem original_frozen_root_cross (p N : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent F F (frozenData fractionLocationF p N N) (d (lower p N) (denominator p N) N) :=
  original_rational_cross _ _ _ _ N (root_guard p N) (lower_guard p N) (root_cross_products p N)

theorem root_diagonal (p N : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (ap2 rootF p (data N (mesh N) N)) (ap2 zeroF p qzero) (rootCost N) (unit p) := by
  let P := unit p
  let B := denominator p N
  let C := coefficient N (mesh N)
  let R := residualCost N
  let x := data N (mesh N) N
  let y := frozenData fractionLocationF p N N
  let z := d (lower p N) B N
  have hp := unit_positive (Γ := Γ) p
  have hb := denominator_positive (Γ := Γ) p N
  have hpp := positive_product _ _ hp hp
  have freeze := diagonal_rate rootF F x y C P p hp (original_frozen_rate fractionLocationF p N (mesh N) N (root_source N))
  have first : Γ ⊢[PRAAx] distanceBounded (ap2 rootF p x) (ap2 F p y) (C+two) P :=
    distance_radius_mono _ _ _ _ _ _ hpp hp (by ipra_le 0) freeze
  have middle : Γ ⊢[PRAAx] distanceBounded (ap2 F p y) (ap2 F p z) two P :=
    distance_radius_mono _ _ _ _ _ _ hpp hp (by ipra_le 0) (cross_at F F y z p p (original_frozen_root_cross p N))
  have hm : Γ ⊢[PRAAx] le one (mesh N) := le_trans (by ipra_le 7) (mesh_minimum N)
  have grow : Γ ⊢[PRAAx] le P B := by unfold B denominator; ipra_le 𝔞(P)*sl hm
  have last : Γ ⊢[PRAAx] distanceBounded (ap2 F p z) qzero (R+one) P :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hb hp) hp
      (by ipra_le 𝔞(R*P)*sl grow) (original_residual_at p p N)
  exact distance_congr (.eqRefl _) (zero_at p qzero).eqSymm (by unfold rootCost; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hp (distance_triangle_same _ _ _ _ _ _ hp first middle) last)

theorem root_zero (N : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent rootF zeroF (data N (mesh N) N) qzero := by
  refine GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (rootCost N)
    (name_regular fractionLocationF N (mesh N) N (root_source N)) (zero_fast qzero) (.allI ?_)
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,subst_data,subst_rootCost,
    GaussianGammaNegativeCriticalEndpoints.subst_mesh,GaussianRationalHorner.subst_qzero,Syn.shift] using
    root_diagonal (Γ := Γ.map Fm.shift) (var 0) (Syn.shift N)

theorem unique_zero (f : PR 2) (x E N : PTm n) (hf : Γ ⊢[PRAAx] source f x E)
    (h : Γ ⊢[PRAAx] crossEquivalent (nameF f) zeroF (data x E N) qzero) :
    Γ ⊢[PRAAx] crossEquivalent f fractionLocationF x N :=
  zeros_equal f fractionLocationF x N E (mesh N) N hf (root_source N) h (root_zero N)

theorem actual_original_negative_interval_named_digamma_root_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
      (pointCN rootF (data (var 0) (mesh (var 0)) (var 0)) ⋏
        crossEquivalent rootF zeroF (data (var 0) (mesh (var 0)) (var 0)) qzero) :=
  closeUniv 1 (.andI (name_regular fractionLocationF _ _ _ (root_source _)) (root_zero _))

theorem actual_original_negative_interval_named_digamma_unique_root_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (source f (var 0) (var 1) ⟶ crossEquivalent (nameF f) zeroF (data (var 0) (var 1) (var 2)) qzero ⟶
        crossEquivalent f fractionLocationF (var 0) (var 2)) :=
  closeUniv 3 (.impI (.impI (unique_zero f _ _ _ Prf.hyp1 Prf.hyp0)))

theorem unique_ordered_zero (f : PR 2) (x E N : PTm n) (hf : Γ ⊢[PRAAx] orderedWindow f x E)
    (h : Γ ⊢[PRAAx] crossEquivalent (nameF (retimedF f)) zeroF (data (retimedData x E) (two*E) N) qzero) :
    Γ ⊢[PRAAx] crossEquivalent f fractionLocationF x N :=
  cross_trans _ _ _ _ _ _ (original_cross f x E hf.andE₁)
    (unique_zero (retimedF f) (retimedData x E) (two*E) N (retimed_source f x E hf) h)

theorem actual_original_negative_interval_named_digamma_unique_ordered_root_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (orderedWindow f (var 0) (var 1) ⟶ crossEquivalent (nameF (retimedF f)) zeroF
        (data (retimedData (var 0) (var 1)) (two*var 1) (var 2)) qzero ⟶ crossEquivalent f fractionLocationF (var 0) (var 2)) :=
  closeUniv 3 (.impI (.impI (unique_ordered_zero f _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedDigammaRoot
