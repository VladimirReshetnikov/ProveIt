import IPRADerivations.Analysis.Gamma.Digamma.NegativeAxis.GaussianGammaNegativeIntervalNamedDigamma
import IPRADerivations.Analysis.Gamma.Digamma.NegativeAxis.GaussianGammaNegativeIntervalNamedDigammaInverseSlope

/-!
# Injectivity and uniqueness of a zero on the negative interval

Equivalent shifted digamma names give cofinally close original
rational digamma observations at certified frozen offsets. The lower
slope makes the offsets cofinally close as well. Their original
regular names therefore agree, even with separate pole margins.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedDigammaUniqueness

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaNegativeCriticalSlope (coefficient)
open GaussianGammaNegativeIntervalNamedDigamma (source nameF data frozenData original_frozen_rate)
open GaussianGammaNegativeIntervalNamedDigammaInverseSlope (input_distance inverseNumerator)
open GaussianNameEquivalence (crossEquivalent cross_at cross_symm cross_trans)
open GaussianNameRingLaws (zeroF)
open GaussianNamedInverseRate (diagonal_rate)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product qzero)
open GaussianRationalMetric (distanceBounded)
open GaussianUnitIntervalInputDecoding (decoded_distance)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "NF" => GaussianGammaNegativeCriticalEndpoints.nameF

def cost (E F N : PTm n) : PTm n := (coefficient N E+two)+two+(coefficient N F+two)

@[simp] theorem subst_cost {m : ℕ} (σ : Fin n → PTm m) (E F N : PTm n) :
    Syn.subst σ (cost E F N) = cost (Syn.subst σ E) (Syn.subst σ F) (Syn.subst σ N) := by simp [cost]

private theorem frozen_diagonal (f : PR 2) (p x E N : PTm n) (hf : Γ ⊢[PRAAx] source f x E) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF f) p (data x E N)) (ap2 NF p (frozenData f p x N))
      (coefficient N E+two) (unit p) := by
  have hp := unit_positive (Γ := Γ) p
  have d := diagonal_rate (nameF f) NF (data x E N) (frozenData f p x N) (coefficient N E) (unit p) p hp
    (original_frozen_rate f p x E N hf)
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hp hp) hp (by ipra_le 0) d

theorem offset_distance (f g : PR 2) (p x y E F N : PTm n)
    (hf : Γ ⊢[PRAAx] source f x E) (hg : Γ ⊢[PRAAx] source g y F)
    (he : Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF g) (data x E N) (data y F N)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 f p x) (ap2 g p y) (inverseNumerator (cost E F N)) (unit p) := by
  let P := unit p
  let v := ap2 (nameF f) p (data x E N)
  let w := ap2 (nameF g) p (data y F N)
  have hp := unit_positive (Γ := Γ) p
  have hpp := positive_product _ _ hp hp
  have mid : Γ ⊢[PRAAx] distanceBounded v w two P :=
    distance_radius_mono _ _ _ _ _ _ hpp hp (by ipra_le 0) (cross_at _ _ _ _ p p he)
  have left := distance_symmetric _ _ _ _ hp (frozen_diagonal f p x E N hf)
  have right := frozen_diagonal g p y F N hg
  have native := distance_triangle_same _ _ _ _ _ _ hp (distance_triangle_same _ _ _ _ _ _ hp left mid) right
  have material := GaussianNamedEulerUnitTime.encoded_source f p x E hf
  have other := GaussianNamedEulerUnitTime.encoded_source g p y F hg
  have bounded := input_distance p _ _ _ _ N (cost E F N) material.andE₁ other.andE₁ native
  have first := decoded_distance _ E (GaussianNamedEulerUnitTime.source_at f p x E hf)
  have last := decoded_distance _ F (GaussianNamedEulerUnitTime.source_at g p y F hg)
  have hleft := distance_radius_mono _ _ _ _ zero P (le_refl one) hp (by ipra_le 0)
    (distance_symmetric _ _ _ _ (le_refl one) first)
  have hright := distance_radius_mono _ _ _ _ zero P (le_refl one) hp (by ipra_le 0) last
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hp (distance_triangle_same _ _ _ _ _ _ hp hleft bounded) hright)

theorem injective (f g : PR 2) (x y E F N : PTm n)
    (hf : Γ ⊢[PRAAx] source f x E) (hg : Γ ⊢[PRAAx] source g y F)
    (he : Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF g) (data x E N) (data y F N)) :
    Γ ⊢[PRAAx] crossEquivalent f g x y := by
  refine GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (inverseNumerator (cost E F N)) hf.andE₁ hg.andE₁ (.allI ?_)
  let sh (t : PTm n) := Syn.shift t
  let Δ := Γ.map Fm.shift
  have fs : Δ ⊢[PRAAx] source f (sh x) (sh E) := by simpa [Δ,Fm.shift,Syn.shift,sh] using hf.shift
  have gs : Δ ⊢[PRAAx] source g (sh y) (sh F) := by simpa [Δ,Fm.shift,Syn.shift,sh] using hg.shift
  have es : Δ ⊢[PRAAx] crossEquivalent (nameF f) (nameF g) (data (sh x) (sh E) (sh N)) (data (sh y) (sh F) (sh N)) :=
    by simpa [Δ,Fm.shift,Syn.shift,sh] using he.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,inverseNumerator,subst_cost,PTm.subst_mul,PTm.subst_add,
    PTm.subst_num,Syn.shift,sh] using offset_distance f g (var 0) (sh x) (sh y) (sh E) (sh F) (sh N) fs gs es

theorem zeros_equal (f g : PR 2) (x y E F N : PTm n)
    (hf : Γ ⊢[PRAAx] source f x E) (hg : Γ ⊢[PRAAx] source g y F)
    (h0 : Γ ⊢[PRAAx] crossEquivalent (nameF f) zeroF (data x E N) qzero)
    (h1 : Γ ⊢[PRAAx] crossEquivalent (nameF g) zeroF (data y F N) qzero) :
    Γ ⊢[PRAAx] crossEquivalent f g x y :=
  injective f g x y E F N hf hg (cross_trans _ _ _ _ _ _ h0 (cross_symm _ _ _ _ h1))

theorem actual_original_negative_interval_named_digamma_unique_zero_closed (f g : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      ((source f (var 0) (var 2) ⋏ source g (var 1) (var 3)) ⟶
        (crossEquivalent (nameF f) zeroF (data (var 0) (var 2) (var 4)) qzero ⋏
          crossEquivalent (nameF g) zeroF (data (var 1) (var 3) (var 4)) qzero) ⟶ crossEquivalent f g (var 0) (var 1)) :=
  closeUniv 5 (.impI (.impI (zeros_equal f g _ _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0.andE₁ Prf.hyp0.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedDigammaUniqueness
