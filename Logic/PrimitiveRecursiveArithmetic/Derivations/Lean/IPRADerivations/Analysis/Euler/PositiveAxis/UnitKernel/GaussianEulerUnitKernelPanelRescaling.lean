import IPRADerivations.Analysis.Euler.PositiveAxis.UnitKernel.GaussianEulerUnitKernelCompactName
import IPRADerivations.Analysis.Integration.CompactGrids.GaussianCompactIntervalRescaling

/-!
# The original rational unit-kernel names respect panel rescaling

A positive native multiple of all three physical panel coordinates keeps
the original unit compact source. The actual evaluator, parameter datum,
Lipschitz budget and compact guard remain the original ones. Only the
interval encoding changes; the two independently queried names are
cross-equivalent by the genuine original zero-distance sampled modulus.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitKernelPanelRescaling

open_ipra
open GaussianEulerUnitKernelCompactName (source nameF data evaluatorF fixedData lipschitz compact_input)
open GaussianRationalHorner (positive_product)
open GaussianNameEquivalence (crossEquivalent cross_at)
open GaussianRationalMetric (distanceBounded)
open GaussianCoefficientNameBounds (unit)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The physical margins are preserved by positive native rescaling;
the unchanged parameter disk has no interval-encoding dependency. -/
theorem source_rescaling (z R B a C E G k : PTm n)
    (h : Γ ⊢[PRAAx] source z R B a C E G) (hk : Γ ⊢[PRAAx] le one k) : Γ ⊢[PRAAx]
    source z R B (k*a) (k*C) (k*E) G := by
  have lower : Γ ⊢[PRAAx] le (k*E) (G*(k*a)) :=
    le_congr (.eqRefl _) (by ipra_ring)
      (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl k) h.andE₂.andE₂.andE₁)
  have upper : Γ ⊢[PRAAx] le (G*(k*a+k*C)+k*E) (G*(k*E)) :=
    le_congr (by ipra_ring) (by ipra_ring)
      (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl k) h.andE₂.andE₂.andE₂)
  exact .andI h.andE₁ (.andI (positive_product _ _ hk h.andE₂.andE₁) (.andI lower upper))

/-- Actual compact-name equivalence, retaining the original kernel and
both original interval tuples. Zero panel width is allowed. -/
theorem original_rescaling (z R B a C E G k : PTm n)
    (h : Γ ⊢[PRAAx] source z R B a C E G) (hk : Γ ⊢[PRAAx] le one k) : Γ ⊢[PRAAx]
    crossEquivalent nameF nameF (data z R B a C E G) (data z R B (k*a) (k*C) (k*E) G) :=
  GaussianCompactIntervalRescaling.name_rescaling evaluatorF k a C E (lipschitz R G) one (fixedData z B)
    (.andI hk (compact_input z R B a C E G h))

theorem original_observations (p q z R B a C E G k : PTm n)
    (h : Γ ⊢[PRAAx] source z R B a C E G) (hk : Γ ⊢[PRAAx] le one k) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (data z R B a C E G))
      (ap2 nameF q (data z R B (k*a) (k*C) (k*E) G)) (unit p+unit q) (unit p*unit q) :=
  cross_at _ _ _ _ p q (original_rescaling z R B a C E G k h hk)

theorem actual_unit_kernel_rescaled_source_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    ((source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⋏ le one (var 7)) ⟶
      source (var 0) (var 1) (var 2) (var 7*var 3) (var 7*var 4) (var 7*var 5) (var 6)) :=
  closeUniv 8 (.impI (source_rescaling _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem actual_original_unit_kernel_panel_rescaling_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    ((source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⋏ le one (var 7)) ⟶
      crossEquivalent nameF nameF (data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
        (data (var 0) (var 1) (var 2) (var 7*var 3) (var 7*var 4) (var 7*var 5) (var 6))) :=
  closeUniv 8 (.impI (original_rescaling _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem actual_unit_kernel_rescaled_independent_observations_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    ((source (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⋏ le one (var 9)) ⟶
      distanceBounded (ap2 nameF (var 0) (data (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)))
        (ap2 nameF (var 1) (data (var 2) (var 3) (var 4) (var 9*var 5) (var 9*var 6) (var 9*var 7) (var 8)))
        (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 10 (.impI (original_observations _ _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerUnitKernelPanelRescaling
