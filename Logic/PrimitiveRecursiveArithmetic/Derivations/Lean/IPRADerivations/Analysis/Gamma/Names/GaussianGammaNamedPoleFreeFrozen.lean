import IPRADerivations.Analysis.Gamma.Names.GaussianGammaNamedPoleFree

/-!
# Independent clocks for the late freeze of pole-free named Gamma

A sufficiently late raw input observation encodes an exact native
Gamma name. It is compared to the actual regular pole-free sampler at
two independent output clocks.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNamedPoleFreeFrozen

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianExponentialReference (unit_monotone)
open GaussianGammaNamedPoleFree (clock clock_demand data encodedData encoded_rate encoded_regular
  nameF name_at name_regular sample source)
open GaussianNameEquivalence (cross_refl point_at)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator denominator_positive rate_at)
open GaussianNamedLipschitzRate (diagonalNumerator diagonalDenominator diagonalEnvelope)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "L" => GaussianGammaReciprocalInverse.gammaF
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

theorem sample_step (f : PR 2) (u q s k x R E : PTm n) (hf : Γ ⊢[PRAAx] source f x R E)
    (hs : Γ ⊢[PRAAx] le s (succ u)) (hk : Γ ⊢[PRAAx] le (clock s R E) k) : Γ ⊢[PRAAx]
    distanceBounded (sample f u x R E) (ap2 L q (encodedData f k x R E))
      (rateNumerator one (unit s) (succ u) q) (rateDenominator (unit s) (succ u) q) := by
  have near := encoded_rate f f (clock u R E) k s x x R E hf hf (cross_refl f x hf.andE₁)
    (clock_demand u R E s hs) (le_trans (clock_demand s R E s (le_succ_self _)) hk)
  exact rate_at L L (encodedData f (clock u R E) x R E) (encodedData f k x R E) one (unit s) (succ u) q near

theorem diagonal_distance (f : PR 2) (t s k x R E : PTm n) (hf : Γ ⊢[PRAAx] source f x R E)
    (hk : Γ ⊢[PRAAx] le (clock s R E) k) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (nameF f) t (data x R E)) (ap2 L t (encodedData f k x R E))
      (diagonalNumerator one (unit s) (num 4) t) (diagonalDenominator (unit s) t) := by
  let u := s+t
  let D := unit s*unit t
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ (unit_positive _) (unit_positive _)
  have later : Γ ⊢[PRAAx] le t u := le_add_left t s
  have grow := unit_monotone (Γ := Γ) later
  have grow' := unit_monotone (Γ := Γ) (le_trans later (le_succ_self u))
  have actual := point_at (nameF f) (data x R E) t u (name_regular f x R E hf)
  have left := distance_radius_mono _ _ _ _ (two*unit s) D
    (positive_product _ _ (unit_positive _) (unit_positive _)) hD
    (by dsimp only [D]; ipra_le (𝔞(unit s)*𝔞(unit t))*sl grow)
    (distance_congr (.eqRefl _) (name_at f u x R E) (.eqRefl _) (.eqRefl _) actual)
  have step := sample_step f u t s k x R E hf (le_trans (le_add_right s t) (le_succ_self u)) hk
  have right := distance_radius_mono _ _ _ _ (unit t+two*unit s) D
    (denominator_positive _ _ _ (unit_positive s)) hD
    (by unfold rateNumerator rateDenominator; dsimp only [D]; ipra_le (𝔞(unit s)*𝔞(unit s)*𝔞(unit t))*sl grow') step
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold diagonalNumerator; ipra_ring)
    (.eqRefl _) (distance_triangle_same _ _ _ _ _ _ hD left right)

theorem original_frozen_rate (f : PR 2) (s k x R E : PTm n) (hf : Γ ⊢[PRAAx] source f x R E)
    (hk : Γ ⊢[PRAAx] le (clock s R E) k) : Γ ⊢[PRAAx]
    independentRate (nameF f) L (data x R E) (encodedData f k x R E) one (unit s) := by
  refine GaussianNamedLipschitzRate.independent_rate _ _ _ _ _ _ (num 4) (unit_positive s)
    (name_regular f x R E hf) (encoded_regular f k x R E hf) (.allI ?_)
  let Δ := Γ.map Fm.shift
  let sh (u : PTm n) := Syn.shift u
  have hs : Δ ⊢[PRAAx] source f (sh x) (sh R) (sh E) := by
    simpa only [Δ,sh,Syn.shift,Fm.shift,GaussianGammaNamedPoleFree.subst_source] using hf.shift
  have ks : Δ ⊢[PRAAx] le (clock (sh s) (sh R) (sh E)) (sh k) := by
    simpa only [Δ,sh,Syn.shift,Fm.shift,subst_le,GaussianGammaNamedPoleFree.subst_clock] using hk.shift
  simpa only [diagonalEnvelope,GaussianGammaNamedPoleFree.subst_encodedData,
    GaussianGammaNamedPoleFree.subst_data,GaussianCoefficientNameBounds.subst_unit,
    one,LeanProofs.IPRA.PTm.subst_num,Syn.shift,sh,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    diagonal_distance f (var 0) (sh s) (sh k) (sh x) (sh R) (sh E) hs ks

theorem actual_named_pole_free_Gamma_frozen_rate_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      ((source f (var 2) (var 3) (var 4) ⋏ le (clock (var 0) (var 3) (var 4)) (var 1)) ⟶
        independentRate (nameF f) L (data (var 2) (var 3) (var 4)) (encodedData f (var 1) (var 2) (var 3) (var 4))
          one (unit (var 0))) :=
  closeUniv 5 (.impI (original_frozen_rate f _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaNamedPoleFreeFrozen
