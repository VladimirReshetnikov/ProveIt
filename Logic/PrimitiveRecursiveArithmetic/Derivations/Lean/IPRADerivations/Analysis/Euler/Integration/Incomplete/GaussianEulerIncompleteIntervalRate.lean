import IPRADerivations.Analysis.Names.Rates.Perturbations.GaussianNamedSmallAddendRate
import IPRADerivations.Analysis.Euler.Integration.Incomplete.GaussianEulerIncompleteInterval
import IPRADerivations.Analysis.Euler.Integration.Incomplete.GaussianEulerIncompleteLargeEndpoint

/-!
# Exact compact-to-upper-incomplete rate at original integer endpoints

The actual original upper samples are canonical at every raw encoding.
When the interval ends at any original integer top cutoff, its genuine
upper-tail bound discharges the generic small-addend contract internally.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIncompleteIntervalRate

open_ipra
open GaussianEulerIncompleteName (upperF)
open GaussianEulerIncompleteInterval (leftData rightData intervalData sumData)
open GaussianEulerCompactAdditivity (nameF)
open GaussianGammaIntegralCutoffs (top)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedSmallAddendRate (tailSamples)
open GaussianRationalHorner (canonical)
open GaussianRationalMetric (bounded)
open GaussianCoefficientNameBounds (unit)

variable {ℓ : ℕ} {Γ : List (Fm PTm ℓ)}

def source (k z R B A a C E T : PTm ℓ) : Fm PTm ℓ :=
  GaussianEulerIncompleteInterval.source z R B A a C E T ⋏ (a+C ≐ top k A R*E)
ipra_subst source [top, GaussianGammaIntegralCutoffs.height, GaussianGammaIntegralCutoffs.tailCoefficient]

theorem upper_canonical (p z R B A a b : PTm ℓ) : Γ ⊢[PRAAx]
    canonical (ap2 upperF p (GaussianEulerIncompleteName.data z R B A a b)) :=
  GaussianRationalHorner.canonical_congr (GaussianEulerIncompleteName.upper_at p z R B A a b)
    (GaussianCompactRiemannName.name_canonical GaussianEulerIntegrandName.evaluatorF
      (GaussianEulerCutoffCauchyComparison.clock p) _ _ _ _ _ _)

private theorem data_congr (z R B A a a' b : PTm ℓ) (ha : Γ ⊢[PRAAx] a ≐ a') : Γ ⊢[PRAAx]
    GaussianEulerIncompleteName.data z R B A a b ≐ GaussianEulerIncompleteName.data z R B A a' b := by
  unfold GaussianEulerIncompleteName.data
  exact congrPairT (.eqRefl _) (congrPairT (.eqRefl _) (congrPairT ha (.eqRefl _)))

theorem original_tail_sample (p k z R B A a C E T : PTm ℓ) (h : Γ ⊢[PRAAx] source k z R B A a C E T) : Γ ⊢[PRAAx]
    bounded (ap2 upperF p (rightData z R B A a C E)) (one*unit p+unit (k+num 6)) (unit (k+num 6)*unit p) := by
  have bound := GaussianEulerIncompleteLargeEndpoint.original_dyadic_upper_bound p k z R B A E
    (.andI h.andE₁.andE₁ h.andE₁.andE₂.andE₂.andE₂.andE₁)
  have literal := data_congr z R B A _ _ E h.andE₂.eqSymm
  exact GaussianRationalReciprocal.bound_congr (congrAp2 upperF (.eqRefl p) literal) (by ipra_ring) (.eqRefl _) bound

theorem original_tail_samples (k z R B A a C E T : PTm ℓ) (h : Γ ⊢[PRAAx] source k z R B A a C E T) : Γ ⊢[PRAAx]
    tailSamples upperF (rightData z R B A a C E) one (unit (k+num 6)) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift k) (Syn.shift z) (Syn.shift R) (Syn.shift B)
      (Syn.shift A) (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift T) := by simpa [Fm.shift,Syn.shift] using h.shift
  refine .allI ?_
  simpa only [tailSamples,GaussianEulerIncompleteInterval.subst_rightData,GaussianCoefficientNameBounds.subst_unit,
    PTm.subst_add,PTm.subst_num,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using
    (.andI (upper_canonical (Γ := Γ.map Fm.shift) (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift A)
      (Syn.shift a+Syn.shift C) (Syn.shift E))
      (original_tail_sample (var 0) (Syn.shift k) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift A)
        (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift T) hs))

theorem original_interval_rate (k z R B A a C E T : PTm ℓ) (h : Γ ⊢[PRAAx] source k z R B A a C E T) : Γ ⊢[PRAAx]
    independentRate nameF upperF (intervalData z R B a C E T) (leftData z R B A a E) one (unit (k+num 6)) :=
  GaussianNamedSmallAddendRate.independent_rate nameF upperF upperF _ _ _ one (unit (k+num 6))
    (GaussianCoefficientNameBounds.unit_positive _)
    (GaussianEulerCompactAdditivity.name_regular z R B a C E T (GaussianEulerIncompleteInterval.original_interval_source z R B A a C E T h.andE₁))
    (GaussianEulerIncompleteName.original_regular_names z R B A a E (GaussianEulerIncompleteInterval.left_source z R B A a C E T h.andE₁)).andE₂
    (GaussianEulerIncompleteName.original_regular_names z R B A (a+C) E (GaussianEulerIncompleteInterval.right_source z R B A a C E T h.andE₁)).andE₂
    (GaussianEulerIncompleteInterval.original_interval_decomposition z R B A a C E T h.andE₁)
    (original_tail_samples k z R B A a C E T h)

theorem original_later_tail_samples (n k z R B A a C E T : PTm ℓ) (h : Γ ⊢[PRAAx] source k z R B A a C E T)
    (hn : Γ ⊢[PRAAx] le n k) : Γ ⊢[PRAAx] tailSamples upperF (rightData z R B A a C E) one (unit (n+num 6)) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift k) (Syn.shift z) (Syn.shift R) (Syn.shift B)
      (Syn.shift A) (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift T) := by simpa [Fm.shift,Syn.shift] using h.shift
  have ns : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift n) (Syn.shift k) := by simpa [Fm.shift,Syn.shift] using hn.shift
  refine .allI ?_
  have u := GaussianExponentialReference.unit_monotone (add_le_add_right (num 6) ns)
  have old := GaussianNamedSmallAddendRate.tail_at upperF _ _ _ (var 0)
    (original_tail_samples (Syn.shift k) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift A)
      (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift T) hs)
  have bd : Γ.map Fm.shift ⊢[PRAAx] bounded
      (ap2 upperF (var 0) (rightData (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift A) (Syn.shift a) (Syn.shift C) (Syn.shift E)))
      (one*unit (var 0)+unit (Syn.shift n+num 6)) (unit (Syn.shift n+num 6)*unit (var 0)) :=
    GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _
    (GaussianRationalHorner.positive_product _ _ (GaussianCoefficientNameBounds.unit_positive _) (GaussianCoefficientNameBounds.unit_positive _))
    (GaussianRationalHorner.positive_product _ _ (GaussianCoefficientNameBounds.unit_positive _) (GaussianCoefficientNameBounds.unit_positive _))
    (by ipra_le (Groth.ι (Q.mk (Γ.map Fm.shift) (unit (var 0))))^2*sl u) old.andE₂
  simpa only [tailSamples,GaussianEulerIncompleteInterval.subst_rightData,GaussianCoefficientNameBounds.subst_unit,
    PTm.subst_add,PTm.subst_num,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using (.andI old.andE₁ bd)

theorem original_later_interval_rate (n k z R B A a C E T : PTm ℓ) (h : Γ ⊢[PRAAx] source k z R B A a C E T)
    (hn : Γ ⊢[PRAAx] le n k) : Γ ⊢[PRAAx]
    independentRate nameF upperF (intervalData z R B a C E T) (leftData z R B A a E) one (unit (n+num 6)) :=
  GaussianNamedSmallAddendRate.independent_rate nameF upperF upperF _ _ _ one (unit (n+num 6))
    (GaussianCoefficientNameBounds.unit_positive _)
    (GaussianEulerCompactAdditivity.name_regular z R B a C E T (GaussianEulerIncompleteInterval.original_interval_source z R B A a C E T h.andE₁))
    (GaussianEulerIncompleteName.original_regular_names z R B A a E (GaussianEulerIncompleteInterval.left_source z R B A a C E T h.andE₁)).andE₂
    (GaussianEulerIncompleteName.original_regular_names z R B A (a+C) E (GaussianEulerIncompleteInterval.right_source z R B A a C E T h.andE₁)).andE₂
    (GaussianEulerIncompleteInterval.original_interval_decomposition z R B A a C E T h.andE₁)
    (original_later_tail_samples n k z R B A a C E T h hn)

theorem actual_original_compact_upper_incomplete_integer_endpoint_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      independentRate nameF upperF (intervalData (var 1) (var 2) (var 3) (var 5) (var 6) (var 7) (var 8))
        (leftData (var 1) (var 2) (var 3) (var 4) (var 5) (var 7)) one (unit (var 0+num 6))) :=
  closeUniv 9 (.impI (original_interval_rate _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerIncompleteIntervalRate
