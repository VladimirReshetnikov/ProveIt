import IPRADerivations.Analysis.Gamma.Names.PositiveAxis.GaussianGammaPositiveNamedReciprocalFrozen
import IPRADerivations.Analysis.Gamma.Names.PositiveAxis.GaussianGammaPositiveNamedRationalFreeze
import IPRADerivations.Analysis.Gamma.Digamma.PositiveNames.GaussianNamedPositiveDigamma

/-!
# Compare the original positive named digamma to an exact rational freeze

The reciprocal and the first logarithmic Euler integral use the same
input observation. Their quantitative product comparison is uniform
in the numerator and denominator of that observation.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaPositiveNamedDigammaFrozen

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaMinimumFreezeRational (numerator denominator frozen_rational_domain)
open GaussianGammaPositiveNamedRationalFreeze (clock threshold_le)
open GaussianGammaPositiveNamedReciprocalFrozen (bound coefficient)
open GaussianNameBounds (U all_samples_bounded)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedPositiveDigamma (source nameF data inverseF inverseData inverse_regular derivativeF derivativeData derivative_regular)
open GaussianRationalHorner (positive_product)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "P" => GaussianGammaC7Name.nameF
local notation "T" => GaussianEulerLogarithmicImproperName.nameF
local notation "D" => GaussianGammaDigammaNative.nameF
local notation "dd" => GaussianGammaDigammaNative.data

def gain (f : PR 2) (x A : PTm n) : PTm n :=
  U (derivativeF f) (derivativeData x A)*coefficient+bound*num 5

ipra_subst gain [derivativeData, one]

def frozenData (f : PR 2) (k x : PTm n) : PTm n := dd (numerator f k x) (denominator f k x)

ipra_subst frozenData

theorem original_rate (f : PR 2) (s k x A : PTm n) (h : Γ ⊢[PRAAx] source f x A)
    (hk : Γ ⊢[PRAAx] le (clock f s one x A) k) : Γ ⊢[PRAAx]
    independentRate (nameF f) D (data f x A) (frozenData f k x) (gain f x A) (unit s) := by
  let a := numerator f k x
  let b := denominator f k x
  let u := inverseData x A
  let v := derivativeData x A
  let w := GaussianGammaDigammaNative.reciprocalData a b
  let z := GaussianGammaDigammaNative.derivativeData a b
  let B := unit s
  have hB := unit_positive (Γ := Γ) s
  have hf := inverse_regular f x A h
  have hg := derivative_regular f x A h
  have m := le_trans (threshold_le (Γ := Γ) f s one x A) hk
  have hn := (frozen_rational_domain f k x A h m).andE₁
  have hr := GaussianGammaDigammaNative.reciprocal_regular a b hn
  have ht := GaussianGammaDigammaNative.derivative_regular a b hn
  have rate := GaussianNamedMultiplyRate.independent_rate (inverseF f) (derivativeF f) P T u v w z
    coefficient B (num 5) B (U (derivativeF f) v) bound hB hB hf hg hr ht
    (all_samples_bounded _ _ hg) (GaussianGammaPositiveNamedReciprocalFrozen.rational_bounded a b hn)
    (GaussianGammaPositiveNamedReciprocalFrozen.original_rate f s k x A h hk)
    (GaussianGammaPositiveNamedRationalFreeze.euler_rate f s one k x A h hk)
  exact GaussianNamedRateRadius.weaken (nameF f) D (data f x A) (frozenData f k x) _ _ (gain f x A) B
    (positive_product _ _ hB hB) hB
    (le_of_eq_add (d := zero) (by unfold GaussianNamedMultiplyRate.leadingNumerator gain; ipra_ring)) rate

theorem actual_original_positive_named_digamma_frozen_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source f (var 0) (var 1) ⟶ le (clock f (var 2) one (var 0) (var 1)) (var 3) ⟶
      independentRate (nameF f) D (data f (var 0) (var 1)) (frozenData f (var 3) (var 0))
        (gain f (var 0) (var 1)) (unit (var 2))) :=
  closeUniv 4 (.impI (.impI (original_rate f _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaPositiveNamedDigammaFrozen
