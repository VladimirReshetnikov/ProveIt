import IPRADerivations.Analysis.Euler.PositiveAxis.GaussianNamedEulerUnitKernel

/-!
# Freeze an arbitrary original observation of the unit-kernel input

The actual named kernel is compared to the unchanged rational kernel
at the fraction decoded from f(k), for arbitrary k. Its leading radius
is exactly L(R,E)/2^k. The retimed input query pays its own half dyadic;
the independently requested named/rational observations are retained.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedEulerUnitKernelFrozenRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianNamedEulerUnitKernel (source nameF data clock lipschitz encodedData source_at encoded_source)
open GaussianUnitIntervalInputDecoding (numerator denominator fraction_recode)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

/-- Both requested output observations stay fixed, and k is unrestricted. -/
theorem original_observations (f : PR 2) (p q k x z R B E : PTm n)
    (h : Γ ⊢[PRAAx] source f x z R B E) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (nameF f) p (data x z R B E))
      (ap2 GaussianEulerUnitSubstitutionKernel.nameF q (encodedData f k x z B))
      (rateNumerator (lipschitz R E) (unit k) p q) (rateDenominator (unit k) p q) := by
  let r := clock p R E
  let A := unit r+unit k
  let D := unit r*unit k
  let L := lipschitz R E
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ (unit_positive r) (unit_positive k)
  have timeDistance := distance_congr (fraction_recode _ E (source_at f r x z R B E h)).eqSymm
    (fraction_recode _ E (source_at f k x z R B E h)).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianFastValueCut.recode_distance_bound _ _ _ _ hD (GaussianNameEquivalence.point_at f x r k h.andE₂.andE₁))
  have hi : Γ ⊢[PRAAx] GaussianEulerUnitKernelCompactRate.input z R B
      (numerator (ap2 f r x)) (denominator (ap2 f r x)) (numerator (ap2 f k x)) (denominator (ap2 f k x)) E A D :=
    .andI (encoded_source f r x z R B E h) (.andI (encoded_source f k x z R B E h) (.andI hD timeDistance))
  have raw := GaussianEulerUnitKernelCompactRate.original_observations (succ p) q z R B
    (numerator (ap2 f r x)) (denominator (ap2 f r x)) (numerator (ap2 f k x)) (denominator (ap2 f k x)) E A D hi
  have up : Γ ⊢[PRAAx] unit (succ p) ≐ two*unit p := (pw_succ two p).eqTrans (mul_comm _ _)
  have bp : Γ ⊢[PRAAx] le (two*L*unit p) (unit r) :=
    le_congr ((congrMul (.eqRefl L) up).eqTrans (by ipra_ring)) (.eqRefl _) (GaussianFastValueCut.query_budget L (succ p))
  have eN : Γ ⊢[PRAAx] rateNumerator (L*A) D (succ p) q ≐
      (L*A)*(two*unit p)*unit q+D*(two*unit p+unit q) :=
    congrAdd (congrMul (congrMul (.eqRefl _) up) (.eqRefl _)) (congrMul (.eqRefl _) (congrAdd up (.eqRefl _)))
  have eD : Γ ⊢[PRAAx] rateDenominator D (succ p) q ≐ D*(two*unit p)*unit q :=
    congrMul (congrMul (.eqRefl _) up) (.eqRefl _)
  have adjusted := distance_congr (.eqRefl _) (.eqRefl _) eN eD raw
  have coarse := distance_radius_mono _ _ _ _ (rateNumerator L (unit k) p q) (rateDenominator (unit k) p q)
    (positive_product _ _ (positive_product _ _ hD (positive_product _ _ (zero_lt_succ one) (unit_positive p))) (unit_positive q))
    (GaussianNamedInverseRate.denominator_positive _ p q (unit_positive k))
    (by dsimp only [A,D,rateNumerator,rateDenominator]
        ipra_le (𝔞(unit k)^2*𝔞(unit p)*𝔞(unit q)^2)*sl bp) adjusted
  exact distance_congr (GaussianNamedEulerUnitKernel.sample_at f p x z R B E).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) coarse

theorem original_rate (f : PR 2) (k x z R B E : PTm n) (h : Γ ⊢[PRAAx] source f x z R B E) : Γ ⊢[PRAAx]
    independentRate (nameF f) GaussianEulerUnitSubstitutionKernel.nameF (data x z R B E) (encodedData f k x z B)
      (lipschitz R E) (unit k) := by
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source f (sh x) (sh z) (sh R) (sh B) (sh E) :=
    by simpa [Fm.shift,Syn.shift,sh] using h.shift.shift
  refine .allI (.allI ?_)
  simpa only [independentRate,GaussianNamedEulerUnitKernel.subst_data,GaussianNamedEulerUnitKernel.subst_encodedData,
    GaussianCoefficientNameBounds.subst_unit,GaussianEulerUnitKernelCompactRate.subst_lipschitz,Syn.shift,sh] using
    original_observations f (var 1) (var 0) (sh k) (sh x) (sh z) (sh R) (sh B) (sh E) hs

theorem actual_named_unit_kernel_frozen_input_rate_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source f (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      independentRate (nameF f) GaussianEulerUnitSubstitutionKernel.nameF (data (var 1) (var 2) (var 3) (var 4) (var 5))
        (encodedData f (var 0) (var 1) (var 2) (var 4)) (lipschitz (var 3) (var 5)) (unit (var 0))) :=
  closeUniv 6 (.impI (original_rate f _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedEulerUnitKernelFrozenRate
