import IPRADerivations.Analysis.Names.GaussianNamedPositiveReciprocal

/-!
# The positive reciprocal at a literal frozen parameter observation

The frozen value reads the same numerator and denominator as the
rational specialization of the original parameter. The comparison
with the genuine reciprocal name keeps the full E²/2^k rate.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedPositiveReciprocalFrozen

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianNamedPositiveReciprocal (clock observation observation_inverse observation_canonical observation_bound nameF data name_at)
open GaussianNamedPositiveLogarithm (source numerator denominator decoded_domain decoded_value)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalReciprocal (qone)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameEquivalence (point_at)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def frozen (f : PR 2) (k x : PTm n) : PTm n := fraction (denominator f k x) (numerator f k x)

@[simp] theorem subst_frozen {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (k x : PTm n) :
    Syn.subst σ (frozen f k x) = frozen f (Syn.subst σ k) (Syn.subst σ x) := by
  simp [frozen,numerator,denominator]

private theorem frozen_bound (f : PR 2) (k x E T : PTm n) (hs : Γ ⊢[PRAAx] source f x E T) :
    Γ ⊢[PRAAx] bounded (frozen f k x) E one := by
  let a := numerator f k x
  let b := denominator f k x
  have h := decoded_domain f k x E T hs
  have base := GaussianRationalReciprocal.bound_congr
    (GaussianEulerDecayFactorBounds.fraction_is_radius_point b a h.andE₁.andE₁).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianDominantPairAlgebra.radius_bounded b a h.andE₁.andE₁)
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ h.andE₁.andE₁ (le_refl one)
    (le_congr (by ipra_ring) (.eqRefl _) h.andE₂.andE₁) base

private theorem frozen_inverse (f : PR 2) (k x E T : PTm n) (hs : Γ ⊢[PRAAx] source f x E T) :
    Γ ⊢[PRAAx] qmul (frozen f k x) (ap2 f k x) ≐ qone := by
  have h := decoded_domain f k x E T hs
  exact (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _) (decoded_value f k x E T hs).eqSymm).eqTrans
    (GaussianEulerCompactExhaustionNormalization.exact_inverse_product _ _ h.andE₁.andE₁ h.andE₁.andE₂)

theorem original_observations (f : PR 2) (p q k x E T : PTm n)
    (hs : Γ ⊢[PRAAx] source f x E T) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (nameF f) p (data x E)) (ap2 constantF q (frozen f k x))
      (rateNumerator (E*E) (unit k) p q) (rateDenominator (unit k) p q) := by
  let s := clock p E
  let a := ap2 f s x
  let b := ap2 f k x
  let i := observation f p x E
  let j := frozen f k x
  let U := unit s
  let V := unit k
  let P := unit p
  let Q' := unit q
  have hD : Γ ⊢[PRAAx] le one (U*V) := positive_product _ _ (unit_positive _) (unit_positive _)
  have left := observation_inverse f p x E T hs
  have right := frozen_inverse f k x E T hs
  have base := GaussianApproximateInverseDistance.central_distance a b i j E one (U+V) (U*V)
    (le_refl one) hD (observation_bound f p x E T hs) (frozen_bound f k x E T hs) (point_at f x s k hs.andE₁)
  have cj : Γ ⊢[PRAAx] GaussianRationalHorner.canonical j :=
    GaussianRationalHorner.ofGaussian_canonical _ _ (decoded_domain f k x E T hs).andE₁.andE₁
  have l : Γ ⊢[PRAAx] qmul i (qmul b j) ≐ i :=
    (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _) ((GaussianRationalPowerAlgebra.qmul_commutative b j).eqTrans right)).eqTrans
      (GaussianReciprocalHorner.qmul_one_right i (observation_canonical f p x E T hs))
  have r : Γ ⊢[PRAAx] qmul j (qmul a i) ≐ j :=
    (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _) ((GaussianRationalPowerAlgebra.qmul_commutative a i).eqTrans left)).eqTrans
      (GaussianReciprocalHorner.qmul_one_right j cj)
  have pay : Γ ⊢[PRAAx] le (E*E*P) U := GaussianFastValueCut.query_budget (E*E) p
  have budget : Γ ⊢[PRAAx] le ((E*E*(U+V))*(V*P*Q'))
      ((E*E*P*Q'+V*(P+Q'))*(U*V)) := by
    ipra_le 𝔞(V*V*Q')*sl pay+𝔞(V*P*U*V)
  exact distance_radius_mono _ _ _ _ _ _ hD
    (positive_product _ _ (positive_product _ _ (unit_positive _) (unit_positive _)) (unit_positive _)) budget
    (distance_congr (l.eqTrans (name_at f p x E).eqSymm) (r.eqTrans (constant_at q j).eqSymm) (.eqRefl _) (by ipra_ring) base)

theorem original_rate (f : PR 2) (k x E T : PTm n) (hs : Γ ⊢[PRAAx] source f x E T) :
    Γ ⊢[PRAAx] independentRate (nameF f) constantF (data x E) (frozen f k x) (E*E) (unit k) := by
  let sh (v : PTm n) := Syn.shift (Syn.shift v)
  have h : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source f (sh x) (sh E) (sh T) := by
    simpa only [Fm.shift,Syn.shift,GaussianNamedPositiveLogarithm.subst_source,sh] using hs.shift.shift
  refine .allI (.allI ?_)
  simpa only [independentRate,GaussianNamedPositiveReciprocal.subst_data,subst_frozen,subst_ap2,
    GaussianCoefficientNameBounds.subst_unit,LeanProofs.IPRA.PTm.subst_mul,Syn.shift,sh] using
    original_observations f (var 1) (var 0) (sh k) (sh x) (sh E) (sh T) h

theorem actual_named_positive_reciprocal_frozen_rate_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (source f (var 1) (var 2) (var 3) ⟶
        independentRate (nameF f) constantF (data (var 1) (var 2)) (frozen f (var 0) (var 1))
          (var 2*var 2) (unit (var 0))) :=
  closeUniv 4 (.impI (original_rate f _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedPositiveReciprocalFrozen
