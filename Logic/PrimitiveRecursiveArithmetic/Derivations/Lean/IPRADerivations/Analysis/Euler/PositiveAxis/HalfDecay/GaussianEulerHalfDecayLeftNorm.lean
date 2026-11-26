import IPRADerivations.Analysis.Euler.PositiveAxis.HalfDecay.GaussianEulerHalfDecayQuadrature
import IPRADerivations.Analysis.Euler.Integration.Decay.GaussianEulerDecayEndpointBound

/-!
# Half-decay quadrature retains the actual left endpoint norm

The original rational-time half-decay grid is unchanged. A bound A/B
on its actual left decay observation at the independent precision q
gives 2A/B plus explicit mesh and observation errors. In particular
there is no substitution of a dyadic integer-cutoff bound for A/B.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerHalfDecayLeftNorm

open_ipra
open GaussianEulerHalfDecayQuadrature (halfF half_decay_independent_endpoint)
open GaussianEulerDecayMesh (observation)
open GaussianEulerDecayQuadraturePrecision (endpointDifference)
open GaussianCompactRiemannName (quadrature)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bounded_product bound_congr)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def errorNumerator (p q M C E : PTm n) : PTm n :=
  num 3*C*C*unit p*unit q+two*C*E*M*unit q+num 32*E*E*M*unit p
def errorDenominator (p q M E : PTm n) : PTm n := two*E*E*M*unit p*unit q
def numerator (p q M C E A B : PTm n) : PTm n :=
  two*A*errorDenominator p q M E+B*errorNumerator p q M C E
def denominator (p q M E B : PTm n) : PTm n := B*errorDenominator p q M E
def source (M a C E B : PTm n) : Fm PTm n :=
  le one a ⋏ le one M ⋏ le one E ⋏ le one C ⋏ le one B ⋏ le C ((two*E)*M)

ipra_subst errorNumerator
ipra_subst errorDenominator
ipra_subst numerator
ipra_subst denominator
ipra_subst source

theorem error_denominator_positive (p q M E : PTm n) (hM : Γ ⊢[PRAAx] le one M)
    (hE : Γ ⊢[PRAAx] le one E) : Γ ⊢[PRAAx] le one (errorDenominator p q M E) :=
  positive_product _ _ (positive_product _ _ (positive_product _ _
    (positive_product _ _ (positive_product _ _ (le_succ_self one) hE) hE) hM) (unit_positive p)) (unit_positive q)

theorem natural_bound (K : PTm n) : Γ ⊢[PRAAx] bounded (naturalPoint K) K one :=
  bound_congr (GaussianEulerDecayFactorBounds.fraction_is_radius_point K one (le_refl one)).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianDominantPairAlgebra.radius_bounded K one (le_refl one))

/-- Exact bound 2A/B+3C²/(2E²M)+C/(E·2^p)+16/2^q.
The supplied bound concerns the SAME original left observation at q. -/
theorem original_half_decay_left_norm (p q M a C E x A B : PTm n)
    (h : Γ ⊢[PRAAx] source M a C E B)
    (hleft : Γ ⊢[PRAAx] bounded (observation a (two*E) q) A B) : Γ ⊢[PRAAx]
    bounded (quadrature GaussianEulerHalfDecayQuadrature.halfF p M a C E x) (numerator p q M C E A B) (denominator p q M E B) := by
  have ha := h.andE₁
  have hm := h.andE₂.andE₁
  have he := h.andE₂.andE₂.andE₁
  have hc := h.andE₂.andE₂.andE₂.andE₁
  have hb := h.andE₂.andE₂.andE₂.andE₂.andE₁
  have hs := h.andE₂.andE₂.andE₂.andE₂.andE₂
  let D := GaussianEulerDecayQuadraturePrecision.denominator p q M (two*E)
  let V := B*unit q
  let U := two*(A*unit q+num 6*B)
  have h2e := positive_product _ _ (le_succ_self one) he
  have hd : Γ ⊢[PRAAx] le one D := positive_product _ _ (positive_product _ _ (positive_product _ _
    (positive_product _ _ h2e h2e) hm) (unit_positive p)) (unit_positive q)
  have hv : Γ ⊢[PRAAx] le one V := positive_product _ _ hb (unit_positive q)
  have endpoint : Γ ⊢[PRAAx] bounded (qmul (naturalPoint two) (endpointDifference a C (two*E) q)) U V :=
    bound_congr (.eqRefl _) (.eqRefl _) (one_mul V)
      (bounded_product _ _ two one _ V (le_refl one) hv (natural_bound two)
        (GaussianEulerDecayEndpointBound.endpoint_norm a C (two*E) q A B h2e hb hleft))
  have raw := GaussianReconstructionRoots.norm_from_distance _ _
    (two*GaussianEulerDecayQuadraturePrecision.numerator p q M C (two*E)) D U V hd hv
    (half_decay_independent_endpoint p q M a C E x ha hm he hc hs) endpoint
  have target : Γ ⊢[PRAAx] le one (denominator p q M E B) :=
    positive_product _ _ hb (error_denominator_positive p q M E hm he)
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ hd hv) target
    (le_of_eq_add (d := zero) (by dsimp only [D,U,V,numerator,denominator,errorNumerator,errorDenominator,
      GaussianEulerDecayQuadraturePrecision.numerator,GaussianEulerDecayQuadraturePrecision.denominator,GaussianNameRingLaws.three]; ipra_ring)) raw

/-- A native nonnegative weight K retains precisely the coefficient
2K of the actual left decay norm, including the K=0 case. -/
theorem original_weighted_half_decay_left_norm (p q M a C E x A B K : PTm n)
    (h : Γ ⊢[PRAAx] source M a C E B)
    (hleft : Γ ⊢[PRAAx] bounded (observation a (two*E) q) A B) : Γ ⊢[PRAAx]
    bounded (qmul (naturalPoint K) (quadrature GaussianEulerHalfDecayQuadrature.halfF p M a C E x))
      (K*numerator p q M C E A B) (denominator p q M E B) :=
  bound_congr (.eqRefl _) (.eqRefl _) (one_mul _)
    (bounded_product _ _ K one _ _ (le_refl one)
      (positive_product _ _ h.andE₂.andE₂.andE₂.andE₂.andE₁
        (error_denominator_positive p q M E h.andE₂.andE₁ h.andE₂.andE₂.andE₁))
      (natural_bound K) (original_half_decay_left_norm p q M a C E x A B h hleft))

theorem original_rational_time_half_decay_retains_left_observation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    ((source (var 2) (var 3) (var 4) (var 5) (var 8) ⋏ bounded (observation (var 3) (two*var 5) (var 1)) (var 7) (var 8)) ⟶
      bounded (quadrature GaussianEulerHalfDecayQuadrature.halfF (var 0) (var 2) (var 3) (var 4) (var 5) (var 6))
        (numerator (var 0) (var 1) (var 2) (var 4) (var 5) (var 7) (var 8))
        (denominator (var 0) (var 1) (var 2) (var 5) (var 8))) :=
  closeUniv 9 (.impI (original_half_decay_left_norm _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem original_rational_time_weighted_half_decay_left_observation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    ((source (var 2) (var 3) (var 4) (var 5) (var 8) ⋏ bounded (observation (var 3) (two*var 5) (var 1)) (var 7) (var 8)) ⟶
      bounded (qmul (naturalPoint (var 9)) (quadrature GaussianEulerHalfDecayQuadrature.halfF (var 0) (var 2) (var 3) (var 4) (var 5) (var 6)))
        (var 9*numerator (var 0) (var 1) (var 2) (var 4) (var 5) (var 7) (var 8))
        (denominator (var 0) (var 1) (var 2) (var 5) (var 8))) :=
  closeUniv 10 (.impI (original_weighted_half_decay_left_norm _ _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerHalfDecayLeftNorm
