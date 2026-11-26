import IPRADerivations.Analysis.Euler.Logarithms.UpperBounds.GaussianEulerLogarithmicNamedUpperBound
import IPRADerivations.Analysis.Euler.PositiveAxis.UpperBounds.GaussianEulerUpperTailCauchyBudget

/-!
# Genuine logarithmic compact upper-tail cutoff budget

At the exact original integer left cutoff, the fixed positive half-decay
reference has its actual scalar numerator and denominator bounded using
the original decay observations. A second finite rational gap removes
only that reference query. The unchanged logarithmic compact name is
then bounded by 2^(R+j+1)*(R+j)! / 2^height plus its requested error.
The original omitted-tail budget at degree R+j spends that coefficient.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicUpperCutoffBudget

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerWeightedHalfDecay (majorant halfSample)
open GaussianEulerUpperTailPointwise (referenceTop referenceBottom)
open GaussianEulerLogarithmicNamedUpperBound (original_named_bound denominator_positive)
open GaussianEulerHalfDecayReference (scalar numerator denominator denominator_positive scalar_representation decay_reference_error)
open GaussianEulerLogarithmicIntervalName (nameF data)
open GaussianEulerHalfDecayTailBound (integer_left_observation)
open GaussianGammaIntegralCutoffs (height top)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianRationalMetric (bounded)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalHorner (positive_product)
open GaussianReconstructionRoots (norm_from_distance)
open RationalGaussianEmbedding (embed native)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def point (p j z R B k A C E T : PTm n) : PTm n :=
  GaussianEulerLogarithmicNamedUpperBound.point p j z R B (top k A (R+j)*E) C E T
def source (j z R B k A C E T : PTm n) : Fm PTm n :=
  GaussianEulerLogarithmicNamedUpperBound.source z R B (top k A (R+j)*E) C E T

/-- The reference is the actual nonnegative scalar, with its own exact
representation. Its observation allowance is retained explicitly. -/
theorem integer_reference_budget (q L E : PTm n) (hE : Γ ⊢[PRAAx] le one E) : Γ ⊢[PRAAx]
    le (referenceTop q (two*L*E) E*(unit L*unit q))
      ((unit q+num 5*unit L)*referenceBottom q (two*L*E) E) := by
  let a := two*L*E
  let U := unit q
  let V := unit L
  let N := numerator q a E
  let D := denominator q a E
  let g := native (ZT.ofNat N)
  have up := unit_positive (Γ := Γ) q
  have vp := unit_positive (Γ := Γ) L
  have uv := positive_product _ _ up up
  have vu := positive_product _ _ vp up
  have hd : Γ ⊢[PRAAx] le one D := GaussianEulerHalfDecayReference.denominator_positive q a E
  have near := distance_radius_mono _ _ _ _ two U uv up (le_of_eq_add (d := zero) (by ipra_ring))
    (decay_reference_error q q a E hE)
  have old : Γ ⊢[PRAAx] bounded (halfSample q a E) (U+two*V) (V*U) :=
    bound_congr (integer_left_observation L E q hE).eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianEulerDecayFactorBounds.original_integer_decay_bound L q)
  have joined := norm_from_distance _ _ two U (U+two*V) (V*U) up vu near old
  have hb : Γ ⊢[PRAAx] bounded (embed (scalar q a E)) (U+num 4*V) (V*U) :=
    bounded_radius_mono _ _ _ _ _ (positive_product _ _ up vu) vu
      (le_of_eq_add (d := zero) (by ipra_ring)) joined
  have rep := RationalGaussianEmbedding.embed_from_representation _ _ _ (scalar_representation (Γ := Γ) q a E)
  have clear := GaussianRationalMetric.bounded_to_cleared _ g D (U+num 4*V) (V*U) hd vu rep hb
  have norm : Γ ⊢[PRAAx] ComplexLogarithmRemainder.normSq g ≐ N*N := by
    simpa only [g,native,GaussianDominantPairAlgebra.radiusNumerator] using
      GaussianDominantPairAlgebra.radius_numerator_norm (Γ := Γ) N
  have eqleft : Γ ⊢[PRAAx] ((V*U)*(V*U))*ComplexLogarithmRemainder.normSq g ≐
      (N*(V*U))*(N*(V*U)) := (congrMul (.eqRefl _) norm).eqTrans (by ipra_ring)
  have square : Γ ⊢[PRAAx] le ((N*(V*U))*(N*(V*U)))
      (((U+num 4*V)*D)*((U+num 4*V)*D)) := le_congr eqleft (by ipra_ring) clear
  have linear := nat_sqrt_mono square
  exact le_congr (by unfold referenceTop; dsimp only [a,U,V,N,D]; ipra_ring)
    (by unfold referenceBottom; dsimp only [a,U,V,N,D]; ipra_ring)
    (add_le_add_right (D*V*U) (mul_le_mul_right U linear))

theorem integer_observation_slack (p q j z R B L C E T : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerLogarithmicNamedUpperBound.source z R B (two*L*E) C E T) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack
      (GaussianEulerLogarithmicNamedUpperBound.point p j z R B (two*L*E) C E T)
      (two*majorant (R+j)*unit p+unit L) (unit L*unit p) (num 10*majorant (R+j)) q := by
  let a := two*L*E
  let M := majorant (R+j)
  let P := unit p
  let Q := unit q
  let V := unit L
  have he := h.andE₁.andE₁.andE₂.andE₁
  have query := integer_reference_budget q L E he
  have actual := original_named_bound p q j z R B a C E T h
  have newden : Γ ⊢[PRAAx] le one ((V*P)*Q) :=
    positive_product _ _ (positive_product _ _ (unit_positive L) (unit_positive p)) (unit_positive q)
  have compare : Γ ⊢[PRAAx]
      le (GaussianEulerLogarithmicNamedUpperBound.numerator p q (R+j) a E*((V*P)*Q))
        (((two*M*P+V)*Q+(num 10*M)*(V*P))*GaussianEulerLogarithmicNamedUpperBound.denominator p q a E) :=
    le_congr (by unfold GaussianEulerLogarithmicNamedUpperBound.numerator; dsimp only [a,M,P,Q,V]; ipra_ring)
      (by unfold GaussianEulerLogarithmicNamedUpperBound.denominator; dsimp only [a,M,P,Q,V]; ipra_ring)
      (add_le_add_right (referenceBottom q a E*V*P*Q) (mul_le_mul_right (two*M*P*P) query))
  exact bounded_radius_mono _ _ _ _ _
    (GaussianEulerLogarithmicNamedUpperBound.denominator_positive p q a E) newden compare actual

/-- Genuine integral-tail bound for the same logarithmic compact name,
with its exact factorial coefficient and only the requested error. -/
theorem original_integer_tail_bound (p j z R B L C E T : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerLogarithmicNamedUpperBound.source z R B (two*L*E) C E T) : Γ ⊢[PRAAx]
    bounded (GaussianEulerLogarithmicNamedUpperBound.point p j z R B (two*L*E) C E T)
      (two*majorant (R+j)*unit p+unit L) (unit L*unit p) :=
  GaussianRationalSlackRemoval.slack_removal_at _ _ _ (num 10*majorant (R+j))
    (positive_product _ _ (unit_positive L) (unit_positive p)) (integer_observation_slack p _ j z R B L C E T h)

theorem original_cutoff_tail_bound (p j z R B k A C E T : PTm n)
    (h : Γ ⊢[PRAAx] source j z R B k A C E T) : Γ ⊢[PRAAx]
    bounded (point p j z R B k A C E T)
      (unit p+unit (k+num 6)) (unit (k+num 6)*unit p) := by
  let L := height k A (R+j)
  have actual := original_integer_tail_bound p j z R B L C E T h
  have cleared := AnalyticNumberTheory.PhiLower.le_mul_mono
    (GaussianEulerUpperTailCauchyBudget.upper_tail_cutoff_budget (Γ := Γ) k A (R+j))
    (le_refl (unit p*unit p))
  have compare : Γ ⊢[PRAAx] le ((two*majorant (R+j)*unit p+unit L)*(unit (k+num 6)*unit p))
      ((unit p+unit (k+num 6))*(unit L*unit p)) :=
    le_congr (by ipra_ring) (by ipra_ring)
      (add_le_add_right (unit L*unit (k+num 6)*unit p) cleared)
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ (unit_positive L) (unit_positive p))
    (positive_product _ _ (unit_positive _) (unit_positive p)) compare actual

theorem actual_original_logarithmic_integer_upper_tail_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (GaussianEulerLogarithmicNamedUpperBound.source (var 2) (var 3) (var 4) (two*var 5*var 7) (var 6) (var 7) (var 8) ⟶
      bounded (GaussianEulerLogarithmicNamedUpperBound.point (var 0) (var 1) (var 2) (var 3) (var 4)
        (two*var 5*var 7) (var 6) (var 7) (var 8))
        (two*majorant (var 3+var 1)*unit (var 0)+unit (var 5)) (unit (var 5)*unit (var 0))) :=
  closeUniv 9 (.impI (original_integer_tail_bound _ _ _ _ _ _ _ _ _ Prf.hyp0))

theorem actual_original_logarithmic_upper_cutoff_budget_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) ⟶
      bounded (point (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9))
        (unit (var 0)+unit (var 5+num 6)) (unit (var 5+num 6)*unit (var 0))) :=
  closeUniv 10 (.impI (original_cutoff_tail_bound _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicUpperCutoffBudget
