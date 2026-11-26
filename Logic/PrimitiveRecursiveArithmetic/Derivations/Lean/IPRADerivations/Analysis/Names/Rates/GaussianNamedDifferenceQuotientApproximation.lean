import IPRADerivations.Analysis.Names.Rates.GaussianNamedDifferenceQuotient
import IPRADerivations.Analysis.Names.Rates.GaussianNamedInverseRate

/-!
# Endpoint approximation in an actual divided-difference observation

Only the two endpoint errors are multiplied by the actual reciprocal
bound D. The quotient observation retains its one requested dyadic.
Independent endpoint-name rates are reduced to the finite raw endpoint
comparison, then one original rational gap removes auxiliary observations.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedDifferenceQuotientApproximation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianNamedDifferenceQuotient (nameF data inverse raw inverse_bound scale_distance)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator rate_at)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (qsub distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "quotientInput" => GaussianNamedDifferenceQuotient.input

def numerator (D A B C E p q r : PTm n) : PTm n :=
  D*(A*E+C*B)*unit p*unit q*unit r+(B*E)*(unit q*unit r+D*unit p*(unit q+unit r))
def denominator (B E p q r : PTm n) : PTm n := B*E*unit p*unit q*unit r
def input (f g F G : PR 2) (x y u v h D A B C E : PTm n) : Fm PTm n :=
  quotientInput f g x y h D ⋏ (le one B ⋏ (le one E ⋏
    (independentRate f F x u A B ⋏ independentRate g G y v C E)))

@[simp] theorem subst_numerator {m : ℕ} (σ : Fin n → PTm m) (D A B C E p q r : PTm n) :
    Syn.subst σ (numerator D A B C E p q r) = numerator (Syn.subst σ D) (Syn.subst σ A) (Syn.subst σ B)
      (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ r) := by simp [numerator]
@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (B E p q r : PTm n) :
    Syn.subst σ (denominator B E p q r) = denominator (Syn.subst σ B) (Syn.subst σ E)
      (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ r) := by simp [denominator]
@[simp] theorem subst_input {m : ℕ} (σ : Fin n → PTm m) (f g F G : PR 2) (x y u v h D A B C E : PTm n) :
    (input f g F G x y u v h D A B C E).subst σ = input f g F G (Syn.subst σ x) (Syn.subst σ y)
      (Syn.subst σ u) (Syn.subst σ v) (Syn.subst σ h) (Syn.subst σ D) (Syn.subst σ A)
      (Syn.subst σ B) (Syn.subst σ C) (Syn.subst σ E) := by simp [input]

theorem denominator_positive (B E p q r : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hE : Γ ⊢[PRAAx] le one E) : Γ ⊢[PRAAx]
    le one (denominator B E p q r) :=
  positive_product _ _ (positive_product _ _ (positive_product _ _ (positive_product _ _ hB hE) (unit_positive p)) (unit_positive q)) (unit_positive r)

theorem finite_error (f g : PR 2) (p s t x y h D a b A B C E : PTm n)
    (hq : Γ ⊢[PRAAx] quotientInput f g x y h D) (hB : Γ ⊢[PRAAx] le one B) (hE : Γ ⊢[PRAAx] le one E)
    (hl : Γ ⊢[PRAAx] distanceBounded (ap2 f s x) a A B) (hr : Γ ⊢[PRAAx] distanceBounded (ap2 g t y) b C E) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (nameF f g) p (data f g x y h D)) (GaussianRationalHorner.qmul (inverse h D) (qsub a b))
      (numerator D A B C E p s t) (denominator B E p s t) := by
  have first := GaussianNamedDifferenceQuotient.independent_readback f g p s t x y h D hq
  have second := scale_distance (inverse h D) _ _ D (A*E+C*B) (B*E) (positive_product _ _ hB hE)
    (inverse_bound h D hq.andE₂.andE₂) (GaussianFastValueCut.distance_difference _ _ _ _ A B C E hB hE hl hr)
  have joined := GaussianReconstructionRoots.distance_triangle _ _ _
    (GaussianNamedDifferenceQuotient.numerator D p s t) (GaussianNamedDifferenceQuotient.denominator p s t)
    (D*(A*E+C*B)) (B*E) (GaussianNamedDifferenceQuotient.denominator_positive p s t) (positive_product _ _ hB hE) first second
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold numerator GaussianNamedDifferenceQuotient.numerator GaussianNamedDifferenceQuotient.denominator; ipra_ring)
    (by unfold denominator GaussianNamedDifferenceQuotient.denominator; ipra_ring) joined

theorem observation_slack (f g F G : PR 2) (p q r t x y u v h D A B C E : PTm n)
    (hq : Γ ⊢[PRAAx] quotientInput f g x y h D) (hB : Γ ⊢[PRAAx] le one B) (hE : Γ ⊢[PRAAx] le one E)
    (hl : Γ ⊢[PRAAx] independentRate f F x u A B) (hr : Γ ⊢[PRAAx] independentRate g G y v C E) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack (qsub (ap2 (nameF f g) p (data f g x y h D)) (raw F G q r u v h D))
      (numerator D A B C E p q r) (denominator B E p q r) (two*two*D) t := by
  have left := rate_at f F x u A B t q hl
  have right := rate_at g G y v C E t r hr
  have first := finite_error f g p t t x y h D (ap2 F q u) (ap2 G r v)
    (rateNumerator A B t q) (rateDenominator B t q) (rateNumerator C E t r) (rateDenominator E t r)
    hq (GaussianNamedInverseRate.denominator_positive B t q hB) (GaussianNamedInverseRate.denominator_positive E t r hE) left right
  have oldDen := denominator_positive (rateDenominator B t q) (rateDenominator E t r) p t t
    (GaussianNamedInverseRate.denominator_positive B t q hB) (GaussianNamedInverseRate.denominator_positive E t r hE)
  have newDen := positive_product _ _ (denominator_positive B E p q r hB hE) (unit_positive t)
  exact distance_radius_mono _ _ _ _ _ _ oldDen newDen
    (le_of_eq_add (d := zero) (by dsimp only [numerator,denominator,rateNumerator,rateDenominator]; unfold unit; ipra_ring)) first

def gapQuery (f g F G : PR 2) (p q r x y u v h D A B C E : PTm n) : PTm n :=
  GaussianRationalSlackRemoval.precision (qsub (ap2 (nameF f g) p (data f g x y h D)) (raw F G q r u v h D))
    (numerator D A B C E p q r) (denominator B E p q r) (two*two*D)

theorem independent_at (f g F G : PR 2) (p q r x y u v h D A B C E : PTm n)
    (hq : Γ ⊢[PRAAx] quotientInput f g x y h D) (hB : Γ ⊢[PRAAx] le one B) (hE : Γ ⊢[PRAAx] le one E)
    (hl : Γ ⊢[PRAAx] independentRate f F x u A B) (hr : Γ ⊢[PRAAx] independentRate g G y v C E) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (nameF f g) p (data f g x y h D)) (raw F G q r u v h D)
      (numerator D A B C E p q r) (denominator B E p q r) :=
  GaussianRationalSlackRemoval.slack_removal_at _ _ _ (two*two*D) (denominator_positive B E p q r hB hE)
    (observation_slack f g F G p q r (gapQuery f g F G p q r x y u v h D A B C E) x y u v h D A B C E hq hB hE hl hr)

theorem actual_original_quotient_endpoint_rate_transport_closed (f g F G : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 13
    (input f g F G (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) ⟶
      distanceBounded (ap2 (nameF f g) (var 10) (data f g (var 0) (var 1) (var 4) (var 5)))
        (raw F G (var 11) (var 12) (var 2) (var 3) (var 4) (var 5))
        (numerator (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12))
        (denominator (var 7) (var 9) (var 10) (var 11) (var 12))) :=
  closeUniv 13 (.impI (independent_at f g F G _ _ _ _ _ _ _ _ _ _ _ _ _
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianNamedDifferenceQuotientApproximation
