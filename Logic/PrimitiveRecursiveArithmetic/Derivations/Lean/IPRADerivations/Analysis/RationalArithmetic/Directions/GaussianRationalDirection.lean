import IPRADerivations.Analysis.RationalArithmetic.Directions.GaussianRationalDirectionConstruction
import IPRADerivations.Analysis.RationalArithmetic.Directions.GaussianRationalPhaseCertificate

/-!
# Actual rational direction with the source's algebraic certificate

The nonzero original Gaussian-rational input, numerical degree and
epsilon=p/q determine the actual primitive recursive output. The exact
source certificate uses A=normSq(c), b=normSq(w^k)+1-epsilon^2, and
d=2*Re(w^k*conjugate(c)). All approximation, initialization, power and
phase premises are discharged by the computed construction. The output
also retains its actual positive normalizer and exact 65/64 bound.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalDirection

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRationalDirectionConstruction (direction normalized)
open LeanProofs.IPRA.Analysis.GaussianRationalReciprocal (power)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (canonical positive_product)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qnormSq bounded distanceBounded)
open LeanProofs.IPRA.Analysis.GaussianRationalDirectionNormalizer (norm)
open LeanProofs.IPRA.Analysis.GaussianRationalPhaseCertificate (directionDot directionCoefficient)
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName (fraction)
open LeanProofs.IPRA.Analysis.GaussianDominantSyntax (four)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def input (c k p q : PTm n) : Fm PTm n := le one (norm c) ⋏
  (le one k ⋏ (le one p ⋏ le ((num 16)*p) q))
def value (c k q : PTm n) : PTm n := power (direction c k q) k
def certificate (c k p q : PTm n) : Fm PTm n := canonical (direction c k q) ⋏
  (bounded (direction c k q) one one ⋏
    (GaussianRationalHalfAngle.unit (direction c k q) ⋏
      (GaussianRationalPhaseCertificate.certificate c (value c k q) p q ⋏
        (neg (RationalArgmin.rationalLE (directionCoefficient (value c k q) p q) (fraction zero one)) ⋏
          GaussianRationalDirectionConstruction.certificate c k q))))

ipra_subst input
ipra_subst value
ipra_subst certificate

theorem input_denominator (c k p q : PTm n) (h : Γ ⊢[PRAAx] input c k p q) : Γ ⊢[PRAAx] le one q := by
  have hp := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ h))
  have hpq : Γ ⊢[PRAAx] le p q := le_trans
    (le_of_eq_add (d := (num 15)*p) (by ipra_ring)) (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h)))
  exact le_trans hp hpq

theorem input_numerator_bound (c k p q : PTm n) (h : Γ ⊢[PRAAx] input c k p q) : Γ ⊢[PRAAx] le p q :=
  le_trans (le_of_eq_add (d := (num 15)*p) (by ipra_ring)) (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h)))

theorem phase_error (c k p q : PTm n) (h : Γ ⊢[PRAAx] input c k p q) : Γ ⊢[PRAAx]
    distanceBounded (value c k q) (normalized c k q) p (two*q) := by
  have hq := input_denominator c k p q h
  have hp := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ h))
  have constant : Γ ⊢[PRAAx] le two (four : PTm n) := le_of_eq_add (d := two) (by unfold four; ipra_ring)
  have gain := mul_le_mul_right q (LeanProofs.IPRA.AnalyticNumberTheory.PhiLower.le_mul_mono constant hp)
  exact GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ (le_of_eq_add (d := one+two) (by unfold four; ipra_ring)) hq)
    (positive_product _ _ (le_succ_self one) hq)
    (le_congr (by ipra_ring) (by ipra_ring) gain)
    (GaussianRationalDirectionConstruction.power_close_normalized c k q (Prf.andE₁ h)
      (Prf.andE₁ (Prf.andE₂ h)) hq)

theorem phase_certificate (c k p q : PTm n) (h : Γ ⊢[PRAAx] input c k p q) : Γ ⊢[PRAAx]
    GaussianRationalPhaseCertificate.certificate c (value c k q) p q :=
  GaussianRationalPhaseCertificate.direction_phase_certificate c (value c k q)
    (GaussianRationalDirectionNormalizer.factor c (GaussianRationalDirectionClock.height k q))
    (GaussianRationalDirectionNormalizer.S c (GaussianRationalDirectionClock.height k q)) p q
    (GaussianRationalDirectionNormalizer.factor_positive _ _ (GaussianRationalDirectionClock.height_positive k q))
    (GaussianRationalDirectionNormalizer.S_positive _ _)
    (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ h))) (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h)))
    (GaussianRationalPowerAlgebra.unit_power _ _ (GaussianRationalDirectionConstruction.output_unit c k q))
    (phase_error c k p q h)

/-- The exact radical-free source certificate for the actual constructed
direction, with no phase, local error, degree or normalization oracle. -/
theorem rational_direction (c k p q : PTm n) (h : Γ ⊢[PRAAx] input c k p q) : Γ ⊢[PRAAx]
    certificate c k p q :=
  .andI (GaussianRationalDirectionConstruction.output_canonical c k q)
    (.andI (GaussianRationalPowerAlgebra.unit_bounded _ (GaussianRationalDirectionConstruction.output_unit c k q))
      (.andI (GaussianRationalDirectionConstruction.output_unit c k q)
        (.andI (phase_certificate c k p q h)
          (.andI (GaussianRationalPhaseCertificate.coefficient_positive _ _ _ (input_denominator c k p q h)
            (input_numerator_bound c k p q h)
            (GaussianRationalPowerAlgebra.unit_power _ _ (GaussianRationalDirectionConstruction.output_unit c k q)))
            (GaussianRationalDirectionConstruction.construction_correct c k q
              (Prf.andE₁ h) (Prf.andE₁ (Prf.andE₂ h)) (input_denominator c k p q h))))))

def output (c k p q : PTm n) : PTm n := pairT (direction c k q)
  (pairT (qnormSq c) (pairT (directionCoefficient (value c k q) p q)
    (pairT (directionDot c (value c k q)) (GaussianRationalDirectionConstruction.run c k q))))
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (c k p q : PTm n) : PTm n := PTm.app outputF ![c,k,p,q]

ipra_subst output
ipra_subst run

theorem program_at (c k p q : PTm n) : Γ ⊢[PRAAx] run c k p q ≐ output c k p q := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![c,k,p,q]

theorem returned_direction (c k p q : PTm n) : Γ ⊢[PRAAx] fstT (run c k p q) ≐ direction c k q :=
  (program_at c k p q).fstE

theorem returned_norm (c k p q : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run c k p q)) ≐ qnormSq c :=
  (program_at c k p q).sndE.fstE

theorem returned_coefficient (c k p q : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run c k p q))) ≐ directionCoefficient (value c k q) p q :=
  (program_at c k p q).sndE.sndE.fstE

theorem returned_dot (c k p q : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (run c k p q)))) ≐ directionDot c (value c k q) :=
  (program_at c k p q).sndE.sndE.sndE.fstE

theorem returned_construction (c k p q : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (sndT (run c k p q)))) ≐ GaussianRationalDirectionConstruction.run c k q :=
  (program_at c k p q).sndE.sndE.sndE.sndE

theorem rational_direction_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (input (var 0) (var 1) (var 2) (var 3) ⟶ certificate (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (rational_direction _ _ _ _ Prf.hyp0))

theorem rational_direction_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (program_at _ _ _ _)

def returnedCertificate (c k p q : PTm n) : Fm PTm n :=
  RationalArgmin.rationalLE (fraction zero one) (fstT (sndT (sndT (sndT (run c k p q))))) ⋏
    RationalArgmin.rationalLE
      (RationalArithmetic.multiply (fstT (sndT (run c k p q)))
        (GaussianRationalPhaseCertificate.square (fstT (sndT (sndT (run c k p q))))))
      (GaussianRationalPhaseCertificate.square (fstT (sndT (sndT (sndT (run c k p q))))))

ipra_subst returnedCertificate

theorem returned_source_certificate (c k p q : PTm n) (h : Γ ⊢[PRAAx] input c k p q) : Γ ⊢[PRAAx]
    returnedCertificate c k p q := by
  have phase := phase_certificate c k p q h
  exact .andI (RationalArgmin.rationalLE_congr (.eqRefl _) (returned_dot c k p q).eqSymm (Prf.andE₁ phase))
    (RationalArgmin.rationalLE_congr
      (RationalAlgebra.multiply_congr (returned_norm c k p q).eqSymm
        (RationalAlgebra.multiply_congr (returned_coefficient c k p q).eqSymm (returned_coefficient c k p q).eqSymm))
      (RationalAlgebra.multiply_congr (returned_dot c k p q).eqSymm (returned_dot c k p q).eqSymm) (Prf.andE₂ phase))

theorem returned_rational_direction_certificate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (input (var 0) (var 1) (var 2) (var 3) ⟶ returnedCertificate (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (returned_source_certificate _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianRationalDirection
