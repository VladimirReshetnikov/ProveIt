import IPRADerivations.Analysis.Gamma.GaussianGammaInputContinuity
import IPRADerivations.Analysis.Gamma.GaussianGammaEncodingRescaling
import IPRADerivations.Analysis.Gamma.GaussianGammaPoleLimitModulus
import IPRADerivations.Analysis.Gamma.GaussianGammaPoleDifferenceQuotient

/-!
# The original C23 difference quotient and C25 residue limits

A computed input precision and a computed observation precision work
for every encoded rational complex increment. The endpoints observe
the actual divided reciprocal Gamma and the actual cleared Gamma
with its computed puncture certificate.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaPoleLimits

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianGammaPoleLimitModulus (clock half_clock pole_observations_at_clock)
open GaussianGammaInputContinuity (modulus original_C7_independent_rate)
open GaussianGammaLocalPoleGuards (terminal terminal_Gamma_domain)
open GaussianGammaTerminalContinuity (encodedOne terminal_input_distance uniform_terminal_domain)
open GaussianGammaPoleLimitTransport (terminalRate)
open GaussianGammaPoleInverseContinuity (halfDisk)
open GaussianGammaPoleReciprocalFactor (quotientF quotientData)
open GaussianGammaPoleDifferenceQuotient (divisionF divisionData original_C23_literal_difference_quotient)
open GaussianGammaLocalPoleFormula
  (resultF regularData regularMultiplier clearedData punctureDenominator punctureUpper
    puncture_denominator_positive actual_puncture_certificate original_cleared_local_formula)
open GaussianGammaPoleFiniteFactors (signedFactorial)
open GaussianGammaPoleMultiplier (signedInverseFactorial)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaReciprocalInverse (gammaF gammaData gamma_regular)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_at cross_trans)
open GaussianNameRingLaws (oneF)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianExponentialReference (unit_monotone)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalHorner (positive_product)
open GaussianRationalDistanceOrder (distance_radius_mono distance_triangle_same)
open ComplexLogarithmRemainder (bounded normSq scale normSq_scale oneCode)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def inputClock (j s : PTm n) : PTm n := clock j s+modulus (clock j s) two
def closeIncrement (h B j s : PTm n) : Fm PTm n :=
  bounded (scale (unit (inputClock j s)) h) B

private theorem smaller_scale (h B D E : PTm n) (hd : Γ ⊢[PRAAx] le D E)
    (hE : Γ ⊢[PRAAx] bounded (scale E h) B) : Γ ⊢[PRAAx] bounded (scale D h) B := by
  have smaller : Γ ⊢[PRAAx] le (normSq (scale D h)) (normSq (scale E h)) :=
    le_congr (normSq_scale D h).eqSymm (normSq_scale E h).eqSymm
      (mul_le_mul_right (normSq h) (sq_le_sq hd))
  exact le_trans smaller hE

theorem half_from_clock (h B j s : PTm n) (hnear : Γ ⊢[PRAAx] closeIncrement h B j s) :
    Γ ⊢[PRAAx] halfDisk h B :=
  smaller_scale h B two (unit (inputClock j s))
    (le_trans (half_clock j s) (unit_monotone (le_add_right _ _))) hnear

theorem positive_increment_at_clock (j s : PTm n) :
    Γ ⊢[PRAAx] GaussianGammaPoleDifferenceQuotient.input oneCode (unit (inputClock j s)) ⋏
      closeIncrement oneCode (unit (inputClock j s)) j s := by
  let B := unit (inputClock j s)
  have hb : Γ ⊢[PRAAx] le one B := unit_positive _
  have large : Γ ⊢[PRAAx] le two B :=
    le_trans (half_clock j s) (unit_monotone (le_add_right _ _))
  have nb := ComplexLogarithmRemainder.normSq_one (Γ := Γ)
  have norm : Γ ⊢[PRAAx] normSq (scale B oneCode) ≐ B*B :=
    (normSq_scale _ _).eqTrans ((congrMul (.eqRefl _) nb).eqTrans (by ipra_ring))
  have strict : Γ ⊢[PRAAx] lt (normSq oneCode) (B*B) :=
    le_congr (congrSucc nb).eqSymm (.eqRefl _)
      (le_trans large (le_congr (by ipra_ring) (.eqRefl _) (mul_le_mul_right B hb)))
  exact .andI (.andI hb (.andI (le_congr (.eqRefl _) nb.eqSymm (le_refl one)) strict))
    (le_congr norm.eqSymm (.eqRefl _) (le_refl (B*B)))

theorem terminal_rate_from_clock (h B j s : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hnear : Γ ⊢[PRAAx] closeIncrement h B j s) :
    Γ ⊢[PRAAx] terminalRate h B j one (unit (clock j s)) := by
  let k := clock j s
  let z := terminal h B j
  let w := encodedOne B
  let P := GaussianGammaC7Name.nameF
  let x := GaussianGammaC7Name.data z two B
  let y := GaussianGammaC7Name.data w two B
  have rpos : Γ ⊢[PRAAx] le one two := zero_lt_succ one
  have half := half_from_clock h B j s hnear
  have hz := (uniform_terminal_domain h B j hB half).andE₁
  have hw := GaussianGammaEncodingRescaling.encoded_one_radius_source two B rpos hB
  have smaller := smaller_scale h B (unit (modulus k two)) (unit (inputClock j s))
    (unit_monotone (le_add_left (modulus k two) k)) hnear
  have hd := terminal_input_distance h B j one (unit (modulus k two)) hB (unit_positive _)
    (le_congr (.eqRefl _) (by ipra_ring) smaller)
  have rate := original_C7_independent_rate k z w two B hz hw hd
  have oneEq := GaussianGammaEncodingRescaling.original_encoded_one_at_radius two B rpos hB
  exact GaussianNamedRateTransport.transport P P P oneF x y x zero one (unit k)
    (unit_positive k) rate (cross_refl P x (GaussianGammaC7Name.name_regular z two B hz))
    (cross_symm P oneF y zero oneEq)

theorem regularized_limits (h B j s p : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hnear : Γ ⊢[PRAAx] closeIncrement h B j s) (hp : Γ ⊢[PRAAx] le (clock j s) p) :
    Γ ⊢[PRAAx] distanceBounded (ap2 quotientF p (quotientData h B j)) (signedFactorial j) one (unit s) ⋏
      distanceBounded (ap2 resultF p (regularData h B j two)) (signedInverseFactorial j) one (unit s) := by
  let k := clock j s
  have smaller := smaller_scale h B (unit k) (unit (inputClock j s))
    (unit_monotone (le_add_right _ _)) hnear
  have hk := unit_positive (Γ := Γ) k
  have hi : Γ ⊢[PRAAx] GaussianGammaPoleFactorContinuity.input h B one (unit k) :=
    .andI hB (.andI hk (.andI hk (le_congr (.eqRefl _) (by ipra_ring) smaller)))
  exact pole_observations_at_clock h B j s p hi (half_from_clock h B j s hnear) hp
    (terminal_rate_from_clock h B j s hB hnear)

theorem cleared_certificate_comparison (h B j : PTm n)
    (hp : Γ ⊢[PRAAx] GaussianGammaPoleDifferenceQuotient.input h B)
    (half : Γ ⊢[PRAAx] halfDisk h B) : Γ ⊢[PRAAx]
    crossEquivalent resultF resultF (clearedData h B j (punctureDenominator B)) (regularData h B j two) := by
  let d := punctureDenominator B
  let w := terminal h B j
  let m := regularMultiplier h B j
  let y := gammaData w two B d
  let z := gammaData w two B two
  have hB := hp.andE₁
  have hd := puncture_denominator_positive B hB
  have hm := actual_puncture_certificate h B hB hp.andE₂.andE₁ hp.andE₂.andE₂
  have first := original_cleared_local_formula h B one (punctureUpper B) d j hB (le_refl one) hd hm
  have hy := terminal_Gamma_domain h B one (punctureUpper B) d j hB (le_refl one)
    hd hm.andE₁ hm.andE₂.andE₁
  have hz := uniform_terminal_domain h B j hB half
  have eq := GaussianGammaRadiusOverlap.original_Gamma_overlap w two two B one d one two hy hz
  have reg := constant_regular (Γ := Γ) m
  have product := GaussianGammaAdjacentCutoff.multiply_cross constantF constantF gammaF gammaF m m y z reg reg
    (gamma_regular w two B one d hy) (gamma_regular w two B one two hz) (cross_refl constantF m reg) eq
  exact cross_trans resultF resultF resultF _ _ _ first product

private theorem transport_limit_observation (F G : PR 2) (x y c j s p : PTm n)
    (hp : Γ ⊢[PRAAx] le (clock j (succ s)) p)
    (he : Γ ⊢[PRAAx] crossEquivalent F G x y)
    (h : Γ ⊢[PRAAx] distanceBounded (ap2 G p y) c one (unit (succ s))) :
    Γ ⊢[PRAAx] distanceBounded (ap2 F p x) c one (unit s) := by
  let a := unit (succ s)
  let b := unit p
  have earlier : Γ ⊢[PRAAx] le (succ (succ s)) (clock j (succ s)) :=
    (succ_monus_succ _ _).eqTrans (le_add_right _ _)
  have later := le_trans earlier hp
  have gain : Γ ⊢[PRAAx] le (a*two) b :=
    le_congr (pw_succ two (succ s)) (.eqRefl _) (unit_monotone later)
  have posA : Γ ⊢[PRAAx] le one a := unit_positive _
  have posB : Γ ⊢[PRAAx] le one b := unit_positive _
  have near : Γ ⊢[PRAAx] distanceBounded (ap2 F p x) (ap2 G p y) one a :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ posB posB) posA
      (le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right b gain)) (cross_at F G x y p p he)
  have joined := distance_triangle_same _ _ _ _ _ _ posA near h
  exact distance_radius_mono _ _ _ _ _ _ posA (unit_positive s)
    (le_of_eq_add (d := zero) (by
      have e := natEq (pw_succ (Γ := Γ) two s)
      apply deriveNat
      unfold a unit
      ipra_simps
      rw [e]
      ring)) joined

theorem original_punctured_limits (h B j s p : PTm n)
    (hpole : Γ ⊢[PRAAx] GaussianGammaPoleDifferenceQuotient.input h B)
    (hnear : Γ ⊢[PRAAx] closeIncrement h B j (succ s))
    (hp : Γ ⊢[PRAAx] le (clock j (succ s)) p) :
    Γ ⊢[PRAAx] distanceBounded (ap2 divisionF p (divisionData h B j)) (signedFactorial j) one (unit s) ⋏
      distanceBounded (ap2 resultF p (clearedData h B j (punctureDenominator B))) (signedInverseFactorial j) one (unit s) := by
  have reg := regularized_limits h B j (succ s) p hpole.andE₁ hnear hp
  exact .andI
    (transport_limit_observation divisionF quotientF _ _ _ j s p hp
      (original_C23_literal_difference_quotient h B j hpole) reg.andE₁)
    (transport_limit_observation resultF resultF _ _ _ j s p hp
      (cleared_certificate_comparison h B j hpole (half_from_clock h B j (succ s) hnear)) reg.andE₂)

theorem original_C23_C25_punctured_limits_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (GaussianGammaPoleDifferenceQuotient.input (var 0) (var 1) ⟶ closeIncrement (var 0) (var 1) (var 2) (succ (var 3)) ⟶
      le (clock (var 2) (succ (var 3))) (var 4) ⟶
      (distanceBounded (ap2 divisionF (var 4) (divisionData (var 0) (var 1) (var 2)))
          (signedFactorial (var 2)) one (unit (var 3)) ⋏
        distanceBounded (ap2 resultF (var 4) (clearedData (var 0) (var 1) (var 2) (punctureDenominator (var 1))))
          (signedInverseFactorial (var 2)) one (unit (var 3)))) :=
  closeUniv 5 (.impI (.impI (.impI (original_punctured_limits _ _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

theorem actual_positive_pole_increment_at_clock_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (GaussianGammaPoleDifferenceQuotient.input oneCode (unit (inputClock (var 0) (var 1))) ⋏
      closeIncrement oneCode (unit (inputClock (var 0) (var 1))) (var 0) (var 1)) :=
  closeUniv 2 (positive_increment_at_clock _ _)

end LeanProofs.IPRA.Analysis.GaussianGammaPoleLimits
