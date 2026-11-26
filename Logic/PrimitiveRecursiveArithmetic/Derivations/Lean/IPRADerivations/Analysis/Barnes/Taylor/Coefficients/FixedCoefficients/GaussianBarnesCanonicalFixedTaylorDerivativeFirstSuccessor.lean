import IPRADerivations.Analysis.Barnes.Taylor.Grids.Differentiation.GaussianBarnesCanonicalFiniteTaylorFirstDerivative

/-!
# The first transition of the fixed Barnes factorial names

The actual degree-zero name agrees with the literal finite product at
both endpoints. Thus its original named quotient has the same rate to
degree one at the shared finite cutoff.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFixedTaylorDerivativeFirstSuccessor

open_ipra
open ComplexLogarithmRemainder (add normSq)
open GaussianBarnesCanonicalFiniteTaylorFirstDerivative (gain literalQuotientData wide_sources)
open GaussianBarnesCanonicalFixedTaylorDerivativeZero (value_cross)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogSchedule (initial)
open GaussianBarnesCanonicalWeightedTaylorBallSource (stepDivisor)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianFastValueCut (exponent query_budget)
open GaussianL1 (norm1)
open GaussianNameEquivalence (crossEquivalent cross_refl)
open GaussianNamedInverseRate (independentRate)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "V" => GaussianBarnesCanonicalValue.prefixF
local notation "vd" => GaussianBarnesCanonicalProduct.literalData
local notation "F" => GaussianBarnesCanonicalFixedTaylorDerivativeName.nameF
local notation "fd" => GaussianBarnesCanonicalFixedTaylorDerivativeName.data
local notation "QF" => GaussianNamedDifferenceQuotient.nameF
local notation "qd" => GaussianNamedDifferenceQuotient.data

abbrev nameF : PR 2 := QF F F

def quotientData (z h R B r J : PTm n) : PTm n :=
  qd F F (fd (add z h) (R+one) B r J zero) (fd z (R+one) B r J zero) h B

def stepClock (p R : PTm n) : PTm n := exponent (two*stepDivisor R+gain R) p

theorem quotient_cross (z h R B r J : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hs : Γ ⊢[PRAAx] le ((two*stepDivisor R)*norm1 h) B) :
    Γ ⊢[PRAAx] crossEquivalent (QF F F) (QF V V) (quotientData z h R B r J) (literalQuotientData z h R B r) := by
  let S := R+one
  let w := add z h
  let N := initial S+r
  have dom := wide_sources z h R B hz hs
  exact GaussianNamedDifferenceQuotientProperness.proper F V F V (fd w S B r J zero) (vd w S B N)
    (fd z S B r J zero) (vd z S B N) h B
    (GaussianBarnesCanonicalFixedTaylorDerivativeName.regular w S B r J zero dom.andE₂ (zero_le _))
    (GaussianBarnesCanonicalProduct.literal_regular w S B N dom.andE₂)
    (GaussianBarnesCanonicalFixedTaylorDerivativeName.regular z S B r J zero dom.andE₁ (zero_le _))
    (GaussianBarnesCanonicalProduct.literal_regular z S B N dom.andE₁)
    (value_cross w S B r J dom.andE₂) (value_cross z S B r J dom.andE₁)

theorem rate (z h R B r J : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hn : Γ ⊢[PRAAx] le one (normSq h)) (hs : Γ ⊢[PRAAx] le ((two*stepDivisor R)*norm1 h) B) :
    Γ ⊢[PRAAx] independentRate (QF F F) F (quotientData z h R B r J) (fd z (R+one) B r J one) (gain R*norm1 h) B := by
  have regular := GaussianBarnesCanonicalFixedTaylorDerivativeName.regular z (R+one) B r J one
    (wide_sources z h R B hz hs).andE₁ (zero_lt_succ (succ J))
  exact GaussianNamedRateTransport.transport _ _ _ _ _ _ _ _ _ _ hz.andE₁
    (GaussianBarnesCanonicalFiniteTaylorFirstDerivative.rate z h R B r J hz hn hs)
    (quotient_cross z h R B r J hz hs) (cross_refl _ _ regular)

theorem dyadic_rate (p z h R B r J : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hn : Γ ⊢[PRAAx] le one (normSq h)) (hs : Γ ⊢[PRAAx] le (norm1 h*unit (stepClock p R)) B) :
    Γ ⊢[PRAAx] independentRate nameF F (quotientData z h R B r J) (fd z (R+one) B r J one) one (unit p) := by
  let A := two*stepDivisor R
  let G := gain R
  let H := norm1 h
  let P := unit p
  let T := unit (stepClock p R)
  have fit : Γ ⊢[PRAAx] le ((A+G)*P) T := query_budget _ _
  have admission : Γ ⊢[PRAAx] le A T :=
    le_trans (le_add_right A G) (le_trans
      (le_congr (one_mul (A+G)) (mul_comm _ _) (mul_le_mul_right (A+G) (unit_positive p))) fit)
  have guard : Γ ⊢[PRAAx] le (A*H) B :=
    le_trans (le_congr (.eqRefl _) (mul_comm _ _) (mul_le_mul_right H admission)) hs
  have pay : Γ ⊢[PRAAx] le (G*P) T := le_trans (mul_le_mul_right P (le_add_left G A)) fit
  have error : Γ ⊢[PRAAx] le ((G*H)*P) (one*B) :=
    le_congr (by ipra_ring) (one_mul B).eqSymm (le_trans (mul_le_mul_right H pay)
      (le_congr (mul_comm H T) (.eqRefl _) hs))
  exact GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ hz.andE₁ (unit_positive p) error
    (rate z h R B r J hz hn guard)

theorem actual_Barnes_fixed_factorial_first_successor_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (let z := var 0
       let h := var 1
       let R := var 2
       let B := var 3
       let r := var 4
       let J := var 5
       (source z R B ⋏ le one (normSq h) ⋏ le ((two*stepDivisor R)*norm1 h) B) ⟶
         independentRate (QF F F) F (quotientData z h R B r J) (fd z (R+one) B r J one) (gain R*norm1 h) B) :=
  closeUniv 6 (.impI (rate _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFixedTaylorDerivativeFirstSuccessor
