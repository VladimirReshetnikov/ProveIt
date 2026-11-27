import IPRADerivations.Analysis.Barnes.Taylor.Grids.Finite.GaussianBarnesCanonicalFiniteTaylorGridIncrementRate
import IPRADerivations.Analysis.Barnes.Taylor.Grids.Differentiation.CofinalIdentities.GaussianBarnesCanonicalTaylorNamedQuotient

/-!
# Named fixed-cutoff Barnes factorial quotient

The evaluator uses the original neighboring fixed factorial names
at the same literal cutoff. The normalized grid estimate applies
after reading those names at one late endpoint clock.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteTaylorNamedQuotient

open_ipra
open ComplexLogarithmRemainder (add bounded_mono normSq)
open GaussianBarnesCanonicalFiniteTaylorGridIncrementRate (observationClock numerator)
open GaussianBarnesCanonicalFiniteTaylorMixedGridPolynomial (mixedGrid)
open GaussianBarnesCanonicalTaylorNamedQuotient (endpointClock rate_of_grid_bound)
open GaussianBarnesCanonicalFiniteTaylorEvenGridLimit (quadraticClock)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalWeightedTaylorBallSource (stepDivisor)
open GaussianCoefficientNameBounds (unit)
open GaussianEuclideanDistanceName (pointCN)
open GaussianL1 (norm1)
open GaussianNamedDifferenceQuotient (input)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalNaturalScale (natScale)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "F" => GaussianBarnesCanonicalFixedTaylorDerivativeName.nameF
local notation "fd" => GaussianBarnesCanonicalFixedTaylorDerivativeName.data

abbrev nameF : PR 2 := GaussianNamedDifferenceQuotient.nameF F F

def data (z h R B r J e : PTm n) : PTm n :=
  GaussianNamedDifferenceQuotient.data F F (fd (add z h) (R+one) B r J e) (fd z (R+one) B r J e) h B

def leadingNumerator (R M e h : PTm n) : PTm n := numerator R M e h+norm1 h

private theorem widen (z R B : PTm n) (hz : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx] source z (R+one) B :=
  .andI hz.andE₁ (bounded_mono hz.andE₂ (le_of_eq_add (d := B) (by ipra_ring)))

private theorem quotient_input (z h R B r J e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hw : Γ ⊢[PRAAx] source (add z h) R B) (hn : Γ ⊢[PRAAx] le one (normSq h))
    (hJ : Γ ⊢[PRAAx] le e (previous J)) : Γ ⊢[PRAAx]
    input F F (fd (add z h) (R+one) B r J e) (fd z (R+one) B r J e) h B :=
  .andI (GaussianBarnesCanonicalFixedTaylorDerivativeName.regular _ _ _ _ _ _ (widen _ _ _ hw) hJ)
    (.andI (GaussianBarnesCanonicalFixedTaylorDerivativeName.regular _ _ _ _ _ _ (widen _ _ _ hz) hJ)
      (.andI hz.andE₁ hn))

theorem regular (z h R B r J e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hw : Γ ⊢[PRAAx] source (add z h) R B) (hn : Γ ⊢[PRAAx] le one (normSq h))
    (hJ : Γ ⊢[PRAAx] le e (previous J)) : Γ ⊢[PRAAx] pointCN nameF (data z h R B r J e) :=
  GaussianNamedDifferenceQuotient.name_regular _ _ _ _ _ _ (quotient_input z h R B r J e hz hw hn hJ)

theorem rate (p z h R B r M J e t : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hw : Γ ⊢[PRAAx] source (add z h) R B) (hn : Γ ⊢[PRAAx] le one (normSq h))
    (hsmall : Γ ⊢[PRAAx] le ((e*stepDivisor R)*norm1 h) B)
    (hdeg : Γ ⊢[PRAAx] previous M ≐ succ e) (hJ : Γ ⊢[PRAAx] le e (previous J))
    (ht : Γ ⊢[PRAAx] le (observationClock z h R B r M e) t) : Γ ⊢[PRAAx]
    distanceBounded (natScale two (ap2 nameF p (data z h R B r J e))) (mixedGrid t z h R B r e)
      (leadingNumerator R M e h*unit p+two*B) (B*unit p) := by
  let k := endpointClock B
  let x := fd (add z h) (R+one) B r J e
  let y := fd z (R+one) B r J e
  have forward : Γ ⊢[PRAAx] le (quadraticClock B) k := le_add_right _ _
  exact rate_of_grid_bound F F p x y h B (mixedGrid t z h R B r e) (numerator R M e h)
    (quotient_input z h R B r J e hz hw hn hJ)
    (GaussianBarnesCanonicalFiniteTaylorGridIncrementRate.rate z h R B r M J e t k k
      hz hw hn hsmall hdeg hJ ht forward forward)

theorem actual_Barnes_finite_named_factorial_quotient_grid_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (let z := var 0
     let h := var 1
     let R := var 2
     let B := var 3
     let r := var 4
     let M := var 5
     let J := var 6
     let e := var 7
     let t := var 8
     let p := var 9
     (source z R B ⋏ source (add z h) R B ⋏ le one (normSq h) ⋏ le ((e*stepDivisor R)*norm1 h) B) ⟶
       (previous M ≐ succ e ⋏ le e (previous J)) ⟶ le (observationClock z h R B r M e) t ⟶
       (pointCN nameF (data z h R B r J e) ⋏
         distanceBounded (natScale two (ap2 nameF p (data z h R B r J e))) (mixedGrid t z h R B r e)
           (leadingNumerator R M e h*unit p+two*B) (B*unit p))) :=
  closeUniv 10 (.impI (.impI (.impI (.andI
    (regular _ _ _ _ _ _ _ Prf.hyp1.wk.andE₁ Prf.hyp1.wk.andE₂.andE₁ Prf.hyp1.wk.andE₂.andE₂.andE₁ Prf.hyp1.andE₂)
    (rate _ _ _ _ _ _ _ _ _ _ Prf.hyp1.wk.andE₁ Prf.hyp1.wk.andE₂.andE₁ Prf.hyp1.wk.andE₂.andE₂.andE₁
      Prf.hyp1.wk.andE₂.andE₂.andE₂ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteTaylorNamedQuotient
