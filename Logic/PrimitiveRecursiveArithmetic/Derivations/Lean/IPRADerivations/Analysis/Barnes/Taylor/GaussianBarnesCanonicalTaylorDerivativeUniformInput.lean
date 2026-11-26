import IPRADerivations.Analysis.Barnes.Taylor.Grids.GaussianBarnesCanonicalTaylorDerivativeLocalContinuity
import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.GaussianBarnesCanonicalTaylorDerivativeChart
import IPRADerivations.Analysis.Names.GaussianNamedIncrementChart
import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianRationalFiniteRoots

/-!
# Uniform continuity of every cofinal Barnes factorial name

Use the original Gaussian increment chart for the difference of two
arbitrary rational inputs. Its nonzero step is small enough for the
uniform local derivative bound. The zero step uses chart equality.
Both cases retain the original independent observation clocks.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTaylorDerivativeUniformInput

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (add bounded_mono normSq)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalTaylorDerivativeLocalContinuity (local_rate localCap threshold)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianExponentialReference (recode_fixed unit_monotone)
open GaussianFastValueCut (exponent query_budget)
open GaussianL1 (norm1)
open GaussianNameEquivalence (cross_refl cross_symm)
open GaussianNamedIncrementChart (baseNumerator stepNumerator denominator denominator_positive base_fraction sum_fraction_raw
  base_disk sum_disk_of_raw_sum step_small step_separated)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalHorner (ofGaussian ofGaussian_canonical ofGaussian_represents qadd qzero)
open GaussianRationalL1 (rawGaussian)
open GaussianRationalMetric (bounded bounded_iff distanceBounded qsub qsub_canonical)
open GaussianRationalReciprocal (bound_congr)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "F" => GaussianBarnesCanonicalTaylorProductDerivativeName.nameF
local notation "fd" => GaussianBarnesCanonicalTaylorProductDerivativeName.data

def demand (R e p : PTm n) : PTm n := threshold R e+exponent (localCap R e) p
def inputClock (R e p : PTm n) : PTm n := succ (demand R e p)

@[simp] theorem subst_inputClock {m : ℕ} (σ : Fin n → PTm m) (R e p : PTm n) :
    Syn.subst σ (inputClock R e p) = inputClock (Syn.subst σ R) (Syn.subst σ e) (Syn.subst σ p) := by
  simp [inputClock,demand,threshold,localCap,GaussianBarnesCanonicalTaylorDerivativeLocalContinuity.cap,
    GaussianBarnesCanonicalTaylorAllOrderDerivative.stepClock,GaussianBarnesCanonicalTaylorDerivativeBase.stepClock,
    GaussianBarnesCanonicalTaylorDerivativeBase.stepCost,GaussianBarnesCanonicalTaylorDerivativeBase.gain,
    GaussianBarnesCanonicalTaylorDerivativeSuccessor.stepClock,GaussianBarnesCanonicalTaylorDerivativeSuccessor.stepCost,
    GaussianBarnesCanonicalValueDerivative.stepGain,GaussianBarnesCanonicalValueDerivative.numerator,
    GaussianBarnesCanonicalValueDerivativeJoin.numerator,GaussianBarnesCanonicalValueDerivativeJoin.tailDerivativeBound,
    GaussianBarnesCanonicalValueDerivativeJoin.prefixGain,GaussianBarnesCanonicalDiskBound.prefixBound,
    GaussianBarnesCanonicalUniformContinuity.gain,GaussianBarnesCanonicalPrefactorLipschitz.gain,
    GaussianBarnesCanonicalPrefactorLipschitz.disk,GaussianBarnesCanonicalPrefactorLipschitz.exponentGain,
    GaussianBarnesCanonicalPrefactorLipschitz.linearGain,GaussianBarnesCanonicalPrefactorLipschitz.halfGain,
    GaussianBarnesCanonicalPrefactorLipschitz.quadraticGain,GaussianBarnesCanonicalPrefactor.quadraticCoefficientData,
    GaussianBarnesCanonicalPrefactor.negativeHalf,
    GaussianBarnesCanonicalCentralUniformBound.centralCap,GaussianBarnesCanonicalCentralUniformBound.centralArgumentCap,
    GaussianBarnesCanonicalCentralUniformBound.prefixArgumentCap,GaussianBarnesCanonicalCentralUniformBound.correctionCap,
    GaussianBarnesCanonicalFactor.exponentRadius,
    GaussianBarnesCanonicalFixedTaylorDerivativeUniformConvergence.factorialCap,
    GaussianBarnesCanonicalFixedTaylorDerivativeName.scaleGain,LeanProofs.IPRA.Analysis.Products.fact,one,two]

private theorem widen (z R B : PTm n) (hz : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx] source z (R+one) B :=
  .andI hz.andE₁ (bounded_mono hz.andE₂ (le_of_eq_add (d := B) (by ipra_ring)))

theorem point_bound (z R B : PTm n) (hz : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] bounded (ofGaussian z B) R one :=
  (bounded_iff _ _ _ _ _ hz.andE₁ (le_refl one) (ofGaussian_represents z B hz.andE₁)).iffMpr
    (le_congr (by ipra_ring) (by ipra_ring) hz.andE₂)

private theorem pay (R e p L : PTm n) (hL : Γ ⊢[PRAAx] le L (unit (demand R e p))) :
    Γ ⊢[PRAAx] le (two*L*one) (unit (inputClock R e p)) :=
  le_congr (by ipra_ring) (pw_succ two (demand R e p)).eqSymm (mul_le_mul_right two hL)

private theorem equal_point_rate (z w R B D J e p : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hw : Γ ⊢[PRAAx] source w R D) (he : Γ ⊢[PRAAx] le e (previous J))
    (h : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) : Γ ⊢[PRAAx]
    independentRate F F (fd z (R+one) B J e) (fd w (R+one) D J e) one (unit p) := by
  let x := fd z (R+one) B J e
  let y := fd w (R+one) D J e
  have r := GaussianBarnesCanonicalTaylorProductDerivativeName.regular z (R+one) B J e (widen z R B hz) he
  have cross := GaussianBarnesCanonicalTaylorDerivativeChart.cofinal_cross w z (R+one) D B J e
    (widen w R D hw) (widen z R B hz) he h.eqSymm
  have exact_rate := GaussianNamedRateTransport.transport F F F F x x x y zero one (le_refl one)
    (GaussianNamedDifferenceRate.self_rate F x r) (cross_refl _ _ r) cross
  exact GaussianNamedRateRadius.weaken F F x y zero one one (unit p) (le_refl one) (unit_positive p)
    (le_congr (zero_mul _).eqSymm (one_mul _).eqSymm (zero_le one)) exact_rate

theorem inputClock_monotone (R e p q : PTm n) (hpq : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] le (inputClock R e p) (inputClock R e q) := by
  unfold inputClock demand exponent
  exact Common.succ_le_succ (add_le_add₂ (le_refl _) (add_le_add₂ hpq (le_refl _)))

theorem uniform_input (z w R B D J e p : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B) (hw : Γ ⊢[PRAAx] source w R D)
    (he : Γ ⊢[PRAAx] le e (previous J))
    (hin : Γ ⊢[PRAAx] distanceBounded (ofGaussian z B) (ofGaussian w D) one (unit (inputClock R e p))) : Γ ⊢[PRAAx]
    independentRate F F (fd z (R+one) B J e) (fd w (R+one) D J e) one (unit p) := by
  let q := ofGaussian z B
  let v := ofGaussian w D
  let r := qsub v q
  let N := normSq (rawGaussian r)
  let C := denominator q r
  let x := baseNumerator q r
  let h := stepNumerator q r
  let y := add x h
  let K := unit (inputClock R e p)
  let L := unit (threshold R e)
  let G := localCap R e
  let S := R+one
  let U := unit p
  have den := denominator_positive (Γ := Γ) q r
  have rv : Γ ⊢[PRAAx] qadd q r ≐ v :=
    GaussianRationalLinearProduct.add_sub_right q v (ofGaussian_canonical _ _ hw.andE₁)
  have qx : Γ ⊢[PRAAx] ofGaussian x C ≐ q :=
    (base_fraction q r).eqTrans (recode_fixed q (ofGaussian_canonical _ _ hz.andE₁))
  have vy : Γ ⊢[PRAAx] ofGaussian y C ≐ v := (sum_fraction_raw q r).eqTrans rv
  have hx : Γ ⊢[PRAAx] source x R C := .andI den (base_disk q r R (point_bound z R B hz))
  have hy : Γ ⊢[PRAAx] source y R C := .andI den
    (sum_disk_of_raw_sum q r R (bound_congr rv.eqSymm (.eqRefl _) (.eqRefl _) (point_bound w R D hw)))
  have rb : Γ ⊢[PRAAx] bounded r one K :=
    GaussianRationalDistanceOrder.distance_symmetric _ _ _ _ (unit_positive _) hin
  have fitL : Γ ⊢[PRAAx] le L (unit (demand R e p)) :=
    unit_monotone (le_add_right (threshold R e) (exponent G p))
  have fitG : Γ ⊢[PRAAx] le (G*U) (unit (demand R e p)) :=
    le_trans (query_budget G p) (unit_monotone (le_add_left (exponent G p) (threshold R e)))
  have hs : Γ ⊢[PRAAx] le (norm1 h*L) C :=
    le_congr (mul_comm _ _) (.eqRefl _) (step_small q r one K L (unit_positive _) rb (pay R e p L fitL))
  have ha : Γ ⊢[PRAAx] le ((norm1 h*G)*U) (one*C) :=
    le_congr (by ipra_ring) (one_mul C).eqSymm (step_small q r one K (G*U) (unit_positive _) rb (pay R e p (G*U) fitG))
  have ex := GaussianBarnesCanonicalTaylorDerivativeChart.cofinal_cross z x S B C J e
    (widen z R B hz) (widen x R C hx) he qx.eqSymm
  have ey := GaussianBarnesCanonicalTaylorDerivativeChart.cofinal_cross w y S D C J e
    (widen w R D hw) (widen y R C hy) he vy.eqSymm
  refine .orE (lt_or_le zero N) ?_ ?_
  · have hn := (step_separated (Γ := _ :: Γ) q r Prf.hyp0).andE₂
    have hr := local_rate x h R C J e hx.wk hy.wk hn he.wk hs.wk
    have weaken := GaussianNamedRateRadius.weaken F F _ _ _ C one U den.wk (unit_positive p) ha.wk hr
    have sym := GaussianNamedRateComposition.symmetric F F (fd y S C J e) (fd x S C J e) one U (unit_positive p) weaken
    exact GaussianNamedRateTransport.transport F F F F _ _ _ _ one U (unit_positive p) sym ex.wk ey.wk
  · let Δ := le N zero :: Γ
    have rn : Δ ⊢[PRAAx] N ≐ zero := le_antisymm Prf.hyp0 (zero_le _)
    have eq := GaussianRationalFiniteRoots.canonical_zero_of_norm_zero r (qsub_canonical v q) rn
    have yq := (GaussianRationalValueEquality.recode_eq_iff_difference_zero v q).iffMpr eq
    have same := ((GaussianTranslatedNonconstant.recode_eq v (ofGaussian_canonical _ _ hw.andE₁.wk)).eqSymm.eqTrans
      (yq.eqTrans (GaussianTranslatedNonconstant.recode_eq q (ofGaussian_canonical _ _ hz.andE₁.wk)))).eqSymm
    exact equal_point_rate z w R B D J e p hz.wk hw.wk he.wk same

theorem actual_Barnes_factorial_Taylor_uniform_input_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (let z := var 0
     let w := var 1
     let R := var 2
     let B := var 3
     let D := var 4
     let J := var 5
     let e := var 6
     let p := var 7
     (source z R B ⋏ source w R D) ⟶ le e (previous J) ⟶
       distanceBounded (ofGaussian z B) (ofGaussian w D) one (unit (inputClock R e p)) ⟶
       independentRate F F (fd z (R+one) B J e) (fd w (R+one) D J e) one (unit p)) :=
  closeUniv 8 (.impI (.impI (.impI (uniform_input _ _ _ _ _ _ _ _ Prf.hyp1.wk.andE₁ Prf.hyp1.wk.andE₂ Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTaylorDerivativeUniformInput
