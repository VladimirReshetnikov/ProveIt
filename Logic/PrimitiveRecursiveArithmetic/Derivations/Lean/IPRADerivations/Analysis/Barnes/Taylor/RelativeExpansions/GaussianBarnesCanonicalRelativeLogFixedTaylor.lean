/-
Second-order expansion of the original relative Barnes logarithm against
fixed cofinal derivative names. Both named observations are independent
of the step-size bound and the precision used to prove the rate.
-/
import IPRADerivations.Analysis.Barnes.Taylor.RelativeExpansions.GaussianBarnesCanonicalRelativeLogTaylor
import IPRADerivations.Analysis.Barnes.Taylor.RelativeExpansions.GaussianBarnesCanonicalTailQuadraticName

set_option autoImplicit false
set_option maxHeartbeats 550000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalRelativeLogFixedTaylor

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalLogSchedule (initial initial_positive)
open GaussianBarnesCanonicalRelativeLogIncrement (nameF data prefixF prefixData tailF tailData)
open GaussianBarnesCanonicalRelativeLogTaylor (source prefixQuadratic cubicScale prefix_rate tail_admission)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNameArithmetic (addF addData add_fast)
open GaussianNamedDifferenceRate (rate_parameters_congr)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalHorner (positive_product)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "E" => GaussianBarnesCanonicalPrefactorInverse.exponentF
local notation "G" => GaussianBarnesCanonicalHeadRelativeLogTaylor.errorGain
local notation "Q" => GaussianBarnesCanonicalTailQuadraticName.nameF
local notation "qd" => GaussianBarnesCanonicalTailQuadraticName.data

def nameQuadraticF : PR 2 := addF (addF E (addF constantF constantF)) Q
def nameQuadraticData (z h R B : PTm n) : PTm n := addData (prefixQuadratic z h R B) (qd z h R B)

def errorGain (R M : PTm n) : PTm n := cubicScale R*G R (initial R) M+num 16
def errorDenominator (R B : PTm n) : PTm n := cubicScale R*(B*B*B)

@[simp] theorem subst_nameQuadraticData {m : ℕ} (σ : Fin n → PTm m) (z h R B : PTm n) :
    Syn.subst σ (nameQuadraticData z h R B) =
      nameQuadraticData (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ R) (Syn.subst σ B) := by
  simp [nameQuadraticData,prefixQuadratic,GaussianBarnesCanonicalRelativeLogTaylor.headQuadratic]

@[simp] theorem subst_errorGain {m : ℕ} (σ : Fin n → PTm m) (R M : PTm n) :
    Syn.subst σ (errorGain R M) = errorGain (Syn.subst σ R) (Syn.subst σ M) := by
  simp [errorGain,cubicScale]

@[simp] theorem subst_errorDenominator {m : ℕ} (σ : Fin n → PTm m) (R B : PTm n) :
    Syn.subst σ (errorDenominator R B) = errorDenominator (Syn.subst σ R) (Syn.subst σ B) := by
  simp [errorDenominator,cubicScale]

theorem increment_source (z h R B H M : PTm n) (hs : Γ ⊢[PRAAx] source z h R B H M) :
    Γ ⊢[PRAAx] GaussianBarnesCanonicalRelativeLogIncrement.source z h R B := by
  have tail := tail_admission z h R B H M hs
  have head := hs.andE₁
  exact .andI tail.andE₁ (.andI tail.andE₂.andE₁
    (GaussianBarnesCanonicalHeadRelativeLogMargin.source_of_small z h R B H (initial R) M
      head.andE₁ head.andE₂.andE₁ head.andE₂.andE₂.andE₁
      head.andE₂.andE₂.andE₂.andE₁ head.andE₂.andE₂.andE₂.andE₂))

private theorem fixed_tail_input (z h R B H M : PTm n) (hs : Γ ⊢[PRAAx] source z h R B H M) :
    Γ ⊢[PRAAx] GaussianBarnesCanonicalTailQuadraticName.input z h R B H :=
  .andI (tail_admission z h R B H M hs) hs.andE₁.andE₂.andE₁

theorem model_regular (z h R B H M : PTm n) (hs : Γ ⊢[PRAAx] source z h R B H M) :
    Γ ⊢[PRAAx] pointCN nameQuadraticF (nameQuadraticData z h R B) := by
  let q := GaussianBarnesCanonicalHeadRelativeLogTaylor.quadratic z h B (initial R)
  let c := GaussianBarnesCanonicalRelativeExponentTaylor.correctionQuadratic z h B (initial R)
  let a := GaussianBarnesCanonicalRelativeExponentTaylor.prefactorQuadratic z h B
  have head := add_fast constantF constantF q c (constant_regular (Γ := Γ) q) (constant_regular c)
  have hpre : Γ ⊢[PRAAx] pointCN E a := GaussianBarnesCanonicalPrefactorExponentDerivative.regular _ _
  have pref := add_fast E (addF constantF constantF) a (addData q c) hpre head
  exact add_fast (addF E (addF constantF constantF)) Q (prefixQuadratic z h R B) (qd z h R B) pref
    (GaussianBarnesCanonicalTailQuadraticName.regular z h R B H (fixed_tail_input z h R B H M hs))

theorem error_denominator_positive (R B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] le one (errorDenominator R B) :=
  positive_product _ _ (positive_product _ _ (zero_lt_succ two) (initial_positive R))
    (positive_product _ _ (positive_product _ _ hB hB) hB)

private theorem cube (a : PTm n) : Γ ⊢[PRAAx] pw a (succ two) ≐ a*a*a :=
  (pw_succ a two).eqTrans (congrMul (Common.pw_two a) (.eqRefl _))

private theorem tail_rate (z h R B H M : PTm n) (hs : Γ ⊢[PRAAx] source z h R B H M) :
    Γ ⊢[PRAAx] independentRate tailF Q (tailData z h R B) (qd z h R B)
      (num 16*H*H*H) (errorDenominator R B) := by
  have h := GaussianBarnesCanonicalTailQuadraticName.rate z h R B H (fixed_tail_input z h R B H M hs)
  have a : Γ ⊢[PRAAx] GaussianBarnesCanonicalTailQuadraticName.errorNumerator H ≐ num 16*H*H*H :=
    (congrMul (.eqRefl two) (cube (two*H))).eqTrans (by ipra_ring)
  have d : Γ ⊢[PRAAx] GaussianBarnesCanonicalTailQuadraticName.errorDenominator R B ≐ errorDenominator R B := by
    refine (congrMul (congrMul (.eqRefl (num 3 : PTm n)) (cube B)) (.eqRefl (initial R))).eqTrans ?_
    unfold errorDenominator cubicScale
    ipra_ring
  exact rate_parameters_congr tailF Q _ _ _ _ _ _ a d h

/-- The two independent clocks have only their intrinsic observation errors,
in addition to the cubic remainder in the physical displacement. -/
theorem rate (z h R B H M : PTm n) (hs : Γ ⊢[PRAAx] source z h R B H M) :
    Γ ⊢[PRAAx] independentRate nameF nameQuadraticF (data z h R B) (nameQuadraticData z h R B)
      (errorGain R M*H*H*H) (errorDenominator R B) := by
  let A := G R (initial R) M*H*H*H
  let D := B*B*B
  let C := num 16*H*H*H
  let J := errorDenominator R B
  have hB := hs.andE₁.andE₁.andE₁
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ (positive_product _ _ hB hB) hB
  have hJ := error_denominator_positive R B hB
  have r := GaussianNamedAddRate.independent_rate prefixF tailF (addF E (addF constantF constantF)) Q
    (prefixData z h R B) (tailData z h R B) (prefixQuadratic z h R B) (qd z h R B) A D C J
    hD hJ (prefix_rate z h R B H M hs.andE₁) (tail_rate z h R B H M hs)
  exact GaussianNamedRateRadius.weaken nameF nameQuadraticF (data z h R B) (nameQuadraticData z h R B)
    _ _ _ _ (positive_product _ _ hD hJ) hJ
    (le_of_eq_add (d := zero) (by dsimp only [A,D,C,J,errorGain,errorDenominator,
      GaussianNamedRateComposition.leadingNumerator,GaussianNamedRateComposition.leadingDenominator]; ipra_ring)) r

theorem actual_Barnes_relative_logarithm_fixed_second_order_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      independentRate nameF nameQuadraticF (data (var 0) (var 1) (var 2) (var 3))
        (nameQuadraticData (var 0) (var 1) (var 2) (var 3))
        (errorGain (var 2) (var 5)*var 4*var 4*var 4) (errorDenominator (var 2) (var 3))) :=
  closeUniv 6 (.impI (rate _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalRelativeLogFixedTaylor
