/-
The quadratic observation of the original local relative Barnes logarithm.
Both finite exponents are evaluated exactly. The kept Mercator and the
corrected cofinal tail contribute cubic error, with a scheduled dyadic
error for freezing the latter at a finite cutoff.
-/
import IPRADerivations.Analysis.Barnes.Taylor.GaussianBarnesCanonicalHeadRelativeLogTaylor
import IPRADerivations.Analysis.Barnes.Taylor.GaussianBarnesCanonicalRelativeExponentTaylor
import IPRADerivations.Analysis.Barnes.Taylor.GaussianBarnesCanonicalCorrectedMercatorCofinal

set_option autoImplicit false
set_option maxHeartbeats 550000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalRelativeLogTaylor

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalLogSchedule (initial initial_positive)
open GaussianBarnesCanonicalRelativeLogIncrement
  (nameF data prefactorF prefactorData headF headData prefixF prefixData correctionF correctionData tailF tailData)
open GaussianBarnesCanonicalRelativeExponentTaylor (prefactorQuadratic correctionQuadratic)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNameArithmetic (addF addData)
open GaussianNameEquivalence (crossEquivalent cross_refl)
open GaussianNamedDifferenceRate (self_rate rate_parameters_congr)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalHorner (ofGaussian positive_product)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "E" => GaussianBarnesCanonicalPrefactorInverse.exponentF
local notation "T" => GaussianBarnesCanonicalCorrectedMercatorCofinal.approximation
local notation "G" => GaussianBarnesCanonicalHeadRelativeLogTaylor.errorGain
local notation "L" => GaussianBarnesCanonicalHeadRelativeLog.nameF
local notation "C" => constantF

def source (z h R B H M : PTm n) : Fm PTm n :=
  GaussianBarnesCanonicalHeadRelativeLogTaylor.source z h R B H (initial R) M ⋏
    le (num 16*H) (B*initial R)

def headQuadratic (z h B N : PTm n) : PTm n :=
  addData (GaussianBarnesCanonicalHeadRelativeLogTaylor.quadratic z h B N) (correctionQuadratic z h B N)

def prefixQuadratic (z h R B : PTm n) : PTm n :=
  addData (prefactorQuadratic z h B) (headQuadratic z h B (initial R))

def nameQuadraticF : PR 2 := addF (addF E (addF C C)) C
def nameQuadraticData (p z h R B : PTm n) : PTm n :=
  addData (prefixQuadratic z h R B) (T p two z h R B)

def cubicScale (R : PTm n) : PTm n := num 3*initial R
def errorNumerator (p R B H M : PTm n) : PTm n :=
  ((cubicScale R*G R (initial R) M+num 16)*H*H*H)*unit p+cubicScale R*(B*B*B)
def errorDenominator (p R B : PTm n) : PTm n := unit p*(cubicScale R*(B*B*B))

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (z h R B H M : PTm n) :
    (source z h R B H M).subst σ =
      source (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ H) (Syn.subst σ M) := by simp [source]

@[simp] theorem subst_nameQuadraticData {m : ℕ} (σ : Fin n → PTm m) (p z h R B : PTm n) :
    Syn.subst σ (nameQuadraticData p z h R B) =
      nameQuadraticData (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ R) (Syn.subst σ B) := by
  simp [nameQuadraticData,prefixQuadratic,headQuadratic,two]

@[simp] theorem subst_errorNumerator {m : ℕ} (σ : Fin n → PTm m) (p R B H M : PTm n) :
    Syn.subst σ (errorNumerator p R B H M) =
      errorNumerator (Syn.subst σ p) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ H) (Syn.subst σ M) := by
  simp [errorNumerator,cubicScale]

@[simp] theorem subst_errorDenominator {m : ℕ} (σ : Fin n → PTm m) (p R B : PTm n) :
    Syn.subst σ (errorDenominator p R B) =
      errorDenominator (Syn.subst σ p) (Syn.subst σ R) (Syn.subst σ B) := by simp [errorDenominator,cubicScale]

private theorem exact_rate (F H : PR 2) (x y : PTm n)
    (h : Γ ⊢[PRAAx] pointCN H y) (e : Γ ⊢[PRAAx] crossEquivalent F H x y) :
    Γ ⊢[PRAAx] independentRate F H x y zero one :=
  GaussianNamedRateTransport.transport H H F H y y x y zero one (le_refl one) (self_rate H y h)
    e (cross_refl H y h)

theorem prefix_rate (z h R B H M : PTm n)
    (hs : Γ ⊢[PRAAx] GaussianBarnesCanonicalHeadRelativeLogTaylor.source z h R B H (initial R) M) :
    Γ ⊢[PRAAx] independentRate prefixF (addF E (addF C C)) (prefixData z h R B) (prefixQuadratic z h R B)
      (G R (initial R) M*H*H*H) (B*B*B) := by
  let N := initial R
  let x := GaussianBarnesCanonicalHeadRelativeLog.data z h B N
  let v := GaussianBarnesCanonicalHeadRelativeLogTaylor.quadratic z h B N
  let c := correctionData z h B N
  let q := correctionQuadratic z h B N
  let p := prefactorData z h B
  let w := prefactorQuadratic z h B
  let A := G R N M*H*H*H
  let D := B*B*B
  have hB := hs.andE₁.andE₁
  have hD := positive_product _ _ (positive_product _ _ hB hB) hB
  have rat : Γ ⊢[PRAAx] independentRate L C x v A D :=
    GaussianBarnesCanonicalHeadRelativeLogTaylor.rate z h R B H N M hs
  have corr := exact_rate correctionF C c q (constant_regular q)
    (GaussianBarnesCanonicalRelativeExponentTaylor.correction_cross z h B N hB)
  have pre := exact_rate prefactorF E p w (GaussianBarnesCanonicalPrefactorExponentDerivative.regular _ _)
    (GaussianBarnesCanonicalRelativeExponentTaylor.prefactor_cross z h B hB)
  have head := GaussianNamedAddRate.independent_rate L correctionF C C x c v q A D zero one hD (le_refl one) rat corr
  have headRate : Γ ⊢[PRAAx] independentRate headF (addF C C) (headData z h B N) (headQuadratic z h B N) A D :=
    rate_parameters_congr _ _ _ _ _ _ _ _
      (by unfold GaussianNamedRateComposition.leadingNumerator; ipra_ring)
      (by unfold GaussianNamedRateComposition.leadingDenominator; ipra_ring) head
  have sum := GaussianNamedAddRate.independent_rate prefactorF headF E (addF C C)
    p (headData z h B N) w (headQuadratic z h B N) zero one A D (le_refl one) hD pre headRate
  exact rate_parameters_congr _ _ _ _ _ _ _ _
    (by unfold GaussianNamedRateComposition.leadingNumerator A N; ipra_ring)
    (by unfold GaussianNamedRateComposition.leadingDenominator D; ipra_ring) sum

theorem tail_admission (z h R B H M : PTm n) (hs : Γ ⊢[PRAAx] source z h R B H M) :
    Γ ⊢[PRAAx] GaussianBarnesCanonicalCorrectedMercatorCofinal.input two z h R B H := by
  have h := hs.andE₁.andE₁
  exact .andI (.andI h.andE₁ h.andE₂.andE₁)
    (.andI (.andI h.andE₁ h.andE₂.andE₂.andE₁) (.andI h.andE₂.andE₂.andE₂ (.andI hs.andE₂ (le_refl two))))

private theorem cube (a : PTm n) : Γ ⊢[PRAAx] pw a (ConciseIPRA.PTm.succ two) ≐ a*a*a :=
  (pw_succ a two).eqTrans (congrMul (Common.pw_two a) (.eqRefl _))

private theorem tail_rate (p z h R B H M : PTm n) (hs : Γ ⊢[PRAAx] source z h R B H M) :
    Γ ⊢[PRAAx] independentRate tailF C (tailData z h R B) (T p two z h R B)
      ((num 16*H*H*H)*unit p+cubicScale R*(B*B*B)) (errorDenominator p R B) := by
  have h := GaussianBarnesCanonicalCorrectedMercatorCofinal.scheduled_rate p two z h R B H (tail_admission z h R B H M hs)
  have d : Γ ⊢[PRAAx] GaussianBarnesCanonicalCorrectedMercatorCofinal.analyticDenominator two R B ≐
      cubicScale R*(B*B*B) := by
    refine (congrMul (congrMul (.eqRefl (num 3 : PTm n)) (cube B)) (.eqRefl (initial R))).eqTrans ?_
    unfold cubicScale
    ipra_ring
  have a : Γ ⊢[PRAAx] GaussianBarnesCanonicalCorrectedMercator.numerator two H ≐ num 16*H*H*H := by
    refine (congrMul (.eqRefl two) (cube (two*H))).eqTrans ?_
    ipra_ring
  have en : Γ ⊢[PRAAx] GaussianBarnesCanonicalCorrectedMercatorCofinal.scheduledNumerator p two R B H ≐
      (num 16*H*H*H)*unit p+cubicScale R*(B*B*B) := by
    refine (congrAdd (congrMul (.eqRefl one) d) (congrMul a (.eqRefl (unit p)))).eqTrans ?_
    ipra_ring
  exact rate_parameters_congr tailF C _ _ _ _ _ _ en (congrMul (.eqRefl _) d) h

theorem rate (p z h R B H M : PTm n) (hs : Γ ⊢[PRAAx] source z h R B H M) :
    Γ ⊢[PRAAx] independentRate nameF nameQuadraticF (data z h R B) (nameQuadraticData p z h R B)
      (errorNumerator p R B H M) (errorDenominator p R B) := by
  let A := G R (initial R) M*H*H*H
  let D := B*B*B
  let C0 := (num 16*H*H*H)*unit p+cubicScale R*D
  let E0 := errorDenominator p R B
  let f := nameF
  let g := nameQuadraticF
  let x := data z h R B
  let y := nameQuadraticData p z h R B
  have hB := hs.andE₁.andE₁.andE₁
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ (positive_product _ _ hB hB) hB
  have hE : Γ ⊢[PRAAx] le one E0 :=
    positive_product _ _ (unit_positive _) (positive_product _ _
      (positive_product _ _ (by exact zero_lt_succ two) (initial_positive R)) hD)
  have r := GaussianNamedAddRate.independent_rate prefixF tailF (addF E (addF C C)) C
    (prefixData z h R B) (tailData z h R B) (prefixQuadratic z h R B) (T p two z h R B) A D C0 E0
    hD hE (prefix_rate z h R B H M hs.andE₁) (tail_rate p z h R B H M hs)
  exact GaussianNamedRateRadius.weaken f g x y _ _ _ _ (positive_product _ _ hD hE) hE
    (le_of_eq_add (d := zero) (by dsimp only [A,D,C0,E0,errorNumerator,errorDenominator,
      GaussianNamedRateComposition.leadingNumerator,GaussianNamedRateComposition.leadingDenominator]; ipra_ring)) r

theorem actual_Barnes_relative_logarithm_second_order_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      independentRate nameF nameQuadraticF (data (var 1) (var 2) (var 3) (var 4))
        (nameQuadraticData (var 0) (var 1) (var 2) (var 3) (var 4))
        (errorNumerator (var 0) (var 3) (var 4) (var 5) (var 6)) (errorDenominator (var 0) (var 3) (var 4))) :=
  closeUniv 7 (.impI (rate _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalRelativeLogTaylor
