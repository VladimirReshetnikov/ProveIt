import IPRADerivations.Analysis.Barnes.Taylor.RelativeExpansions.GaussianBarnesCanonicalCorrectedMercatorInterval
import IPRADerivations.Analysis.Barnes.Logarithms.GaussianBarnesCanonicalLogCofinalRate
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateComposition
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateRadius

/-!
# Rational Taylor polynomials for the original cofinal Barnes logarithm

A fixed finite interval approximates each actual cofinal endpoint.
The interval's Taylor estimate is uniform in the number of rows.
A separate cutoff precision pays the two omitted tails, independently
of the clocks observing the original name and the rational polynomial.
-/

set_option autoImplicit false
set_option maxHeartbeats 750000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalCorrectedMercatorCofinal

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (add)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogCofinalRate (initial_source finite_tail_rate)
open GaussianBarnesCanonicalLogSchedule (initial initial_positive)
open GaussianBarnesCanonicalLogTail (tailDenominator tail_denominator_positive)
open GaussianBarnesCanonicalCorrectedMercator (numerator scaleDenominator scale_denominator_positive)
open GaussianBarnesCanonicalCorrectedMercatorInterval (value errorDenominator error_denominator_positive)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalHorner (positive_product)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "G" => GaussianBarnesCanonicalLogCofinal.nameF
local notation "gd" => GaussianBarnesCanonicalLogCofinal.data
local notation "F" => GaussianBarnesCanonicalFiniteLog.nameF
local notation "fd" => GaussianBarnesCanonicalFiniteLog.data
local notation "Diff" => GaussianNamedDifference.nameF
local notation "dd" => GaussianNamedDifference.data
local notation "finiteIncrement" => GaussianBarnesCanonicalDerivativeInterval.incrementF
local notation "finiteData" => GaussianBarnesCanonicalDerivativeInterval.incrementData
local notation "Bound" => GaussianBarnesCanonicalLogRow.boundNumerator

abbrev nameF : PR 2 := Diff G G

def data (z h R B : PTm n) : PTm n := dd (gd (add z h) R B) (gd z R B)

def input (m z h R B H : PTm n) : Fm PTm n :=
  source z R B ⋏ (source (add z h) R B ⋏ (ComplexLogarithmRemainder.bounded h H ⋏
    (le (num 16*H) (B*initial R) ⋏ le two m)))

def freezeNumerator (R : PTm n) : PTm n := Bound R+Bound R
def freezeDenominator (R r : PTm n) : PTm n := tailDenominator (initial R+r)
def analyticDenominator (m R B : PTm n) : PTm n := scaleDenominator m B*initial R

def rateNumerator (m R B H r : PTm n) : PTm n :=
  GaussianNamedRateComposition.leadingNumerator (freezeNumerator R) (freezeDenominator R r)
    (numerator m H*r) (errorDenominator m B (initial R) r)

def rateDenominator (m R B r : PTm n) : PTm n := freezeDenominator R r*errorDenominator m B (initial R) r

def cutoff (p R : PTm n) : PTm n := freezeNumerator R*unit p

def approximation (p m z h R B : PTm n) : PTm n := value m z h B (initial R) (cutoff p R)

def approximationF : PR 6 := PTm.toPR (approximation (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))

def scheduledNumerator (p m R B H : PTm n) : PTm n :=
  GaussianNamedRateComposition.leadingNumerator one (unit p) (numerator m H) (analyticDenominator m R B)

def scheduledDenominator (p m R B : PTm n) : PTm n := unit p*analyticDenominator m R B

@[simp] theorem subst_data {l : ℕ} (σ : Fin n → PTm l) (z h R B : PTm n) :
    Syn.subst σ (data z h R B) = data (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ R) (Syn.subst σ B) :=
  by simp [data]

@[simp] theorem subst_input {l : ℕ} (σ : Fin n → PTm l) (m z h R B H : PTm n) :
    (input m z h R B H).subst σ = input (Syn.subst σ m) (Syn.subst σ z) (Syn.subst σ h)
      (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ H) := by simp [input,two]

@[simp] theorem subst_approximation {l : ℕ} (σ : Fin n → PTm l) (p m z h R B : PTm n) :
    Syn.subst σ (approximation p m z h R B) = approximation (Syn.subst σ p) (Syn.subst σ m)
      (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ R) (Syn.subst σ B) :=
  by simp [approximation,cutoff,freezeNumerator]

theorem approximation_at (p m z h R B : PTm n) :
    Γ ⊢[PRAAx] PTm.app approximationF ![p,m,z,h,R,B] ≐ approximation p m z h R B := by
  simpa [approximationF] using
    toPR_eq (Γ := Γ) (approximation (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) ![p,m,z,h,R,B]

theorem interval_input (m z h R B H : PTm n) (hs : Γ ⊢[PRAAx] input m z h R B H) :
    Γ ⊢[PRAAx] GaussianBarnesCanonicalCorrectedMercatorInterval.input m z h R B (initial R) H :=
  .andI (initial_source z R B hs.andE₁)
    (.andI (initial_source (add z h) R B hs.andE₂.andE₁) hs.andE₂.andE₂)

theorem regular (z h R B : PTm n) (hz : Γ ⊢[PRAAx] source z R B) (hw : Γ ⊢[PRAAx] source (add z h) R B) :
    Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN nameF (data z h R B) :=
  GaussianNamedDifference.name_regular G G _ _
    (GaussianBarnesCanonicalLogCofinal.regular (add z h) R B hw)
    (GaussianBarnesCanonicalLogCofinal.regular z R B hz)

theorem freeze_denominator_positive (R r : PTm n) : Γ ⊢[PRAAx] le one (freezeDenominator R r) :=
  tail_denominator_positive _ (le_trans (initial_positive R) (le_add_right _ _))

theorem freeze_rate (z h R B r : PTm n) (hz : Γ ⊢[PRAAx] source z R B) (hw : Γ ⊢[PRAAx] source (add z h) R B) :
    Γ ⊢[PRAAx] independentRate nameF finiteIncrement (data z h R B) (finiteData z h R B (initial R) r)
      (freezeNumerator R) (freezeDenominator R r) := by
  let w := add z h
  let N := initial R
  let E := freezeDenominator R r
  let A := Bound R
  let x := gd w R B
  let y := gd z R B
  let u := fd w R B N r
  let v := fd z R B N r
  have hE := freeze_denominator_positive (Γ := Γ) R r
  have nearW := GaussianNamedRateComposition.symmetric F G u x A E hE (finite_tail_rate w R B r hw)
  have nearZ := GaussianNamedRateComposition.symmetric F G v y A E hE (finite_tail_rate z R B r hz)
  have regularW := GaussianBarnesCanonicalLogCofinal.regular w R B hw
  have regularZ := GaussianBarnesCanonicalLogCofinal.regular z R B hz
  have finiteW := GaussianBarnesCanonicalFiniteLog.regular w R B N r (initial_source w R B hw)
  have finiteZ := GaussianBarnesCanonicalFiniteLog.regular z R B N r (initial_source z R B hz)
  have raw := GaussianNamedDifferenceRate.original_rate G G F F x y u v A E A E
    (.andI (.andI hE hE) (.andI (.andI regularW regularZ) (.andI (.andI finiteW finiteZ) (.andI nearW nearZ))))
  have fit : Γ ⊢[PRAAx] le (GaussianNamedDifferenceRate.leadingNumerator A E A E*E)
      (freezeNumerator R*GaussianNamedDifferenceRate.leadingDenominator E E) :=
    le_of_eq_add (d := zero) (by
      dsimp only [GaussianNamedDifferenceRate.leadingNumerator,GaussianNamedDifferenceRate.leadingDenominator,freezeNumerator,A]
      ipra_ring)
  exact GaussianNamedRateRadius.weaken nameF finiteIncrement (data z h R B) (finiteData z h R B N r)
    _ _ _ _ (positive_product _ _ hE hE) hE fit raw

theorem rate (m z h R B H r : PTm n) (hs : Γ ⊢[PRAAx] input m z h R B H) :
    Γ ⊢[PRAAx] independentRate nameF constantF (data z h R B) (value m z h B (initial R) r)
      (rateNumerator m R B H r) (rateDenominator m R B r) :=
  GaussianNamedRateComposition.compose nameF finiteIncrement constantF (data z h R B) (finiteData z h R B (initial R) r)
    (value m z h B (initial R) r) (freezeNumerator R) (freezeDenominator R r) (numerator m H*r)
    (errorDenominator m B (initial R) r) (freeze_denominator_positive R r)
    (error_denominator_positive m B (initial R) r hs.andE₁.andE₁ (initial_positive R))
    (freeze_rate z h R B r hs.andE₁ hs.andE₂.andE₁)
    (GaussianBarnesCanonicalCorrectedMercatorInterval.rate m z h R B (initial R) H r (interval_input m z h R B H hs))

theorem analytic_denominator_positive (m R B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] le one (analyticDenominator m R B) :=
  positive_product _ _ (scale_denominator_positive m B hB) (initial_positive R)

theorem interval_uniform_rate (m z h R B H r : PTm n) (hs : Γ ⊢[PRAAx] input m z h R B H) :
    Γ ⊢[PRAAx] independentRate finiteIncrement constantF (finiteData z h R B (initial R) r)
      (value m z h B (initial R) r) (numerator m H) (analyticDenominator m R B) :=
  GaussianNamedRateRadius.weaken finiteIncrement constantF (finiteData z h R B (initial R) r)
    (value m z h B (initial R) r) (numerator m H*r) (errorDenominator m B (initial R) r)
    (numerator m H) (analyticDenominator m R B)
    (error_denominator_positive m B (initial R) r hs.andE₁.andE₁ (initial_positive R))
    (analytic_denominator_positive m R B hs.andE₁.andE₁)
    (le_of_eq_add (d := numerator m H*analyticDenominator m R B*initial R) (by
      unfold errorDenominator GaussianReciprocalSquareInterval.denominator analyticDenominator; ipra_ring))
    (GaussianBarnesCanonicalCorrectedMercatorInterval.rate m z h R B (initial R) H r (interval_input m z h R B H hs))

theorem rate_of_cutoff (p m z h R B H r : PTm n) (hs : Γ ⊢[PRAAx] input m z h R B H)
    (hr : Γ ⊢[PRAAx] le (cutoff p R) (freezeDenominator R r)) :
    Γ ⊢[PRAAx] independentRate nameF constantF (data z h R B) (value m z h B (initial R) r)
      (scheduledNumerator p m R B H) (scheduledDenominator p m R B) := by
  have freeze := GaussianNamedRateRadius.weaken nameF finiteIncrement (data z h R B) (finiteData z h R B (initial R) r)
    (freezeNumerator R) (freezeDenominator R r) one (unit p) (freeze_denominator_positive R r) (unit_positive p)
    (le_congr (.eqRefl _) (one_mul _).eqSymm hr) (freeze_rate z h R B r hs.andE₁ hs.andE₂.andE₁)
  exact GaussianNamedRateComposition.compose _ _ _ _ _ _ _ _ _ _ (unit_positive p)
    (analytic_denominator_positive m R B hs.andE₁.andE₁) freeze (interval_uniform_rate m z h R B H r hs)

theorem cutoff_budget (p R : PTm n) : Γ ⊢[PRAAx] le (cutoff p R) (freezeDenominator R (cutoff p R)) :=
  le_of_eq_add (d := num 3*initial R+two*cutoff p R) (by unfold freezeDenominator tailDenominator; ipra_ring)

theorem scheduled_rate (p m z h R B H : PTm n) (hs : Γ ⊢[PRAAx] input m z h R B H) :
    Γ ⊢[PRAAx] independentRate nameF constantF (data z h R B) (approximation p m z h R B)
      (scheduledNumerator p m R B H) (scheduledDenominator p m R B) :=
  rate_of_cutoff p m z h R B H (cutoff p R) hs (cutoff_budget p R)

theorem actual_Barnes_cofinal_corrected_Mercator_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (let p := var 0
     let m := var 1
     let z := var 2
     let h := var 3
     let R := var 4
     let B := var 5
     let H := var 6
     let r := var 7
     (input m z h R B H ⋏ le (cutoff p R) (freezeDenominator R r)) ⟶
       independentRate nameF constantF (data z h R B) (value m z h B (initial R) r)
         (scheduledNumerator p m R B H) (scheduledDenominator p m R B)) :=
  closeUniv 8 (.impI (rate_of_cutoff _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem actual_Barnes_cofinal_corrected_Mercator_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (let p := var 0
     let m := var 1
     let z := var 2
     let h := var 3
     let R := var 4
     let B := var 5
     let H := var 6
     input m z h R B H ⟶
       independentRate nameF constantF (data z h R B) (PTm.app approximationF ![p,m,z,h,R,B])
         (scheduledNumerator p m R B H) (scheduledDenominator p m R B)) := by
  refine closeUniv 7 (.impI ?_)
  let Δ : List (Fm PTm 7) := [input (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)]
  have moved := Prf.eqSubst1 (Γ := Δ) (independentRate nameF constantF
      (Syn.shift (data (var 2) (var 3) (var 4) (var 5) : PTm 7)) (var 0)
      (Syn.shift (scheduledNumerator (var 0) (var 1) (var 4) (var 5) (var 6) : PTm 7))
      (Syn.shift (scheduledDenominator (var 0) (var 1) (var 4) (var 5) : PTm 7)))
    (approximation_at (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)).eqSymm
    (by simpa using scheduled_rate (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) Prf.hyp0)
  simpa [Δ] using moved

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalCorrectedMercatorCofinal
