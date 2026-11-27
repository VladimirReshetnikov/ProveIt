import IPRADerivations.Analysis.Barnes.Vigneras.GaussianBarnesVignerasCandidateCalculus
import IPRADerivations.Analysis.Barnes.Vigneras.GaussianBarnesVignerasRefinementChart

/-! Convert each supplied compact-strip derivative query to the original fine-grid
observations and the metric bounds used in the periodic refinement proof. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesVignerasRefinementNode

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesVignerasCandidateCalculus (Candidate row)
open GaussianBarnesVignerasRefinementChart (scheduled precision precision_unit)
open GaussianBarnesVignerasRefinementJet (firstBody secondBody thirdBody radius successor_numerator)
open GaussianBarnesVignerasRefinementWrap (body numerator observationClock)
open GaussianBarnesVignerasIntegerPeriod (input margin bound)
open GaussianBarnesVignerasQuotientJet (firstF secondF thirdF data1 data2 data3)
open GaussianBarnesCanonicalThirdDerivativePositiveMargin (step)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianDiscretePeriodicUniformCertificate (window)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (qzero)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalNaturalScale (natScale)
open GaussianRationalSyntheticDivision (qsub_congr)
open RationalValueBounds (upper upper_mono upper_congr)
open SignedDiscreteDerivativeOperators (width divisor)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "Q" => GaussianNamedDifferenceQuotient.nameF
local notation "qd" => GaussianNamedDifferenceQuotient.data
local notation "Clock" => GaussianBarnesVignerasAdjacentObservation.clock
local notation "F₀" => GaussianBarnesVignerasIntegerPeriod.nameF
local notation "d₀" => GaussianBarnesVignerasIntegerPeriod.data

def derivativeAt (f g : PTm 2) (x k U : PTm n) : Fm PTm n :=
  distanceBounded (natScale (divisor x) (qsub (inst2 f (succ k) x) (inst2 f k x))) (inst2 g k x) one U

def floorAt (j : PTm 2) (x k U : PTm n) : Fm PTm n :=
  upper (fstT qzero) (fstT (inst2 j k x)) one (num 3*U)

private theorem observed (f g : PR 2) (F G : PTm 2) (x k p u v w : PTm n)
    (h : Γ ⊢[PRAAx] scheduled x p)
    (hu : Γ ⊢[PRAAx] pointCN f u) (hv : Γ ⊢[PRAAx] pointCN f v) (hD : Γ ⊢[PRAAx] le one (divisor x))
    (eu : Γ ⊢[PRAAx] ap2 f (observationClock x) u ≐ inst2 F (succ k) x)
    (ev : Γ ⊢[PRAAx] ap2 f (observationClock x) v ≐ inst2 F k x)
    (ew : Γ ⊢[PRAAx] ap2 g (observationClock x) w ≐ inst2 G k x)
    (rate : Γ ⊢[PRAAx] independentRate (Q f f) g
      (qd f f u v (step (numerator x k) (succ (numerator x k))) (divisor x)) w two (unit (precision p))) :
    Γ ⊢[PRAAx] derivativeAt F G x k (unit p) := by
  let D := divisor x
  let A := numerator x k
  let s := Clock D (precision p)
  let r := observationClock x
  have clockEq : Γ ⊢[PRAAx] s ≐ r := h.andE₂.andE₂.eqSymm
  have read := GaussianBarnesVignerasAdjacentObservation.readback f g u v w A D (precision p) hu hv hD rate
  have er := qsub_congr ((congrAp2 f clockEq (.eqRefl u)).eqTrans eu) ((congrAp2 f clockEq (.eqRefl v)).eqTrans ev)
  have ex : Γ ⊢[PRAAx] natScale D (qsub (ap2 f s u) (ap2 f s v)) ≐
      natScale D (qsub (inst2 F (succ k) x) (inst2 F k x)) := by
    ipra_congr (natScale (var 0) (var 1) : PTm 2) with [.eqRefl D,er]
  have ey := (congrAp2 g clockEq (.eqRefl w)).eqTrans ew
  have fit : Γ ⊢[PRAAx] le (num 3*unit p) (one*unit (precision p)) :=
    le_congr (.eqRefl _) ((one_mul _).eqTrans (precision_unit p)).eqSymm
      (le_of_eq_add (d := num 29*unit p) (by ipra_ring))
  exact distance_congr ex ey (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ (unit_positive (precision p)) (unit_positive p) fit read)

theorem at_node (c : Candidate) (x N k p : PTm n) (hN : Γ ⊢[PRAAx] le one N) (hM : Γ ⊢[PRAAx] le one (width x))
    (hD : Γ ⊢[PRAAx] divisor x ≐ N*width x) (h : Γ ⊢[PRAAx] scheduled x p)
    (hk : Γ ⊢[PRAAx] lt k (window x N)) (hr : Γ ⊢[PRAAx] row c (precision p) (numerator x k) (divisor x)) :
    let F := body c.value c.valueData
    let G := firstBody c.first c.firstData
    let H := secondBody c.second c.secondData
    let J := thirdBody c.third c.thirdData
    Γ ⊢[PRAAx] derivativeAt F G x k (unit p) ⋏ (derivativeAt G H x k (unit p) ⋏
      (derivativeAt H J x k (unit p) ⋏ floorAt J x k (unit p))) := by
  let A := numerator x k
  let C := succ A
  let D := divisor x
  let R := radius x
  let r := observationClock x
  let p₀ := precision p
  let t := c.valueData
  let f := c.value
  let g := c.first
  let j := c.second
  let l := c.third
  let t₁ := c.firstData
  let t₂ := c.secondData
  let t₃ := c.thirdData
  let a := inst2 t₁ A D
  let b := inst2 t₁ C D
  let d := inst2 t₂ A D
  let e := inst2 t₂ C D
  let v := inst2 t₃ A D
  let F := body f t
  let G := firstBody g t₁
  let H := secondBody j t₂
  let J := thirdBody l t₃
  have chart := GaussianBarnesVignerasRefinementChart.admitted x N k p hN hM hD h hk
  have hd := chart.andE₁.andE₁.andE₁
  have ha := chart.andE₁.andE₁.andE₂.andE₁
  have hc := chart.andE₁.andE₁.andE₂.andE₂.andE₁
  have da := chart.andE₁.andE₂.andE₁
  have dc := chart.andE₁.andE₂.andE₂
  have ca := hr.andE₁
  have cc := hr.andE₂.andE₁
  have rates := hr.andE₂.andE₂
  have ea : Γ ⊢[PRAAx] C ≐ numerator x (succ k) := (successor_numerator x k).eqSymm
  have valueAt : Γ ⊢[PRAAx] ap2 (F₀ f) r (d₀ t A D) ≐ inst2 F k x := by
    rw [GaussianBarnesVignerasRefinementWrap.sample_at]
    exact .eqRefl _
  have valueNext : Γ ⊢[PRAAx] ap2 (F₀ f) r (d₀ t C D) ≐ inst2 F (succ k) x := by
    rw [GaussianBarnesVignerasRefinementWrap.sample_at]
    ipra_congr (ap2 (F₀ f) (var 0) (d₀ t (var 1) (var 2)) : PTm 3) with [.eqRefl r,ea,.eqRefl D]
  have G₀ : Γ ⊢[PRAAx] ap2 (firstF g) r (data1 A D R a) ≐ inst2 G k x := by
    rw [GaussianBarnesVignerasRefinementJet.first_at]
    exact .eqRefl _
  have G₁ : Γ ⊢[PRAAx] ap2 (firstF g) r (data1 C D R b) ≐ inst2 G (succ k) x := by
    rw [GaussianBarnesVignerasRefinementJet.first_at]
    ipra_congr (ap2 (firstF g) (var 0) (data1 (var 1) (var 2) (var 3) (inst2 t₁ (var 1) (var 2))) : PTm 4)
      with [.eqRefl r,ea,.eqRefl D,.eqRefl R]
      using [GaussianBarnesVignerasRefinementJet.data1,GaussianBarnesVignerasRefinementJet.candidate]
  have H₀ : Γ ⊢[PRAAx] ap2 (secondF j) r (data2 A D R d) ≐ inst2 H k x := by
    rw [GaussianBarnesVignerasRefinementJet.second_at]
    exact .eqRefl _
  have H₁ : Γ ⊢[PRAAx] ap2 (secondF j) r (data2 C D R e) ≐ inst2 H (succ k) x := by
    rw [GaussianBarnesVignerasRefinementJet.second_at]
    ipra_congr (ap2 (secondF j) (var 0) (data2 (var 1) (var 2) (var 3) (inst2 t₂ (var 1) (var 2))) : PTm 4)
      with [.eqRefl r,ea,.eqRefl D,.eqRefl R]
      using [GaussianBarnesVignerasRefinementJet.data2,GaussianBarnesVignerasRefinementJet.candidate]
  have J₀ : Γ ⊢[PRAAx] ap2 (thirdF l) r (data3 A D v) ≐ inst2 J k x := by
    rw [GaussianBarnesVignerasRefinementJet.third_at]
    exact .eqRefl _
  have fourth := GaussianBarnesVignerasThirdJetFloor.sample_floor l v p₀ r A D hd
    (GaussianBarnesVignerasRefinementChart.lower_numerator x k)
    (GaussianBarnesVignerasRefinementChart.observation_late x p h)
    (GaussianBarnesVignerasRefinementChart.far_numerator x k p h)
    ca.andE₂.andE₂.andE₂.andE₁ ca.andE₂.andE₂.andE₂.andE₂
  have floorFit : Γ ⊢[PRAAx] le (num 9*(num 3*unit p)) (one*unit p₀) :=
    le_congr (.eqRefl _) ((one_mul _).eqTrans (precision_unit p)).eqSymm
      (le_of_eq_add (d := num 5*unit p) (by ipra_ring))
  have floor : Γ ⊢[PRAAx] floorAt J x k (unit p) :=
    upper_congr (.eqRefl _) (congrFst J₀) (.eqRefl _) (.eqRefl _)
      (upper_mono _ _ _ _ _ _ (unit_positive p₀) fourth floorFit)
  have fRate := GaussianBarnesVignerasQuotientJet.first_rate f g p₀ A C D R one
    (input t A D) (input t C D) (margin t A D) (bound t A D) (margin t C D) (bound t C D) a
    chart ca.andE₁ cc.andE₁ ca.andE₂.andE₁ rates.andE₁
  have gRate := GaussianBarnesVignerasQuotientJet.second_rate g j p₀ A C D R one a b d
    chart ca.andE₂.andE₁ cc.andE₂.andE₁ ca.andE₂.andE₂.andE₁ rates.andE₂.andE₁
  have hRate := GaussianBarnesVignerasQuotientJet.third_rate j l p₀ A C D R one d e v
    chart ca.andE₂.andE₂.andE₁ cc.andE₂.andE₂.andE₁ ca.andE₂.andE₂.andE₂.andE₁ rates.andE₂.andE₂
  have fpointA := GaussianBarnesVignerasLogQuotient.regular f A D _ _ _ ha hd ca.andE₁
  have fpointC := GaussianBarnesVignerasLogQuotient.regular f C D _ _ _ hc hd cc.andE₁
  have gpointA := GaussianBarnesVignerasQuotientJet.first_regular g A D R a ca.andE₂.andE₁ da
  have gpointC := GaussianBarnesVignerasQuotientJet.first_regular g C D R b cc.andE₂.andE₁ dc
  have hpointA := GaussianBarnesVignerasQuotientJet.second_regular j A D R d ca.andE₂.andE₂.andE₁ da
  have hpointC := GaussianBarnesVignerasQuotientJet.second_regular j C D R e cc.andE₂.andE₂.andE₁ dc
  exact .andI (observed (F₀ f) (firstF g) F G x k p _ _ _ h fpointC fpointA hd valueNext valueAt G₀ fRate)
    (.andI (observed (firstF g) (secondF j) G H x k p _ _ _ h gpointC gpointA hd G₁ G₀ H₀ gRate)
      (.andI (observed (secondF j) (thirdF l) H J x k p _ _ _ h hpointC hpointA hd H₁ H₀ J₀ hRate) floor))

end LeanProofs.IPRA.Analysis.GaussianBarnesVignerasRefinementNode
