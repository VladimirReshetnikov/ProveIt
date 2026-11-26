import IPRADerivations.Analysis.FiniteOperations.PeriodicGrids.GaussianDiscretePeriodicThirdFloor

/-!
# Direct real-axis input certificate for the periodic derivative estimate

The inputs are original Gaussian finite derivative and periodicity
comparisons at radius 1/U and a real third-derivative lower estimate
at radius 1/(3U). The wrapper handles the common-lattice rounding,
fine refinement and cyclic signed range internally.
-/

set_option autoImplicit false
set_option maxHeartbeats 1550000

namespace LeanProofs.IPRA.Analysis.GaussianDiscretePeriodicMetricCertificate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianDiscretePeriodicDerivativeSchedule (padding clock denominator)
open GaussianDiscreteDerivativeRounding (latticeScale subst_latticeScale)
open GaussianDiscretePeriodicGridReadback (sample)
open SignedDiscreteThirdDerivativeEstimate (window)
open SignedDiscreteDerivativeOperators (width divisor subst_divisor)
open GaussianSignedObservationReadback (realProjection)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalNaturalScale (natScale)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianCoefficientNameBounds (unit unit_positive)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def derivative (f g : PTm 2) (x K U : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift K) ⟶
    distanceBounded (natScale (divisor (Syn.shift x))
      (qsub (inst2 f (succ (var 0)) (Syn.shift x)) (inst2 f (var 0) (Syn.shift x))))
      (inst2 g (var 0) (Syn.shift x)) one (Syn.shift U))

def node (f : PTm 2) (x N U j k : PTm n) : Fm PTm n :=
  distanceBounded (sample f x (rem j N)) (inst2 f k x) one U

def wrapping (f : PTm 2) (x N i U : PTm n) : Fm PTm n :=
  let k₀ := i*width x
  let k₁ := k₀+width x
  let k₂ := k₁+width x
  let k₃ := k₂+width x
  node f x N U i k₀ ⋏ (node f x N U (succ i) k₁ ⋏
    (node f x N U (succ (succ i)) k₂ ⋏ node f x N U (succ (succ (succ i))) k₃))

def row (f g h j : PTm 2) (x N i U : PTm n) : Fm PTm n :=
  let K := window x (i*width x)
  derivative f g x K U ⋏ (derivative g h x K U ⋏
    (derivative h j x K U ⋏ (GaussianDiscretePeriodicThirdFloor.source j x K U ⋏ wrapping f x N i U)))

def source (f g h j : PTm 2) (x N U : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift N) ⟶ row f g h j (Syn.shift x) (Syn.shift N) (var 0) (Syn.shift U))

private theorem radius_on_lattice (q r x U : PTm n) (hU : Γ ⊢[PRAAx] le one U)
    (hS : Γ ⊢[PRAAx] latticeScale x ≐ U*padding (divisor x))
    (h : Γ ⊢[PRAAx] distanceBounded q r one U) :
    Γ ⊢[PRAAx] distanceBounded q r (padding (divisor x)) (latticeScale x) := by
  have pos : Γ ⊢[PRAAx] le one (latticeScale x) := le_congr (.eqRefl _) hS.eqSymm
    (positive_product _ _ hU (GaussianDiscretePeriodicDerivativeSchedule.padding_positive _))
  have eq : Γ ⊢[PRAAx] one*latticeScale x ≐ padding (divisor x)*U :=
    ((one_mul _).eqTrans hS).eqTrans (mul_comm _ _)
  exact distance_radius_mono _ _ _ _ _ _ hU pos (le_congr eq.eqSymm (.eqRefl _) (le_refl _)) h

private theorem derivative_on_lattice (f g : PTm 2) (x K U : PTm n) (hU : Γ ⊢[PRAAx] le one U)
    (hS : Γ ⊢[PRAAx] latticeScale x ≐ U*padding (divisor x)) (h : Γ ⊢[PRAAx] derivative f g x K U) :
    Γ ⊢[PRAAx] GaussianDiscreteDerivativeRounding.source f g x K (padding (divisor x)) := by
  refine .allI (.impI ?_)
  let X := Syn.shift x
  let P := Syn.shift U
  let i : PTm (n+1) := var 0
  let Δ := lt i (Syn.shift K) :: Γ.map Fm.shift
  have hu : Δ ⊢[PRAAx] le one P := by
    simpa only [Δ,i,P,Fm.shift,Syn.shift,subst_le,one,ConciseIPRA.PTm.subst_succ,
      ConciseIPRA.PTm.subst_zero] using hU.shift.wk
  have hs : Δ ⊢[PRAAx] latticeScale X ≐ P*padding (divisor X) := by
    simpa [Δ,i,X,P,Fm.shift,Syn.shift,padding,two,one] using hS.shift.wk
  have shiftPadding : Syn.shift (padding (divisor x)) = padding (divisor X) := by
    simp [X,Syn.shift,padding,two,one]
  rw [shiftPadding]
  exact radius_on_lattice _ _ X P hu hs (.impE h.allOpen.wk Prf.hyp0)

private theorem wrapping_on_lattice (f : PTm 2) (x N i U : PTm n) (hU : Γ ⊢[PRAAx] le one U)
    (hS : Γ ⊢[PRAAx] latticeScale x ≐ U*padding (divisor x)) (h : Γ ⊢[PRAAx] wrapping f x N i U) :
    Γ ⊢[PRAAx] GaussianDiscretePeriodicThirdDerivative.wrapping f x N i (padding (divisor x)) :=
  .andI (radius_on_lattice _ _ x U hU hS h.andE₁)
    (.andI (radius_on_lattice _ _ x U hU hS h.andE₂.andE₁)
      (.andI (radius_on_lattice _ _ x U hU hS h.andE₂.andE₂.andE₁)
        (radius_on_lattice _ _ x U hU hS h.andE₂.andE₂.andE₂)))

theorem row_on_lattice (f g h j : PTm 2) (x N i U : PTm n)
    (hD : Γ ⊢[PRAAx] le one (divisor x)) (hU : Γ ⊢[PRAAx] le one U)
    (hS : Γ ⊢[PRAAx] latticeScale x ≐ U*padding (divisor x)) (hr : Γ ⊢[PRAAx] row f g h j x N i U) :
    let R := padding (divisor x)
    Γ ⊢[PRAAx] GaussianDiscretePeriodicThirdDerivative.row f g h j x N i R R R R R :=
  .andI (derivative_on_lattice f g x _ U hU hS hr.andE₁)
    (.andI (derivative_on_lattice g h x _ U hU hS hr.andE₂.andE₁)
      (.andI (derivative_on_lattice h j x _ U hU hS hr.andE₂.andE₂.andE₁)
        (.andI (GaussianDiscretePeriodicThirdFloor.floor_on j x _ U hD hU hS hr.andE₂.andE₂.andE₂.andE₁)
          (wrapping_on_lattice f x N i U hU hS hr.andE₂.andE₂.andE₂.andE₂))))

theorem certified (f g h j : PTm 2) (x N U : PTm n)
    (hD : Γ ⊢[PRAAx] le one (divisor x)) (hU : Γ ⊢[PRAAx] le one U)
    (hS : Γ ⊢[PRAAx] latticeScale x ≐ U*padding (divisor x)) (hr : Γ ⊢[PRAAx] source f g h j x N U) :
    let R := padding (divisor x)
    Γ ⊢[PRAAx] GaussianDiscretePeriodicThirdDerivative.certified f g h j x N R R R R R := by
  refine .allI (.impI ?_)
  let sh (z : PTm n) := Syn.shift z
  let i : PTm (n+1) := var 0
  let Δ := lt i (sh N) :: Γ.map Fm.shift
  have hd : Δ ⊢[PRAAx] le one (divisor (sh x)) := by
    simpa only [Δ,i,sh,Fm.shift,Syn.shift,subst_le,subst_divisor,one,ConciseIPRA.PTm.subst_succ,
      ConciseIPRA.PTm.subst_zero] using hD.shift.wk
  have hu : Δ ⊢[PRAAx] le one (sh U) := by
    simpa only [Δ,i,sh,Fm.shift,Syn.shift,subst_le,one,ConciseIPRA.PTm.subst_succ,
      ConciseIPRA.PTm.subst_zero] using hU.shift.wk
  have hs : Δ ⊢[PRAAx] latticeScale (sh x) ≐ sh U*padding (divisor (sh x)) := by
    simpa [Δ,i,sh,Fm.shift,Syn.shift,padding,two,one] using hS.shift.wk
  have shiftPadding : Syn.shift (padding (divisor x)) = padding (divisor (sh x)) := by
    simp [sh,Syn.shift,padding,two,one]
  rw [shiftPadding]
  exact row_on_lattice f g h j (sh x) (sh N) i (sh U) hd hu hs (.impE hr.allOpen.wk Prf.hyp0)

theorem dyadic_distance (f g h j : PTm 2) (x N i p : PTm n)
    (hM : Γ ⊢[PRAAx] le one (width x)) (hD : Γ ⊢[PRAAx] divisor x ≐ N*width x)
    (hS : Γ ⊢[PRAAx] latticeScale x ≐ denominator x N p)
    (hN : Γ ⊢[PRAAx] le one N) (hi : Γ ⊢[PRAAx] le i N)
    (hr : Γ ⊢[PRAAx] source f g h j x N (unit (clock N p))) :
    Γ ⊢[PRAAx] distanceBounded (realProjection (sample f x (rem i N)))
      (realProjection (sample f x (rem zero N))) one (unit p) := by
  have hd : Γ ⊢[PRAAx] le one (divisor x) :=
    le_congr (.eqRefl _) hD.eqSymm (positive_product _ _ hN hM)
  exact GaussianDiscretePeriodicDerivativeSchedule.dyadic_distance f g h j x N i p hM hD hS hN hi
    (certified f g h j x N _ hd (unit_positive _) hS hr)

theorem actual_Gaussian_periodic_original_rates_distance_closed (f g h j : PTm 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (let x := var 0
       let N := var 1
       let i := var 2
       let p := var 3
       le one (width x) ⟶ divisor x ≐ N*width x ⟶ latticeScale x ≐ denominator x N p ⟶
       le one N ⟶ le i N ⟶ source f g h j x N (unit (clock N p)) ⟶
         distanceBounded (realProjection (sample f x (rem i N)))
           (realProjection (sample f x (rem zero N))) one (unit p)) :=
  closeUniv 4 (.impI (.impI (.impI (.impI (.impI (.impI (dyadic_distance f g h j _ _ _ _
    Prf.hyp1.wk.wk.wk.wk Prf.hyp1.wk.wk.wk Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))))

end LeanProofs.IPRA.Analysis.GaussianDiscretePeriodicMetricCertificate
