import IPRADerivations.Analysis.Stirling.Raabe.GaussianRaabeOriginLogStrip
import IPRADerivations.Analysis.Stirling.Raabe.GaussianRaabeCofinalSchedule
import IPRADerivations.Analysis.Logarithm.FiniteSeries.GaussianFiniteLogarithmDyadicTail

/-!
# A common budget for the original dyadic Raabe truncation

Choose the time cutoff first, the common mesh next, and the original
positive-interval observation clock last. The same clock pays the
mesh-preserving recurrence and the logarithm primitive observations.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianRaabeOriginSchedule

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRaabeOriginStripAlignment (width total_width)
open GaussianRaabeOriginLogStrip (lowerCost)
open GaussianRationalHorner (positive_product)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.PTm (num)
open ConciseIPRA.PTm (succ zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

private def base (k C : PTm n) : PTm n := k+C+one

def cutoff (k C : PTm n) : PTm n := base k C+base k C+num 8

def mesh (k C : PTm n) : PTm n :=
  let h := cutoff k C
  let E := unit h
  GaussianRaabeCofinalSchedule.count k E E+two*width h*unit k

def fullMesh (k C : PTm n) : PTm n := unit (cutoff k C)*mesh k C

def clock (k C : PTm n) : PTm n :=
  let E := unit (cutoff k C)
  GaussianRaabeCofinalSchedule.clockFor k (fullMesh k C) E E

private theorem unit_eight : Γ ⊢[PRAAx] unit (num 8 : PTm n) ≐ num 256 :=
  (congrAp2 powF (show Γ ⊢[PRAAx] (num 8 : PTm n) ≐ num 4+num 4 by ipra_ring) (.eqRefl two)).eqTrans
    ((pw_add two (num 4) (num 4)).eqTrans
      ((congrMul GaussianFiniteLogarithmDyadicTail.two_four GaussianFiniteLogarithmDyadicTail.two_four).eqTrans
        (by ipra_ring)))

theorem cutoff_budget (k C : PTm n) :
    Γ ⊢[PRAAx] le ((lowerCost (cutoff k C)+C)*unit k) (unit (cutoff k C)) := by
  let t := base k C
  let h := cutoff k C
  have c : Γ ⊢[PRAAx] le (lowerCost h+C) (num 256*succ t) := by
    dsimp only [lowerCost,GaussianRaabeDyadicPrimitive.cost,h,cutoff,t,base]
    ipra_le 194*𝔞(k)+193*𝔞(C)+197
  have unitLarge : Γ ⊢[PRAAx] le (num 256*succ t) (num 256*unit t) :=
    le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right (num 256) (RationalClosure.succ_le_two_pow t))
  have grow : Γ ⊢[PRAAx] le (unit k) (unit t) :=
    GaussianExponentialReference.unit_monotone (le_trans (le_add_right k C) (le_add_right (k+C) one))
  have e : Γ ⊢[PRAAx] unit h ≐ num 256*unit t*unit t :=
    (pw_add two (t+t) (num 8)).eqTrans
      ((congrMul (pw_add two t t) unit_eight).eqTrans (by unfold unit; ipra_ring))
  exact le_congr (.eqRefl _) e.eqSymm (le_mul_mono (le_trans c unitLarge) grow)

theorem cutoff_positive (k C : PTm n) : Γ ⊢[PRAAx] le two (unit (cutoff k C)) := by
  have h : Γ ⊢[PRAAx] le one (cutoff k C) :=
    le_of_eq_add (d := base k C+base k C+num 7) (by unfold cutoff; ipra_ring)
  exact le_congr (pw_one two) (.eqRefl _) (GaussianExponentialReference.unit_monotone h)

theorem mesh_floors (k C : PTm n) :
    let h := cutoff k C
    let E := unit h
    Γ ⊢[PRAAx] le one (mesh k C) ⋏
      (le (GaussianRaabeCofinalSchedule.count k E E) (mesh k C) ⋏
      (le (GaussianRaabeCofinalSchedule.count k E E) (fullMesh k C) ⋏
        le (two*width h*unit k) (mesh k C))) := by
  let h := cutoff k C
  let E := unit h
  let K := mesh k C
  let Q := GaussianRaabeCofinalSchedule.count k E E
  let V := two*width h*unit k
  have hQ : Γ ⊢[PRAAx] le Q K := le_add_right Q V
  have hK : Γ ⊢[PRAAx] le one K :=
    le_trans (GaussianRaabeCofinalSchedule.count_positive k E E) hQ
  have more : Γ ⊢[PRAAx] le K (fullMesh k C) :=
    le_congr (one_mul K) (.eqRefl _) (mul_le_mul_right K (unit_positive h))
  exact .andI hK (.andI hQ (.andI (le_trans hQ more) (le_add_left V Q)))

theorem clock_budget (k C : PTm n) :
    let h := cutoff k C
    let N := GaussianRaabeOriginStripAlignment.mesh h (mesh k C)
    Γ ⊢[PRAAx] le ((two*N+num 20)*unit k) (unit (clock k C)) := by
  let h := cutoff k C
  let E := unit h
  let K := mesh k C
  let N := GaussianRaabeOriginStripAlignment.mesh h K
  let Q := fullMesh k C
  let J := unit k
  let R := GaussianRaabeCofinalSchedule.farStart k E E
  let B := GaussianRaabeCofinalSchedule.clockCost J Q R E E
  have hk := (mesh_floors (Γ := Γ) k C).andE₁
  have hE := unit_positive (Γ := Γ) h
  have hQ : Γ ⊢[PRAAx] le one Q := positive_product _ _ hE hk
  have hR := le_trans hE (GaussianRaabeCofinalSchedule.far_admitted (Γ := Γ) k E E)
  have hCE : Γ ⊢[PRAAx] le (width h) E :=
    le_congr (.eqRefl _) ((add_comm (width h) one).eqTrans (total_width h).eqSymm) (le_add_right _ _)
  have hNQ : Γ ⊢[PRAAx] le N Q := mul_le_mul_right K hCE
  have qr : Γ ⊢[PRAAx] le Q (R*Q) := le_congr (one_mul Q) (.eqRefl _) (mul_le_mul_right Q hR)
  have qe : Γ ⊢[PRAAx] le Q (E*Q) := le_congr (one_mul Q) (.eqRefl _) (mul_le_mul_right Q hE)
  have needed : Γ ⊢[PRAAx] le (N+one) ((R+E)*Q) :=
    le_congr (.eqRefl _) (by ipra_ring) (add_le_add₂ (le_trans hNQ qr) (le_trans hQ qe))
  have pay : Γ ⊢[PRAAx] le (two*N+num 20) (num 18+two*((R+E)*Q)) := by
    ipra_le 2*sl needed
  have widen : Γ ⊢[PRAAx] le (num 18+two*((R+E)*Q)) B := by
    dsimp only [B,GaussianRaabeCofinalSchedule.clockCost]
    ipra_le 1+8*𝔞(J)+2*𝔞(J)*𝔞(R)*𝔞(Q)+(4*𝔞(R)+1)+2*𝔞(E)+𝔞(GaussianRaabeRightSide.cost E)
  exact le_trans (mul_le_mul_right J (le_trans pay widen)) (GaussianFastValueCut.query_budget B k)

theorem log_budget (k C : PTm n) :
    let h := cutoff k C
    let K := mesh k C
    let p := clock k C
    Γ ⊢[PRAAx] le (GaussianRaabeOriginLogStrip.numerator p h K*unit k)
      (num 3*GaussianRaabeOriginLogStrip.denominator p h K) := by
  let h := cutoff k C
  let K := mesh k C
  let p := clock k C
  let E := unit h
  let S := width h
  let N := GaussianRaabeOriginStripAlignment.mesh h K
  let J := unit k
  let U := unit p
  have hm : Γ ⊢[PRAAx] le (two*(S*S)*J) N :=
    le_congr (by ipra_ring) (mul_comm K S)
      (mul_le_mul_right S (mesh_floors k C).andE₂.andE₂.andE₂)
  have hp : Γ ⊢[PRAAx] le ((two*N+num 10)*J) U :=
    le_trans (mul_le_mul_right J (le_of_eq_add (d := num 10) (by ipra_ring))) (clock_budget k C)
  have hc : Γ ⊢[PRAAx] le (lowerCost h*J) E :=
    le_trans (mul_le_mul_right J (le_add_right (lowerCost h) C)) (cutoff_budget k C)
  change Γ ⊢[PRAAx] le (((two*(S*S)*U+(two*N+num 10)*N)*E+lowerCost h*N*U)*J)
    (num 3*(N*E*U))
  ipra_le 𝔞(E*U)*sl hm+𝔞(N*E)*sl hp+𝔞(N*U)*sl hc

theorem actual_dyadic_Raabe_cutoff_and_logarithm_budgets_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (let k := var 0
       let C := var 1
       let h := cutoff k C
       let K := mesh k C
       let p := clock k C
       le ((lowerCost h+C)*unit k) (unit h) ⋏
         le (GaussianRaabeOriginLogStrip.numerator p h K*unit k) (num 3*GaussianRaabeOriginLogStrip.denominator p h K)) :=
  closeUniv 2 (.andI (cutoff_budget _ _) (log_budget _ _))

end LeanProofs.IPRA.Analysis.GaussianRaabeOriginSchedule
