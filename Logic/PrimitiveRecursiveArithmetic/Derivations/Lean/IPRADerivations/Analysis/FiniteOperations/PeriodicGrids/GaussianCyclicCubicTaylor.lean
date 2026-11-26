import IPRADerivations.Analysis.FiniteOperations.PeriodicGrids.GaussianSignedObservationReadback
import IPRADerivations.Analysis.FiniteOperations.PeriodicGrids.SignedCubicTaylorGrid

/-!
# From cyclic Gaussian Taylor observations to a periodic grid bound

A cubic jet at each mesh point is stored in four signed PR bodies.
Its Taylor error is certified against the original Gaussian evaluator
at all four stencil nodes, with indices taken modulo the period. The
cubic lower bound and the four errors imply the required actual
third-difference bound after one signed rounding unit per observation.
-/

set_option autoImplicit false
set_option maxHeartbeats 1250000

namespace LeanProofs.IPRA.Analysis.GaussianCyclicCubicTaylor

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianSignedObservationGrid (realPoint wrapped_near_lattice)
open GaussianSignedObservationReadback (cyclicThirdLower cyclic_distance cyclic_dyadic_distance observationClock realProjection)
open GaussianRationalMetric (distanceBounded)
open GaussianCoefficientNameBounds (unit unit_positive)
open SignedCubicTaylorGrid (value force third_lower_at)
open PeriodicThirdDifferenceConstancy (cubicBudget)
open PeriodicThirdDifferenceModulo (third)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

structure Jet where
  c₀ : ZB
  c₁ : ZB
  c₂ : ZB
  c₃ : ZB

def error (A E : PTm n) : PTm n := SignedCubicTaylorGrid.error A (E+one)

def model (J : Jet) (y i H j : PTm n) : ZT n :=
  value (J.c₀.val i y) (J.c₁.val i y) (J.c₂.val i y) (J.c₃.val i y) H j

def nodeError (f : PTm 2) (J : Jet) (x y S N H E i j k : PTm n) : Fm PTm n :=
  distanceBounded (inst2 f (rem k N) x) (realPoint (model J y i H j) S) E S

def row (f : PTm 2) (J : Jet) (x y S N H A E i : PTm n) : Fm PTm n :=
  zle (-ZT.ofNat A) (force (J.c₃.val i y) H) ⋏
    (nodeError f J x y S N H E i zero i ⋏
      (nodeError f J x y S N H E i one (succ i) ⋏
        (nodeError f J x y S N H E i two (succ (succ i)) ⋏
          nodeError f J x y S N H E i (num 3) (succ (succ (succ i))))))

def source (f : PTm 2) (J : Jet) (x y S N H A E : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift N) ⟶ row f J (Syn.shift x) (Syn.shift y) (Syn.shift S)
    (Syn.shift N) (Syn.shift H) (Syn.shift A) (Syn.shift E) (var 0))

theorem row_third_lower (f : PTm 2) (J : Jet) (x y S N H A E i : PTm n)
    (hS : Γ ⊢[PRAAx] le one S) (h : Γ ⊢[PRAAx] row f J x y S N H A E i) :
    let b := PeriodicThirdDifferenceModulo.wrapped (GaussianSignedObservationGrid.body f)
    let d := PeriodicThirdDifferenceModulo.data (GaussianSignedObservationGrid.data x S) N
    Γ ⊢[PRAAx] zle (-ZT.ofNat (error A E)) ((third b).val i d) := by
  have a := h.andE₂
  have b := a.andE₂
  have c := b.andE₂
  exact third_lower_at _ i _ (J.c₀.val i y) (J.c₁.val i y) (J.c₂.val i y) (J.c₃.val i y)
    H A (E+one) h.andE₁
    (wrapped_near_lattice f x S i N E _ hS a.andE₁)
    (wrapped_near_lattice f x S (succ i) N E _ hS b.andE₁)
    (wrapped_near_lattice f x S (succ (succ i)) N E _ hS c.andE₁)
    (wrapped_near_lattice f x S (succ (succ (succ i))) N E _ hS c.andE₂)

theorem third_lower (f : PTm 2) (J : Jet) (x y S N H A E : PTm n)
    (hS : Γ ⊢[PRAAx] le one S) (h : Γ ⊢[PRAAx] source f J x y S N H A E) :
    Γ ⊢[PRAAx] cyclicThirdLower f x S N (error A E) := by
  refine .allI (.impI ?_)
  let sh (z : PTm n) := Syn.shift z
  let i : PTm (n+1) := var 0
  let Δ := lt i (sh N) :: Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] le one (sh S) := by
    simpa only [Δ,sh,Syn.shift,Fm.shift,subst_le,one,ConciseIPRA.PTm.subst_succ,
      ConciseIPRA.PTm.subst_zero] using hS.shift.wk
  have rowAt : Δ ⊢[PRAAx] row f J (sh x) (sh y) (sh S) (sh N) (sh H) (sh A) (sh E) i :=
    .impE h.allOpen.wk Prf.hyp0
  simpa only [Δ,i,sh,error,SignedCubicTaylorGrid.error,GaussianSignedObservationGrid.data,
    PeriodicThirdDifferenceModulo.data,Syn.shift,subst_pairT,LeanProofs.IPRA.PTm.subst_add,
    LeanProofs.IPRA.PTm.subst_mul,one,num,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ]
    using row_third_lower f J (sh x) (sh y) (sh S) (sh N) (sh H) (sh A) (sh E) i hs rowAt

theorem distance_of_source (f : PTm 2) (J : Jet) (x y S N H A E i : PTm n)
    (hS : Γ ⊢[PRAAx] le one S) (hN : Γ ⊢[PRAAx] le one N) (hi : Γ ⊢[PRAAx] le i N)
    (h : Γ ⊢[PRAAx] source f J x y S N H A E) :
    Γ ⊢[PRAAx] distanceBounded (realProjection (inst2 f (rem i N) x))
      (realProjection (inst2 f (rem zero N) x)) (cubicBudget N (error A E)+two) S :=
  cyclic_distance f x S N (error A E) i hS hN hi (third_lower f J x y S N H A E hS h)

theorem dyadic_distance_of_source (f : PTm 2) (J : Jet) (x y N H A E i p : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hi : Γ ⊢[PRAAx] le i N)
    (h : Γ ⊢[PRAAx] source f J x y (unit (observationClock N (error A E) p)) N H A E) :
    Γ ⊢[PRAAx] distanceBounded (realProjection (inst2 f (rem i N) x))
      (realProjection (inst2 f (rem zero N) x)) one (unit p) :=
  cyclic_dyadic_distance f x N (error A E) i p hN hi
    (third_lower f J x y _ N H A E (unit_positive _) h)

theorem actual_cyclic_cubic_taylor_dyadic_distance_closed (f : PTm 2) (J : Jet) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      (let x := var 0
       let y := var 1
       let N := var 2
       let H := var 3
       let A := var 4
       let E := var 5
       let i := var 6
       let p := var 7
       le one N ⟶ le i N ⟶ source f J x y (unit (observationClock N (error A E) p)) N H A E ⟶
         distanceBounded (realProjection (inst2 f (rem i N) x))
           (realProjection (inst2 f (rem zero N) x)) one (unit p)) :=
  closeUniv 8 (.impI (.impI (.impI (dyadic_distance_of_source f J _ _ _ _ _ _ _ _
    Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianCyclicCubicTaylor
