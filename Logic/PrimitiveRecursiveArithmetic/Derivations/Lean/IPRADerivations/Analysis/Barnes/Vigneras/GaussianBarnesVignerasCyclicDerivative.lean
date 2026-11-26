import IPRADerivations.Analysis.Barnes.Vigneras.GaussianBarnesVignerasCubicForce
import IPRADerivations.Analysis.FiniteOperations.PeriodicGrids.GaussianCyclicCubicTaylor

/-!
# Finite Vignéras step with the original far-axis cubic derivative

At grid tag A/B+i/N, the cubic coefficient is the literal difference
of rounded candidate and original Barnes third derivatives after the
common integer translation. Only the lower three coefficient bodies
and a four-node Taylor certificate are supplied. Set the common
observation denominator to 6N³·2^q, corresponding to the cubic
coefficient at step 1/N. The precision bound cancels N³, so the
observation clock can be chosen before the mesh is refined.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesVignerasCyclicDerivative

open_ipra
open GaussianBarnesVignerasCubicForce (coefficient farNumerator forceBudget force_lower)
open GaussianCyclicCubicTaylor (error)
open GaussianGammaCanonicalExponent (constantF)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianRationalHorner (qzero positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianSignedObservationGrid (realPoint wrapped_near_lattice)
open GaussianSignedObservationReadback (cyclicThirdLower cyclic_distance realProjection)
open SignedCubicTaylorGrid (third_lower_at value)
open PeriodicThirdDifferenceConstancy (cubicBudget)
open PeriodicThirdDifferenceModulo (third)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

structure LowerJet where
  c₀ : ZB
  c₁ : ZB
  c₂ : ZB

def numerator (A B N i : PTm n) : PTm n := A*N+i*B

def denominator (B N : PTm n) : PTm n := B*N

def candidateData (t : PTm 2) (A B N i q : PTm n) : PTm n :=
  inst2 t (farNumerator q (numerator A B N i) (denominator B N)) (denominator B N)

def cubicCoefficient (g : PR 2) (t : PTm 2) (A B N i q : PTm n) : ZT n :=
  coefficient g (candidateData t A B N i q) q (numerator A B N i) (denominator B N)

def scale (N q : PTm n) : PTm n := num 6*(N*(N*N))*unit q

def slack (E : PTm n) : PTm n := error (forceBudget one) E

def clock (E p : PTm n) : PTm n := GaussianFastValueCut.exponent (slack E) p

def model (g : PR 2) (t : PTm 2) (J : LowerJet) (y A B N i q j : PTm n) : ZT n :=
  value (J.c₀.val i y) (J.c₁.val i y) (J.c₂.val i y) (cubicCoefficient g t A B N i q) one j

def nodeError (f : PTm 2) (g : PR 2) (t : PTm 2) (J : LowerJet)
    (x y A B N q E i j k : PTm n) : Fm PTm n :=
  distanceBounded (inst2 f (rem k N) x) (realPoint (model g t J y A B N i q j) (scale N q)) E (scale N q)

def row (f : PTm 2) (g : PR 2) (t : PTm 2) (J : LowerJet)
    (x y A B N q E i : PTm n) : Fm PTm n :=
  realOrder constantF g qzero (candidateData t A B N i q) ⋏
    (nodeError f g t J x y A B N q E i zero i ⋏
      (nodeError f g t J x y A B N q E i one (succ i) ⋏
        (nodeError f g t J x y A B N q E i two (succ (succ i)) ⋏
          nodeError f g t J x y A B N q E i (num 3) (succ (succ (succ i))))))

def source (f : PTm 2) (g : PR 2) (t : PTm 2) (J : LowerJet)
    (x y A B N q E : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift N) ⟶ row f g t J (Syn.shift x) (Syn.shift y) (Syn.shift A)
    (Syn.shift B) (Syn.shift N) (Syn.shift q) (Syn.shift E) (var 0))

private theorem six_positive : Γ ⊢[PRAAx] le one (num 6 : PTm n) :=
  le_of_eq_add (d := num 5) (by ipra_ring)

private theorem scale_positive (N q : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] le one (scale N q) :=
  positive_product _ _ (positive_product _ _ six_positive
    (positive_product _ _ hN (positive_product _ _ hN hN))) (unit_positive q)

theorem row_third_lower (f : PTm 2) (g : PR 2) (t : PTm 2) (J : LowerJet)
    (x y A B N q E i : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hN : Γ ⊢[PRAAx] le one N)
    (h : Γ ⊢[PRAAx] row f g t J x y A B N q E i) :
    let b := PeriodicThirdDifferenceModulo.wrapped (GaussianSignedObservationGrid.body f)
    let d := PeriodicThirdDifferenceModulo.data (GaussianSignedObservationGrid.data x (scale N q)) N
    Γ ⊢[PRAAx] zle (-ZT.ofNat (slack E)) ((third b).val i d) := by
  let S := scale N q
  have hS := scale_positive N q hN
  have force := force_lower g (candidateData t A B N i q) q (numerator A B N i) (denominator B N)
    one (positive_product _ _ hB hN) h.andE₁
  have a := h.andE₂
  have b := a.andE₂
  have c := b.andE₂
  exact third_lower_at _ i _ (J.c₀.val i y) (J.c₁.val i y) (J.c₂.val i y) (cubicCoefficient g t A B N i q)
    one (forceBudget one) (E+one) force
    (wrapped_near_lattice f x S i N E _ hS a.andE₁)
    (wrapped_near_lattice f x S (succ i) N E _ hS b.andE₁)
    (wrapped_near_lattice f x S (succ (succ i)) N E _ hS c.andE₁)
    (wrapped_near_lattice f x S (succ (succ (succ i))) N E _ hS c.andE₂)

theorem third_lower (f : PTm 2) (g : PR 2) (t : PTm 2) (J : LowerJet)
    (x y A B N q E : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hN : Γ ⊢[PRAAx] le one N)
    (h : Γ ⊢[PRAAx] source f g t J x y A B N q E) :
    Γ ⊢[PRAAx] cyclicThirdLower f x (scale N q) N (slack E) := by
  refine .allI (.impI ?_)
  let sh (z : PTm n) := Syn.shift z
  let i : PTm (n+1) := var 0
  let Δ := lt i (sh N) :: Γ.map Fm.shift
  have hb : Δ ⊢[PRAAx] le one (sh B) := by
    simpa only [Δ,sh,Syn.shift,Fm.shift,subst_le,one,ConciseIPRA.PTm.subst_succ,
      ConciseIPRA.PTm.subst_zero] using hB.shift.wk
  have hn : Δ ⊢[PRAAx] le one (sh N) := by
    simpa only [Δ,sh,Syn.shift,Fm.shift,subst_le,one,ConciseIPRA.PTm.subst_succ,
      ConciseIPRA.PTm.subst_zero] using hN.shift.wk
  have ht : Δ ⊢[PRAAx] row f g t J (sh x) (sh y) (sh A) (sh B) (sh N) (sh q) (sh E) i :=
    .impE h.allOpen.wk Prf.hyp0
  simpa only [Δ,i,sh,slack,error,SignedCubicTaylorGrid.error,scale,forceBudget,
    GaussianSignedObservationGrid.data,PeriodicThirdDifferenceModulo.data,Syn.shift,subst_pairT,
    LeanProofs.IPRA.PTm.subst_add,LeanProofs.IPRA.PTm.subst_mul,one,num,ConciseIPRA.PTm.subst_zero,
    ConciseIPRA.PTm.subst_succ,GaussianCoefficientNameBounds.subst_unit] using
    row_third_lower f g t J (sh x) (sh y) (sh A) (sh B) (sh N) (sh q) (sh E) i hb hn ht

private theorem budget_le (N E : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] le (cubicBudget N (slack E)+two) ((num 6*(N*(N*N)))*slack E) := by
  let W := N*(N*N)*slack E
  have hW : Γ ⊢[PRAAx] le one W := by
    apply positive_product _ _ (positive_product _ _ hN (positive_product _ _ hN hN))
    unfold slack error SignedCubicTaylorGrid.error
    exact le_trans (le_of_eq_add (d := num 29) (by unfold forceBudget; ipra_ring)) (le_add_right _ _)
  have h2w : Γ ⊢[PRAAx] le two (two*W) :=
    le_congr (one_mul two) (mul_comm _ _) (mul_le_mul_right two hW)
  have sum := add_le_add_right (num 4*W) h2w
  exact le_congr (by unfold W cubicBudget; ipra_ring) (by unfold W; ipra_ring) sum

theorem clock_budget (N E p : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] le ((cubicBudget N (slack E)+two)*unit p) (scale N (clock E p)) := by
  let D := num 6*(N*(N*N))
  have clockBudget : Γ ⊢[PRAAx] le (slack E*unit p) (unit (clock E p)) :=
    GaussianFastValueCut.query_budget _ _
  have scaledClock : Γ ⊢[PRAAx] le (D*(slack E*unit p)) (D*unit (clock E p)) :=
    le_mul_mono (le_refl D) clockBudget
  have association : Γ ⊢[PRAAx] D*(slack E*unit p) ≐ (D*slack E)*unit p := by ipra_ring
  have paid : Γ ⊢[PRAAx] le ((D*slack E)*unit p) (scale N (clock E p)) :=
    le_congr association (.eqRefl _) scaledClock
  exact le_trans (mul_le_mul_right (unit p) (budget_le N E hN)) paid

theorem dyadic_distance (f : PTm 2) (g : PR 2) (t : PTm 2) (J : LowerJet)
    (x y A B N E i p : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hN : Γ ⊢[PRAAx] le one N)
    (hi : Γ ⊢[PRAAx] le i N) (h : Γ ⊢[PRAAx] source f g t J x y A B N (clock E p) E) :
    Γ ⊢[PRAAx] distanceBounded (realProjection (inst2 f (rem i N) x))
      (realProjection (inst2 f (rem zero N) x)) one (unit p) := by
  let S := scale N (clock E p)
  have hS := scale_positive N (clock E p) hN
  exact distance_radius_mono _ _ (cubicBudget N (slack E)+two) S one (unit p) hS (unit_positive p)
    (le_congr (.eqRefl _) (one_mul _).eqSymm (clock_budget N E p hN))
    (cyclic_distance f x S N (slack E) i hS hN hi (third_lower f g t J x y A B N _ E hB hN h))

theorem actual_Vigneras_periodic_observation_rate_closed (f : PTm 2) (g : PR 2) (t : PTm 2) (J : LowerJet) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      (let x := var 0
       let y := var 1
       let A := var 2
       let B := var 3
       let N := var 4
       let E := var 5
       let i := var 6
       let p := var 7
       le one B ⟶ le one N ⟶ le i N ⟶ source f g t J x y A B N (clock E p) E ⟶
         distanceBounded (realProjection (inst2 f (rem i N) x))
           (realProjection (inst2 f (rem zero N) x)) one (unit p)) :=
  closeUniv 8 (.impI (.impI (.impI (.impI (dyadic_distance f g t J _ _ _ _ _ _ _ _
    Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianBarnesVignerasCyclicDerivative
