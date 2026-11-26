import IPRADerivations.Analysis.FiniteOperations.PeriodicGrids.PeriodicThirdDifferenceConstancy
import IPRADerivations.Core.CommonLemmas
import IPRADerivations.DiophantineNumberTheory.DigitCode
import IPRADerivations.DiophantineNumberTheory.ModularCertificate

/-!
# Third differences on a cyclic grid of signed samples

Read each input sample at its residue modulo the period. The first two
differences are then periodic as well, including when the period is one
or two. A lower bound on the actual cyclic third difference suffices
for the finite constancy estimate.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.PeriodicThirdDifferenceModulo

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.DiophantineNumberTheory.ModularCertificate (rem_add_mul)
open LeanProofs.IPRA.DiophantineNumberTheory.DigitCode (rem_small)
open LeanProofs.IPRA.Common (pos_of_one_le)
open PolynomialBisection (zle_add zle_congr zle_refl)
open SignedGridStepBounds (difference difference_value liftZT lowerSteps read_index)
open PeriodicThirdDifferenceConstancy (periodic band cubicBudget periodic_range)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def data (x N : PTm n) : PTm n := pairT N x

def wrapBody (b : PTm 2) : PTm 2 := inst2 b (rem (var 0) (fstT (var 1))) (sndT (var 1))

def wrapped (b : ZB) : ZB := ⟨wrapBody b.pos, wrapBody b.neg⟩

private theorem component_at (b : PTm 2) (x N i : PTm n) :
    Γ ⊢[PRAAx] inst2 (wrapBody b) i (data x N) ≐ inst2 b (rem i N) x := by
  have e : inst2 (wrapBody b) i (data x N) =
      inst2 b (rem i (fstT (data x N))) (sndT (data x N)) := by
    change Syn.subst ![i,data x N] (wrapBody b) = _
    rw [wrapBody,subst_inst2]
    simp
  rw [e]
  exact congrInst2 b (congrAp2 remF (.eqRefl i) (fst_pair N x)) (snd_pair N x)

theorem sample_at (b : ZB) (x N i : PTm n) :
    Γ ⊢[PRAAx] ZT.eq ((wrapped b).val i (data x N)) (b.val (rem i N) x) := by
  apply ZT.derive
  simp only [ZB.toZ_val,wrapped]
  rw [natEq (component_at b.pos x N i),natEq (component_at b.neg x N i)]

theorem sample_inside (b : ZB) (x N i : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] ZT.eq ((wrapped b).val i (data x N)) (b.val i x) :=
  ZT.derive ((ZT.toZ_eq (sample_at b x N i)).trans (read_index b x (rem_small (pos_of_one_le hN) hi)))

private theorem residue_period (N i : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] rem (N+i) N ≐ rem i N :=
  (congrAp2 remF (by ipra_ring) (.eqRefl N)).eqTrans (rem_add_mul (pos_of_one_le hN) one i)

theorem sample_period (b : ZB) (x N i : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] ZT.eq ((wrapped b).val (N+i) (data x N)) ((wrapped b).val i (data x N)) := by
  apply ZT.derive
  exact (ZT.toZ_eq (sample_at b x N (N+i))).trans
    ((read_index b x (residue_period N i hN)).trans (ZT.toZ_eq (sample_at b x N i)).symm)

private theorem difference_period (b : ZB) (x N i : PTm n)
    (atI : Γ ⊢[PRAAx] ZT.eq (b.val (N+i) x) (b.val i x))
    (atNext : Γ ⊢[PRAAx] ZT.eq (b.val (N+succ i) x) (b.val (succ i) x)) :
    Γ ⊢[PRAAx] ZT.eq ((difference b).val (N+i) x) ((difference b).val i x) := by
  apply ZT.derive
  rw [difference_value,difference_value,
    read_index b x (add_succ N i).eqSymm,ZT.toZ_eq atI,ZT.toZ_eq atNext]

private theorem wrapped_difference_period (b : ZB) (x N i : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] ZT.eq ((difference (wrapped b)).val (N+i) (data x N))
      ((difference (wrapped b)).val i (data x N)) :=
  difference_period _ _ _ _ (sample_period b x N i hN) (sample_period b x N (succ i) hN)

private theorem period_at_zero (b : ZB) (x N : PTm n)
    (h : Γ ⊢[PRAAx] ZT.eq (b.val (N+zero) x) (b.val zero x)) : Γ ⊢[PRAAx] periodic b x N :=
  ZT.derive ((read_index b x (add_zero N).eqSymm).trans (ZT.toZ_eq h))

theorem periodic_endpoints (b : ZB) (x N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    let c := wrapped b
    let d := data x N
    Γ ⊢[PRAAx] periodic c d N ⋏ (periodic (difference c) d N ⋏ periodic (difference (difference c)) d N) :=
  .andI (period_at_zero _ _ _ (sample_period b x N zero hN))
    (.andI (period_at_zero _ _ _ (wrapped_difference_period b x N zero hN))
      (period_at_zero _ _ _ (difference_period _ _ _ _
        (wrapped_difference_period b x N zero hN) (wrapped_difference_period b x N (succ zero) hN))))

def third (b : ZB) : ZB := difference (difference (difference b))

theorem third_value (b : ZB) (i x : PTm n) :
    ZT.toZ Γ ((third b).val i x) =
      ZT.toZ Γ (b.val (succ (succ (succ i))) x) - 3*ZT.toZ Γ (b.val (succ (succ i)) x)
        + 3*ZT.toZ Γ (b.val (succ i) x) - ZT.toZ Γ (b.val i x) := by
  simp only [third,difference_value]
  ring

def thirdLower (b : ZB) (x N E : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift N) ⟶ zle (-ZT.ofNat (Syn.shift E)) ((third b).val (var 0) (Syn.shift x)))

theorem third_lower_steps (b : ZB) (x N E : PTm n) (h : Γ ⊢[PRAAx] thirdLower b x N E) :
    Γ ⊢[PRAAx] lowerSteps (difference (difference b)) x N (-ZT.ofNat E) := by
  refine .allI (.impI ?_)
  let i : PTm (n+1) := var 0
  let y := Syn.shift x
  let Δ := lt i (Syn.shift N) :: Γ.map Fm.shift
  let c := difference (difference b)
  have raw : Δ ⊢[PRAAx] zle (-ZT.ofNat (Syn.shift E)) ((difference c).val i y) :=
    .impE h.allOpen.wk Prf.hyp0
  have shiftNeg : liftZT (-ZT.ofNat E) = -ZT.ofNat (Syn.shift E) := by
    change (-ZT.ofNat E).subst (fun j => var j.succ) = _
    simp only [ZT.subst_neg,ZT.subst_ofNat,Syn.shift]
  have value : ZT.toZ Δ (c.val i y + (difference c).val i y) = ZT.toZ Δ (c.val (succ i) y) := by
    rw [ZT.toZ_add,difference_value (Γ := Δ) c i y]
    ring
  exact zle_congr (by rw [shiftNeg]) value (zle_add (zle_refl (c.val i y)) raw)

theorem range (b : ZB) (x N E i : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hi : Γ ⊢[PRAAx] le i N)
    (h : Γ ⊢[PRAAx] thirdLower (wrapped b) (data x N) N E) :
    Γ ⊢[PRAAx] band ((wrapped b).val i (data x N)-(wrapped b).val zero (data x N)) (cubicBudget N E) :=
  let p := periodic_endpoints b x N hN
  periodic_range _ _ _ _ _ hN hi p.andE₁ p.andE₂.andE₁ p.andE₂.andE₂ (third_lower_steps _ _ _ _ h)

theorem actual_wrapped_periodic_third_difference_bound_closed (b : ZB) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (let x := var 0
       let N := var 1
       let E := var 2
       let i := var 3
       le one N ⟶ le i N ⟶ thirdLower (wrapped b) (data x N) N E ⟶
         band ((wrapped b).val i (data x N)-(wrapped b).val zero (data x N)) (cubicBudget N E)) :=
  closeUniv 4 (.impI (.impI (.impI (range b _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.PeriodicThirdDifferenceModulo
