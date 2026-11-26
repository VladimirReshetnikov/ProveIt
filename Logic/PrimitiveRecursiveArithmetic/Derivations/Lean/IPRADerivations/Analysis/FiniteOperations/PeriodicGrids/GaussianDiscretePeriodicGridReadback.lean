import IPRADerivations.Analysis.FiniteOperations.PeriodicGrids.GaussianDiscreteDerivativeRounding
import IPRADerivations.Analysis.FiniteOperations.PeriodicGrids.GaussianSignedObservationReadback
import IPRADerivations.Analysis.FiniteOperations.PeriodicGrids.SignedCubicTaylorGrid

/-!
# Read an actual periodic coarse grid after exact cubic scaling

Coarse indices sample the original fine body at multiples of its stored
stride. The signed cyclic body multiplies every rounded sample by N³.
This accepts the normalized third-difference bound without rounding its
numerator. After the periodic range theorem, cancel the same N³ and read
the displacement back to projections of the original Gaussian samples.
-/

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace LeanProofs.IPRA.Analysis.GaussianDiscretePeriodicGridReadback

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianDiscreteDerivativeRounding (body latticeScale sample_at)
open GaussianSignedObservationGrid (rounded)
open GaussianSignedObservationReadback (realProjection projected_distance)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalHorner (positive_product)
open SignedDiscreteDerivativeOperators (width)
open SignedCubicTaylorGrid (combination)
open PeriodicThirdDifferenceModulo (wrapped third thirdLower third_value)
open PeriodicThirdDifferenceConstancy (band cubicBudget)
open PolynomialBisection (zle_congr zle_scale_cancel)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def factor (N : PTm n) : PTm n := N*(N*N)

def sample (f : PTm 2) (x i : PTm n) : PTm n := inst2 f (i*width x) x

def coarseBody (f : PTm 2) : PTm 2 := sample f (var 1) (var 0)

theorem coarse_at (f : PTm 2) (x i : PTm n) :
    inst2 (coarseBody f) i x = sample f x i := by
  change Syn.subst ![i,x] (inst2 f (var 0*width (var 1)) (var 1)) = _
  rw [subst_inst2]
  simp [sample]

private def scaledTerm (f : PTm 2) : PTm 2 :=
  fstT (var 1)*inst2 f (var 0) (sndT (var 1))

def scaledBody (b : ZB) : ZB := ⟨scaledTerm b.pos,scaledTerm b.neg⟩

private theorem term_at (f : PTm 2) (x C i : PTm n) :
    Γ ⊢[PRAAx] inst2 (scaledTerm f) i (pairT C x) ≐ C*inst2 f i x := by
  have e : inst2 (scaledTerm f) i (pairT C x) =
      fstT (pairT C x)*inst2 f i (sndT (pairT C x)) := by
    change Syn.subst ![i,pairT C x] (fstT (var 1)*inst2 f (var 0) (sndT (var 1))) = _
    rw [LeanProofs.IPRA.PTm.subst_mul,subst_inst2]
    simp
  rw [e]
  exact congrMul (fst_pair _ _) (congrInst2 f (.eqRefl _) (snd_pair _ _))

theorem scaled_at (b : ZB) (x C i : PTm n) :
    ZT.toZ Γ ((scaledBody b).val i (pairT C x)) = ZT.toZ Γ (ZT.ofNat C)*ZT.toZ Γ (b.val i x) := by
  simp only [scaledBody,ZB.toZ_val,ZT.toZ_ofNat,natEq (term_at b.pos x C i),natEq (term_at b.neg x C i),
    Q.mk_mul,map_mul]
  ring

def grid (f : PTm 2) : ZB := wrapped (scaledBody (body (coarseBody f)))

def data (x N : PTm n) : PTm n := PeriodicThirdDifferenceModulo.data (pairT (factor N) x) N

theorem read_at (f : PTm 2) (x N i : PTm n) :
    ZT.toZ Γ ((grid f).val i (data x N)) =
      ZT.toZ Γ (ZT.ofNat (factor N))*ZT.toZ Γ (rounded (sample f x (rem i N)) (latticeScale x)) := by
  have raw := ZT.toZ_eq (PeriodicThirdDifferenceModulo.sample_at (Γ := Γ)
    (scaledBody (body (coarseBody f))) (pairT (factor N) x) N i)
  exact raw.trans (by rw [scaled_at,sample_at,coarse_at])

def wrappedStencil (f : PTm 2) (x N i : PTm n) : ZT n :=
  let r (j : PTm n) := rounded (sample f x (rem j N)) (latticeScale x)
  combination (r i) (r (succ i)) (r (succ (succ i))) (r (succ (succ (succ i))))

theorem third_at (f : PTm 2) (x N i : PTm n) :
    ZT.toZ Γ ((third (grid f)).val i (data x N)) =
      ZT.toZ Γ (ZT.ofNat (factor N)*wrappedStencil f x N i) := by
  simp only [third_value,read_at,wrappedStencil,combination,ZT.toZ_add,ZT.toZ_sub,ZT.toZ_mul,ZT.toZ_ofNat]
  ipra_simps
  ring

theorem projected_distance_of_third_lower (f : PTm 2) (x N i E : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hi : Γ ⊢[PRAAx] le i N)
    (hS : Γ ⊢[PRAAx] le one (latticeScale x))
    (h : Γ ⊢[PRAAx] thirdLower (grid f) (data x N) N E) :
    Γ ⊢[PRAAx] distanceBounded (realProjection (sample f x (rem i N)))
      (realProjection (sample f x (rem zero N))) (num 4*E+two) (latticeScale x) := by
  let C := factor N
  let S := latticeScale x
  let q := sample f x (rem i N)
  let r := sample f x (rem zero N)
  let d := rounded q S-rounded r S
  have pos : Γ ⊢[PRAAx] le one C := positive_product _ _ hN (positive_product _ _ hN hN)
  have span : Γ ⊢[PRAAx] band ((grid f).val i (data x N)-(grid f).val zero (data x N)) (cubicBudget N E) :=
    PeriodicThirdDifferenceModulo.range (scaledBody (body (coarseBody f))) (pairT C x) N E i hN hi h
  have read : ZT.toZ Γ ((grid f).val i (data x N)-(grid f).val zero (data x N)) =
      ZT.toZ Γ (ZT.ofNat C*d) := by
    simp only [ZT.toZ_sub,ZT.toZ_mul,read_at,d,C,S,q,r]
    ring
  have lower : Γ ⊢[PRAAx] zle (ZT.ofNat C*(-ZT.ofNat (num 4*E))) (ZT.ofNat C*d) :=
    zle_congr (by
      simp only [cubicBudget,C,factor,ZT.toZ_mul,ZT.toZ_neg,ZT.toZ_ofNat,Q.mk_mul,map_mul]
      ipra_simps
      ring) read span.andE₁
  have upper : Γ ⊢[PRAAx] zle (ZT.ofNat C*d) (ZT.ofNat C*ZT.ofNat (num 4*E)) :=
    zle_congr read (by
      simp only [cubicBudget,C,factor,ZT.toZ_mul,ZT.toZ_ofNat,Q.mk_mul,map_mul]
      ipra_simps
      ring) span.andE₂
  exact projected_distance q r S (num 4*E) hS (.andI (zle_scale_cancel pos lower) (zle_scale_cancel pos upper))

theorem actual_scaled_periodic_grid_projected_distance_closed (f : PTm 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (let x := var 0
       let N := var 1
       let i := var 2
       let E := var 3
       le one N ⟶ le i N ⟶ le one (latticeScale x) ⟶ thirdLower (grid f) (data x N) N E ⟶
         distanceBounded (realProjection (sample f x (rem i N))) (realProjection (sample f x (rem zero N)))
           (num 4*E+two) (latticeScale x)) :=
  closeUniv 4 (.impI (.impI (.impI (.impI
    (projected_distance_of_third_lower f _ _ _ _ Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianDiscretePeriodicGridReadback
