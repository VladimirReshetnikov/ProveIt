import IPRADerivations.Analysis.FiniteOperations.PeriodicGrids.SignedDiscreteDerivativeOperators
import IPRADerivations.Analysis.FiniteOperations.PeriodicGrids.SignedCubicTaylorGrid

/-!
# Exact third difference from three coded derivative blocks

Write A for the literal block sum and D for the scaled stride
difference. Each residual is D applied to one observation body
minus A applied to the next derivative body. Commutation and signed
linearity give the exact third difference as A³ of the third
derivative plus D², AD, and A² of the three respective residuals.
-/

set_option autoImplicit false
set_option maxHeartbeats 1350000

namespace LeanProofs.IPRA.Analysis.SignedDiscreteThirdDerivativeIdentity

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open SignedDiscreteDerivativeOperators
  (width divisor subtract delta accumulate subtract_at delta_at accumulate_delta
    delta_subtract accumulate_subtract delta_congr accumulate_congr)
open SignedCubicTaylorGrid (combination)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def defect (b g : ZB) : ZB := subtract (delta b) (accumulate g)

def coarseThird (b : ZB) (x i : PTm n) : ZT n :=
  let j := i+width x
  let k := j+width x
  let l := k+width x
  ZT.ofNat (divisor x*(divisor x*divisor x))*
    combination (b.val i x) (b.val j x) (b.val k x) (b.val l x)

theorem coarse_third_at (b : ZB) (x i : PTm n) :
    ZT.toZ Γ ((delta (delta (delta b))).val i x) = ZT.toZ Γ (coarseThird b x i) := by
  simp only [delta_at,coarseThird,combination,ZT.toZ_sub,ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat,
    Q.mk_mul,map_mul]
  ipra_simps
  ring

private theorem first_term (b g : ZB) (x i : PTm n) :
    ZT.toZ Γ ((delta (delta (defect b g))).val i x) =
      ZT.toZ Γ ((delta (delta (delta b))).val i x)-
        ZT.toZ Γ ((accumulate (delta (delta g))).val i x) := by
  calc
    _ = ZT.toZ Γ ((delta (subtract (delta (delta b)) (delta (accumulate g)))).val i x) :=
      delta_congr _ _ (by intro m Δ y j; rw [defect,delta_subtract,subtract_at]) x i
    _ = ZT.toZ Γ ((delta (delta (delta b))).val i x)-
        ZT.toZ Γ ((delta (delta (accumulate g))).val i x) := delta_subtract _ _ x i
    _ = _ := by
      have e := delta_congr (Γ := Γ) (delta (accumulate g)) (accumulate (delta g))
        (fun y j => (accumulate_delta g y j).symm) x i
      rw [e,← accumulate_delta]

private theorem second_term (b g : ZB) (x i : PTm n) :
    ZT.toZ Γ ((accumulate (delta (defect b g))).val i x) =
      ZT.toZ Γ ((accumulate (delta (delta b))).val i x)-
        ZT.toZ Γ ((accumulate (accumulate (delta g))).val i x) := by
  calc
    _ = ZT.toZ Γ ((accumulate (subtract (delta (delta b)) (delta (accumulate g)))).val i x) :=
      accumulate_congr _ _ (by intro m Δ y j; rw [defect,delta_subtract,subtract_at]) x i
    _ = ZT.toZ Γ ((accumulate (delta (delta b))).val i x)-
        ZT.toZ Γ ((accumulate (delta (accumulate g))).val i x) := accumulate_subtract _ _ x i
    _ = _ := by
      rw [accumulate_congr (delta (accumulate g)) (accumulate (delta g))
        (fun y j => (accumulate_delta g y j).symm) x i]

private theorem third_term (b g : ZB) (x i : PTm n) :
    ZT.toZ Γ ((accumulate (accumulate (defect b g))).val i x) =
      ZT.toZ Γ ((accumulate (accumulate (delta b))).val i x)-
        ZT.toZ Γ ((accumulate (accumulate (accumulate g))).val i x) := by
  calc
    _ = ZT.toZ Γ ((accumulate (subtract (accumulate (delta b)) (accumulate (accumulate g)))).val i x) :=
      accumulate_congr _ _ (by intro m Δ y j; rw [defect,accumulate_subtract,subtract_at]) x i
    _ = _ := accumulate_subtract _ _ x i

def decomposition (b g h j : ZB) (x i : PTm n) : ZT n :=
  (accumulate (accumulate (accumulate j))).val i x+
    (delta (delta (defect b g))).val i x+
    (accumulate (delta (defect g h))).val i x+
    (accumulate (accumulate (defect h j))).val i x

theorem third_decomposition (b g h j : ZB) (x i : PTm n) :
    ZT.toZ Γ (coarseThird b x i) = ZT.toZ Γ (decomposition b g h j x i) := by
  rw [← coarse_third_at]
  simp only [decomposition,ZT.toZ_add,first_term,second_term,third_term]
  ring

theorem actual_signed_third_derivative_decomposition_closed (b g h j : ZB) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (ZT.eq (coarseThird b (var 0) (var 1)) (decomposition b g h j (var 0) (var 1))) :=
  closeUniv 2 (ZT.derive (third_decomposition b g h j _ _))

end LeanProofs.IPRA.Analysis.SignedDiscreteThirdDerivativeIdentity
