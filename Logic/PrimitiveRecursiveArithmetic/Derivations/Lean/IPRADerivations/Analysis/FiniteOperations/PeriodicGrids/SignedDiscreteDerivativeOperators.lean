import IPRADerivations.Analysis.FiniteOperations.PeriodicGrids.SignedDiscreteDerivativeBlock
import IPRADerivations.Foundations.SignedSumScale

/-!
# Block sums commute with the scaled stride difference

The persistent data encode the positive stride and the derivative
scale. All transformed bodies use that same data and the original
signed observations. The commutation identity is exact, including
empty stride, and uses finite signed sum congruence and scaling.
-/

set_option autoImplicit false
set_option maxHeartbeats 1450000

namespace LeanProofs.IPRA.Analysis.SignedDiscreteDerivativeOperators

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open SignedDiscreteDerivativeBlock (sliceBody slice block slice_at)
open SignedGridStepBounds (neg_value read_index)
open LeanProofs.IPRA.Foundations.SignedSumScale (sum_scale)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def width (x : PTm n) : PTm n := fstT x
def divisor (x : PTm n) : PTm n := fstT (sndT x)

def subtract (b c : ZB) : ZB := b + -c

def shiftBody (b : PTm 2) : PTm 2 := inst2 b (var 0+width (var 1)) (var 1)
def strideShift (b : ZB) : ZB := ⟨shiftBody b.pos,shiftBody b.neg⟩
def difference (b : ZB) : ZB := strideShift b + -b
def weight (b : ZB) : ZB := ⟨divisor (var 1)*b.pos,divisor (var 1)*b.neg⟩
def delta (b : ZB) : ZB := weight (difference b)

def sumBody (b : PTm 2) : PTm 2 :=
  ap2 (sumF (sliceBody b)) (width (var 1)) (pairT (var 0) (var 1))
def accumulate (b : ZB) : ZB := ⟨sumBody b.pos,sumBody b.neg⟩

@[simp] theorem subst_width {m : ℕ} (σ : Fin n → PTm m) (x : PTm n) :
    Syn.subst σ (width x) = width (Syn.subst σ x) := by simp [width]
@[simp] theorem subst_divisor {m : ℕ} (σ : Fin n → PTm m) (x : PTm n) :
    Syn.subst σ (divisor x) = divisor (Syn.subst σ x) := by simp [divisor]

theorem add_at (b c : ZB) (i x : PTm n) :
    ZT.toZ Γ ((b+c).val i x) = ZT.toZ Γ (b.val i x)+ZT.toZ Γ (c.val i x) := by
  show ZT.toZ Γ ((⟨addBody b.pos c.pos,addBody b.neg c.neg⟩ : ZB).val i x) = _
  simp only [ZB.toZ_val,inst2_addBody,Q.mk_add,map_add]
  ring

theorem subtract_at (b c : ZB) (x i : PTm n) :
    ZT.toZ Γ ((subtract b c).val i x) = ZT.toZ Γ (b.val i x)-ZT.toZ Γ (c.val i x) := by
  rw [subtract,add_at,neg_value,sub_eq_add_neg]

theorem shifted_at (b : ZB) (x i : PTm n) :
    ZT.toZ Γ ((strideShift b).val i x) = ZT.toZ Γ (b.val (i+width x) x) := by
  have at' (a : PTm 2) : inst2 (shiftBody a) i x = inst2 a (i+width x) x := by
    change Syn.subst ![i,x] (shiftBody a) = _
    rw [shiftBody,subst_inst2]
    simp
  simp only [ZB.toZ_val,strideShift,at']

theorem difference_at (b : ZB) (x i : PTm n) :
    ZT.toZ Γ ((difference b).val i x) = ZT.toZ Γ (b.val (i+width x) x)-ZT.toZ Γ (b.val i x) := by
  rw [difference,add_at,shifted_at,neg_value,sub_eq_add_neg]

theorem weighted_at (b : ZB) (x i : PTm n) :
    ZT.toZ Γ ((weight b).val i x) = ZT.toZ Γ (ZT.ofNat (divisor x))*ZT.toZ Γ (b.val i x) := by
  have e (a : PTm 2) : inst2 (divisor (var 1)*a) i x = divisor x*inst2 a i x := by
    change Syn.subst ![i,x] (divisor (var 1)*a) = _
    simp [inst2]
  simp only [ZB.toZ_val,weight,e,ZT.toZ_ofNat,Q.mk_mul,map_mul]
  ring

theorem delta_at (b : ZB) (x i : PTm n) :
    ZT.toZ Γ ((delta b).val i x) =
      ZT.toZ Γ (ZT.ofNat (divisor x))*(ZT.toZ Γ (b.val (i+width x) x)-ZT.toZ Γ (b.val i x)) := by
  rw [delta,weighted_at,difference_at]

theorem accumulate_at (b : ZB) (x i : PTm n) :
    ZT.toZ Γ ((accumulate b).val i x) = ZT.toZ Γ (block b x i (width x)) := by
  have e (a : PTm 2) : inst2 (sumBody a) i x = ap2 (sumF (sliceBody a)) (width x) (pairT i x) := by
    simp [inst2,sumBody]
  simp only [accumulate,ZB.toZ_val,e,block,ZB.toZ_sum,slice]

private def mixSigned (b c : ZB) : ZB := ⟨mixB b.pos c.pos,mixB b.neg c.neg⟩

private theorem mix_value (b c : ZB) (x y j : PTm n) :
    ZT.toZ Γ ((mixSigned b c).val j (pairT x y)) = ZT.toZ Γ (b.val j x)+ZT.toZ Γ (c.val j y) := by
  have ep := natEq (mix_at (Γ := Γ) b.pos c.pos j x y)
  have en := natEq (mix_at (Γ := Γ) b.neg c.neg j x y)
  simp only [mixSigned,ZB.toZ_val]
  simp only [Q.mk_add,map_add] at ep en
  linear_combination ep-en

private theorem mix_sum (b c : ZB) (x y M : PTm n) :
    ZT.toZ Γ ((mixSigned b c).sum M (pairT x y)) = ZT.toZ Γ (b.sum M x)+ZT.toZ Γ (c.sum M y) := by
  have ep := natEq (sum_mix (Γ := Γ) b.pos c.pos M x y)
  have en := natEq (sum_mix (Γ := Γ) b.neg c.neg M x y)
  simp only [mixSigned,ZB.toZ_sum]
  simp only [Q.mk_add,map_add] at ep en
  linear_combination ep-en

theorem block_difference (b : ZB) (x i M : PTm n) :
    ZT.toZ Γ (block (difference b) x i M) =
      ZT.toZ Γ (block b x (i+width x) M)-ZT.toZ Γ (block b x i M) := by
  let P := pairT (i+width x) x
  let Q := pairT i x
  have e := ZB.toZ_sum_congr (Γ := Γ) (slice (difference b)) (mixSigned (slice b) (-slice b))
    Q (pairT P Q) M (by
      refine .allI (.impI ?_)
      let X := Syn.shift x
      let I := Syn.shift i
      let j : PTm (n+1) := var 0
      let Δ := lt j (Syn.shift M) :: Γ.map Fm.shift
      apply ZT.derive
      have hs : Syn.shift (i+width x) = I+width X := by simp [I,X,Syn.shift]
      simp only [P,Q,shift_pairT,hs]
      rw [slice_at,difference_at,mix_value,neg_value,slice_at,slice_at]
      have h : Δ ⊢[PRAAx] (I+j)+width X ≐ (I+width X)+j := by ipra_ring
      rw [read_index b X h]
      ring)
  exact e.trans (by rw [mix_sum,ZB.toZ_sum_neg]; rfl)

theorem block_weight (b : ZB) (x i M : PTm n) :
    ZT.toZ Γ (block (weight b) x i M) =
      ZT.toZ Γ (ZT.ofNat (divisor x))*ZT.toZ Γ (block b x i M) := by
  apply sum_scale
  refine .allI (.impI ?_)
  apply ZT.derive
  have hd : (ZT.ofNat (divisor x)).subst (fun j => var j.succ) =
      ZT.ofNat (divisor (Syn.shift x)) := by simp [Syn.shift]
  simp only [shift_pairT,hd,ZT.toZ_mul,slice_at,weighted_at]

theorem accumulate_delta (b : ZB) (x i : PTm n) :
    ZT.toZ Γ ((accumulate (delta b)).val i x) = ZT.toZ Γ ((delta (accumulate b)).val i x) := by
  rw [delta_at,accumulate_at,accumulate_at,accumulate_at,delta,block_weight,block_difference]

theorem block_subtract (b c : ZB) (x i M : PTm n) :
    ZT.toZ Γ (block (subtract b c) x i M) = ZT.toZ Γ (block b x i M)-ZT.toZ Γ (block c x i M) := by
  have e := ZB.toZ_sum_congr (Γ := Γ) (slice (subtract b c)) (slice b + -slice c)
    (pairT i x) (pairT i x) M (by
      refine .allI (.impI ?_)
      apply ZT.derive
      rw [shift_pairT,slice_at,subtract_at,add_at,neg_value,slice_at,slice_at,sub_eq_add_neg])
  exact e.trans (by rw [ZB.toZ_sum_add,ZB.toZ_sum_neg]; rfl)

theorem delta_subtract (b c : ZB) (x i : PTm n) :
    ZT.toZ Γ ((delta (subtract b c)).val i x) =
      ZT.toZ Γ ((delta b).val i x)-ZT.toZ Γ ((delta c).val i x) := by
  simp only [delta_at,subtract_at]
  ring

theorem accumulate_subtract (b c : ZB) (x i : PTm n) :
    ZT.toZ Γ ((accumulate (subtract b c)).val i x) =
      ZT.toZ Γ ((accumulate b).val i x)-ZT.toZ Γ ((accumulate c).val i x) := by
  simp only [accumulate_at,block_subtract]

theorem accumulate_congr (b c : ZB)
    (h : ∀ {m : ℕ} {Δ : List (Fm PTm m)} (x i : PTm m),
      ZT.toZ Δ (b.val i x) = ZT.toZ Δ (c.val i x))
    (x i : PTm n) :
    ZT.toZ Γ ((accumulate b).val i x) = ZT.toZ Γ ((accumulate c).val i x) := by
  rw [accumulate_at,accumulate_at]
  apply ZB.toZ_sum_congr
  refine .allI (.impI ?_)
  apply ZT.derive
  rw [shift_pairT,slice_at,slice_at]
  exact h _ _

theorem delta_congr (b c : ZB)
    (h : ∀ {m : ℕ} {Δ : List (Fm PTm m)} (x i : PTm m),
      ZT.toZ Δ (b.val i x) = ZT.toZ Δ (c.val i x))
    (x i : PTm n) :
    ZT.toZ Γ ((delta b).val i x) = ZT.toZ Γ ((delta c).val i x) := by
  rw [delta_at,delta_at,h x (i+width x),h x i]

end LeanProofs.IPRA.Analysis.SignedDiscreteDerivativeOperators
