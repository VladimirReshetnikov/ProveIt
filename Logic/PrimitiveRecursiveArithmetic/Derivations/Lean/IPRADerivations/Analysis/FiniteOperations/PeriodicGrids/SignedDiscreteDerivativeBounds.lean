import IPRADerivations.Analysis.FiniteOperations.PeriodicGrids.SignedDiscreteThirdDerivativeIdentity
import IPRADerivations.Foundations.FiniteCoverAssignment

/-!
# Certified error propagation on signed derivative blocks

A block sum multiplies a common bound by its width. A scaled stride
difference multiplies a two-sided bound by twice the scale. Both
rules apply to the original transformed PR bodies on a specified
finite window.
-/

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace LeanProofs.IPRA.Analysis.SignedDiscreteDerivativeBounds

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open SignedDiscreteDerivativeBlock (slice block slice_at source residual residual_bound)
open SignedDiscreteDerivativeOperators (width divisor delta accumulate delta_at accumulate_at subtract_at)
open SignedDiscreteThirdDerivativeIdentity (defect)
open SignedGridStepBounds (subst_val subst_order neg_order neg_value)
open PeriodicThirdDifferenceConstancy (band band_add band_congr band_neg band_scale subst_band)
open PolynomialBisection (zle_congr)
open PowerSums (sum_le)
open LeanProofs.IPRA.Foundations.FiniteCoverAssignment (constant_sum)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def floorOn (b : ZB) (x L E : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift L) ⟶ zle (-ZT.ofNat (Syn.shift E)) (b.val (var 0) (Syn.shift x)))

def bandOn (b : ZB) (x L E : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift L) ⟶ band (b.val (var 0) (Syn.shift x)) (Syn.shift E))

@[simp] theorem subst_floorOn {m : ℕ} (σ : Fin n → PTm m) (b : ZB) (x L E : PTm n) :
    (floorOn b x L E).subst σ = floorOn b (Syn.subst σ x) (Syn.subst σ L) (Syn.subst σ E) := by
  simp [floorOn,Syn.subst_shift,Syn.shift_subst]

@[simp] theorem subst_bandOn {m : ℕ} (σ : Fin n → PTm m) (b : ZB) (x L E : PTm n) :
    (bandOn b x L E).subst σ = bandOn b (Syn.subst σ x) (Syn.subst σ L) (Syn.subst σ E) := by
  simp [bandOn,Syn.subst_shift,Syn.shift_subst]

theorem floor_at (b : ZB) (x L E i : PTm n)
    (h : Γ ⊢[PRAAx] floorOn b x L E) (hi : Γ ⊢[PRAAx] lt i L) :
    Γ ⊢[PRAAx] zle (-ZT.ofNat E) (b.val i x) := by
  have u : Γ ⊢[PRAAx] lt i L ⟶ zle (-ZT.ofNat E) (b.val i x) := by
    simpa only [floorOn,Fm.subst_imp,subst_lt,subst_order,subst_val,ZT.subst_neg,ZT.subst_ofNat,
      Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE i
  exact .impE u hi

theorem band_at (b : ZB) (x L E i : PTm n)
    (h : Γ ⊢[PRAAx] bandOn b x L E) (hi : Γ ⊢[PRAAx] lt i L) :
    Γ ⊢[PRAAx] band (b.val i x) E := by
  have u : Γ ⊢[PRAAx] lt i L ⟶ band (b.val i x) E := by
    simpa only [bandOn,Fm.subst_imp,subst_lt,subst_band,subst_val,Syn.subst_var,Syn.inst_zero,
      Syn.subst_inst_shift] using h.allE i
  exact .impE u hi

private theorem sum_order (b c : ZB) (x y M : PTm n)
    (h : Γ ⊢[PRAAx] .all (lt (var 0) (Syn.shift M) ⟶
      zle (b.val (var 0) (Syn.shift x)) (c.val (var 0) (Syn.shift y)))) :
    Γ ⊢[PRAAx] zle (b.sum M x) (c.sum M y) := by
  have hs : Γ ⊢[PRAAx] le (ap2 (sumF (mixB b.pos c.neg)) M (pairT x y))
      (ap2 (sumF (mixB b.neg c.pos)) M (pairT x y)) := by
    refine sum_le _ _ _ _ (.allI (.impI ?_))
    rw [shift_pairT]
    have raw : (lt (var 0) (Syn.shift M) :: Γ.map Fm.shift) ⊢[PRAAx]
        zle (b.val (var 0) (Syn.shift x)) (c.val (var 0) (Syn.shift y)) :=
      .impE h.allOpen.wk Prf.hyp0
    exact le_congr (mix_at _ _ _ _ _).eqSymm
      ((add_comm _ _).eqTrans (mix_at _ _ _ _ _).eqSymm) raw
  exact le_congr (sum_mix _ _ _ _ _)
    ((sum_mix _ _ _ _ _).eqTrans (add_comm _ _)) hs

private def constantBody : ZB := ZB.ofNat (var 1)

private theorem constant_at (M j : PTm n) :
    ZT.toZ Γ (constantBody.val j M) = ZT.toZ Γ (ZT.ofNat M) := by
  simp [constantBody,ZT.toZ,ZB.val,ZB.ofNat,inst2,ZT.ofNat]

private theorem constant_total (M E : PTm n) :
    ZT.toZ Γ (constantBody.sum M E) = ZT.toZ Γ (ZT.ofNat (M*E)) := by
  rw [constantBody,ZB.toZ_sum_ofNat,ZT.toZ_ofNat,natEq (constant_sum M E)]

private theorem in_block (i j M L : PTm n) (hj : Γ ⊢[PRAAx] lt j M)
    (h : Γ ⊢[PRAAx] le (i+M) L) : Γ ⊢[PRAAx] lt (i+j) L := by
  have moved : Γ ⊢[PRAAx] le (i+succ j) (i+M) :=
    le_congr (add_comm (succ j) i) (add_comm M i) (add_le_add_right i hj)
  exact le_trans (le_congr (add_succ i j) (.eqRefl _) moved) h

theorem block_floor (b : ZB) (x L E i M : PTm n)
    (h : Γ ⊢[PRAAx] floorOn b x L E) (hi : Γ ⊢[PRAAx] le (i+M) L) :
    Γ ⊢[PRAAx] zle (-ZT.ofNat (M*E)) (block b x i M) := by
  apply zle_congr (by rw [ZB.toZ_sum_neg,constant_total,ZT.toZ_neg]) rfl
  refine sum_order (-constantBody) (slice b) E (pairT i x) M (.allI (.impI ?_))
  let sh (z : PTm n) := Syn.shift z
  let j : PTm (n+1) := var 0
  let Δ := lt j (sh M) :: Γ.map Fm.shift
  have p : Δ ⊢[PRAAx] floorOn b (sh x) (sh L) (sh E) := by
    simpa only [Δ,sh,Fm.shift,Syn.shift,subst_floorOn] using h.shift.wk
  have w : Δ ⊢[PRAAx] le (sh i+sh M) (sh L) := by
    simpa only [Δ,sh,Fm.shift,Syn.shift,subst_le,LeanProofs.IPRA.PTm.subst_add] using hi.shift.wk
  rw [shift_pairT]
  exact zle_congr (by rw [neg_value,constant_at,ZT.toZ_neg])
    (slice_at (Γ := Δ) b (sh x) (sh i) j).symm
    (floor_at b (sh x) (sh L) (sh E) (sh i+j) p (in_block _ _ _ _ Prf.hyp0 w))

theorem block_band (b : ZB) (x L E i M : PTm n)
    (h : Γ ⊢[PRAAx] bandOn b x L E) (hi : Γ ⊢[PRAAx] le (i+M) L) :
    Γ ⊢[PRAAx] band (block b x i M) (M*E) := by
  have floor : Γ ⊢[PRAAx] floorOn b x L E :=
    .allI (.impI ((Prf.impE h.allOpen.wk Prf.hyp0).andE₁))
  have ceiling : Γ ⊢[PRAAx] floorOn (-b) x L E := by
    refine .allI (.impI ?_)
    have r := neg_order ((Prf.impE h.allOpen.wk Prf.hyp0).andE₂)
    exact zle_congr rfl (by rw [neg_value,ZT.toZ_neg]) r
  have up := neg_order (block_floor (-b) x L E i M ceiling hi)
  have neg : slice (-b) = -slice b := rfl
  exact .andI (block_floor b x L E i M floor hi)
    (zle_congr (by simp only [block,neg,ZT.toZ_neg,ZB.toZ_sum_neg,neg_neg])
      (by simp only [ZT.toZ_neg,neg_neg]) up)

theorem delta_band (b : ZB) (x L E i : PTm n)
    (h : Γ ⊢[PRAAx] bandOn b x L E) (hi : Γ ⊢[PRAAx] lt (i+width x) L) :
    Γ ⊢[PRAAx] band ((delta b).val i x) (divisor x*(two*E)) := by
  have a := band_at b x L E i h (lt_of_le_of_lt (le_add_right _ _) hi)
  have c := band_at b x L E (i+width x) h hi
  refine band_congr ?_ (by ipra_ring) (band_scale (divisor x) (band_add c (band_neg a)))
  rw [delta_at]
  simp only [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_neg]
  ring

theorem defect_band (b g : ZB) (x L E i : PTm n)
    (h : Γ ⊢[PRAAx] source b g x L (divisor x) E) (hi : Γ ⊢[PRAAx] le (i+width x) L) :
    Γ ⊢[PRAAx] band ((defect b g).val i x) (width x*E) := by
  have raw := residual_bound b g x L i (divisor x) E (width x) h hi
  have e : ZT.toZ Γ (residual b g x i (divisor x) (width x)) = ZT.toZ Γ ((defect b g).val i x) := by
    simp only [residual,defect,subtract_at,delta_at,accumulate_at,ZT.toZ_sub,ZT.toZ_mul]
  exact band_congr e (.eqRefl _) raw

end LeanProofs.IPRA.Analysis.SignedDiscreteDerivativeBounds
