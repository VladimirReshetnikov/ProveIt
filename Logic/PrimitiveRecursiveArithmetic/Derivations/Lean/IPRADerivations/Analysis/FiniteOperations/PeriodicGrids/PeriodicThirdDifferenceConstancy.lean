import IPRADerivations.Analysis.FiniteOperations.PeriodicGrids.SignedGridStepBounds

/-!
# Constancy from signed third differences on a periodic grid

The grid and its first two differences return to their starting
values. If every third difference is at least −δ, one traversal
bounds the second difference, and a second traversal bounds the first.
The original grid values then differ by at most 4N³δ from the start.
-/

set_option autoImplicit false
set_option maxHeartbeats 1700000

namespace LeanProofs.IPRA.Analysis.PeriodicThirdDifferenceConstancy

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open PolynomialBisection (slack zle_add zle_antisym zle_congr zle_refl zle_scale_cancel zle_trans)
open SignedGridStepBounds
  (difference difference_value liftZT lowerSteps upperSteps lower_span upper_span neg_order read_index)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem natural_order {a b : PTm n} (h : Γ ⊢[PRAAx] le a b) :
    Γ ⊢[PRAAx] zle (ZT.ofNat a) (ZT.ofNat b) :=
  le_congr (add_zero _).eqSymm (add_zero _).eqSymm h

private theorem add_cancel {u v c : ZT n} (h : Γ ⊢[PRAAx] zle (u+c) (v+c)) :
    Γ ⊢[PRAAx] zle u v := by
  have e := zle_toZ h
  apply zle_of_toZ (slack (u+c) (v+c))
  simp only [slack,ZT.toZ_add] at e ⊢
  linear_combination e

private theorem lift_is_subst (u : ZT n) : liftZT u = u.subst (fun i => var i.succ) := rfl

private theorem add_difference (b : ZB) (i x : PTm n) :
    ZT.toZ Γ (b.val i x + (difference b).val i x) = ZT.toZ Γ (b.val (succ i) x) := by
  rw [ZT.toZ_add, difference_value]
  ring

def periodic (b : ZB) (x N : PTm n) : Fm PTm n :=
  ZT.eq (b.val N x) (b.val zero x)

@[simp] theorem subst_periodic {m : ℕ} (σ : Fin n → PTm m) (b : ZB) (x N : PTm n) :
    (periodic b x N).subst σ = periodic b (Syn.subst σ x) (Syn.subst σ N) := by simp [periodic]

def band (u : ZT n) (D : PTm n) : Fm PTm n := zle (-ZT.ofNat D) u ⋏ zle u (ZT.ofNat D)

def derivativeBand (b : ZB) (x N D : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift N) ⟶ band ((difference b).val (var 0) (Syn.shift x)) (Syn.shift D))

private theorem relative_band (d : ZB) (x N E i : PTm n) (hp : Γ ⊢[PRAAx] periodic d x N)
    (h : Γ ⊢[PRAAx] lowerSteps d x N (-ZT.ofNat E)) (hi : Γ ⊢[PRAAx] le i N) :
    Γ ⊢[PRAAx] zle (d.val zero x-ZT.ofNat (N*E)) (d.val i x) ⋏
      zle (d.val i x) (d.val zero x+ZT.ofNat (N*E)) := by
  let a := d.val zero x
  let w := d.val i x
  let c := -ZT.ofNat E
  let j := monus N i
  have lo := lower_span d x N zero i c h (le_congr (zero_add i).eqSymm (.eqRefl _) hi)
  have leftBound : Γ ⊢[PRAAx] zle (a-ZT.ofNat (i*E)) w := by
    refine zle_congr ?_ (read_index d x (zero_add i)) lo
    simp only [c,a,ZT.toZ_add,ZT.toZ_mul,ZT.toZ_sub,ZT.toZ_neg,ZT.toZ_ofNat,Q.mk_mul,map_mul]
    ring
  have grow := natural_order (mul_le_mul_right E hi)
  have leftPay : Γ ⊢[PRAAx] zle (a-ZT.ofNat (N*E)) (a-ZT.ofNat (i*E)) :=
    zle_add (zle_refl a) (neg_order grow)
  have endpoint := eq_add_of_le hi
  have hi' : Γ ⊢[PRAAx] le (i+j) N := le_congr endpoint (.eqRefl _) (le_refl N)
  have hj : Γ ⊢[PRAAx] le j N := le_congr (.eqRefl _) endpoint.eqSymm (le_add_left j i)
  have tail := lower_span d x N i j c h hi'
  have tailBound : Γ ⊢[PRAAx] zle (w-ZT.ofNat (j*E)) a := by
    refine zle_congr ?_ ((read_index d x endpoint.eqSymm).trans (ZT.toZ_eq hp)) tail
    simp only [c,w,ZT.toZ_add,ZT.toZ_mul,ZT.toZ_sub,ZT.toZ_neg,ZT.toZ_ofNat,Q.mk_mul,map_mul]
    ring
  have rightBound : Γ ⊢[PRAAx] zle w (a+ZT.ofNat (j*E)) :=
    zle_congr (by simp only [ZT.toZ_add,ZT.toZ_sub]; ring) rfl
      (zle_add tailBound (zle_refl (ZT.ofNat (j*E))))
  exact .andI (zle_trans leftPay leftBound)
    (zle_trans rightBound (zle_add (zle_refl a) (natural_order (mul_le_mul_right E hj))))

private theorem lower_balance (b : ZB) (x N : PTm n) (c : ZT n) (hN : Γ ⊢[PRAAx] le one N)
    (hp : Γ ⊢[PRAAx] periodic b x N) (h : Γ ⊢[PRAAx] lowerSteps b x N c) :
    Γ ⊢[PRAAx] zle c (ZT.ofNat zero) := by
  let a := b.val zero x
  let M := ZT.ofNat N
  have raw := lower_span b x N zero N c h (le_congr (zero_add _).eqSymm (.eqRefl _) (le_refl N))
  have endpoint := (read_index b x (zero_add N)).trans (ZT.toZ_eq hp)
  have m := zle_congr rfl endpoint raw
  apply zle_scale_cancel hN
  apply zle_congr rfl (by simp : ZT.toZ Γ (ZT.ofNat zero) = ZT.toZ Γ (M*ZT.ofNat zero))
  exact add_cancel (c := a) (zle_congr (by simp only [ZT.toZ_add]; ring) (by simp [a]) m)

private theorem upper_balance (b : ZB) (x N : PTm n) (c : ZT n) (hN : Γ ⊢[PRAAx] le one N)
    (hp : Γ ⊢[PRAAx] periodic b x N) (h : Γ ⊢[PRAAx] upperSteps b x N c) :
    Γ ⊢[PRAAx] zle (ZT.ofNat zero) c := by
  let a := b.val zero x
  let M := ZT.ofNat N
  have raw := upper_span b x N zero N c h (le_congr (zero_add _).eqSymm (.eqRefl _) (le_refl N))
  have endpoint := (read_index b x (zero_add N)).trans (ZT.toZ_eq hp)
  have m := zle_congr endpoint rfl raw
  apply zle_scale_cancel hN
  apply zle_congr (by simp : ZT.toZ Γ (ZT.ofNat zero) = ZT.toZ Γ (M*ZT.ofNat zero)) rfl
  exact add_cancel (c := a) (zle_congr (by simp [a]) (by simp only [ZT.toZ_add]; ring) m)

private theorem relative_steps (b : ZB) (x N E : PTm n)
    (hp : Γ ⊢[PRAAx] periodic (difference b) x N)
    (h : Γ ⊢[PRAAx] lowerSteps (difference b) x N (-ZT.ofNat E)) :
    let a := (difference b).val zero x
    let d := ZT.ofNat (N*E)
    Γ ⊢[PRAAx] lowerSteps b x N (a-d) ⋏ upperSteps b x N (a+d) := by
  let a := (difference b).val zero x
  let d := ZT.ofNat (N*E)
  let S := Γ.map Fm.shift
  let X := Syn.shift x
  let K := Syn.shift N
  let Q := Syn.shift E
  let i : PTm (n+1) := var 0
  let Δ := lt i K :: S
  have hp' : Δ ⊢[PRAAx] periodic (difference b) X K := by
    simpa only [Δ,S,X,K,Fm.shift,subst_periodic,Syn.shift] using hp.shift.wk
  have h' : Δ ⊢[PRAAx] lowerSteps (difference b) X K (-ZT.ofNat Q) := by
    simpa only [Δ,S,X,K,Q,Fm.shift,SignedGridStepBounds.subst_lowerSteps,ZT.subst_neg,
      ZT.subst_ofNat,Syn.shift] using h.shift.wk
  have raw := relative_band (difference b) X K Q i hp' h' (le_of_lt (Prf.hyp0 : Δ ⊢[PRAAx] lt i K))
  have ha : liftZT a = (difference b).val zero X := by simp [lift_is_subst,a,X,Syn.shift]
  have hd : liftZT d = ZT.ofNat (K*Q) := by simp [lift_is_subst,d,K,Q,Syn.shift]
  have hlo : liftZT (a-d) = (difference b).val zero X-ZT.ofNat (K*Q) := by
    rw [lift_is_subst,ZT.subst_sub,← lift_is_subst,← lift_is_subst,ha,hd]
  have hhi : liftZT (a+d) = (difference b).val zero X+ZT.ofNat (K*Q) := by
    rw [lift_is_subst,ZT.subst_add,← lift_is_subst,← lift_is_subst,ha,hd]
  refine .andI (.allI (.impI ?_)) (.allI (.impI ?_))
  · exact zle_congr (by rw [hlo]) (add_difference (Γ := Δ) b i X)
      (zle_add (zle_refl (b.val i X)) raw.andE₁)
  · exact zle_congr (add_difference (Γ := Δ) b i X) (by rw [hhi])
      (zle_add (zle_refl (b.val i X)) raw.andE₂)

private theorem derivative_bound_at (b : ZB) (x N E i : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hp : Γ ⊢[PRAAx] periodic b x N) (hd : Γ ⊢[PRAAx] periodic (difference b) x N)
    (h : Γ ⊢[PRAAx] lowerSteps (difference b) x N (-ZT.ofNat E)) (hi : Γ ⊢[PRAAx] le i N) :
    Γ ⊢[PRAAx] band ((difference b).val i x) (two*(N*E)) := by
  let a := (difference b).val zero x
  let d := ZT.ofNat (N*E)
  have steps := relative_steps b x N E hd h
  have ha := lower_balance b x N (a-d) hN hp steps.andE₁
  have hb := upper_balance b x N (a+d) hN hp steps.andE₂
  have lo : Γ ⊢[PRAAx] zle (-d) a :=
    zle_congr (by simp only [ZT.toZ_add,ZT.toZ_ofNat,ZT.toZ_neg]; ipra_simps; ring)
      (by simp only [ZT.toZ_add,ZT.toZ_neg]; ring) (zle_add hb (zle_refl (-d)))
  have up : Γ ⊢[PRAAx] zle a d :=
    zle_congr (by simp only [ZT.toZ_add,ZT.toZ_sub]; ring) (by simp)
      (zle_add ha (zle_refl d))
  have r := relative_band (difference b) x N E i hd h hi
  have l := zle_trans (zle_add lo (zle_refl (-d))) r.andE₁
  have u := zle_trans r.andE₂ (zle_add up (zle_refl d))
  exact .andI
    (zle_congr (by simp only [d,ZT.toZ_add,ZT.toZ_neg,ZT.toZ_ofNat,Q.mk_mul,map_mul]; ipra_simps; ring) rfl l)
    (zle_congr rfl (by simp only [d,ZT.toZ_add,ZT.toZ_ofNat,Q.mk_mul,map_mul]; ipra_simps; ring) u)

theorem derivative_bound (b : ZB) (x N E : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hp : Γ ⊢[PRAAx] periodic b x N) (hd : Γ ⊢[PRAAx] periodic (difference b) x N)
    (h : Γ ⊢[PRAAx] lowerSteps (difference b) x N (-ZT.ofNat E)) :
    Γ ⊢[PRAAx] derivativeBand b x N (two*(N*E)) := by
  refine .allI (.impI ?_)
  let sh (u : PTm n) := Syn.shift u
  let i : PTm (n+1) := var 0
  let Δ := lt i (sh N) :: Γ.map Fm.shift
  have n' : Δ ⊢[PRAAx] le one (sh N) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hN.shift.wk
  have p' : Δ ⊢[PRAAx] periodic b (sh x) (sh N) :=
    by simpa only [Δ,sh,Fm.shift,subst_periodic,Syn.shift] using hp.shift.wk
  have d' : Δ ⊢[PRAAx] periodic (difference b) (sh x) (sh N) :=
    by simpa only [Δ,sh,Fm.shift,subst_periodic,Syn.shift] using hd.shift.wk
  have h' : Δ ⊢[PRAAx] lowerSteps (difference b) (sh x) (sh N) (-ZT.ofNat (sh E)) :=
    by simpa only [Δ,sh,Fm.shift,SignedGridStepBounds.subst_lowerSteps,ZT.subst_neg,ZT.subst_ofNat,
      Syn.shift] using h.shift.wk
  simpa only [Δ,i,sh,Syn.shift,two,one,LeanProofs.IPRA.PTm.subst_mul,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    derivative_bound_at b (sh x) (sh N) (sh E) i n' p' d' h'
    (le_of_lt (Prf.hyp0 : Δ ⊢[PRAAx] lt i (sh N)))

theorem band_steps (b : ZB) (x N D : PTm n) (h : Γ ⊢[PRAAx] derivativeBand b x N D) :
    Γ ⊢[PRAAx] lowerSteps b x N (-ZT.ofNat D) ⋏ upperSteps b x N (ZT.ofNat D) := by
  let i : PTm (n+1) := var 0
  let X := Syn.shift x
  let Δ := lt i (Syn.shift N) :: Γ.map Fm.shift
  have raw : Δ ⊢[PRAAx] band ((difference b).val i X) (Syn.shift D) := .impE h.allOpen.wk Prf.hyp0
  refine .andI (.allI (.impI ?_)) (.allI (.impI ?_))
  · exact zle_congr
      (by simp only [i,X,lift_is_subst,ZT.subst_neg,ZT.subst_ofNat,Syn.shift])
      (add_difference (Γ := Δ) b i X)
      (zle_add (zle_refl (b.val i X)) raw.andE₁)
  · exact zle_congr (add_difference (Γ := Δ) b i X)
      (by simp only [i,X,lift_is_subst,ZT.subst_ofNat,Syn.shift])
      (zle_add (zle_refl (b.val i X)) raw.andE₂)

def cubicBudget (N E : PTm n) : PTm n := N*(two*(N*(two*(N*E))))

theorem periodic_range (b : ZB) (x N E i : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hi : Γ ⊢[PRAAx] le i N)
    (h0 : Γ ⊢[PRAAx] periodic b x N) (h1 : Γ ⊢[PRAAx] periodic (difference b) x N)
    (h2 : Γ ⊢[PRAAx] periodic (difference (difference b)) x N)
    (h3 : Γ ⊢[PRAAx] lowerSteps (difference (difference b)) x N (-ZT.ofNat E)) :
    Γ ⊢[PRAAx] band (b.val i x-b.val zero x) (cubicBudget N E) := by
  let a := b.val zero x
  let v := b.val i x
  let D := two*(N*(two*(N*E)))
  have d2 := derivative_bound (difference b) x N E hN h1 h2 h3
  have d1 := derivative_bound b x N (two*(N*E)) hN h0 h1 (band_steps _ _ _ _ d2).andE₁
  have both := band_steps b x N D d1
  have lens : Γ ⊢[PRAAx] le (zero+i) N := le_congr (zero_add i).eqSymm (.eqRefl _) hi
  have budget := natural_order (mul_le_mul_right D hi)
  have low := lower_span b x N zero i (-ZT.ofNat D) both.andE₁ lens
  have high := upper_span b x N zero i (ZT.ofNat D) both.andE₂ lens
  have atEnd := read_index (Γ := Γ) b x (zero_add i)
  have l : Γ ⊢[PRAAx] zle (-ZT.ofNat (i*D)) (v-a) :=
    add_cancel (c := a) (zle_congr
      (by simp only [ZT.toZ_add,ZT.toZ_mul,ZT.toZ_neg,ZT.toZ_ofNat,Q.mk_mul,map_mul]; ring)
      (atEnd.trans (by simp only [v,ZT.toZ_add,ZT.toZ_sub]; ring)) low)
  have u : Γ ⊢[PRAAx] zle (v-a) (ZT.ofNat (i*D)) :=
    add_cancel (c := a) (zle_congr
      (atEnd.trans (by simp only [v,ZT.toZ_add,ZT.toZ_sub]; ring))
      (by simp only [ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat,Q.mk_mul,map_mul]; ring) high)
  exact .andI (zle_trans (neg_order budget) l) (zle_trans u budget)

theorem constant_at (b : ZB) (x N i : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hi : Γ ⊢[PRAAx] le i N)
    (h0 : Γ ⊢[PRAAx] periodic b x N) (h1 : Γ ⊢[PRAAx] periodic (difference b) x N)
    (h2 : Γ ⊢[PRAAx] periodic (difference (difference b)) x N)
    (h3 : Γ ⊢[PRAAx] lowerSteps (difference (difference b)) x N (-ZT.ofNat zero)) :
    Γ ⊢[PRAAx] ZT.eq (b.val i x) (b.val zero x) := by
  have h := periodic_range b x N zero i hN hi h0 h1 h2 h3
  have left : Γ ⊢[PRAAx] zle (ZT.ofNat zero) (b.val i x-b.val zero x) :=
    zle_congr (by simp [cubicBudget]) rfl h.andE₁
  have right : Γ ⊢[PRAAx] zle (b.val i x-b.val zero x) (ZT.ofNat zero) :=
    zle_congr rfl (by simp [cubicBudget]) h.andE₂
  have e := ZT.toZ_eq (zle_antisym right left)
  apply ZT.derive
  simp only [ZT.toZ_sub,ZT.toZ_ofNat,Q.mk_zero,map_zero] at e
  linear_combination e

theorem actual_periodic_third_difference_bound_closed (b : ZB) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (let x := var 0
       let N := var 1
       let E := var 2
       let i := var 3
       le one N ⟶ le i N ⟶ periodic b x N ⟶ periodic (difference b) x N ⟶
         periodic (difference (difference b)) x N ⟶ lowerSteps (difference (difference b)) x N (-ZT.ofNat E) ⟶
           band (b.val i x-b.val zero x) (cubicBudget N E)) :=
  closeUniv 4 (.impI (.impI (.impI (.impI (.impI (.impI
    (periodic_range b _ _ _ _ (Prf.hyp1.wk.wk.wk.wk) (Prf.hyp1.wk.wk.wk) (Prf.hyp1.wk.wk)
      (Prf.hyp1.wk) Prf.hyp1 Prf.hyp0)))))))

theorem actual_periodic_third_difference_constancy_closed (b : ZB) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (let x := var 0
       let N := var 1
       let i := var 2
       le one N ⟶ le i N ⟶ periodic b x N ⟶ periodic (difference b) x N ⟶
         periodic (difference (difference b)) x N ⟶
           lowerSteps (difference (difference b)) x N (-ZT.ofNat zero) ⟶
             ZT.eq (b.val i x) (b.val zero x)) :=
  closeUniv 3 (.impI (.impI (.impI (.impI (.impI (.impI
    (constant_at b _ _ _ (Prf.hyp1.wk.wk.wk.wk) (Prf.hyp1.wk.wk.wk) (Prf.hyp1.wk.wk)
      (Prf.hyp1.wk) Prf.hyp1 Prf.hyp0)))))))

end LeanProofs.IPRA.Analysis.PeriodicThirdDifferenceConstancy
