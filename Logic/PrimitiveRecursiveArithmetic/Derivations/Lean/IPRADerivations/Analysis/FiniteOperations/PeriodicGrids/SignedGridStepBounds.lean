import IPRADerivations.Foundations.SignedSums
import IPRADerivations.Analysis.Polynomials.PolynomialBisection

/-!
# Signed step bounds on finite grids

A lower bound for each adjacent increment on an actual signed body
gives the corresponding lower bound across any subinterval. The
upper bound follows by negating the same body.
-/

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace LeanProofs.IPRA.Analysis.SignedGridStepBounds

open_ipra
open PolynomialBisection (slack zle_add zle_congr zle_refl zle_trans)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def nextBody (b : PTm 2) : PTm 2 := inst2 b (succ (var 0)) (var 1)
def difference (b : ZB) : ZB :=
  ⟨addBody (nextBody b.pos) b.neg, addBody (nextBody b.neg) b.pos⟩

@[simp] theorem subst_val {m : ℕ} (σ : Fin n → PTm m) (b : ZB) (i x : PTm n) :
    (b.val i x).subst σ = b.val (Syn.subst σ i) (Syn.subst σ x) := by simp [ZB.val,ZT.subst]

@[simp] theorem subst_order {m : ℕ} (σ : Fin n → PTm m) (u v : ZT n) :
    (zle u v).subst σ = zle (u.subst σ) (v.subst σ) := by simp [zle,ZT.subst]

private theorem next_at (b : PTm 2) (i x : PTm n) :
    inst2 (nextBody b) i x = inst2 b (succ i) x := by
  change Syn.subst ![i,x] (inst2 b (succ (var 0)) (var 1)) = _
  rw [subst_inst2]
  rfl

theorem difference_value (b : ZB) (i x : PTm n) :
    ZT.toZ Γ ((difference b).val i x) = ZT.toZ Γ (b.val (succ i) x)-ZT.toZ Γ (b.val i x) := by
  simp only [difference,ZB.toZ_val,inst2_addBody,next_at,Q.mk_add,map_add]
  ring

theorem neg_value (b : ZB) (i x : PTm n) :
    ZT.toZ Γ ((-b).val i x) = -ZT.toZ Γ (b.val i x) := by
  change Groth.ι (IPRA.Q.mk Γ (inst2 b.neg i x)) - Groth.ι (IPRA.Q.mk Γ (inst2 b.pos i x)) = _
  rw [ZB.toZ_val]
  ring

theorem neg_order {u v : ZT n} (h : Γ ⊢[PRAAx] zle u v) : Γ ⊢[PRAAx] zle (-v) (-u) := by
  have e := zle_toZ h
  apply zle_of_toZ (slack u v)
  simp only [ZT.toZ_neg,slack]
  linear_combination e

def liftZT (c : ZT n) : ZT (n+1) := ⟨Syn.shift c.pos,Syn.shift c.neg⟩

@[simp] theorem subst_liftZT {m : ℕ} (σ : Fin n → PTm m) (c : ZT n) :
    (liftZT c).subst (Syn.up σ) = liftZT (c.subst σ) := by
  cases c
  simp only [liftZT,ZT.subst,Syn.subst_shift,Syn.shift_subst,Syn.up_succ]

@[simp] theorem inst_liftZT (i : PTm n) (c : ZT n) :
    (liftZT c).subst (Syn.inst i) = c := by
  cases c
  simp only [liftZT,ZT.subst,Syn.subst_inst_shift]

@[simp] theorem repl_liftZT (i : PTm (n+1)) (c : ZT n) :
    (liftZT c).subst (Syn.repl i) = liftZT c := by
  cases c
  simp only [liftZT,ZT.subst,subst_repl_shift]

theorem read_index (b : ZB) (x : PTm n) {i j : PTm n} (h : Γ ⊢[PRAAx] i ≐ j) :
    ZT.toZ Γ (b.val i x) = ZT.toZ Γ (b.val j x) := by
  simp only [ZB.toZ_val]
  rw [natEq (congrInst2 b.pos h (.eqRefl x)),natEq (congrInst2 b.neg h (.eqRefl x))]

def lowerSteps (b : ZB) (x N : PTm n) (c : ZT n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift N) ⟶
    zle (b.val (var 0) (Syn.shift x)+liftZT c) (b.val (succ (var 0)) (Syn.shift x)))

def upperSteps (b : ZB) (x N : PTm n) (c : ZT n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift N) ⟶
    zle (b.val (succ (var 0)) (Syn.shift x)) (b.val (var 0) (Syn.shift x)+liftZT c))

@[simp] theorem subst_lowerSteps {m : ℕ} (σ : Fin n → PTm m) (b : ZB) (x N : PTm n) (c : ZT n) :
    (lowerSteps b x N c).subst σ = lowerSteps b (Syn.subst σ x) (Syn.subst σ N) (c.subst σ) := by
  simp only [lowerSteps,Fm.subst_all,Fm.subst_imp,subst_lt,subst_order,ZT.subst_add,
    subst_val,subst_liftZT,Syn.subst_var,Syn.up_zero,ConciseIPRA.PTm.subst_succ,
    Syn.subst_shift,Syn.shift_subst,Syn.up_succ]

theorem lower_at (b : ZB) (x N i : PTm n) (c : ZT n)
    (h : Γ ⊢[PRAAx] lowerSteps b x N c) (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] zle (b.val i x+c) (b.val (succ i) x) := by
  have read := h.allE i
  have inst : Γ ⊢[PRAAx] lt i N ⟶ zle (b.val i x+c) (b.val (succ i) x) := by
    simpa only [lowerSteps,Fm.subst_imp,subst_lt,subst_order,ZT.subst_add,inst_liftZT,subst_val,
      Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,ConciseIPRA.PTm.subst_succ] using read
  exact .impE inst hi

private def spanLaw (b : ZB) (x N i k : PTm n) (c : ZT n) : Fm PTm n :=
  le (i+k) N ⟶ zle (b.val i x+ZT.ofNat k*c) (b.val (i+k) x)

@[simp] private theorem subst_spanLaw {m : ℕ} (σ : Fin n → PTm m) (b : ZB) (x N i k : PTm n) (c : ZT n) :
    (spanLaw b x N i k c).subst σ = spanLaw b (Syn.subst σ x) (Syn.subst σ N)
      (Syn.subst σ i) (Syn.subst σ k) (c.subst σ) := by simp [spanLaw]

private theorem span_zero (b : ZB) (x N i : PTm n) (c : ZT n) :
    Γ ⊢[PRAAx] spanLaw b x N i zero c := by
  refine .impI ?_
  exact zle_congr (by simp) (read_index b x (add_zero i).eqSymm) (zle_refl (b.val i x))

private theorem span_step (b : ZB) (x N i k : PTm n) (c : ZT n)
    (h : Γ ⊢[PRAAx] lowerSteps b x N c) (ih : Γ ⊢[PRAAx] spanLaw b x N i k c) :
    Γ ⊢[PRAAx] spanLaw b x N i (succ k) c := by
  refine .impI ?_
  have edge : le (i+succ k) N :: Γ ⊢[PRAAx] lt (i+k) N :=
    le_congr (add_succ i k) (.eqRefl _) Prf.hyp0
  have old := Prf.impE ih.wk (le_of_lt edge)
  have next := lower_at b x N (i+k) c h.wk edge
  have move := zle_trans (zle_add old (zle_refl c)) next
  exact zle_congr (by simp only [ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat]; ipra_simps; ring)
    (read_index b x (add_succ i k).eqSymm) move

theorem lower_span (b : ZB) (x N i k : PTm n) (c : ZT n)
    (h : Γ ⊢[PRAAx] lowerSteps b x N c) (hk : Γ ⊢[PRAAx] le (i+k) N) :
    Γ ⊢[PRAAx] zle (b.val i x+ZT.ofNat k*c) (b.val (i+k) x) := by
  let sh (u : PTm n) := Syn.shift u
  have steps : Γ.map Fm.shift ⊢[PRAAx] lowerSteps b (sh x) (sh N) (liftZT c) := by
    simpa [sh,Fm.shift,Syn.shift,liftZT,ZT.subst] using h.shift
  have all : Γ ⊢[PRAAx] .all (spanLaw b (sh x) (sh N) (sh i) (var 0) (liftZT c)) := by
    refine PRA.qfInd _ ⟨le_QF _ _, le_QF _ _⟩ ?_ ?_
    · simpa only [subst_spanLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,inst_liftZT,sh] using
        span_zero (Γ := Γ) b x N i c
    · simp only [subst_spanLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift,repl_liftZT,sh]
      exact span_step b _ _ _ _ _ steps.wk Prf.hyp0
  have selected : Γ ⊢[PRAAx] spanLaw b x N i k c := by
    simpa only [subst_spanLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,inst_liftZT,sh] using all.allE k
  exact .impE selected hk

theorem upper_span (b : ZB) (x N i k : PTm n) (c : ZT n)
    (h : Γ ⊢[PRAAx] upperSteps b x N c) (hk : Γ ⊢[PRAAx] le (i+k) N) :
    Γ ⊢[PRAAx] zle (b.val (i+k) x) (b.val i x+ZT.ofNat k*c) := by
  have negSteps : Γ ⊢[PRAAx] lowerSteps (-b) x N (-c) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
    let cu := liftZT c
    have step : Δ ⊢[PRAAx] zle (b.val (succ (var 0)) (Syn.shift x)) (b.val (var 0) (Syn.shift x)+cu) :=
      .impE h.allOpen.wk Prf.hyp0
    refine zle_congr ?_ ?_ (neg_order step)
    · simp only [ZT.toZ_neg,ZT.toZ_add,neg_value,cu,show liftZT (-c) = -liftZT c from rfl]
      ring
    · simp only [ZT.toZ_neg,neg_value]
  have bound := neg_order (lower_span (-b) x N i k (-c) negSteps hk)
  refine zle_congr ?_ ?_ bound
  · simp only [ZT.toZ_neg,neg_value,neg_neg]
  · simp only [ZT.toZ_neg,ZT.toZ_add,ZT.toZ_mul,neg_value]
    ring

end LeanProofs.IPRA.Analysis.SignedGridStepBounds
