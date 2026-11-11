import ConciseIPRA.TeqOrder

/-!
# Pairing in `T_eq`

The pairing function is `pair a b = 2 ^ (a + b) + a`.  Since `a < 2 ^ (a + b)`,
the exponent is the binary logarithm of the pair, and the logarithm is a
saturating counter:

  `lstep k v = sel (2 ^ (S v) ∸ k) (S v) v`,  `lgc t k = I(t, 0; v. lstep k v)`,
  `lg w = lgc w w`.

The counter follows its index up to the exponent and then stays there, so
`lg (pair a b) = a + b`, and the projections

  `pfst w = w ∸ 2 ^ (lg w)`,  `psnd w = lg w ∸ pfst w`

satisfy `pfst (pair a b) = a` and `psnd (pair a b) = b` in every context.  No
multiplication is involved.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm

variable {n m : ℕ}

/-- One step of the logarithm counter: increment `v` while `2 ^ (v + 1) ≤ k`. -/
def Tm.lstep (k v : Tm n) : Tm n :=
  Tm.sel (Tm.monus (Tm.pow2 (Tm.succ v)) k) (Tm.succ v) v

/-- The logarithm counter `I(t, 0; v. lstep k v)`. -/
def Tm.lgc (t k : Tm n) : Tm n := Tm.iter t Tm.zero (Tm.lstep (Syn.shift k) (Syn.var 0))

/-- The binary logarithm. -/
def Tm.lg (a : Tm n) : Tm n := Tm.lgc a a

/-- The pairing function `2 ^ (a + b) + a`. -/
def Tm.pair (a b : Tm n) : Tm n := Tm.add (Tm.pow2 (Tm.add a b)) a

/-- The first projection. -/
def Tm.pfst (w : Tm n) : Tm n := Tm.monus w (Tm.pow2 (Tm.lg w))

/-- The second projection. -/
def Tm.psnd (w : Tm n) : Tm n := Tm.monus (Tm.lg w) (Tm.pfst w)

@[simp] theorem Tm.subst_lstep (σ : Fin n → Tm m) (k v : Tm n) :
    Syn.subst σ (Tm.lstep k v) = Tm.lstep (Syn.subst σ k) (Syn.subst σ v) := by
  simp [Tm.lstep]

@[simp] theorem Tm.subst_lgc (σ : Fin n → Tm m) (t k : Tm n) :
    Syn.subst σ (Tm.lgc t k) = Tm.lgc (Syn.subst σ t) (Syn.subst σ k) := by
  simp [Tm.lgc, Syn.subst_up_shift]

@[simp] theorem Tm.subst_lg (σ : Fin n → Tm m) (a : Tm n) :
    Syn.subst σ (Tm.lg a) = Tm.lg (Syn.subst σ a) := by
  simp [Tm.lg]

@[simp] theorem Tm.subst_pair (σ : Fin n → Tm m) (a b : Tm n) :
    Syn.subst σ (Tm.pair a b) = Tm.pair (Syn.subst σ a) (Syn.subst σ b) := by
  simp [Tm.pair]

@[simp] theorem Tm.subst_pfst (σ : Fin n → Tm m) (w : Tm n) :
    Syn.subst σ (Tm.pfst w) = Tm.pfst (Syn.subst σ w) := by
  simp [Tm.pfst]

@[simp] theorem Tm.subst_psnd (σ : Fin n → Tm m) (w : Tm n) :
    Syn.subst σ (Tm.psnd w) = Tm.psnd (Syn.subst σ w) := by
  simp [Tm.psnd]

namespace Q

variable {Γ : List (Fm Tm n)}

/-- The logarithm step on classes. -/
def lstep : Q Γ → Q Γ → Q Γ := op₂ (fun _ => Tm.lstep) Tm.subst_lstep

/-- The logarithm counter on classes. -/
def lgc : Q Γ → Q Γ → Q Γ := op₂ (fun _ => Tm.lgc) Tm.subst_lgc

/-- The binary logarithm on classes. -/
def lg : Q Γ → Q Γ := op₁ (fun _ => Tm.lg) Tm.subst_lg

/-- Pairing on classes. -/
def pair : Q Γ → Q Γ → Q Γ := op₂ (fun _ => Tm.pair) Tm.subst_pair

/-- The first projection on classes. -/
def pfst : Q Γ → Q Γ := op₁ (fun _ => Tm.pfst) Tm.subst_pfst

/-- The second projection on classes. -/
def psnd : Q Γ → Q Γ := op₁ (fun _ => Tm.psnd) Tm.subst_psnd

@[simp] theorem mk_lstep (k v : Tm n) : mk Γ (Tm.lstep k v) = lstep (mk Γ k) (mk Γ v) := rfl
@[simp] theorem mk_lgc (t k : Tm n) : mk Γ (Tm.lgc t k) = lgc (mk Γ t) (mk Γ k) := rfl
@[simp] theorem mk_lg (a : Tm n) : mk Γ (Tm.lg a) = lg (mk Γ a) := rfl
@[simp] theorem mk_pair (a b : Tm n) : mk Γ (Tm.pair a b) = pair (mk Γ a) (mk Γ b) := rfl
@[simp] theorem mk_pfst (w : Tm n) : mk Γ (Tm.pfst w) = pfst (mk Γ w) := rfl
@[simp] theorem mk_psnd (w : Tm n) : mk Γ (Tm.psnd w) = psnd (mk Γ w) := rfl

end Q

namespace Ext

variable {Γ : List (Fm Tm n)} {Γ' : List (Fm Tm m)}

@[simp] theorem map_lstep (e : Ext Γ Γ') (k v : Q Γ) :
    e.map (Q.lstep k v) = Q.lstep (e.map k) (e.map v) :=
  map_op₂ e (fun _ => Tm.lstep) Tm.subst_lstep k v

@[simp] theorem map_lgc (e : Ext Γ Γ') (t k : Q Γ) :
    e.map (Q.lgc t k) = Q.lgc (e.map t) (e.map k) :=
  map_op₂ e (fun _ => Tm.lgc) Tm.subst_lgc t k

@[simp] theorem map_lg (e : Ext Γ Γ') (x : Q Γ) : e.map (Q.lg x) = Q.lg (e.map x) :=
  map_op₁ e (fun _ => Tm.lg) Tm.subst_lg x

@[simp] theorem map_pair (e : Ext Γ Γ') (x y : Q Γ) :
    e.map (Q.pair x y) = Q.pair (e.map x) (e.map y) :=
  map_op₂ e (fun _ => Tm.pair) Tm.subst_pair x y

@[simp] theorem map_pfst (e : Ext Γ Γ') (x : Q Γ) : e.map (Q.pfst x) = Q.pfst (e.map x) :=
  map_op₁ e (fun _ => Tm.pfst) Tm.subst_pfst x

@[simp] theorem map_psnd (e : Ext Γ Γ') (x : Q Γ) : e.map (Q.psnd x) = Q.psnd (e.map x) :=
  map_op₁ e (fun _ => Tm.psnd) Tm.subst_psnd x

end Ext

namespace Q

variable {Γ : List (Fm Tm n)}

/-! ### The logarithm counter -/

theorem lstep_eq (k v : Q Γ) :
    lstep k v = sel (monus (pow2 (succ v)) k) (succ v) v := by
  induction k using Q.ind with | _ a
  induction v using Q.ind with | _ b
  rfl

@[simp] theorem lgc_zero (k : Q Γ) : lgc 0 k = 0 := by
  induction k using Q.ind with | _ a
  exact sound (Teq.iterZero _ _)

@[simp] theorem lgc_succ (t k : Q Γ) : lgc (succ t) k = lstep k (lgc t k) := by
  induction t using Q.ind with | _ a
  induction k using Q.ind with | _ b
  have h := Teq.iterSucc (Γ := Γ) a Tm.zero (Tm.lstep (shift b) (var 0))
  simp only [Tm.subst_lstep, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at h
  exact sound h

theorem lg_eq (x : Q Γ) : lg x = lgc x x := by
  induction x using Q.ind with | _ a
  rfl

/-- Below the exponent the counter follows its index: the induction step. -/
theorem lgc_low_step (i c k r : Q Γ) (hk : monus (pow2 c) k = 0)
    (ih : sel (monus i c) r i = i) :
    sel (monus (succ i) c) (lstep k r) (succ i) = succ i := by
  refine Q.cases (monus (succ i) c) (fun e he => ?_) (fun e z he => ?_)
  · have ih' := congrArg e.map ih
    have hk' := congrArg e.map hk
    simp only [Ext.map_sel, Ext.map_monus, Ext.map_succ, Ext.map_pow2, Ext.map_lstep,
      Ext.map_zero] at he ih' hk' ⊢
    rw [le_of_succ_le he, sel_zero] at ih'
    rw [he, sel_zero, ih', lstep_eq, monus_trans (pow2_mono he) hk', sel_zero]
  · simp only [Ext.map_sel, Ext.map_succ, he, sel_succ]

/-- Below the exponent the counter follows its index. -/
theorem sel_lgc_low (c a i : Q Γ) : sel (monus i c) (lgc i (pow2 c + a)) i = i := by
  induction c using Q.ind with | _ c
  induction a using Q.ind with | _ a
  induction i using Q.ind with | _ i
  have h := eqInd (Γ := Γ)
    (Tm.sel (Tm.monus (var 0) (shift c))
      (Tm.lgc (var 0) (Tm.add (Tm.pow2 (shift c)) (shift a))) (var 0))
    (var 0) (by simp)
    (fun ih => by simp at ih ⊢; exact lgc_low_step _ _ _ _ (monus_add_right _ _) ih) i
  simpa using h

theorem lgc_low (c a : Q Γ) : lgc c (pow2 c + a) = c := by
  have h := sel_lgc_low c a c
  rwa [monus_self, sel_zero] at h

/-- At the exponent of a pair the counter stops. -/
theorem lstep_pair (a b : Q Γ) : lstep (pow2 (a + b) + a) (a + b) = a + b := by
  have hp := add_monus_of_le (succ_le_pow2 (a + b))
  generalize monus (pow2 (a + b)) (succ (a + b)) = d at hp
  have e : pow2 (a + b) + pow2 (a + b) = (pow2 (a + b) + a) + succ (b + d) := by
    conv_lhs => rhs; rw [← hp]
    simp only [succ_add, add_succ, succ_inj_iff]
    abel
  rw [lstep_eq, pow2_succ, e, monus_add_left, sel_succ]

theorem lgc_pair_add (a b j : Q Γ) : lgc (a + b + j) (pow2 (a + b) + a) = a + b := by
  induction a using Q.ind with | _ a
  induction b using Q.ind with | _ b
  induction j using Q.ind with | _ j
  have h := eqInd (Γ := Γ)
    (Tm.lgc (Tm.add (Tm.add (shift a) (shift b)) (var 0))
      (Tm.add (Tm.pow2 (Tm.add (shift a) (shift b))) (shift a)))
    (Tm.add (shift a) (shift b)) (by simp [lgc_low])
    (fun ih => by simp at ih; simp [add_succ, ih, lstep_pair]) j
  simpa using h

/-! ### Pairing -/

theorem pair_eq (a b : Q Γ) : pair a b = pow2 (a + b) + a := by
  induction a using Q.ind with | _ a
  induction b using Q.ind with | _ b
  rfl

theorem pfst_eq (w : Q Γ) : pfst w = monus w (pow2 (lg w)) := by
  induction w using Q.ind with | _ a
  rfl

theorem psnd_eq (w : Q Γ) : psnd w = monus (lg w) (pfst w) := by
  induction w using Q.ind with | _ a
  rfl

@[simp] theorem lg_pair (a b : Q Γ) : lg (pair a b) = a + b := by
  have hle : monus (a + b) (pow2 (a + b) + a) = 0 :=
    le_add_right (le_of_succ_le (succ_le_pow2 (a + b))) a
  have h := lgc_pair_add a b (monus (pow2 (a + b) + a) (a + b))
  rw [add_monus_of_le hle] at h
  rw [lg_eq, pair_eq]
  exact h

@[simp] theorem pfst_pair (a b : Q Γ) : pfst (pair a b) = a := by
  rw [pfst_eq, lg_pair, pair_eq, monus_add_left]

@[simp] theorem psnd_pair (a b : Q Γ) : psnd (pair a b) = b := by
  rw [psnd_eq, lg_pair, pfst_pair, monus_add_left]

end Q

end LeanProofs.ConciseIPRA
