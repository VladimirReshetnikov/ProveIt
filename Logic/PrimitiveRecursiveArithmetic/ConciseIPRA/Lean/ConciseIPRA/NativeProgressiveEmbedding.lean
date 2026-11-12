import ConciseIPRA.NativeProgressiveLeibniz

/-!
# The kernel inside the uniform calculus

The uniform calculus `RPrf` reads `Q` at a literal equation as progressivity,
so a formula of the kernel does not mean the same thing in it.  The
translation `NFm.emb` of the package `Research/uniform_progress` repairs this
by *padding*: below every binder an equation `s = t` is replaced by the
compound formula

  `L(s = t) = D_{r,v} (sel(v, 0, s) = sel(v, 0, t))`,

whose matrix is `0 = 0` at `v = 0` and `s = t` at a successor.  In `RPrf` an
equation and its padding are interderivable (`RPrf.padI`, `RPrf.padE`), and
after the translation every binder stands over a compound matrix, where the
two calculi read it alike.

* `NPrf.toR`: every derivation of the kernel translates into `RPrf`.  The
  elimination of `Q` pads its minor premise, applies the uniform `QE`, removes
  the redex `I(0, t; v.S v)` by the Leibniz rule and removes the padding;
  progress for an equation is the introduction of `Q` at the padded matrix and
  the equation induction of `RPrf`.
* `NEquiv.rd_emb`: in the kernel, the progressive reading of the translation
  of a formula is equivalent to the formula.
* `rprf_emb_iff : RPrf (Γ.map NFm.emb) A.emb ↔ NPrf Γ A`: the kernel derives a
  sequent exactly when the uniform calculus derives its translation.
* `rprf_emb_iff_pra`: hence exactly when iPRA proves its reading.

The other formula round trip, from a formula of `RPrf` through `NFm.rd` and
back through `NFm.emb`, is not formalized.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm
open Tm (zero succ iter)

variable {n m k : ℕ}

namespace NFm

/-- The matrix of the padding of `s = t`. -/
def padM (s t : Tm n) : NFm (n + 2) :=
  .eq (Tm.sel (Syn.var 0) zero (Syn.shift (Syn.shift s)))
    (Tm.sel (Syn.var 0) zero (Syn.shift (Syn.shift t)))

/-- Padding: an equation becomes a compound formula; a compound formula is
unchanged. -/
def pad : {n : ℕ} → NFm n → NFm n
  | _, .eq s t => .D (padM s t)
  | _, .Q B => .Q B
  | _, .D B => .D B

theorem padM_subst (s t : Tm n) (σ : Fin n → Tm m) :
    (padM s t).subst (up (up σ)) = padM (Syn.subst σ s) (Syn.subst σ t) := by
  simp [padM, Syn.subst_up_shift]

theorem padM_inst (s t : Tm n) (c : Tm (n + 1)) :
    (padM s t).subst (inst c)
      = .eq (Tm.sel c zero (Syn.shift s)) (Tm.sel c zero (Syn.shift t)) := by
  simp [padM]

theorem padM_wit (s t w : Tm n) (c : Tm (n + 1)) :
    ((padM s t).subst (up (inst w))).subst (repl c)
      = .eq (Tm.sel c zero (Syn.shift s)) (Tm.sel c zero (Syn.shift t)) := by
  simp [padM, Syn.subst_up_shift, Syn.subst_repl_shift]

theorem pad_subst (A : NFm n) (σ : Fin n → Tm m) : (pad A).subst σ = pad (A.subst σ) := by
  cases A with
  | eq s t => exact congrArg NFm.D (padM_subst s t σ)
  | Q B => rfl
  | D B => rfl

theorem pad_shift (A : NFm n) : (pad A).shift = pad A.shift := pad_subst A _

theorem pad_isEq (A : NFm n) : (pad A).isEq = false := by cases A <;> rfl

/-- The translation of the kernel into the uniform calculus: every matrix
below a binder is padded. -/
def emb : {n : ℕ} → NFm n → NFm n
  | _, .eq s t => .eq s t
  | _, .Q B => .Q (pad (emb B))
  | _, .D B => .D (pad (emb B))

theorem emb_subst (A : NFm n) : ∀ {m : ℕ} (σ : Fin n → Tm m),
    emb (A.subst σ) = (emb A).subst σ := by
  induction A with intro m σ
  | eq s t => rfl
  | Q B ih =>
    show NFm.Q (pad (emb (B.subst (up σ)))) = NFm.Q ((pad (emb B)).subst (up σ))
    rw [ih, pad_subst]
  | D B ih =>
    show NFm.D (pad (emb (B.subst (up (up σ))))) = NFm.D ((pad (emb B)).subst (up (up σ)))
    rw [ih, pad_subst]

theorem emb_shift (A : NFm n) : emb A.shift = (emb A).shift := emb_subst A _

theorem map_emb_shift (Γ : List (NFm n)) :
    (Γ.map NFm.shift).map emb = (Γ.map emb).map NFm.shift := by
  rw [List.map_map, List.map_map]
  exact List.map_congr_left fun A _ => emb_shift A

end NFm

namespace RPrf

variable {Γ : List (NFm n)}

theorem selZero (a b : Tm n) : RPrf Γ (.eq (Tm.sel zero a b) a) := .iterZero a _

theorem selSucc (c a b : Tm n) : RPrf Γ (.eq (Tm.sel (succ c) a b) b) := by
  have h := RPrf.iterSucc (Γ := Γ) c a (Syn.shift b)
  rwa [Syn.subst_inst_shift] at h

theorem selEq (c a : Tm n) {s t : Tm n} (h : RPrf Γ (.eq s t)) :
    RPrf Γ (.eq (Tm.sel (succ c) a s) (Tm.sel (succ c) a t)) :=
  eqTrans (selSucc c a s) (eqTrans h (eqSymm (selSucc c a t)))

theorem ofSelEq {c a s t : Tm n}
    (h : RPrf Γ (.eq (Tm.sel (succ c) a s) (Tm.sel (succ c) a t))) : RPrf Γ (.eq s t) :=
  eqTrans (eqSymm (selSucc c a s)) (eqTrans h (selSucc c a t))

/-- A formula gives its padding: at an equation, by the introduction at a
literal equation, whose hypothesis is not used. -/
theorem padI {A : NFm n} (h : RPrf Γ A) : RPrf Γ A.pad := by
  cases A with
  | eq s t =>
    refine .dI _ zero ?_
    rw [NFm.padM_wit s t zero (succ (Syn.var 0))]
    exact (selEq (Syn.var 0) zero h.shift).wk
  | Q B => exact h
  | D B => exact h

/-- The padding gives the formula: at an equation, the opened progressive
closure is used once, from `0` with the initializer `1`. -/
theorem padE {A : NFm n} (h : RPrf Γ A.pad) : RPrf Γ A := by
  cases A with
  | eq s t =>
    refine .dE h ?_
    have base : RPrf (.Q (NFm.padM s t) :: Γ.map NFm.shift)
        ((NFm.padM s t).subst (inst (NFm.eta (NFm.padM s t) (zero : Tm (n + 1))))) := by
      rw [show NFm.eta (NFm.padM s t) (zero : Tm (n + 1)) = zero from rfl, NFm.padM_inst]
      exact eqTrans (selZero _ _) (eqSymm (selZero _ _))
    have q := RPrf.qE zero (succ zero) hyp0 base
    rw [show NFm.eta (NFm.padM s t) (zero : Tm (n + 1)) = zero from rfl] at q
    have q' := RPrf.trF (NFm.padM s t) rfl (RPrf.iterZero (succ zero) (succ (Syn.var 0))) q
    rw [NFm.padM_inst] at q'
    exact ofSelEq q'
  | Q B => exact h
  | D B => exact h

end RPrf

/-! ### The translation of derivations -/

/-- **Every derivation of the kernel translates into the uniform calculus.** -/
theorem NPrf.toR {Γ : List (NFm n)} {A : NFm n} (h : NPrf Γ A) :
    RPrf (Γ.map NFm.emb) A.emb := by
  induction h with
  | hyp h => exact .hyp (List.mem_map_of_mem h)
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | trOne h _ _ ih₁ ih₂ => exact RPrf.trOne h ih₁ ih₂
  | @qE _ Γ B t _ _ ih₁ ih₂ =>
    rw [NFm.emb_subst] at ih₂ ⊢
    have hM : (NFm.pad (NFm.emb B)).isEq = false := NFm.pad_isEq _
    have base : RPrf (Γ.map NFm.emb) ((NFm.pad (NFm.emb B)).subst
        (inst (NFm.eta (NFm.pad (NFm.emb B)) (zero : Tm _)))) := by
      rw [NFm.eta_of_ne hM, NFm.pad_subst]
      exact RPrf.padI ih₂
    have q := RPrf.qE zero t ih₁ base
    rw [NFm.eta_of_ne hM] at q
    have q' := RPrf.tr (NFm.pad (NFm.emb B)) (RPrf.iterZero t (succ (Syn.var 0))) q
    rw [NFm.pad_subst] at q'
    exact RPrf.padE q'
  | @dE _ Γ B A _ _ ih₁ ih₂ =>
    rw [List.map_cons, NFm.map_emb_shift, NFm.emb_shift] at ih₂
    exact .dE ih₁ ih₂
  | @dICase _ Γ B t _ ih =>
    rw [List.map_cons, NFm.map_emb_shift, NFm.emb_shift] at ih
    refine .dI _ t ?_
    rw [NFm.eta_of_ne (B := NFm.pad (NFm.emb B)) (NFm.pad_isEq _),
      ← NFm.shift_subst_inst_zero]
    simp only [NFm.pad_subst, ← NFm.emb_subst]
    rw [NFm.pad_shift]
    exact RPrf.padI (RPrf.cut1 (RPrf.padE RPrf.hyp0)
      (ih.weaken (List.cons_subset_cons _ (List.subset_cons_self _ _))))
  | @qIInd _ Γ s₁ s₂ _ ih =>
    rw [List.map_cons, NFm.map_emb_shift] at ih
    show RPrf (Γ.map NFm.emb) (.Q (NFm.pad (.eq s₁ s₂)))
    refine RPrf.qIC _ (NFm.pad_isEq _) ?_
    rw [NFm.pad_subst, NFm.pad_subst, NFm.pad_shift]
    refine RPrf.padI ?_
    rw [← NFm.subst_dummy_up_inst (NFm.eq s₁ s₂) (succ (Syn.var 0))]
    show RPrf _ ((NFm.eq (Syn.subst (up fun i => Syn.var i.succ) s₁)
      (Syn.subst (up fun i => Syn.var i.succ) s₂)).subst (inst (succ (Syn.var 0))))
    refine RPrf.eqInd _ _ _ ?_ ?_
    · show RPrf _ (((NFm.eq s₁ s₂).subst (up fun i => Syn.var i.succ)).subst (inst zero))
      rw [NFm.subst_dummy_up_inst, ← NFm.shift_subst_inst_zero]
      exact RPrf.padE RPrf.hyp0
    · have ih' : RPrf (NFm.eq s₁ s₂ :: (Γ.map NFm.emb).map NFm.shift)
          ((NFm.eq s₁ s₂).subst (repl (succ (Syn.var 0)))) := ih
      have k := ih'.subst (up fun i => Syn.var i.succ)
      rw [List.map_cons, NFm.map_shift_subst, NFm.subst_repl_succ] at k
      exact k.weaken (List.cons_subset_cons _ (List.map_subset _ (List.subset_cons_self _ _)))

/-! ### The round trip in the kernel -/

/-- In the kernel, the progressive reading of the padding of `s = t` is
equivalent to `s = t`. -/
theorem NEquiv.exProgPad (s t : Tm n) :
    NEquiv (NFm.ex (NFm.prog (NFm.padM s t))) (.eq s t) := by
  constructor
  · refine NPrf.exE NPrf.hyp0 ?_
    have a : NPrf (NFm.prog (NFm.padM s t)
          :: ([NFm.ex (NFm.prog (NFm.padM s t))]).map NFm.shift)
        ((NFm.imp (NFm.padM s t) ((NFm.padM s t).subst (repl (succ (Syn.var 0))))).subst
          (inst zero)) := NPrf.allE zero NPrf.hyp0
    rw [NFm.imp_subst, NFm.subst_repl_inst, NFm.padM_inst, NFm.padM_inst] at a
    have g1 := NPrf.impE a (NPrf.eqTrans (NPrf.selZero _ _) (NPrf.eqSymm (NPrf.selZero _ _)))
    exact NPrf.eqTrans (NPrf.eqSymm (NPrf.selSucc zero zero (Syn.shift s)))
      (NPrf.eqTrans g1 (NPrf.selSucc zero zero (Syn.shift t)))
  · refine NPrf.exI zero ?_
    rw [NFm.prog_subst]
    refine NPrf.allI (NPrf.impI ?_)
    rw [NFm.padM_wit]
    exact (NPrf.eqTrans (NPrf.selSucc (Syn.var 0) zero (Syn.shift s))
      (NPrf.eqTrans (NPrf.hyp0 (Γ := []) (A := NFm.eq s t)).shift
        (NPrf.eqSymm (NPrf.selSucc (Syn.var 0) zero (Syn.shift t))))).wk

theorem NEquiv.rd_pad (X : NFm n) : NEquiv (NFm.rd (NFm.pad X)) (NFm.rd X) := by
  cases X with
  | eq s t => exact NEquiv.exProgPad s t
  | Q B => exact NEquiv.refl _
  | D B => exact NEquiv.refl _

/-- **The round trip in the kernel.**  The progressive reading of the
translation of a formula is equivalent to the formula. -/
theorem NEquiv.rd_emb (A : NFm n) : NEquiv (NFm.rd (NFm.emb A)) A := by
  induction A with
  | eq s t => exact NEquiv.refl _
  | Q B ih =>
    have e : NFm.rd (NFm.emb (.Q B)) = .Q (NFm.rd (NFm.pad (NFm.emb B))) := by
      show (if (NFm.pad (NFm.emb B)).isEq then NFm.prog (NFm.rd (NFm.pad (NFm.emb B)))
        else NFm.Q (NFm.rd (NFm.pad (NFm.emb B)))) = _
      simp [NFm.pad_isEq]
    rw [e]
    exact NEquiv.Q ((NEquiv.rd_pad _).trans ih)
  | D B ih =>
    have e : NFm.rd (NFm.emb (.D B)) = .D (NFm.rd (NFm.pad (NFm.emb B))) := by
      show (if (NFm.pad (NFm.emb B)).isEq
          then NFm.ex (NFm.prog (NFm.rd (NFm.pad (NFm.emb B))))
        else NFm.D (NFm.rd (NFm.pad (NFm.emb B)))) = _
      simp [NFm.pad_isEq]
    rw [e]
    exact NEquiv.D ((NEquiv.rd_pad _).trans ih)

variable {Γ : List (NFm n)} {A : NFm n}

/-- **The kernel and the uniform calculus.**  The kernel derives a sequent
exactly when the uniform calculus derives its translation. -/
theorem rprf_emb_iff : RPrf (Γ.map NFm.emb) A.emb ↔ NPrf Γ A := by
  constructor
  · intro h
    refine (NEquiv.rd_emb A).mp (h.toNPrf.cut fun C hC => ?_)
    rw [List.map_map, List.mem_map] at hC
    obtain ⟨X, hX, rfl⟩ := hC
    exact (NEquiv.rd_emb X).mpr (.hyp hX)
  · exact NPrf.toR

/-- The uniform calculus derives the translation of a sequent exactly when
iPRA proves its reading. -/
theorem rprf_emb_iff_pra :
    RPrf (Γ.map NFm.emb) A.emb ↔ (Γ.map NFm.toPRA ⊢[PRAAx] A.toPRA) :=
  rprf_emb_iff.trans native_iff_pra

end LeanProofs.ConciseIPRA
