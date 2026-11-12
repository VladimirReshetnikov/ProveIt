import ConciseIPRA.NativeClausal

/-!
# One-body contexts

The calculus of the package `one_body`.  A context entry is one formula body
`B(y)`, read as `B(0) → ∀y B(y)`; there is no separate antecedent and no
ordinary assumption.  An assumption `A` is stored as its *gate body*
`gate_v A`, the formula `A` with `sel(v, 0, ·)` on both sides of its equation
(`NFm.gt`, `NFm.gb`).  The rules of `OBPrf` are reflexivity, the two cases of
Eval, Use, Open and Intro:

* Use: for a body `B` of the context, from `B(0)` infer `B(t)`;
* Open: from `D_{x,y} B`, continue with the body `B(b, y)` for a fresh `b`;
* Intro: the witness-selected introduction of `NativeClausal`, with its
  assumption stored as a gate body.

`obprf_iff_nprf : OBPrf (Γ.map gb) A ↔ NPrf Γ A` for `Q`-free `Γ` and `A`, and
`obprf_unQ_iff_nprf` for arbitrary ones through the `Q`-free form.

Soundness reads a body `B` as the kernel formula `Q B` (`OBPrf.toNPrf`).
Completeness translates the two-field clause calculus `CPrf` occurrence by
occurrence (`CPrf.toOB`): an opened clause `[B(b, 0); y.B(b, y)]` is the body
`B(b, y)`, and an assumption clause `[0 = 0; v.A]` is the gate body of `A`.
The only step that is not literal is the use of an assumption clause.  It is
the package's argument, by induction on the depth of the formula:

* conversion (`OBPrf.conv`): formulas with the same binders whose equations
  have provably equal sides (`LEq`) are interderivable; at a binder, open the
  given formula at `b`, introduce the other at `b`, and use access one level
  down for the gate body that the introduction stores;
* access (`OBPrf.acc`, `OBPrf.access`): from the gate body of `A` infer `A`,
  by Use at `1` and conversion along the computation `sel(1, 0, s) = s`; the
  instance at `0` is derivable outright (`OBPrf.gtZero`).

No cut or weakening of `OBPrf` is used.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open Tm (zero succ iter)

variable {n m : ℕ}

namespace NFm

/-- The gate: `sel(v, 0, ·)` on both sides of the equation of a formula. -/
def gt : {n : ℕ} → Tm n → NFm n → NFm n
  | _, v, .eq s t => .eq (Tm.sel v zero s) (Tm.sel v zero t)
  | _, v, .Q B => .Q (gt (Syn.shift v) B)
  | _, v, .D B => .D (gt (Syn.shift (Syn.shift v)) B)

theorem gt_subst (A : NFm n) : ∀ {m : ℕ} (v : Tm n) (σ : Fin n → Tm m),
    (gt v A).subst σ = gt (Syn.subst σ v) (A.subst σ) := by
  induction A with intro m v σ
  | eq s t => simp only [gt, subst_eq, Tm.subst_sel, Tm.subst_zero]
  | Q B ih => simp only [gt, subst_Q, ih, Syn.subst_up_shift]
  | D B ih => simp only [gt, subst_D, ih, Syn.subst_up_shift]

theorem gt_zero_subst (A : NFm n) (σ : Fin n → Tm m) :
    (gt zero A).subst σ = gt zero (A.subst σ) := gt_subst A zero σ

theorem qfree_gt (A : NFm n) : ∀ v : Tm n, (gt v A).QFree ↔ A.QFree := by
  induction A with intro v
  | eq s t => exact Iff.rfl
  | Q B _ => exact Iff.rfl
  | D B ih => exact ih _

/-- The number of binders above the equation. -/
def depth : {n : ℕ} → NFm n → ℕ
  | _, .eq _ _ => 0
  | _, .Q B => depth B + 1
  | _, .D B => depth B + 1

theorem depth_subst (A : NFm n) : ∀ {m : ℕ} (σ : Fin n → Tm m), (A.subst σ).depth = A.depth := by
  induction A with intro m σ
  | eq s t => rfl
  | Q B ih => simp only [subst_Q, depth, ih]
  | D B ih => simp only [subst_D, depth, ih]

theorem depth_gt (A : NFm n) : ∀ v : Tm n, (gt v A).depth = A.depth := by
  induction A with intro v
  | eq s t => rfl
  | Q B ih => simp only [gt, depth, ih]
  | D B ih => simp only [gt, depth, ih]

/-- The body that stores an ordinary assumption. -/
def gb (A : NFm n) : NFm (n + 1) := gt (Syn.var 0) A.shift

/-- A body moved under a fresh variable. -/
def bsh (B : NFm (n + 1)) : NFm (n + 2) := B.subst (up fun i => Syn.var i.succ)

theorem gb_inst (A : NFm n) (c : Tm n) : (gb A).subst (inst c) = gt c A := by
  rw [gb, gt_subst, subst_inst_shift, Syn.subst_var, Syn.inst_zero]

theorem gb_repl (A : NFm n) (c : Tm (n + 1)) : (gb A).subst (repl c) = gt c A.shift := by
  rw [gb, gt_subst, subst_repl_shift, Syn.subst_var, Syn.repl_zero]

theorem gb_bsh (A : NFm n) : (gb A).bsh = gb A.shift := by
  rw [bsh, gb, gt_subst, shift_subst_up, Syn.subst_var, Syn.up_zero]
  rfl

theorem map_Q_bsh (Γ : List (NFm (n + 1))) :
    (Γ.map bsh).map NFm.Q = (Γ.map NFm.Q).map NFm.shift := by
  rw [List.map_map, List.map_map]
  exact List.map_congr_left fun B _ => rfl

end NFm

/-- Derivability with one-body contexts. -/
inductive OBPrf : {n : ℕ} → List (NFm (n + 1)) → NFm n → Prop
  | refl {n : ℕ} {Γ : List (NFm (n + 1))} (t : Tm n) : OBPrf Γ (.eq t t)
  | evalZero {n : ℕ} {Γ : List (NFm (n + 1))} (h : Tm (n + 1)) {a t r : Tm n}
      (h₁ : OBPrf Γ (.eq a t)) (h₂ : OBPrf Γ (.eq (iter zero a h) r)) : OBPrf Γ (.eq r t)
  | evalSucc {n : ℕ} {Γ : List (NFm (n + 1))} {c a : Tm n} {h : Tm (n + 1)} {t r : Tm n}
      (h₁ : OBPrf Γ (.eq (iter c a h) t)) (h₂ : OBPrf Γ (.eq (iter (succ c) a h) r)) :
      OBPrf Γ (.eq r (Syn.subst (inst t) h))
  /-- Use: from the instance of a body at `0` infer its instance at `t`. -/
  | use {n : ℕ} {Γ : List (NFm (n + 1))} {B : NFm (n + 1)} (t : Tm n) (hB : B ∈ Γ)
      (h : OBPrf Γ (B.subst (inst zero))) : OBPrf Γ (B.subst (inst t))
  /-- Open: `D_{x,y} B` at a fresh `b` adds the body `B(b, y)`. -/
  | opn {n : ℕ} {Γ : List (NFm (n + 1))} {B : NFm (n + 2)} {A : NFm n} (h₁ : OBPrf Γ (.D B))
      (h₂ : OBPrf (B :: Γ.map NFm.bsh) A.shift) : OBPrf Γ A
  /-- Intro: from `B(t, η) ⊢ B(t, S z)` with `z` fresh infer `D_{x,y} B`; the
  assumption is stored as a gate body. -/
  | intro {n : ℕ} {Γ : List (NFm (n + 1))} (B : NFm (n + 2)) (t : Tm n) (hB : B.QFree)
      (h : OBPrf (NFm.gb ((B.subst (up (inst t))).subst (repl (NFm.start B t)))
          :: Γ.map NFm.bsh)
        ((B.subst (up (inst t))).subst (repl (succ (var 0))))) :
      OBPrf Γ (.D B)

/-! ### Soundness -/

/-- The gate at a successor is the formula. -/
theorem NEquiv.gtSucc (X : NFm n) : ∀ v : Tm n, NEquiv (NFm.gt (succ v) X) X := by
  induction X with intro v
  | eq s t =>
    exact ⟨NPrf.eqTrans (NPrf.eqSymm (NPrf.selSucc _ _ _))
        (NPrf.eqTrans NPrf.hyp0 (NPrf.selSucc _ _ _)),
      NPrf.eqTrans (NPrf.selSucc _ _ _)
        (NPrf.eqTrans NPrf.hyp0 (NPrf.eqSymm (NPrf.selSucc _ _ _)))⟩
  | Q B ih => exact NEquiv.Q (ih _)
  | D B ih => exact NEquiv.D (ih _)

/-- A formula gives the closure of its gate body. -/
theorem NPrf.gbI {Γ : List (NFm n)} {X : NFm n} (h : NPrf Γ X) : NPrf Γ (.Q (NFm.gb X)) := by
  refine .qI _ ?_
  rw [NFm.gb_repl]
  exact (NEquiv.gtSucc _ _).mpr h.shift.wk

/-- **Soundness**: a body `B` is read as `Q B`. -/
theorem OBPrf.toNPrf {Γ : List (NFm (n + 1))} {A : NFm n} (h : OBPrf Γ A) :
    NPrf (Γ.map NFm.Q) A := by
  induction h with
  | refl t => exact NPrf.eqRefl t
  | evalZero h _ _ ih₁ ih₂ =>
    exact NPrf.eqTrans (NPrf.eqSymm ih₂) (NPrf.eqTrans (.iterZero _ h) ih₁)
  | @evalSucc _ _ c a h t r _ _ ih₁ ih₂ =>
    exact NPrf.eqTrans (NPrf.eqSymm ih₂) (NPrf.eqTrans (.iterSucc c a h) (NPrf.eqCongr h ih₁))
  | use t hB _ ih => exact .qE t (.hyp (List.mem_map_of_mem (f := NFm.Q) hB)) ih
  | opn _ _ ih₁ ih₂ =>
    rw [List.map_cons, NFm.map_Q_bsh] at ih₂
    exact .dE ih₁ ih₂
  | intro B t _ _ ih =>
    rw [List.map_cons, NFm.map_Q_bsh] at ih
    exact .ofDI B t (NPrf.cut1 (NPrf.gbI NPrf.hyp0) (NPrf.wkUnder ih))

namespace OBPrf

variable {Γ : List (NFm (n + 1))} {A : NFm n}

/-! ### Equality from reflexivity and Eval -/

theorem evalId {s t r : Tm n} (h₁ : OBPrf Γ (.eq s t)) (h₂ : OBPrf Γ (.eq s r)) :
    OBPrf Γ (.eq r t) :=
  .evalZero (Syn.var 0) h₁ (.evalZero (Syn.var 0) h₂ (.refl _))

theorem eqSymm {s t : Tm n} (h : OBPrf Γ (.eq s t)) : OBPrf Γ (.eq t s) := evalId (.refl s) h

theorem eqTrans {s t u : Tm n} (h₁ : OBPrf Γ (.eq s t)) (h₂ : OBPrf Γ (.eq t u)) :
    OBPrf Γ (.eq s u) :=
  evalId h₂ (eqSymm h₁)

theorem selZero (a b : Tm n) : OBPrf Γ (.eq (Tm.sel zero a b) a) :=
  .evalZero _ (.refl a) (.refl _)

theorem selSucc (c a b : Tm n) : OBPrf Γ (.eq (Tm.sel (succ c) a b) b) := by
  have h : OBPrf Γ (.eq (iter (succ c) a (Syn.shift b))
      (Syn.subst (inst (iter c a (Syn.shift b))) (Syn.shift b))) :=
    .evalSucc (.refl _) (.refl _)
  rwa [Syn.subst_inst_shift] at h

end OBPrf

/-! ### Formulas with provably equal sides -/

/-- The same binders, and equations whose sides are provably equal in every
context and under every substitution. -/
inductive LEq : {n : ℕ} → NFm n → NFm n → Prop
  | eq {n : ℕ} {s s' t t' : Tm n}
      (hs : ∀ {m : ℕ} (σ : Fin n → Tm m) (Γ : List (NFm (m + 1))),
        OBPrf Γ (.eq (Syn.subst σ s) (Syn.subst σ s')))
      (ht : ∀ {m : ℕ} (σ : Fin n → Tm m) (Γ : List (NFm (m + 1))),
        OBPrf Γ (.eq (Syn.subst σ t) (Syn.subst σ t'))) :
      LEq (.eq s t) (.eq s' t')
  | D {n : ℕ} {B B' : NFm (n + 2)} (h : LEq B B') : LEq (.D B) (.D B')

namespace LEq

variable {A A' : NFm n}

theorem symm (h : LEq A A') : LEq A' A := by
  induction h with
  | eq hs ht => exact .eq (fun σ Γ => (hs σ Γ).eqSymm) (fun σ Γ => (ht σ Γ).eqSymm)
  | D _ ih => exact .D ih

theorem subst (h : LEq A A') : ∀ {m : ℕ} (σ : Fin n → Tm m), LEq (A.subst σ) (A'.subst σ) := by
  induction h with intro m σ
  | eq hs ht =>
    rw [NFm.subst_eq, NFm.subst_eq]
    refine .eq (fun τ Γ => ?_) (fun τ Γ => ?_)
    · rw [Syn.subst_subst, Syn.subst_subst]; exact hs _ Γ
    · rw [Syn.subst_subst, Syn.subst_subst]; exact ht _ Γ
  | D _ ih =>
    rw [NFm.subst_D, NFm.subst_D]
    exact .D (ih _)

theorem depth_eq (h : LEq A A') : A'.depth = A.depth := by
  induction h with
  | eq _ _ => rfl
  | D _ ih => simp only [NFm.depth, ih]

theorem qfree (h : LEq A A') : A.QFree ∧ A'.QFree := by
  induction h with
  | eq _ _ => exact ⟨trivial, trivial⟩
  | D _ ih => exact ih

/-- The gate at a successor has the sides of the formula, by one
computation. -/
theorem gtSucc (X : NFm n) (hX : X.QFree) : ∀ v : Tm n, LEq (NFm.gt (succ v) X) X := by
  induction X with intro v
  | eq s t =>
    refine .eq (fun σ Γ => ?_) (fun σ Γ => ?_)
    · rw [Tm.subst_sel, Tm.subst_succ]; exact OBPrf.selSucc _ _ _
    · rw [Tm.subst_sel, Tm.subst_succ]; exact OBPrf.selSucc _ _ _
  | Q B _ => exact hX.elim
  | D B ih => exact .D (ih hX _)

end LEq

namespace OBPrf

variable {Γ : List (NFm (n + 1))} {A : NFm n}

/-- The gate at `0` is derivable. -/
theorem gtZero (X : NFm n) (hX : X.QFree) :
    ∀ {m : ℕ} (σ : Fin n → Tm m) (Γ : List (NFm (m + 1))), OBPrf Γ (NFm.gt zero (X.subst σ)) := by
  induction X with intro m σ Γ
  | eq s t => exact eqTrans (selZero _ _) (eqSymm (selZero _ _))
  | Q B _ => exact hX.elim
  | D B ih =>
    rw [NFm.subst_D]
    have key : ∀ Δ : List (NFm (m + 1 + 1)),
        OBPrf Δ (((NFm.gt zero (B.subst (up (up σ)))).subst (up (inst (succ zero)))).subst
          (repl (succ (Syn.var 0)))) := by
      intro Δ
      rw [NFm.gt_zero_subst, NFm.gt_zero_subst, NFm.subst_subst, NFm.subst_subst]
      exact ih hX _ Δ
    exact .intro _ (succ zero) ((NFm.qfree_gt _ _).2 ((NFm.qfree_subst _ _).2 hX)) (key _)

/-- **Access** to a stored assumption, from the conversion of its gate at
`1`. -/
theorem acc {X : NFm n} (hX : X.QFree)
    (cv : ∀ Γ : List (NFm (n + 1)), OBPrf Γ (NFm.gt (succ zero) X) → OBPrf Γ X)
    (hm : NFm.gb X ∈ Γ) : OBPrf Γ X := by
  have h0 : OBPrf Γ ((NFm.gb X).subst (inst zero)) := by
    rw [NFm.gb_inst]
    have k := gtZero X hX Syn.var Γ
    rwa [NFm.subst_id] at k
  have h1 := OBPrf.use (succ zero) hm h0
  rw [NFm.gb_inst] at h1
  exact cv Γ h1

theorem convEq {s s' t t' : Tm n} (hs : OBPrf Γ (.eq s s')) (ht : OBPrf Γ (.eq t t'))
    (h : OBPrf Γ (.eq s t)) : OBPrf Γ (.eq s' t') :=
  eqTrans (eqSymm hs) (eqTrans h ht)

/-- **Conversion**: formulas with the same binders and provably equal sides
are interderivable.  By induction on the number of binders. -/
theorem conv : ∀ (d : ℕ) {n : ℕ} {A A' : NFm n}, A.depth ≤ d → LEq A A' →
    ∀ Γ : List (NFm (n + 1)), OBPrf Γ A → OBPrf Γ A' := by
  intro d
  induction d with intro n A A' hd hL Γ h
  | zero =>
    cases hL with
    | eq hs ht =>
      have ks := hs Syn.var Γ
      have kt := ht Syn.var Γ
      rw [Syn.subst_id, Syn.subst_id] at ks kt
      exact convEq ks kt h
    | D hB => exact absurd hd (Nat.not_succ_le_zero _)
  | succ d ih =>
    cases hL with
    | eq hs ht =>
      have ks := hs Syn.var Γ
      have kt := ht Syn.var Γ
      rw [Syn.subst_id, Syn.subst_id] at ks kt
      exact convEq ks kt h
    | @D _ B B' hB =>
      have hdB : B.depth ≤ d := Nat.le_of_succ_le_succ hd
      refine .opn h ?_
      show OBPrf _ (.D (B'.subst (up (up fun i => Syn.var i.succ))))
      refine .intro _ (Syn.var 0) ((NFm.qfree_subst _ _).2 hB.qfree.2) ?_
      rw [NFm.start_of_not (fun h' => by cases h'.2), NFm.subst_upup_inst_var]
      -- the stored assumption `B'(b, 0)`, by access one level down
      have hX : (B'.subst (repl zero)).QFree := (NFm.qfree_subst _ _).2 hB.qfree.2
      have hdX : (B'.subst (repl zero)).depth ≤ d := by
        rw [NFm.depth_subst, hB.depth_eq]; exact hdB
      have e₁ : B.subst (repl (succ (Syn.var 0))) = (NFm.bsh B).subst (inst (succ (Syn.var 0))) :=
        (NFm.subst_dummy_up_inst B _).symm
      have e₀ : (NFm.bsh B).subst (inst zero) = B.subst (repl zero) :=
        NFm.subst_dummy_up_inst B _
      -- back from `B(b, S z)`, which is the retained body used at `S z`
      refine ih (by rw [NFm.depth_subst]; exact hdB) (hB.subst _) _ ?_
      rw [e₁]
      refine .use _
        (List.mem_cons_of_mem _ (List.mem_map_of_mem (f := NFm.bsh) List.mem_cons_self)) ?_
      rw [e₀]
      -- `B(b, 0)` from the stored assumption `B'(b, 0)`, by access one level down
      refine ih hdX (hB.symm.subst (repl zero)) _ ?_
      exact acc hX (fun Γ' => ih (by rw [NFm.depth_gt]; exact hdX)
        (LEq.gtSucc _ hX zero) Γ') List.mem_cons_self

/-- **Access** to a stored assumption. -/
theorem access {X : NFm n} (hX : X.QFree) (hm : NFm.gb X ∈ Γ) : OBPrf Γ X :=
  acc hX (fun Γ' => conv X.depth (NFm.depth_gt _ _).le (LEq.gtSucc X hX zero) Γ') hm

end OBPrf

/-! ### Completeness -/

/-- The origin of a clause of the two-field calculus, with the body that
replaces it. -/
inductive Org : {n : ℕ} → Cl n → NFm (n + 1) → Prop
  | asm {n : ℕ} (A : NFm n) (hA : A.QFree) : Org (Cl.asm A) (NFm.gb A)
  | opened {n : ℕ} (B : NFm (n + 1)) : Org ⟨B.subst (inst zero), B⟩ B

theorem Org.shift {c : Cl n} {b : NFm (n + 1)} (h : Org c b) : Org c.shift b.bsh := by
  cases h with
  | asm A hA =>
    rw [Cl.asm_shift, NFm.gb_bsh]
    exact .asm _ ((NFm.qfree_subst _ _).2 hA)
  | opened =>
    have e : (⟨b.subst (inst zero), b⟩ : Cl n).shift = ⟨b.bsh.subst (inst zero), b.bsh⟩ := by
      show (⟨(b.subst (inst zero)).shift, b.subst (up fun i => Syn.var i.succ)⟩ : Cl (n + 1)) = _
      rw [NFm.shift, NFm.subst_inst]
      rfl
    rw [e]
    exact .opened _

theorem Org.lift {Γc : List (Cl n)} {Γb : List (NFm (n + 1))}
    (R : ∀ c ∈ Γc, ∃ b ∈ Γb, Org c b) {c₀ : Cl (n + 1)} {b₀ : NFm (n + 2)} (h₀ : Org c₀ b₀) :
    ∀ c ∈ c₀ :: Γc.map Cl.shift, ∃ b ∈ b₀ :: Γb.map NFm.bsh, Org c b := by
  intro c hc
  rcases List.mem_cons.1 hc with rfl | hc
  · exact ⟨b₀, List.mem_cons_self, h₀⟩
  · obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
    obtain ⟨b, hb, ho⟩ := R c' hc'
    exact ⟨b.bsh, List.mem_cons_of_mem _ (List.mem_map_of_mem hb), ho.shift⟩

/-- **Completeness**: a derivation of the two-field clause calculus, with each
clause replaced by the body of its origin. -/
theorem CPrf.toOB {Γc : List (Cl n)} {A : NFm n} (h : CPrf Γc A) :
    ∀ Γb : List (NFm (n + 1)), (∀ c ∈ Γc, ∃ b ∈ Γb, Org c b) → OBPrf Γb A := by
  induction h with intro Γb R
  | refl t => exact .refl t
  | evalZero h _ _ ih₁ ih₂ => exact .evalZero h (ih₁ Γb R) (ih₂ Γb R)
  | evalSucc _ _ ih₁ ih₂ => exact .evalSucc (ih₁ Γb R) (ih₂ Γb R)
  | @use _ Γ c t hc _ ih =>
    obtain ⟨b, hb, ho⟩ := R c hc
    cases ho with
    | asm X hX =>
      show OBPrf Γb (X.shift.subst (inst t))
      rw [NFm.subst_inst_shift]
      exact OBPrf.access hX hb
    | opened => exact .use t hb (ih Γb R)
  | elim _ _ ih₁ ih₂ => exact .opn (ih₁ Γb R) (ih₂ _ (Org.lift R (.opened _)))
  | intro B t hB _ ih =>
    exact .intro B t hB (ih _ (Org.lift R (.asm _ ((NFm.qfree_subst _ _).2
      ((NFm.qfree_subst _ _).2 hB)))))

variable {Γ : List (NFm n)} {A : NFm n}

/-- **The one-body calculus derives the `Q`-free form of a sequent exactly when
the kernel derives the sequent.** -/
theorem obprf_unQ_iff_nprf :
    OBPrf (Γ.map fun X => NFm.gb (NFm.unQ X)) (NFm.unQ A) ↔ NPrf Γ A := by
  refine ⟨fun h => (NEquiv.unQ A).mp (h.toNPrf.cut fun C hC => ?_), fun h => ?_⟩
  · rw [List.map_map, List.mem_map] at hC
    obtain ⟨X, hX, rfl⟩ := hC
    exact NPrf.gbI ((NEquiv.unQ X).mpr (.hyp hX))
  · refine (cprf_iff_nprf.mpr h).toOB _ fun c hc => ?_
    obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hc
    exact ⟨_, List.mem_map_of_mem (f := fun X => NFm.gb (NFm.unQ X)) hX,
      .asm _ (NFm.qfree_unQ X)⟩

/-- **On `Q`-free sequents the one-body calculus is the kernel.** -/
theorem obprf_iff_nprf (hΓ : ∀ X ∈ Γ, X.QFree) (hA : A.QFree) :
    OBPrf (Γ.map NFm.gb) A ↔ NPrf Γ A := by
  have e : (Γ.map fun X => NFm.gb (NFm.unQ X)) = Γ.map NFm.gb :=
    List.map_congr_left fun X hX => by rw [NFm.unQ_of_qfree X (hΓ X hX)]
  rw [← obprf_unQ_iff_nprf, e, NFm.unQ_of_qfree A hA]

/-- The same against the two-field clause calculus. -/
theorem obprf_iff_cprf (hΓ : ∀ X ∈ Γ, X.QFree) (hA : A.QFree) :
    OBPrf (Γ.map NFm.gb) A ↔ CPrf (Γ.map Cl.asm) A :=
  (obprf_iff_nprf hΓ hA).trans (cprf_iff_nprf_of_qfree hΓ hA).symm

end LeanProofs.ConciseIPRA
