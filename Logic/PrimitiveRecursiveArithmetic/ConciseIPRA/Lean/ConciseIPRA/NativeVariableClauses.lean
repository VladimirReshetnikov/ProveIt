import ConciseIPRA.NativeNameClauses
import ConciseIPRA.NativeNewestVariable

/-!
# Five rules with clauses and substitution for the newest variable

`VCPrf` is the forward clause calculus of the package
`Research/variable_substitution`.  Formulas are equations and `D` over terms
in full normal form, and a context is a list of clauses `[A; y.B(y)]`.  There
are five rules:

* **Refl**: `t = t`;
* **Sub**: from `x = t`, for the newest variable `x`, and `u = v` infer
  `v = u[t/x]`;
* **Use**: from the antecedent of a clause infer an instance of its
  consequent;
* **Elim**: from `D_{x,y} B` and a derivation of `A` under the clause
  `[B(b, 0); y.B(b, y)]` with `b` fresh, infer `A`;
* **Intro**: from `B(t, η) ⊢ B(t, S z)` with `z` fresh infer `D_{x,y} B`, with
  the start `η` of `NativeOneIntro`.

There is no `Q`, no computation rule, and no transport in a template: the only
equality rule besides reflexivity substitutes for one variable, the newest.

That rule is not stable under weakening by a new variable, which changes the
newest variable, so derivations of `VCPrf` cannot be weakened or renamed.  The
translation of the six-rule calculus `F6Prf` is therefore generalized over
renamings of the source, with an invariant on contexts that is a membership
and not a derivability (`F6Prf.toVC`): a hypothesis `X` is represented by the
assumption clause of its `Q`-free form or, for `Q_y B`, by the closure clause
(`Cl.rep`).  Premises that are needed under further variables are obtained
from the induction hypothesis at a shifted renaming.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm
open Tm (zero succ iter)

variable {n m : ℕ}

/-- Derivability with Refl, Sub, Use, Elim and Intro on full normal forms. -/
inductive VCPrf : {n : ℕ} → List (Cl n) → NFm n → Prop
  | refl {n : ℕ} {Γ : List (Cl n)} (t : Tm n) : VCPrf Γ (.eq t.full t.full)
  /-- Sub: from `x = t`, for the newest variable `x`, and `u = v` infer
  `v = u[t/x]`. -/
  | vsub0 {n : ℕ} {Γ : List (Cl (n + 1))} {t u v : Tm (n + 1)}
      (h₁ : VCPrf Γ (.eq (Syn.var 0) t)) (h₂ : VCPrf Γ (.eq u v)) :
      VCPrf Γ (.eq v (Syn.subst (Function.update Syn.var 0 t) u).full)
  /-- Use: from the antecedent of a clause infer the full normal form of an
  instance of its consequent. -/
  | use {n : ℕ} {Γ : List (Cl n)} {c : Cl n} (t : Tm n) (hc : c ∈ Γ) (h : VCPrf Γ c.ante) :
      VCPrf Γ (c.cons.subst (inst t)).full
  /-- Elim: open `D_{x,y} B` at a fresh `b`, which adds the clause
  `[B(b, 0); y.B(b, y)]`. -/
  | elim {n : ℕ} {Γ : List (Cl n)} {B : NFm (n + 2)} {A : NFm n} (h₁ : VCPrf Γ (.D B))
      (h₂ : VCPrf (⟨(B.subst (inst zero)).full, B⟩ :: Γ.map Cl.shift) A.shift) : VCPrf Γ A
  /-- Intro: from `B(t, η) ⊢ B(t, S z)` with `z` fresh infer `D_{x,y} B`. -/
  | intro {n : ℕ} {Γ : List (Cl n)} (B : NFm (n + 2)) (t : Tm n) (hB : B.full = B)
      (hQ : B.QFree) (ht : t.full = t)
      (h : VCPrf (Cl.asm ((B.subst (up (inst t))).subst (repl (NFm.start B t))).full
          :: Γ.map Cl.shift)
        ((B.subst (up (inst t))).subst (repl (succ (var 0)))).full) :
      VCPrf Γ (.D B)

namespace VCPrf

variable {Γ Δ : List (Cl n)} {A : NFm n}

/-- An ordinary assumption of the context holds. -/
theorem asmHyp {X : NFm n} (hX : X.full = X) (h : Cl.asm X ∈ Γ) : VCPrf Γ X := by
  have k : VCPrf Γ (X.shift.subst (inst zero)).full :=
    VCPrf.use (c := Cl.asm X) zero h (VCPrf.refl zero)
  rwa [NFm.subst_inst_shift, hX] at k

/-! ### Soundness in the kernel -/

theorem toNPrf (h : VCPrf Γ A) : NPrf (Γ.map Cl.toN) A := by
  induction h with
  | refl t => exact NPrf.eqRefl _
  | @vsub0 _ Γ t u v _ _ ih₁ ih₂ =>
    have k := NPrf.trOne
      (Syn.subst (Function.update (fun j => (Syn.var j.succ : Tm _)) 0 (Syn.var 0)) u) ih₁
      (u := v) (by
        rw [Tm.subst_inst_abs, Function.update_eq_self, Syn.subst_id]; exact ih₂)
    rw [Tm.subst_inst_abs] at k
    exact NPrf.eqTrans k (NPrf.eqFull _)
  | @use _ Γ c t hc _ ih =>
    exact (equivFull _).mp
      (NPrf.allE t (NPrf.impE (.hyp (List.mem_map_of_mem (f := Cl.toN) hc)) ih))
  | @elim _ Γ B A _ _ ih₁ ih₂ =>
    rw [List.map_cons, Cl.map_toN_shift] at ih₂
    have cl : NPrf (.Q B :: (Γ.map Cl.toN).map NFm.shift)
        (NFm.imp (B.subst (inst zero)).full (NFm.all B)) :=
      NPrf.impI (NPrf.impE ((NPrf.qComp (NEquiv.refl B)).mpr NPrf.hyp0).wk
        ((equivFull _).mpr NPrf.hyp0))
    exact .dE ih₁ (NPrf.cut1 cl (NPrf.wkUnder ih₂))
  | @intro _ Γ B t _ _ _ _ ih =>
    rw [List.map_cons, Cl.map_toN_shift] at ih
    exact .ofDI B t ((equivFull _).mpr
      (NPrf.cut1 (NPrf.asmClause ((equivFull _).mp NPrf.hyp0)) (NPrf.wkUnder ih)))

/-- From `Q`-free clauses only `Q`-free formulas are derivable. -/
theorem qfree (h : VCPrf Γ A) : (∀ c ∈ Γ, c.ante.QFree ∧ c.cons.QFree) → A.QFree := by
  induction h with
  | refl t => exact fun _ => trivial
  | vsub0 _ _ _ _ => exact fun _ => trivial
  | use t hc _ _ =>
    exact fun hΓ => (NFm.qfree_full _).2 ((NFm.qfree_subst _ _).2 (hΓ _ hc).2)
  | @elim _ Γ B A _ _ ih₁ ih₂ =>
    intro hΓ
    have hB : B.QFree := ih₁ hΓ
    refine (NFm.qfree_subst A _).1 (ih₂ fun c hc => ?_)
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ⟨(NFm.qfree_full _).2 ((NFm.qfree_subst _ _).2 hB), hB⟩
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
      exact ⟨(NFm.qfree_subst _ _).2 (hΓ d hd).1, (NFm.qfree_subst _ _).2 (hΓ d hd).2⟩
  | intro B t hB hQ ht _ _ => exact fun _ => hQ

/-! ### Derived rules -/

/-- Introduction of the `D` formula that stands for `Q`, by cases. -/
theorem qI (M : NFm (n + 1)) (hM : M.full = M) (hQ : M.QFree)
    (h : VCPrf (Cl.asm (M.subst (repl zero)).full :: Γ.map Cl.shift)
      (M.subst (repl (succ (Syn.var 0)))).full) :
    VCPrf Γ (.D (M.subst (up fun i => Syn.var i.succ))) := by
  refine .intro _ (succ zero) (by rw [NFm.full_dummy, hM]) ((NFm.qfree_subst _ _).2 hQ) rfl ?_
  rw [NFm.start_of_not (fun h => by cases h.2), NFm.subst_dummy_inst]
  exact h

/-- The closure clause of a matrix gives the `D` formula that stands for `Q`. -/
theorem ofClause (M : NFm (n + 1)) (hM : M.full = M) (hQ : M.QFree)
    (hc : (⟨(M.subst (inst zero)).full, M⟩ : Cl n) ∈ Γ) :
    VCPrf Γ (.D (M.subst (up fun i => Syn.var i.succ))) := by
  refine qI M hM hQ ?_
  have ha : VCPrf (Cl.asm (M.subst (repl zero)).full :: Γ.map Cl.shift)
      (M.subst (inst zero)).full.shift := by
    rw [← NFm.full_shift, NFm.shift_subst_inst_zero]
    exact asmHyp (NFm.full_idem _) List.mem_cons_self
  have k : VCPrf (Cl.asm (M.subst (repl zero)).full :: Γ.map Cl.shift)
      ((M.subst (up fun i => Syn.var i.succ)).subst (inst (succ (Syn.var 0)))).full :=
    VCPrf.use (c := (⟨(M.subst (inst zero)).full, M⟩ : Cl n).shift) (succ (Syn.var 0))
      (List.mem_cons_of_mem _ (List.mem_map_of_mem hc)) ha
  rwa [NFm.subst_dummy_up_inst _ (succ (Syn.var 0))] at k

/-- `QE`, for the `D` formula that stands for `Q`.  The instance at zero is
needed under the fresh variable of the elimination. -/
theorem qE (M : NFm (n + 1)) (t : Tm n)
    (h₁ : VCPrf Γ (.D (M.subst (up fun i => Syn.var i.succ))))
    (h₂ : ∀ c : Cl (n + 1), VCPrf (c :: Γ.map Cl.shift) (M.subst (inst zero)).full.shift) :
    VCPrf Γ (M.subst (inst t)).full := by
  refine .elim h₁ ?_
  have ha : VCPrf ((⟨((M.subst (up fun i => Syn.var i.succ)).subst (inst zero)).full,
        M.subst (up fun i => Syn.var i.succ)⟩ : Cl (n + 1)) :: Γ.map Cl.shift)
      ((M.subst (up fun i => Syn.var i.succ)).subst (inst zero)).full := by
    have k := h₂ ⟨((M.subst (up fun i => Syn.var i.succ)).subst (inst zero)).full,
      M.subst (up fun i => Syn.var i.succ)⟩
    rwa [← NFm.full_shift, NFm.shift_subst_inst_zero,
      ← NFm.subst_dummy_up_inst M (zero : Tm (n + 1))] at k
  have k : VCPrf ((⟨((M.subst (up fun i => Syn.var i.succ)).subst (inst zero)).full,
        M.subst (up fun i => Syn.var i.succ)⟩ : Cl (n + 1)) :: Γ.map Cl.shift)
      ((M.subst (up fun i => Syn.var i.succ)).subst (inst (Syn.shift t))).full :=
    VCPrf.use (c := ⟨_, _⟩) (Syn.shift t) List.mem_cons_self ha
  rwa [NFm.subst_dummy_up_inst _ (Syn.shift t), ← NFm.shift_subst_inst, NFm.full_shift] at k

/-- Numerical cases, for a normal matrix. -/
theorem cases (M : NFm (n + 1)) (hM : M.full = M) (hQ : M.QFree) (t : Tm n)
    (h0 : ∀ c : Cl (n + 1), VCPrf (c :: Γ.map Cl.shift) (M.subst (inst zero)).full.shift)
    (hS : VCPrf (Cl.asm (M.subst (repl zero)).full :: Γ.map Cl.shift)
      (M.subst (repl (succ (Syn.var 0)))).full) : VCPrf Γ (M.subst (inst t)).full :=
  qE M t (qI M hM hQ hS) h0

/-- **The naming packet.**  Transport, from the two given equations under two
fresh variables: the packet is opened at a fresh `b`, its rows give `h(b) = u`
and `b = t`, and one substitution for the newest variable `b` gives
`u = h(t)`. -/
theorem packet (S T U : Tm n) (H : Tm (n + 1))
    (he : ∀ (c : Cl (n + 1)) (c' : Cl (n + 2)),
      VCPrf (c' :: (c :: Γ.map Cl.shift).map Cl.shift)
        (.eq (Syn.shift (Syn.shift S.full)) (Syn.shift (Syn.shift T.full))))
    (hk : ∀ (c : Cl (n + 1)) (c' : Cl (n + 2)),
      VCPrf (c' :: (c :: Γ.map Cl.shift).map Cl.shift)
        (.eq (Syn.shift (Syn.shift (Syn.subst (inst S) H).full)) (Syn.shift (Syn.shift U.full)))) :
    VCPrf Γ (.eq U.full (Syn.subst (inst T) H).full) := by
  have row : ∀ c : Tm (n + 1), ((NFm.pkt H T U).full.subst (inst c)).full
      = ((NFm.pkt H T U).subst (inst c)).full := fun c =>
    NFm.full_subst_congr (NFm.full_idem _) fun _ => rfl
  have hD : VCPrf Γ (.D (NFm.pkt H T U).full) := by
    refine .intro _ S.full (NFm.full_idem _) trivial (Tm.full_idem _) ?_
    have eA : (((NFm.pkt H T U).full.subst (up (inst S.full))).subst
          (repl (succ (Syn.var 0)))).full
        = ((NFm.pktF S T U (Syn.subst (inst S) H)).full.subst
            (inst (Tm.npar (succ (Syn.var 0))))).full := by
      rw [NFm.full_subst_congr (A' := (NFm.pkt H T U).subst (up (inst S)))
          (σ' := repl (succ (Syn.var 0)))
          (NFm.full_subst_congr (NFm.full_idem _) (Tm.full_up_congr (Tm.full_inst S)))
          (fun _ => rfl),
        NFm.pkt_wit,
        NFm.full_subst_congr (A' := NFm.pktF S T U (Syn.subst (inst S) H))
          (σ' := inst (Tm.npar (succ (Syn.var 0)))) (NFm.full_idem _) (fun _ => rfl),
        NFm.pktF_inst]
      show NFm.eq (Tm.full _) (Tm.full _) = NFm.eq (Tm.full _) (Tm.full _)
      rw [Tm.full_sel_succ' (c := succ (Syn.var 0)) (x := Syn.var 0) rfl,
        Tm.full_sel_succ' (c := succ (Syn.var 0)) (x := Syn.var 0) rfl]
    rw [eA]
    refine cases (NFm.pktF S T U (Syn.subst (inst S) H)).full (NFm.full_idem _) trivial _
      (fun c => ?_) ?_
    · rw [NFm.full_subst_congr (A' := NFm.pktF S T U (Syn.subst (inst S) H)) (σ' := inst zero)
        (NFm.full_idem _) (fun _ => rfl), NFm.pktF_zero]
      exact he _ _
    · rw [NFm.full_subst_congr (A' := NFm.pktF S T U (Syn.subst (inst S) H))
        (σ' := repl (succ (Syn.var 0))) (NFm.full_idem _) (fun _ => rfl), NFm.pktF_succ]
      exact hk _ _
  refine .elim hD ?_
  have base : VCPrf ((⟨((NFm.pkt H T U).full.subst (inst zero)).full, (NFm.pkt H T U).full⟩
        : Cl (n + 1)) :: Γ.map Cl.shift) ((NFm.pkt H T U).full.subst (inst zero)).full := by
    rw [row, NFm.pkt_row0]
    exact .refl zero
  have r1 : VCPrf ((⟨((NFm.pkt H T U).full.subst (inst zero)).full, (NFm.pkt H T U).full⟩
        : Cl (n + 1)) :: Γ.map Cl.shift) ((NFm.pkt H T U).full.subst (inst (succ zero))).full :=
    VCPrf.use (c := ⟨_, _⟩) (succ zero) List.mem_cons_self base
  have r2 : VCPrf ((⟨((NFm.pkt H T U).full.subst (inst zero)).full, (NFm.pkt H T U).full⟩
        : Cl (n + 1)) :: Γ.map Cl.shift)
      ((NFm.pkt H T U).full.subst (inst (succ (succ zero)))).full :=
    VCPrf.use (c := ⟨_, _⟩) (succ (succ zero)) List.mem_cons_self base
  rw [row (succ zero), NFm.pkt_row1] at r1
  rw [row (succ (succ zero)), NFm.pkt_row2] at r2
  have k := VCPrf.vsub0 r2 r1
  have e : (Syn.subst (Function.update Syn.var 0 (Syn.shift T.full)) H.full).full
      = Syn.shift (Syn.subst (inst T) H).full := by
    rw [Tm.full_subst_congr (t' := H) (σ' := Function.update Syn.var 0 (Syn.shift T))
      (Tm.full_idem H) (fun i => by
        by_cases hi : i = 0
        · subst hi; simp
        · simp [Function.update_of_ne hi]),
      ← Tm.psi_var, Tm.psi_var0, Tm.full_shift]
  rw [e] at k
  exact k

end VCPrf

/-! ### The representation of hypotheses by clauses -/

namespace Cl

/-- The clause that stands for a hypothesis: the closure clause for `Q_y B`,
and the assumption clause of the `Q`-free form otherwise. -/
def rep : {n : ℕ} → NFm n → Cl n
  | _, .eq s t => asm (NFm.unQ (.eq s t)).full
  | _, .Q B => ⟨((NFm.unQ B).full.subst (inst zero)).full, (NFm.unQ B).full⟩
  | _, .D B => asm (NFm.unQ (.D B)).full

theorem rep_shift (X : NFm n) : (rep X).shift = rep X.shift := by
  cases X with
  | eq s t =>
    show (asm (NFm.unQ (NFm.eq s t)).full).shift = asm (NFm.unQ (NFm.eq s t).shift).full
    rw [asm_shift, NFm.unQ_shift, NFm.full_shift]
  | Q B =>
    have eM : (NFm.unQ (B.subst (up fun i => Syn.var i.succ))).full
        = (NFm.unQ B).full.subst (up fun i => Syn.var i.succ) := by
      rw [NFm.unQ_subst, NFm.full_dummy]
    show (⟨((NFm.unQ B).full.subst (inst zero)).full.shift,
        (NFm.unQ B).full.subst (up fun i => Syn.var i.succ)⟩ : Cl (n + 1))
      = ⟨((NFm.unQ (B.subst (up fun i => Syn.var i.succ))).full.subst (inst zero)).full,
          (NFm.unQ (B.subst (up fun i => Syn.var i.succ))).full⟩
    rw [eM, ← NFm.full_shift]
    unfold NFm.shift
    rw [NFm.subst_inst]
    rfl
  | D B =>
    show (asm (NFm.unQ (NFm.D B)).full).shift = asm (NFm.unQ (NFm.D B).shift).full
    rw [asm_shift, NFm.unQ_shift, NFm.full_shift]

/-- The invariant of the translation: every hypothesis, renamed, is
represented in the target context. -/
def Inv (ξ : Fin n → Fin m) (Γ : List (NFm n)) (Δ : List (Cl m)) : Prop :=
  ∀ X ∈ Γ, asm (NFm.unQ (X.subst fun i => (Syn.var (ξ i) : Tm m))).full ∈ Δ
    ∨ rep (X.subst fun i => (Syn.var (ξ i) : Tm m)) ∈ Δ

theorem lift_rep {Y : NFm n} {Δ : List (Cl n)}
    (h : asm (NFm.unQ Y).full ∈ Δ ∨ rep Y ∈ Δ) (c : Cl (n + 1)) :
    asm (NFm.unQ Y.shift).full ∈ c :: Δ.map shift ∨ rep Y.shift ∈ c :: Δ.map shift := by
  rcases h with h | h
  · left
    rw [NFm.unQ_shift, NFm.full_shift, ← asm_shift]
    exact List.mem_cons_of_mem _ (List.mem_map_of_mem h)
  · right
    rw [← rep_shift]
    exact List.mem_cons_of_mem _ (List.mem_map_of_mem h)

end Cl

theorem NFm.rn_succ (X : NFm n) (ξ : Fin n → Fin m) :
    X.subst (fun i => (Syn.var (ξ i).succ : Tm (m + 1)))
      = (X.subst fun i => (Syn.var (ξ i) : Tm m)).shift :=
  NFm.subst_shift_fun X fun i => (Syn.var (ξ i) : Tm m)

theorem NFm.shift_uprn (X : NFm n) (ξ : Fin n → Fin m) :
    X.shift.subst (fun i => (Syn.var (Tm.upRen ξ i) : Tm (m + 1)))
      = (X.subst fun i => (Syn.var (ξ i) : Tm m)).shift := by
  rw [← Tm.up_rn, NFm.shift_subst_up]

namespace Cl

/-- The invariant, for the same hypotheses under one more variable. -/
theorem Inv.deeper {ξ : Fin n → Fin m} {Γ : List (NFm n)} {Δ : List (Cl m)} (s : Inv ξ Γ Δ)
    (c : Cl (m + 1)) : Inv (fun i => (ξ i).succ) Γ (c :: Δ.map shift) := by
  intro X hX
  have k := lift_rep (s X hX) c
  rw [← NFm.rn_succ] at k
  exact k

/-- The invariant, under a binder that adds one hypothesis. -/
theorem Inv.under {ξ : Fin n → Fin m} {Γ : List (NFm n)} {Δ : List (Cl m)} (s : Inv ξ Γ Δ)
    (c : Cl (m + 1)) {X' : NFm (n + 1)}
    (h' : asm (NFm.unQ (X'.subst fun i => (Syn.var (Tm.upRen ξ i) : Tm (m + 1)))).full
        ∈ c :: Δ.map shift
      ∨ rep (X'.subst fun i => (Syn.var (Tm.upRen ξ i) : Tm (m + 1))) ∈ c :: Δ.map shift) :
    Inv (Tm.upRen ξ) (X' :: Γ.map NFm.shift) (c :: Δ.map shift) := by
  intro X hX
  rcases List.mem_cons.1 hX with rfl | hX
  · exact h'
  · obtain ⟨X₀, hX₀, rfl⟩ := List.mem_map.1 hX
    have k := lift_rep (s X₀ hX₀) c
    rw [← NFm.shift_uprn] at k
    exact k

end Cl

/-- A represented hypothesis is derivable. -/
theorem VCPrf.ofRep {Δ : List (Cl n)} {Y : NFm n}
    (h : Cl.asm (NFm.unQ Y).full ∈ Δ ∨ Cl.rep Y ∈ Δ) : VCPrf Δ (NFm.unQ Y).full := by
  rcases h with h | h
  · exact VCPrf.asmHyp (NFm.full_idem _) h
  · cases Y with
    | eq s t => exact VCPrf.asmHyp (NFm.full_idem _) h
    | Q B =>
      show VCPrf Δ (.D ((NFm.unQ B).subst (up fun i => Syn.var i.succ)).full)
      rw [NFm.full_dummy]
      exact VCPrf.ofClause _ (NFm.full_idem _) ((NFm.qfree_full _).2 (NFm.qfree_unQ B)) h
    | D B => exact VCPrf.asmHyp (NFm.full_idem _) h

/-! ### Completeness, from the six-rule calculus -/

/-- Every derivation of the six-rule calculus on full normal forms, under any
renaming, is a derivation with the five rules, in every context that
represents its hypotheses.  No derivation of `VCPrf` is renamed or weakened. -/
theorem F6Prf.toVC {Γ : List (NFm n)} {A : NFm n} (h : F6Prf Γ A) :
    ∀ {m : ℕ} (ξ : Fin n → Fin m) {Δ : List (Cl m)}, Cl.Inv ξ Γ Δ →
      VCPrf Δ (NFm.unQ (A.subst fun i => (Syn.var (ξ i) : Tm m))).full := by
  induction h with
  | hyp h => intro m ξ Δ sΓ; exact VCPrf.ofRep (sΓ _ h)
  | refl t =>
    intro m ξ Δ _
    exact VCPrf.refl (Syn.subst (fun i => (Syn.var (ξ i) : Tm m)) t.full)
  | @trOne n' Γ h s t u _ _ ih₁ ih₂ =>
    intro m ξ Δ sΓ
    have eh : ∀ x : Tm n',
        (Syn.subst (fun i => (Syn.var (ξ i) : Tm m)) (Syn.subst (inst x) h).full).full
          = (Syn.subst (inst (Syn.subst (fun i => (Syn.var (ξ i) : Tm m)) x))
              (Syn.subst (up fun i => (Syn.var (ξ i) : Tm m)) h)).full := fun x => by
      rw [← Tm.full_rn, Tm.full_idem, Syn.subst_subst_inst]
    show VCPrf Δ (.eq (Syn.subst (fun i => (Syn.var (ξ i) : Tm m)) u).full
      (Syn.subst (fun i => (Syn.var (ξ i) : Tm m)) (Syn.subst (inst t) h).full).full)
    rw [eh]
    refine VCPrf.packet (Syn.subst (fun i => (Syn.var (ξ i) : Tm m)) s) _ _ _
      (fun c c' => ?_) (fun c c' => ?_)
    · have k := ih₁ (fun i => (ξ i).succ.succ) ((sΓ.deeper c).deeper c')
      rw [NFm.rn_succ _ (fun i => (ξ i).succ), NFm.rn_succ, NFm.unQ_shift, NFm.unQ_shift,
        NFm.full_shift, NFm.full_shift] at k
      exact k
    · have k := ih₂ (fun i => (ξ i).succ.succ) ((sΓ.deeper c).deeper c')
      rw [NFm.rn_succ _ (fun i => (ξ i).succ), NFm.rn_succ, NFm.unQ_shift, NFm.unQ_shift,
        NFm.full_shift, NFm.full_shift] at k
      change VCPrf _ (.eq (Syn.shift (Syn.shift
          (Syn.subst (fun i => (Syn.var (ξ i) : Tm m)) (Syn.subst (inst s) h).full).full))
        (Syn.shift (Syn.shift (Syn.subst (fun i => (Syn.var (ξ i) : Tm m)) u).full))) at k
      rw [eh] at k
      exact k
  | @qE n' Γ B t _ _ ih₁ ih₂ =>
    intro m ξ Δ sΓ
    have e : ∀ u : Tm n',
        (NFm.unQ ((B.subst (inst u)).full.subst fun i => (Syn.var (ξ i) : Tm m))).full
          = ((NFm.unQ (B.subst (up fun i => (Syn.var (ξ i) : Tm m)))).full.subst
              (inst (Syn.subst (fun i => (Syn.var (ξ i) : Tm m)) u))).full := fun u => by
      rw [← NFm.full_rn, NFm.unQ_full, NFm.full_idem, NFm.subst_inst,
        NFm.unQ_subst (B.subst (up fun i => (Syn.var (ξ i) : Tm m)))
          (inst (Syn.subst (fun i => (Syn.var (ξ i) : Tm m)) u))]
      exact NFm.full_subst_congr (NFm.full_idem _).symm fun _ => rfl
    have h₁ : VCPrf Δ (.D ((NFm.unQ (B.subst (up fun i => (Syn.var (ξ i) : Tm m)))).full.subst
        (up fun i => Syn.var i.succ))) := by
      rw [← NFm.full_dummy]
      exact ih₁ ξ sΓ
    rw [e]
    refine VCPrf.qE _ _ h₁ fun c => ?_
    have k := ih₂ (fun i => (ξ i).succ) (sΓ.deeper c)
    rw [NFm.rn_succ, NFm.unQ_shift, NFm.full_shift, e] at k
    exact k
  | @dE n' Γ B A _ _ ih₁ ih₂ =>
    intro m ξ Δ sΓ
    have h₁ : VCPrf Δ (.D (NFm.unQ (B.subst (up (up fun i => (Syn.var (ξ i) : Tm m))))).full) :=
      ih₁ ξ sΓ
    refine .elim h₁ ?_
    have k := ih₂ (Tm.upRen ξ)
      (sΓ.under
        ⟨((NFm.unQ (B.subst (up (up fun i => (Syn.var (ξ i) : Tm m))))).full.subst
            (inst zero)).full,
          (NFm.unQ (B.subst (up (up fun i => (Syn.var (ξ i) : Tm m))))).full⟩ (X' := .Q B)
        (Or.inr (by
          show Cl.rep (NFm.Q (B.subst (up fun i => (Syn.var (Tm.upRen ξ i) : Tm (m + 1))))) ∈ _
          rw [← Tm.up_rn]
          exact List.mem_cons_self)))
    rw [NFm.shift_uprn, NFm.unQ_shift, NFm.full_shift] at k
    exact k
  | @dI n' Γ B t hB ht _ ih =>
    intro m ξ Δ sΓ
    have hB₂ : (B.subst (up (up fun i => (Syn.var (ξ i) : Tm m)))).full
        = B.subst (up (up fun i => (Syn.var (ξ i) : Tm m))) := by
      rw [Tm.up_rn ξ, Tm.up_rn, NFm.full_rn, hB]
    have hB' : (NFm.unQ (B.subst (up (up fun i => (Syn.var (ξ i) : Tm m))))).full
        = NFm.unQ (B.subst (up (up fun i => (Syn.var (ξ i) : Tm m)))) := by
      rw [← NFm.unQ_full, hB₂]
    have e : ∀ d : Tm (n' + 1),
        (NFm.unQ (((B.subst (up (inst t))).subst (repl d)).full.subst
            fun i => (Syn.var (Tm.upRen ξ i) : Tm (m + 1)))).full
          = (((NFm.unQ (B.subst (up (up fun i => (Syn.var (ξ i) : Tm m))))).subst
              (up (inst (Syn.subst (fun i => (Syn.var (ξ i) : Tm m)) t)))).subst
              (repl (Syn.subst (up fun i => (Syn.var (ξ i) : Tm m)) d))).full := fun d => by
      rw [← NFm.full_rn, NFm.unQ_full, NFm.full_idem, ← Tm.up_rn, NFm.subst_repl_up,
        NFm.subst_up_inst,
        NFm.unQ_subst ((B.subst (up (up fun i => (Syn.var (ξ i) : Tm m)))).subst
          (up (inst (Syn.subst (fun i => (Syn.var (ξ i) : Tm m)) t))))
          (repl (Syn.subst (up fun i => (Syn.var (ξ i) : Tm m)) d)),
        NFm.unQ_subst (B.subst (up (up fun i => (Syn.var (ξ i) : Tm m))))
          (up (inst (Syn.subst (fun i => (Syn.var (ξ i) : Tm m)) t)))]
    show VCPrf Δ (.D (NFm.unQ (B.subst (up (up fun i => (Syn.var (ξ i) : Tm m))))).full)
    rw [hB']
    refine .intro _ (Syn.subst (fun i => (Syn.var (ξ i) : Tm m)) t) hB' (NFm.qfree_unQ _)
      (by rw [Tm.full_rn, ht]) ?_
    rw [NFm.start_unQ, NFm.start_rn]
    have k := ih (Tm.upRen ξ)
      (sΓ.under
        (Cl.asm (((NFm.unQ (B.subst (up (up fun i => (Syn.var (ξ i) : Tm m))))).subst
          (up (inst (Syn.subst (fun i => (Syn.var (ξ i) : Tm m)) t)))).subst
          (repl (Syn.subst (up fun i => (Syn.var (ξ i) : Tm m)) (NFm.start B t)))).full)
        (Or.inl (by rw [e]; exact List.mem_cons_self)))
    rw [e] at k
    exact k

variable {Γ : List (NFm n)} {A : NFm n}

/-- **Five rules with substitution for the newest variable.**  The kernel
derives a sequent exactly when Refl, Sub, Use, Elim and Intro derive the full
normal form of its `Q`-free form from the corresponding assumptions. -/
theorem vcprf_iff_nprf :
    VCPrf (Γ.map fun X => Cl.asm (NFm.unQ X).full) (NFm.unQ A).full ↔ NPrf Γ A := by
  constructor
  · intro h
    refine (NEquiv.unQ A).mp ((equivFull _).mpr (h.toNPrf.cut fun C hC => ?_))
    rw [List.map_map, List.mem_map] at hC
    obtain ⟨X, hX, rfl⟩ := hC
    exact NPrf.asmClause ((equivFull _).mp ((NEquiv.unQ X).mpr (.hyp hX)))
  · intro h
    have e : ∀ X : NFm n, (X.subst fun i => (Syn.var (id i) : Tm n)) = X := fun X =>
      NFm.subst_id X
    have k := (f6prf_iff_nprf.2 h).toVC id (Δ := Γ.map fun X => Cl.asm (NFm.unQ X).full)
      fun Y hY => by
        obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hY
        left
        rw [e, NFm.unQ_full, NFm.full_idem]
        exact List.mem_map_of_mem (f := fun X => Cl.asm (NFm.unQ X).full) hX
    rwa [e, NFm.unQ_full, NFm.full_idem] at k

/-- On `Q`-free sequents the five rules derive exactly what the kernel derives,
up to full normal forms. -/
theorem vcprf_iff_nprf_of_qfree (hΓ : ∀ X ∈ Γ, X.QFree) (hA : A.QFree) :
    VCPrf (Γ.map fun X => Cl.asm X.full) A.full ↔ NPrf Γ A := by
  have e : (Γ.map fun X => Cl.asm (NFm.unQ X).full) = Γ.map fun X => Cl.asm X.full :=
    List.map_congr_left fun X hX => by rw [NFm.unQ_of_qfree X (hΓ X hX)]
  rw [← vcprf_iff_nprf, e, NFm.unQ_of_qfree A hA]

/-- The five rules prove a sequent in this form exactly when iPRA proves its
reading. -/
theorem vcprf_iff_pra :
    VCPrf (Γ.map fun X => Cl.asm (NFm.unQ X).full) (NFm.unQ A).full
      ↔ (Γ.map NFm.toPRA ⊢[PRAAx] A.toPRA) :=
  vcprf_iff_nprf.trans native_iff_pra

end LeanProofs.ConciseIPRA
