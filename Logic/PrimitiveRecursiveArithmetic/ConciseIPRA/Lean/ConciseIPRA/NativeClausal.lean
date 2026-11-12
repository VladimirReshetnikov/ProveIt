import ConciseIPRA.NativeEval
import ConciseIPRA.NativeDiagonal
import ConciseIPRA.NativeComposite

/-!
# Five rules with clauses in place of `Q`

`CPrf` is the raw clause calculus of the packages `Research/raw_clausal`,
`Research/reduced_clause_calculus`, `Research/rootfree_clausal` and
`Research/clausal_two_case`.  Its formulas are equations and `D` only.  A
context is a list of *clauses* `[A; y.B(y)]`, read `A → ∀ y, B(y)`; an ordinary
assumption `A` is the clause `[0 = 0; v.A]`.  There are five rules:

* **Refl**: `t = t`;
* **Eval**, in its two cases (`NativeEval`);
* **Use**: from `A` infer `B(t)`, for a clause `[A; y.B(y)]` of the context;
* **Elim**: from `D_{x,y} B` and a derivation of `A` from the clause
  `[B(b, 0); y.B(b, y)]` with `b` fresh, infer `A`;
* **Intro**: from `B(t, η) ⊢ B(t, S z)` with `z` fresh infer `D_{x,y} B`, with
  the start `η` of `NativeOneIntro`.

Terms are the iterator terms with ordinary substitution.  There is no `Q`, no
computation axiom, no transport rule and no template.

* `CPrf.qfree`: from `Q`-free clauses only `Q`-free formulas are derivable;
* `cprf_iff_nprf_of_qfree`: on `Q`-free sequents `CPrf` derives exactly what the
  kernel derives;
* `cprf_iff_nprf`: for arbitrary native sequents, with `Q_y B` rewritten as
  `D_{x,y} B` with `x` unused (`NFm.unQ`): `NPrf Γ A ↔ CPrf (asm ∘ unQ) Γ (unQ A)`.

Completeness is by translating the six-rule calculus `EPrf` rule by rule
(`EPrf.toCPrf`): reflexivity, Eval and the introduction are the same rules, and
only `QE` and `DE` need an argument.  The structural rules that this uses,
weakening, renaming and cut of an ordinary assumption, are direct inductions.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open Tm (zero succ iter)

variable {n m : ℕ}

namespace Tm

theorem up_rn (ξ : Fin n → Fin m) :
    up (fun i => (Syn.var (ξ i) : Tm m)) = fun i => Syn.var (Tm.upRen ξ i) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

end Tm

namespace NFm

/-- No `Q` occurs in the formula. -/
def QFree : {n : ℕ} → NFm n → Prop
  | _, .eq _ _ => True
  | _, .Q _ => False
  | _, .D B => QFree B

theorem qfree_subst (A : NFm n) : ∀ {m : ℕ} (σ : Fin n → Tm m), (A.subst σ).QFree ↔ A.QFree := by
  induction A with
  | eq s t => intro m σ; exact Iff.rfl
  | Q B _ => intro m σ; exact Iff.rfl
  | D B ih => intro m σ; exact ih _

/-- `Q_y B` rewritten as `D_{x,y} B` with `x` unused. -/
def unQ : {n : ℕ} → NFm n → NFm n
  | _, .eq s t => .eq s t
  | _, .Q B => .D ((unQ B).subst (up fun i => Syn.var i.succ))
  | _, .D B => .D (unQ B)

theorem subst_dummy_comm (X : NFm (n + 1)) (σ : Fin n → Tm m) :
    (X.subst (up σ)).subst (up fun i => Syn.var i.succ)
      = (X.subst (up fun i => Syn.var i.succ)).subst (up (up σ)) := by
  rw [subst_subst, subst_subst]
  refine X.subst_ext fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp only [up_succ, Syn.shift_var, Syn.subst_var, Syn.subst_up_shift]
    rfl

theorem unQ_subst (A : NFm n) : ∀ {m : ℕ} (σ : Fin n → Tm m),
    unQ (A.subst σ) = (unQ A).subst σ := by
  induction A with
  | eq s t => intro m σ; rfl
  | Q B ih => intro m σ; simp only [subst_Q, unQ, ih, subst_D, subst_dummy_comm]
  | D B ih => intro m σ; simp only [subst_D, unQ, ih]

theorem unQ_shift (A : NFm n) : unQ A.shift = (unQ A).shift := unQ_subst A _

theorem qfree_unQ (A : NFm n) : (unQ A).QFree := by
  induction A with
  | eq s t => trivial
  | Q B ih => exact (qfree_subst _ _).2 ih
  | D B ih => exact ih

theorem unQ_of_qfree (A : NFm n) (h : A.QFree) : unQ A = A := by
  induction A with
  | eq s t => rfl
  | Q B _ => exact h.elim
  | D B ih => exact congrArg NFm.D (ih h)

theorem start_unQ (B : NFm (n + 2)) (t : Tm n) : start (unQ B) t = start B t := by
  cases B <;> cases t <;> rfl

theorem start_rn (B : NFm (n + 2)) (t : Tm n) (ξ : Fin n → Fin m) :
    start (B.subst (up (up fun i => (Syn.var (ξ i) : Tm m))))
        (Syn.subst (fun i => (Syn.var (ξ i) : Tm m)) t)
      = Syn.subst (up fun i => (Syn.var (ξ i) : Tm m)) (start B t) := by
  cases B <;> cases t <;> rfl

end NFm

/-- A clause `[A; y.B(y)]`, read `A → ∀ y, B(y)`. -/
structure Cl (n : ℕ) where
  /-- The antecedent. -/
  ante : NFm n
  /-- The consequent, with one more variable. -/
  cons : NFm (n + 1)

namespace Cl

def subst (c : Cl n) (σ : Fin n → Tm m) : Cl m := ⟨c.ante.subst σ, c.cons.subst (up σ)⟩

def shift (c : Cl n) : Cl (n + 1) := ⟨c.ante.shift, c.cons.subst (up fun i => Syn.var i.succ)⟩

/-- An ordinary assumption, as the clause `[0 = 0; v.A]`. -/
def asm (A : NFm n) : Cl n := ⟨.eq zero zero, A.shift⟩

/-- The native reading of a clause. -/
def toN (c : Cl n) : NFm n := NFm.imp c.ante (NFm.all c.cons)

theorem shift_eq (c : Cl n) : c.shift = c.subst fun i => Syn.var i.succ := rfl

theorem asm_subst (A : NFm n) (σ : Fin n → Tm m) : (asm A).subst σ = asm (A.subst σ) := by
  show (⟨(NFm.eq zero zero).subst σ, A.shift.subst (up σ)⟩ : Cl m) = ⟨.eq zero zero, _⟩
  rw [NFm.shift_subst_up]
  rfl

theorem asm_shift (A : NFm n) : (asm A).shift = asm A.shift := asm_subst A _

theorem subst_up_shift (c : Cl n) (σ : Fin n → Tm m) :
    c.shift.subst (up σ) = (c.subst σ).shift := by
  show (⟨c.ante.shift.subst (up σ), (c.cons.subst (up fun i => Syn.var i.succ)).subst
      (up (up σ))⟩ : Cl (m + 1))
    = ⟨(c.ante.subst σ).shift, (c.cons.subst (up σ)).subst (up fun i => Syn.var i.succ)⟩
  rw [NFm.shift_subst_up, NFm.subst_dummy_comm]

theorem map_shift_subst (Γ : List (Cl n)) (σ : Fin n → Tm m) :
    (Γ.map shift).map (fun c => c.subst (up σ)) = (Γ.map fun c => c.subst σ).map shift := by
  rw [List.map_map, List.map_map]
  exact List.map_congr_left fun c _ => subst_up_shift c σ

theorem toN_subst (c : Cl n) (σ : Fin n → Tm m) : (c.subst σ).toN = c.toN.subst σ := by
  simp only [toN, subst, NFm.imp_subst, NFm.all_subst]

theorem map_toN_shift (Γ : List (Cl n)) : (Γ.map shift).map toN = (Γ.map toN).map NFm.shift := by
  rw [List.map_map, List.map_map]
  exact List.map_congr_left fun c _ => toN_subst c _

theorem map_asm_unQ_shift (Γ : List (NFm n)) :
    (Γ.map NFm.shift).map (fun X => asm (NFm.unQ X))
      = (Γ.map fun X => asm (NFm.unQ X)).map shift := by
  rw [List.map_map, List.map_map]
  refine List.map_congr_left fun X _ => ?_
  show asm (NFm.unQ X.shift) = (asm (NFm.unQ X)).shift
  rw [NFm.unQ_shift, asm_shift]

end Cl

/-- Derivability in the clause calculus. -/
inductive CPrf : {n : ℕ} → List (Cl n) → NFm n → Prop
  | refl {n : ℕ} {Γ : List (Cl n)} (t : Tm n) : CPrf Γ (.eq t t)
  | evalZero {n : ℕ} {Γ : List (Cl n)} (h : Tm (n + 1)) {a t r : Tm n}
      (h₁ : CPrf Γ (.eq a t)) (h₂ : CPrf Γ (.eq (iter zero a h) r)) : CPrf Γ (.eq r t)
  | evalSucc {n : ℕ} {Γ : List (Cl n)} {c a : Tm n} {h : Tm (n + 1)} {t r : Tm n}
      (h₁ : CPrf Γ (.eq (iter c a h) t)) (h₂ : CPrf Γ (.eq (iter (succ c) a h) r)) :
      CPrf Γ (.eq r (Syn.subst (inst t) h))
  /-- Use: from the antecedent of a clause infer an instance of its consequent. -/
  | use {n : ℕ} {Γ : List (Cl n)} {c : Cl n} (t : Tm n) (hc : c ∈ Γ) (h : CPrf Γ c.ante) :
      CPrf Γ (c.cons.subst (inst t))
  /-- Elim: open `D_{x,y} B` at a fresh `b`, which adds the clause
  `[B(b, 0); y.B(b, y)]`. -/
  | elim {n : ℕ} {Γ : List (Cl n)} {B : NFm (n + 2)} {A : NFm n} (h₁ : CPrf Γ (.D B))
      (h₂ : CPrf (⟨B.subst (inst zero), B⟩ :: Γ.map Cl.shift) A.shift) : CPrf Γ A
  /-- Intro: from `B(t, η) ⊢ B(t, S z)` with `z` fresh infer `D_{x,y} B`. -/
  | intro {n : ℕ} {Γ : List (Cl n)} (B : NFm (n + 2)) (t : Tm n) (hB : B.QFree)
      (h : CPrf (Cl.asm ((B.subst (up (inst t))).subst (repl (NFm.start B t)))
          :: Γ.map Cl.shift)
        ((B.subst (up (inst t))).subst (repl (succ (var 0))))) :
      CPrf Γ (.D B)

namespace CPrf

variable {Γ Δ : List (Cl n)} {A : NFm n}

/-- From `Q`-free clauses only `Q`-free formulas are derivable. -/
theorem qfree (h : CPrf Γ A) : (∀ c ∈ Γ, c.ante.QFree ∧ c.cons.QFree) → A.QFree := by
  induction h with
  | refl t => exact fun _ => trivial
  | evalZero h _ _ _ _ => exact fun _ => trivial
  | evalSucc _ _ _ _ => exact fun _ => trivial
  | use t hc _ _ => exact fun hΓ => (NFm.qfree_subst _ _).2 (hΓ _ hc).2
  | @elim _ Γ B A _ _ ih₁ ih₂ =>
    intro hΓ
    have hB : B.QFree := ih₁ hΓ
    refine (NFm.qfree_subst A _).1 (ih₂ fun c hc => ?_)
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ⟨(NFm.qfree_subst _ _).2 hB, hB⟩
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
      exact ⟨(NFm.qfree_subst _ _).2 (hΓ d hd).1, (NFm.qfree_subst _ _).2 (hΓ d hd).2⟩
  | intro B t hB _ _ => exact fun _ => hB

/-- An ordinary assumption of the context holds. -/
theorem asmHyp {X : NFm n} (h : Cl.asm X ∈ Γ) : CPrf Γ X := by
  have k : CPrf Γ (X.shift.subst (inst zero)) := CPrf.use (c := Cl.asm X) zero h (.refl zero)
  rwa [NFm.subst_inst_shift] at k

/-! ### Structural rules -/

theorem weaken (h : CPrf Γ A) : ∀ {Δ : List (Cl n)}, Γ ⊆ Δ → CPrf Δ A := by
  induction h with
  | refl t => intro Δ _; exact .refl t
  | evalZero h _ _ ih₁ ih₂ => intro Δ s; exact .evalZero h (ih₁ s) (ih₂ s)
  | evalSucc _ _ ih₁ ih₂ => intro Δ s; exact .evalSucc (ih₁ s) (ih₂ s)
  | use t hc _ ih => intro Δ s; exact .use t (s hc) (ih s)
  | elim _ _ ih₁ ih₂ =>
    intro Δ s
    exact .elim (ih₁ s) (ih₂ (List.cons_subset_cons _ (List.map_subset _ s)))
  | intro B t hB _ ih =>
    intro Δ s
    exact .intro B t hB (ih (List.cons_subset_cons _ (List.map_subset _ s)))

theorem wk {c : Cl n} (h : CPrf Γ A) : CPrf (c :: Γ) A := h.weaken (List.subset_cons_self _ _)

/-- Renaming of the free variables of a derivation. -/
theorem ren (h : CPrf Γ A) : ∀ {m : ℕ} (ξ : Fin n → Fin m),
    CPrf (Γ.map fun c => c.subst fun i => (Syn.var (ξ i) : Tm m))
      (A.subst fun i => (Syn.var (ξ i) : Tm m)) := by
  induction h with
  | refl t => intro m ξ; exact .refl _
  | evalZero h _ _ ih₁ ih₂ =>
    intro m ξ
    have h₂ := ih₂ ξ
    rw [NFm.subst_eq, Tm.subst_iter] at h₂
    exact .evalZero _ (ih₁ ξ) h₂
  | evalSucc _ _ ih₁ ih₂ =>
    intro m ξ
    have h₁ := ih₁ ξ
    have h₂ := ih₂ ξ
    rw [NFm.subst_eq, Tm.subst_iter] at h₁ h₂
    rw [NFm.subst_eq, Syn.subst_subst_inst]
    exact .evalSucc h₁ h₂
  | @use _ Γ c t hc _ ih =>
    intro m ξ
    rw [NFm.subst_inst]
    exact .use (c := c.subst fun i => (Syn.var (ξ i) : Tm m)) _
      (List.mem_map_of_mem (f := fun c : Cl _ => c.subst fun i => (Syn.var (ξ i) : Tm m)) hc)
      (ih ξ)
  | @elim _ Γ B A _ _ ih₁ ih₂ =>
    intro m ξ
    have h := ih₂ (Tm.upRen ξ)
    rw [← Tm.up_rn, List.map_cons, Cl.map_shift_subst, NFm.shift_subst_up] at h
    refine .elim (B := B.subst (up (up fun i => (Syn.var (ξ i) : Tm m)))) (ih₁ ξ) ?_
    have e : (⟨B.subst (inst zero), B⟩ : Cl _).subst (up fun i => (Syn.var (ξ i) : Tm m))
        = ⟨(B.subst (up (up fun i => (Syn.var (ξ i) : Tm m)))).subst (inst zero),
            B.subst (up (up fun i => (Syn.var (ξ i) : Tm m)))⟩ := by
      show (⟨(B.subst (inst zero)).subst (up fun i => (Syn.var (ξ i) : Tm m)), _⟩ : Cl _) = _
      rw [NFm.subst_inst]
      rfl
    rw [e] at h
    exact h
  | @intro _ Γ B t hB _ ih =>
    intro m ξ
    have h := ih (Tm.upRen ξ)
    rw [← Tm.up_rn, List.map_cons, Cl.map_shift_subst, Cl.asm_subst, NFm.subst_repl_succ,
      NFm.subst_repl_up _ (NFm.start B t), NFm.subst_up_inst, ← NFm.start_rn] at h
    exact .intro _ _ ((NFm.qfree_subst _ _).2 hB) h

theorem shift (h : CPrf Γ A) : CPrf (Γ.map Cl.shift) A.shift := h.ren Fin.succ

theorem cutLift (h : ∀ c ∈ Γ, c ∈ Δ ∨ ∃ X, c = Cl.asm X ∧ CPrf Δ X) (d : Cl (n + 1)) :
    ∀ c ∈ d :: Γ.map Cl.shift,
      c ∈ d :: Δ.map Cl.shift ∨ ∃ X, c = Cl.asm X ∧ CPrf (d :: Δ.map Cl.shift) X := by
  intro c hc
  rcases List.mem_cons.1 hc with rfl | hc
  · exact .inl List.mem_cons_self
  · obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
    rcases h c₀ hc₀ with h' | ⟨X, rfl, hX⟩
    · exact .inl (List.mem_cons_of_mem _ (List.mem_map_of_mem h'))
    · exact .inr ⟨X.shift, Cl.asm_shift X, hX.shift.wk⟩

/-- Cut of ordinary assumptions: an assumption may be replaced by a derivation
of it. -/
theorem cut (h : CPrf Γ A) : ∀ {Δ : List (Cl n)},
    (∀ c ∈ Γ, c ∈ Δ ∨ ∃ X, c = Cl.asm X ∧ CPrf Δ X) → CPrf Δ A := by
  induction h with
  | refl t => intro Δ _; exact .refl t
  | evalZero h _ _ ih₁ ih₂ => intro Δ s; exact .evalZero h (ih₁ s) (ih₂ s)
  | evalSucc _ _ ih₁ ih₂ => intro Δ s; exact .evalSucc (ih₁ s) (ih₂ s)
  | @use _ Γ c t hc _ ih =>
    intro Δ s
    rcases s c hc with h' | ⟨X, rfl, hX⟩
    · exact .use t h' (ih s)
    · show CPrf Δ (X.shift.subst (inst t))
      rw [NFm.subst_inst_shift]
      exact hX
  | elim _ _ ih₁ ih₂ => intro Δ s; exact .elim (ih₁ s) (ih₂ (cutLift s _))
  | intro B t hB _ ih => intro Δ s; exact .intro B t hB (ih (cutLift s _))

/-! ### Soundness in the kernel -/

/-- An ordinary assumption gives its clause. -/
theorem _root_.LeanProofs.ConciseIPRA.NPrf.asmClause {Γ : List (NFm n)} {X : NFm n}
    (h : NPrf Γ X) : NPrf Γ (Cl.asm X).toN :=
  NPrf.impI (NPrf.allI h.wk.shift)

theorem toNPrf (h : CPrf Γ A) : NPrf (Γ.map Cl.toN) A := by
  induction h with
  | refl t => exact NPrf.eqRefl t
  | evalZero h _ _ ih₁ ih₂ =>
    exact NPrf.eqTrans (NPrf.eqSymm ih₂) (NPrf.eqTrans (.iterZero _ h) ih₁)
  | @evalSucc _ _ c a h t r _ _ ih₁ ih₂ =>
    exact NPrf.eqTrans (NPrf.eqSymm ih₂) (NPrf.eqTrans (.iterSucc c a h) (NPrf.eqCongr h ih₁))
  | @use _ Γ c t hc _ ih =>
    exact NPrf.allE t (NPrf.impE (.hyp (List.mem_map_of_mem (f := Cl.toN) hc)) ih)
  | @elim _ Γ B A _ _ ih₁ ih₂ =>
    rw [List.map_cons, Cl.map_toN_shift] at ih₂
    refine .dE ih₁ (NPrf.cut1 ((NPrf.qComp (NEquiv.refl B)).mpr NPrf.hyp0) (NPrf.wkUnder ih₂))
  | @intro _ Γ B t _ _ ih =>
    rw [List.map_cons, Cl.map_toN_shift] at ih
    exact .ofDI B t (NPrf.cut1 (NPrf.asmClause NPrf.hyp0) (NPrf.wkUnder ih))

end CPrf

/-! ### Completeness, from the six-rule calculus -/

theorem EPrf.toCPrf {Γ : List (NFm n)} {A : NFm n} (h : EPrf Γ A) :
    CPrf (Γ.map fun X => Cl.asm (NFm.unQ X)) (NFm.unQ A) := by
  induction h with
  | hyp h =>
    exact CPrf.asmHyp (List.mem_map_of_mem (f := fun X => Cl.asm (NFm.unQ X)) h)
  | refl t => exact .refl t
  | evalZero h _ _ ih₁ ih₂ => exact .evalZero h ih₁ ih₂
  | evalSucc _ _ ih₁ ih₂ => exact .evalSucc ih₁ ih₂
  | @qE _ Γ B t _ _ ih₁ ih₂ =>
    rw [NFm.unQ_subst] at ih₂ ⊢
    refine .elim ih₁ ?_
    have hp := (ih₂.shift).wk
      (c := (⟨((NFm.unQ B).subst (up fun i => Syn.var i.succ)).subst (inst zero),
        (NFm.unQ B).subst (up fun i => Syn.var i.succ)⟩ : Cl _))
    rw [NFm.shift_subst_inst_zero, ← NFm.subst_dummy_up_inst] at hp
    have hu : CPrf (_ :: (Γ.map fun X => Cl.asm (NFm.unQ X)).map Cl.shift)
        (((NFm.unQ B).subst (up fun i => Syn.var i.succ)).subst (inst (Syn.shift t))) :=
      CPrf.use (c := ⟨_, _⟩) (Syn.shift t) List.mem_cons_self hp
    rw [NFm.subst_dummy_up_inst _ (Syn.shift t), ← NFm.shift_subst_inst] at hu
    exact hu
  | @dE _ Γ B A _ _ ih₁ ih₂ =>
    rw [List.map_cons, Cl.map_asm_unQ_shift, NFm.unQ_shift] at ih₂
    refine .elim ih₁ ?_
    -- the opened clause gives the `D` formula that stands for `Q_y B(b, y)`
    have hD : CPrf ((⟨(NFm.unQ B).subst (inst zero), NFm.unQ B⟩ : Cl _)
          :: (Γ.map fun X => Cl.asm (NFm.unQ X)).map Cl.shift)
        (.D ((NFm.unQ B).subst (up fun i => Syn.var i.succ))) := by
      refine .intro _ (succ zero) ((NFm.qfree_subst _ _).2 (NFm.qfree_unQ B)) ?_
      rw [NFm.start_of_not (fun h => by cases h.2), NFm.subst_dummy_inst]
      have hb : CPrf (Cl.asm ((NFm.unQ B).subst (repl zero))
            :: ((⟨(NFm.unQ B).subst (inst zero), NFm.unQ B⟩ : Cl _)
              :: (Γ.map fun X => Cl.asm (NFm.unQ X)).map Cl.shift).map Cl.shift)
          ((NFm.unQ B).subst (inst zero)).shift := by
        rw [NFm.shift_subst_inst_zero]
        exact CPrf.asmHyp List.mem_cons_self
      have hu : CPrf (Cl.asm ((NFm.unQ B).subst (repl zero))
            :: ((⟨(NFm.unQ B).subst (inst zero), NFm.unQ B⟩ : Cl _)
              :: (Γ.map fun X => Cl.asm (NFm.unQ X)).map Cl.shift).map Cl.shift)
          (((NFm.unQ B).subst (up fun i => Syn.var i.succ)).subst
            (inst (succ (Syn.var 0)))) :=
        CPrf.use (c := (⟨(NFm.unQ B).subst (inst zero), NFm.unQ B⟩ : Cl _).shift)
          (succ (Syn.var 0)) (List.mem_cons_of_mem _ List.mem_cons_self) hb
      rwa [NFm.subst_dummy_up_inst _ (succ (Syn.var 0))] at hu
    refine ih₂.cut fun c hc => ?_
    rcases List.mem_cons.1 hc with rfl | hc
    · exact .inr ⟨_, rfl, hD⟩
    · exact .inl (List.mem_cons_of_mem _ hc)
  | @dI _ Γ B t _ ih =>
    rw [List.map_cons, Cl.map_asm_unQ_shift] at ih
    simp only [NFm.unQ_subst] at ih
    refine .intro (NFm.unQ B) t (NFm.qfree_unQ B) ?_
    rw [NFm.start_unQ]
    exact ih

/-- A formula is interderivable with its `Q`-free form. -/
theorem NEquiv.unQ (A : NFm n) : NEquiv (NFm.unQ A) A := by
  induction A with
  | eq s t => exact NEquiv.refl _
  | Q B ih => exact (NEquiv.dDummy (NFm.unQ B)).trans (NEquiv.Q ih)
  | D B ih => exact NEquiv.D ih

variable {Γ : List (NFm n)} {A : NFm n}

/-- **The five-rule clause calculus and the kernel.**  The kernel derives a
sequent exactly when the clause calculus derives its `Q`-free form from the
corresponding assumptions. -/
theorem cprf_iff_nprf : CPrf (Γ.map fun X => Cl.asm (NFm.unQ X)) (NFm.unQ A) ↔ NPrf Γ A := by
  refine ⟨fun h => (NEquiv.unQ A).mp (h.toNPrf.cut fun C hC => ?_), fun h => h.toEPrf.toCPrf⟩
  rw [List.map_map, List.mem_map] at hC
  obtain ⟨X, hX, rfl⟩ := hC
  exact NPrf.asmClause ((NEquiv.unQ X).mpr (.hyp hX))

/-- On `Q`-free sequents the clause calculus derives exactly what the kernel
derives. -/
theorem cprf_iff_nprf_of_qfree (hΓ : ∀ X ∈ Γ, X.QFree) (hA : A.QFree) :
    CPrf (Γ.map Cl.asm) A ↔ NPrf Γ A := by
  have e : (Γ.map fun X => Cl.asm (NFm.unQ X)) = Γ.map Cl.asm :=
    List.map_congr_left fun X hX => by rw [NFm.unQ_of_qfree X (hΓ X hX)]
  rw [← cprf_iff_nprf, e, NFm.unQ_of_qfree A hA]

end LeanProofs.ConciseIPRA
