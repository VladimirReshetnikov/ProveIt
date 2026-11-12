import ConciseIPRA.NativeProgressiveRules

/-!
# The guarded public language

The packages `Research/guarded_core`, `guarded_source`, `guarded_orbit`,
`deterministic_auxiliary` and `protected_core` restrict the formulas of a
certificate to a *public* language, on which two restrictions of the rules
are compatible:

* the introduction is determined by the root of the matrix alone: progress at
  a literal equation, cases at a compound matrix, with no choice bit and no
  test of the witness;
* no transport has the literal `0` as its source; in `protected_core` every
  transport source is an iterator.

`PGPrf` is the calculus with both restrictions, on all native formulas: the
kernel with the root-determined introduction in place of its two
introductions, and transport at iterator sources only.  It has seven rules.

Every rule of `PGPrf` is a derived rule of the kernel (`PGPrf.toNPrf`).  The
converse is not claimed for arbitrary formulas: a hypothesis `x = y` between
variables is not a transport source of `PGPrf`, and the introduction by cases
of an equation is not an instance of the root-determined rule.  Whether
`PGPrf` is strictly weaker than the kernel on arbitrary sequents is not
proved here.  The public language removes both obstacles.

* `NFm.pub` translates a formula by replacing every equation `s = t` with the
  closure `Q_w (I(w, 0; u.s) = I(w, 0; u.t))` of its gate.  The matrix of that
  closure has the guarded shape `I(y, 0; u.h)` on both sides, and no matrix
  of a translated formula is a bare equation (`NFm.pub_public`).  The
  translation commutes with substitution, and a formula is interderivable
  with its translation in the kernel (`NEquiv.pub`).
* `pgprf_pub_iff`: `PGPrf (Γ.map pub) (pub A) ↔ NPrf Γ A`.

In `PGPrf` the gate is opened at `S 0` to the *wrapped* equation
`wr s = wr t`, where `wr s = I(S 0, 0; u.s)` is an iterator.  Wrapped
equations are transported freely, because both of their sides are admissible
sources (`PGPrf.trW`), and they are closed again by progress
(`PGPrf.gateI`).  Equation induction is done on the wrapped matrix
(`NPrf.toPG`, the case `qIInd`).

The native language has `Q` as a formula, and the translation uses it for the
closure of a gate; in the packages a public formula has `D` only and `Q` is
an administrative resource.  The packages' own certificate formats (clause
contexts in place of `Q`, auxiliary formulas, the wrapper
`W(s) = I(0, s; u.0)` for equations at the root) are not formalized here.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm
open Tm (zero succ iter)

variable {n m k : ℕ}

/-- Derivability with the root-determined introduction and transport at
iterator sources only. -/
inductive PGPrf : {n : ℕ} → List (NFm n) → NFm n → Prop
  | hyp {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (h : A ∈ Γ) : PGPrf Γ A
  | iterZero {n : ℕ} {Γ : List (NFm n)} (a : Tm n) (h : Tm (n + 1)) :
      PGPrf Γ (.eq (iter zero a h) a)
  | iterSucc {n : ℕ} {Γ : List (NFm n)} (c a : Tm n) (h : Tm (n + 1)) :
      PGPrf Γ (.eq (iter (succ c) a h) (Syn.subst (inst (iter c a h)) h))
  /-- Transport in one term at an iterator source: from `J = t` and `h(J) = u`
  infer `u = h(t)`, where `J = I(c, a; v.g)`. -/
  | trI {n : ℕ} {Γ : List (NFm n)} (h : Tm (n + 1)) (c a : Tm n) (g : Tm (n + 1)) {t u : Tm n}
      (h₁ : PGPrf Γ (.eq (iter c a g) t))
      (h₂ : PGPrf Γ (.eq (Syn.subst (inst (iter c a g)) h) u)) :
      PGPrf Γ (.eq u (Syn.subst (inst t) h))
  | qE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 1)} (t : Tm n)
      (h₁ : PGPrf Γ (.Q B)) (h₂ : PGPrf Γ (B.subst (inst zero))) : PGPrf Γ (B.subst (inst t))
  | dE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 2)} {A : NFm n}
      (h₁ : PGPrf Γ (.D B)) (h₂ : PGPrf (.Q B :: Γ.map NFm.shift) A.shift) : PGPrf Γ A
  /-- DI: from `B(t, η) ⊢ B(t, S z)` with `z` fresh infer `D_{x,y} B`, where
  `η = z` for a literal equation and `η = 0` for a compound matrix. -/
  | dI {n : ℕ} {Γ : List (NFm n)} (B : NFm (n + 2)) (t : Tm n)
      (h : PGPrf ((B.subst (up (inst t))).subst (repl (NFm.eta B (Syn.var 0)))
          :: Γ.map NFm.shift)
        ((B.subst (up (inst t))).subst (repl (succ (var 0))))) : PGPrf Γ (.D B)

/-- The wrapper `wr s = I(S 0, 0; u.s)`: an iterator provably equal to `s`. -/
def Tm.wr (a : Tm n) : Tm n := Tm.sel (succ zero) zero a

theorem Tm.subst_wr (σ : Fin n → Tm m) (a : Tm n) :
    Syn.subst σ (Tm.wr a) = Tm.wr (Syn.subst σ a) := by
  simp [Tm.wr]

theorem Tm.shift_wr (a : Tm n) : Syn.shift (Tm.wr a) = Tm.wr (Syn.shift a) := Tm.subst_wr _ a

namespace NFm

/-- The gated translation: every equation is replaced by the closure of its
gate. -/
def pub : {n : ℕ} → NFm n → NFm n
  | _, .eq s t => .Q (gate (Syn.var 0) (NFm.eq s t).shift)
  | _, .Q B => .Q (pub B)
  | _, .D B => .D (pub B)

theorem pub_subst (A : NFm n) : ∀ {m : ℕ} (σ : Fin n → Tm m),
    (A.subst σ).pub = A.pub.subst σ := by
  induction A with
  | eq s t =>
    intro m σ
    show NFm.Q (gate (Syn.var 0) ((NFm.eq s t).subst σ).shift)
      = (NFm.Q (gate (Syn.var 0) (NFm.eq s t).shift)).subst σ
    rw [subst_Q, gate_subst, Syn.subst_var, Syn.up_zero, shift_subst_up]
  | Q B ih =>
    intro m σ
    show NFm.Q ((B.subst (up σ)).pub) = NFm.Q (B.pub.subst (up σ))
    rw [ih]
  | D B ih =>
    intro m σ
    show NFm.D ((B.subst (up (up σ))).pub) = NFm.D (B.pub.subst (up (up σ)))
    rw [ih]

theorem pub_shift (A : NFm n) : A.shift.pub = A.pub.shift := pub_subst A _

theorem map_pub_shift (Γ : List (NFm n)) :
    (Γ.map NFm.shift).map pub = (Γ.map pub).map NFm.shift := by
  rw [List.map_map, List.map_map]
  exact List.map_congr_left fun A _ => pub_shift A

theorem pub_isEq (A : NFm n) : A.pub.isEq = false := by
  cases A <;> rfl

theorem eta_pub (A : NFm k) (a : Tm n) : eta A.pub a = zero := by
  unfold eta
  rw [pub_isEq]
  rfl

end NFm

/-- The term is an iterator. -/
def Tm.IsIter : {n : ℕ} → Tm n → Prop
  | _, .iter _ _ _ => True
  | _, _ => False

/-- The term has the guarded shape `I(y, 0; u.h)`, where `y` is the variable
with index `0`. -/
def Tm.IsGuard : {n : ℕ} → Tm n → Prop
  | _, .iter (.var i) .zero _ => i.val = 0
  | _, _ => False

namespace NFm

/-- A guarded atomic matrix: an equation with both sides of the guarded
shape. -/
def Guarded : {n : ℕ} → NFm n → Prop
  | _, .eq s t => s.IsGuard ∧ t.IsGuard
  | _, _ => False

/-- The public language: an equation between iterators; a binder over a
guarded atomic matrix; a binder over a compound public matrix. -/
def Public : {n : ℕ} → NFm n → Prop
  | _, .eq s t => s.IsIter ∧ t.IsIter
  | _, .Q B => B.Guarded ∨ (B.isEq = false ∧ Public B)
  | _, .D B => B.Guarded ∨ (B.isEq = false ∧ Public B)

/-- Every translated formula is public. -/
theorem pub_public (A : NFm n) : A.pub.Public := by
  induction A with
  | eq s t => exact Or.inl ⟨rfl, rfl⟩
  | Q B ih => exact Or.inr ⟨pub_isEq B, ih⟩
  | D B ih => exact Or.inr ⟨pub_isEq B, ih⟩

end NFm

/-- A formula is interderivable with its translation, in the kernel. -/
theorem NEquiv.pub (A : NFm n) : NEquiv A.pub A := by
  induction A with
  | eq s t => exact NEquiv.qGate (.eq s t)
  | Q B ih => exact NEquiv.Q ih
  | D B ih => exact NEquiv.D ih

namespace PGPrf

variable {Γ Δ : List (NFm n)} {A : NFm n}

/-- Every rule is a derived rule of the kernel. -/
theorem toNPrf (h : PGPrf Γ A) : NPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | trI h c a g _ _ ih₁ ih₂ => exact .trOne h ih₁ ih₂
  | qE t _ _ ih₁ ih₂ => exact .qE t ih₁ ih₂
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | @dI n Γ B t _ ih =>
    cases B with
    | eq a b =>
      -- progress for the equation `E(t, y)`, then cases with the closure
      have ih' : NPrf (NFm.eq (Syn.subst (up (inst t)) a) (Syn.subst (up (inst t)) b)
            :: Γ.map NFm.shift)
          ((NFm.eq (Syn.subst (up (inst t)) a) (Syn.subst (up (inst t)) b)).subst
            (repl (succ (Syn.var 0)))) := by
        have e := ih
        rw [show NFm.eta (NFm.eq a b) (Syn.var 0 : Tm (n + 1)) = Syn.var 0 from rfl,
          NFm.subst_repl_var] at e
        exact e
      have hQ := NPrf.qIInd _ _ ih'
      refine .dICase (.eq a b) t ?_
      refine NPrf.cut1 hQ.shift.wk
        ((NEquiv.qStep (Δ := Γ.map NFm.shift) (NEquiv.refl _)).weaken ?_)
      intro X hX
      rcases List.mem_cons.1 hX with rfl | hX
      · exact List.mem_cons_of_mem _ List.mem_cons_self
      · rcases List.mem_cons.1 hX with rfl | hX
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hX)
    | Q B' =>
      refine .dICase _ t ?_
      rw [NFm.shift_subst_inst_zero]
      exact ih
    | D B' =>
      refine .dICase _ t ?_
      rw [NFm.shift_subst_inst_zero]
      exact ih

theorem hyp0 : PGPrf (A :: Γ) A := .hyp List.mem_cons_self

/-! ### Structural rules -/

theorem weaken (h : PGPrf Γ A) : ∀ {Δ : List (NFm n)}, Γ ⊆ Δ → PGPrf Δ A := by
  induction h with
  | hyp h => intro Δ s; exact .hyp (s h)
  | iterZero a h => intro Δ _; exact .iterZero a h
  | iterSucc c a h => intro Δ _; exact .iterSucc c a h
  | trI h c a g _ _ ih₁ ih₂ => intro Δ s; exact .trI h c a g (ih₁ s) (ih₂ s)
  | qE t _ _ ih₁ ih₂ => intro Δ s; exact .qE t (ih₁ s) (ih₂ s)
  | dE _ _ ih₁ ih₂ =>
    intro Δ s
    exact .dE (ih₁ s) (ih₂ (List.cons_subset_cons _ (List.map_subset _ s)))
  | dI B t _ ih =>
    intro Δ s
    exact .dI B t (ih (List.cons_subset_cons _ (List.map_subset _ s)))

theorem wk {B : NFm n} (h : PGPrf Γ A) : PGPrf (B :: Γ) A :=
  h.weaken (List.subset_cons_self _ _)

/-- Substitution of terms for the free variables of a derivation.  Neither
restriction looks at a term that a substitution can change: a source stays an
iterator and the root of a matrix stays what it is. -/
theorem subst (h : PGPrf Γ A) : ∀ {m : ℕ} (σ : Fin n → Tm m),
    PGPrf (Γ.map fun B => B.subst σ) (A.subst σ) := by
  induction h with
  | hyp h => intro m σ; exact .hyp (List.mem_map_of_mem h)
  | iterZero a h => intro m σ; exact .iterZero _ _
  | iterSucc c a h =>
    intro m σ
    simp only [NFm.subst_eq, Tm.subst_iter, Tm.subst_succ, Syn.subst_subst_inst]
    exact .iterSucc _ _ _
  | trI h c a g _ _ ih₁ ih₂ =>
    intro m σ
    have h₁ := ih₁ σ
    have h₂ := ih₂ σ
    simp only [NFm.subst_eq, Syn.subst_subst_inst, Tm.subst_iter] at h₁ h₂ ⊢
    exact .trI _ _ _ _ h₁ h₂
  | qE t _ _ ih₁ ih₂ =>
    intro m σ
    have h₂ := ih₂ σ
    rw [NFm.subst_inst] at h₂ ⊢
    exact .qE _ (ih₁ σ) h₂
  | dE _ _ ih₁ ih₂ =>
    intro m σ
    have h := ih₂ (up σ)
    rw [List.map_cons, NFm.map_shift_subst, NFm.shift_subst_up] at h
    exact .dE (ih₁ σ) h
  | @dI _ Γ B t _ ih =>
    intro m σ
    have h := ih (up σ)
    rw [List.map_cons, NFm.map_shift_subst, NFm.subst_repl_up_comm _ (NFm.eta B (Syn.var 0)),
      NFm.subst_repl_succ, NFm.subst_up_inst,
      NFm.eta_subst B (up (up σ)) (up σ) (Syn.var 0)] at h
    simp only [Syn.subst_var, Syn.up_zero] at h
    exact .dI _ _ h

theorem shift (h : PGPrf Γ A) : PGPrf (Γ.map NFm.shift) A.shift := h.subst _

theorem cutLift (h : ∀ B ∈ Γ, PGPrf Δ B) (C : NFm (n + 1)) :
    ∀ B ∈ C :: Γ.map NFm.shift, PGPrf (C :: Δ.map NFm.shift) B := by
  intro B hB
  rcases List.mem_cons.1 hB with rfl | hB
  · exact hyp0
  · obtain ⟨B₀, hB₀, rfl⟩ := List.mem_map.1 hB
    exact (h B₀ hB₀).shift.wk

/-- Cut: hypotheses may be replaced by derivations of them. -/
theorem cut (h : PGPrf Γ A) : ∀ {Δ : List (NFm n)}, (∀ B ∈ Γ, PGPrf Δ B) → PGPrf Δ A := by
  induction h with
  | hyp h => intro Δ hΔ; exact hΔ _ h
  | iterZero a h => intro Δ _; exact .iterZero a h
  | iterSucc c a h => intro Δ _; exact .iterSucc c a h
  | trI h c a g _ _ ih₁ ih₂ => intro Δ hΔ; exact .trI h c a g (ih₁ hΔ) (ih₂ hΔ)
  | qE t _ _ ih₁ ih₂ => intro Δ hΔ; exact .qE t (ih₁ hΔ) (ih₂ hΔ)
  | dE _ _ ih₁ ih₂ => intro Δ hΔ; exact .dE (ih₁ hΔ) (ih₂ (cutLift hΔ _))
  | dI B t _ ih => intro Δ hΔ; exact .dI B t (ih (cutLift hΔ _))

/-! ### Equality at iterator sources -/

/-- From `J = t` and `J = u` infer `u = t`, for an iterator `J`. -/
theorem euclid (c a : Tm n) (g : Tm (n + 1)) {t u : Tm n} (h₁ : PGPrf Γ (.eq (iter c a g) t))
    (h₂ : PGPrf Γ (.eq (iter c a g) u)) : PGPrf Γ (.eq u t) :=
  .trI (Syn.var 0) c a g h₁ h₂

theorem eqRefl (t : Tm n) : PGPrf Γ (.eq t t) :=
  euclid zero t (Syn.var 0) (.iterZero t (Syn.var 0)) (.iterZero t (Syn.var 0))

/-- Symmetry of every equation: a constant template reverses it. -/
theorem eqSymm {s t : Tm n} (h : PGPrf Γ (.eq s t)) : PGPrf Γ (.eq t s) := by
  have h₂ : PGPrf Γ (.eq (Syn.subst (inst (iter zero zero zero)) (Syn.shift s)) t) := by
    rw [Syn.subst_inst_shift]
    exact h
  have k := PGPrf.trI (Syn.shift s) zero zero zero (.iterZero zero zero) h₂
  rw [Syn.subst_inst_shift] at k
  exact k

/-- Transitivity through an iterator. -/
theorem trans (c a : Tm n) (g : Tm (n + 1)) {x z : Tm n} (h₁ : PGPrf Γ (.eq x (iter c a g)))
    (h₂ : PGPrf Γ (.eq (iter c a g) z)) : PGPrf Γ (.eq x z) :=
  euclid c a g h₂ (eqSymm h₁)

theorem selZero (a b : Tm n) : PGPrf Γ (.eq (Tm.sel zero a b) a) := .iterZero a _

theorem selSucc (c a b : Tm n) : PGPrf Γ (.eq (Tm.sel (succ c) a b) b) := by
  have h := PGPrf.iterSucc (Γ := Γ) c a (Syn.shift b)
  rwa [Syn.subst_inst_shift] at h

theorem wrEq (a : Tm n) : PGPrf Γ (.eq (Tm.wr a) a) := selSucc zero zero a

/-- Wrapping the right side of an equation whose left side is an iterator. -/
theorem wrapR (c a : Tm n) (g : Tm (n + 1)) {s : Tm n} (h : PGPrf Γ (.eq (iter c a g) s)) :
    PGPrf Γ (.eq (iter c a g) (Tm.wr s)) := by
  have h₂ : PGPrf Γ (.eq (Syn.subst (inst (iter c a g)) (Tm.wr (Syn.var 0))) (iter c a g)) := by
    rw [Tm.subst_wr]
    exact wrEq _
  have k := PGPrf.trI (Tm.wr (Syn.var 0)) c a g h h₂
  rw [Tm.subst_wr] at k
  exact k

/-- Congruence of the wrapper along an equation whose left side is an
iterator. -/
theorem wrCong (c a : Tm n) (g : Tm (n + 1)) {s : Tm n} (h : PGPrf Γ (.eq (iter c a g) s)) :
    PGPrf Γ (.eq (Tm.wr (iter c a g)) (Tm.wr s)) := by
  have h₂ : PGPrf Γ (.eq (Syn.subst (inst (iter c a g)) (Tm.wr (Syn.var 0)))
      (Tm.wr (iter c a g))) := by
    rw [Tm.subst_wr]
    exact eqRefl _
  have k := PGPrf.trI (Tm.wr (Syn.var 0)) c a g h h₂
  rw [Tm.subst_wr] at k
  exact k

/-- **Transport for wrapped equations**: from `wr s = wr t` and
`wr h(s) = wr u` infer `wr u = wr h(t)`.  Every source is a wrapper. -/
theorem trW (h : Tm (n + 1)) {s t u : Tm n} (h₁ : PGPrf Γ (.eq (Tm.wr s) (Tm.wr t)))
    (h₂ : PGPrf Γ (.eq (Tm.wr (Syn.subst (inst s) h)) (Tm.wr u))) :
    PGPrf Γ (.eq (Tm.wr u) (Tm.wr (Syn.subst (inst t) h))) := by
  -- unwrapping inside the template `wr h`
  have key : ∀ x : Tm n, PGPrf Γ (.eq (Tm.wr (Syn.subst (inst (Tm.wr x)) h))
      (Tm.wr (Syn.subst (inst x) h))) := by
    intro x
    have k := PGPrf.trI (Γ := Γ) (Tm.wr h) (succ zero) zero (Syn.shift x) (t := x)
      (u := Syn.subst (inst (Tm.wr x)) (Tm.wr h)) (wrEq x) (eqRefl _)
    rw [Tm.subst_wr, Tm.subst_wr] at k
    exact k
  have s₁ : PGPrf Γ (.eq (Tm.wr (Syn.subst (inst (Tm.wr s)) h)) (Tm.wr u)) :=
    trans (succ zero) zero (Syn.shift (Syn.subst (inst s) h)) (key s) h₂
  have s₂ := PGPrf.trI (Γ := Γ) (Tm.wr h) (succ zero) zero (Syn.shift s) (t := Tm.wr t)
    (u := Tm.wr u) h₁ (by rw [Tm.subst_wr]; exact s₁)
  rw [Tm.subst_wr] at s₂
  exact trans (succ zero) zero (Syn.shift (Syn.subst (inst (Tm.wr t)) h)) s₂ (key t)

/-! ### Closures -/

/-- `Q` by progress for an equation. -/
theorem qIProg (s t : Tm (n + 1))
    (h : PGPrf (NFm.eq s t :: Γ.map NFm.shift)
      ((NFm.eq s t).subst (repl (succ (Syn.var 0))))) : PGPrf Γ (.Q (.eq s t)) := by
  have hD : PGPrf Γ (.D ((NFm.eq s t).subst (up (fun i => Syn.var i.succ)))) := by
    refine .dI _ zero ?_
    rw [show NFm.eta ((NFm.eq s t).subst (up (fun i => Syn.var i.succ)))
        (Syn.var 0 : Tm (n + 1)) = Syn.var 0 from rfl, NFm.subst_repl_var,
      NFm.subst_dummy_inst]
    exact h
  exact .dE hD (.hyp List.mem_cons_self)

/-- `Q` by cases for a compound matrix. -/
theorem qICases (B : NFm (n + 1)) (hB : B.isEq = false)
    (h : PGPrf ((B.subst (inst zero)).shift :: Γ.map NFm.shift)
      (B.subst (repl (succ (Syn.var 0))))) : PGPrf Γ (.Q B) := by
  have hD : PGPrf Γ (.D (B.subst (up (fun i => Syn.var i.succ)))) := by
    refine .dI _ zero ?_
    have e : NFm.eta (B.subst (up (fun i => Syn.var i.succ))) (Syn.var 0 : Tm (n + 1))
        = zero := by
      unfold NFm.eta
      rw [NFm.isEq_subst, hB]
      rfl
    rw [e, NFm.subst_dummy_inst, ← NFm.shift_subst_inst_zero]
    exact h
  exact .dE hD (.hyp List.mem_cons_self)

/-- From the base and a closure moved under a fresh variable, the successor
instance. -/
theorem qStep (B : NFm (n + 1)) {Δ : List (NFm (n + 1))} (hQ : PGPrf Δ (NFm.Q B).shift)
    (h0 : PGPrf Δ (B.subst (repl zero))) : PGPrf Δ (B.subst (repl (succ (Syn.var 0)))) := by
  rw [← NFm.subst_dummy_up_inst] at h0 ⊢
  exact .qE (succ (Syn.var 0)) hQ h0

/-- The two gates at zero are equal. -/
theorem gateZero (s t : Tm n) : PGPrf Γ (.eq (Tm.sel zero zero s) (Tm.sel zero zero t)) := by
  have h₂ : PGPrf Γ (.eq (Syn.subst (inst (iter zero zero (Syn.shift s)))
      (Tm.sel zero (Syn.var 0) (Syn.shift t))) (Tm.sel zero zero s)) := by
    rw [Tm.subst_sel, Syn.subst_inst_shift]
    exact selZero _ _
  have k := PGPrf.trI (Tm.sel zero (Syn.var 0) (Syn.shift t)) zero zero (Syn.shift s)
    (.iterZero zero (Syn.shift s)) h₂
  rw [Tm.subst_sel, Syn.subst_inst_shift] at k
  exact k

/-- Opening a gated equation: the wrapped equation. -/
theorem gateE {s t : Tm n} (h : PGPrf Γ (NFm.eq s t).pub) :
    PGPrf Γ (.eq (Tm.wr s) (Tm.wr t)) := by
  have k := PGPrf.qE (succ zero) h (by rw [NFm.gate_shift_inst]; exact gateZero s t)
  rw [NFm.gate_shift_inst] at k
  exact k

/-- Closing a wrapped equation: the gated equation, by progress. -/
theorem gateI {s t : Tm n} (h : PGPrf Γ (.eq (Tm.wr s) (Tm.wr t))) :
    PGPrf Γ (NFm.eq s t).pub := by
  show PGPrf Γ (.Q (.eq (Tm.sel (Syn.var 0) zero (Syn.shift s))
    (Tm.sel (Syn.var 0) zero (Syn.shift t))))
  refine qIProg _ _ ?_
  simp only [NFm.subst_eq, Tm.subst_sel, Syn.subst_var, Syn.repl_zero, Syn.subst_repl_shift,
    Tm.subst_zero]
  have hw : PGPrf (NFm.eq (Tm.sel (Syn.var 0) zero (Syn.shift s))
        (Tm.sel (Syn.var 0) zero (Syn.shift t)) :: Γ.map NFm.shift)
      (.eq (Tm.wr (Syn.shift s)) (Tm.wr (Syn.shift t))) := by
    have k : PGPrf (Γ.map NFm.shift)
        (.eq (Syn.shift (Tm.wr s)) (Syn.shift (Tm.wr t))) := h.shift
    rw [Tm.shift_wr, Tm.shift_wr] at k
    exact k.wk
  have a₁ := wrapR (succ (Syn.var 0)) zero (Syn.shift (Syn.shift s))
    (selSucc (Γ := NFm.eq (Tm.sel (Syn.var 0) zero (Syn.shift s))
      (Tm.sel (Syn.var 0) zero (Syn.shift t)) :: Γ.map NFm.shift) (Syn.var 0) zero (Syn.shift s))
  have a₂ := wrapR (succ (Syn.var 0)) zero (Syn.shift (Syn.shift t))
    (selSucc (Γ := NFm.eq (Tm.sel (Syn.var 0) zero (Syn.shift s))
      (Tm.sel (Syn.var 0) zero (Syn.shift t)) :: Γ.map NFm.shift) (Syn.var 0) zero (Syn.shift t))
  exact trans (succ zero) zero (Syn.shift (Syn.shift t))
    (trans (succ zero) zero (Syn.shift (Syn.shift s)) a₁ hw) (eqSymm a₂)

end PGPrf

variable {Γ : List (NFm n)} {A : NFm n}

/-- Every kernel derivation becomes a derivation of `PGPrf` between the
translations. -/
theorem NPrf.toPG (h : NPrf Γ A) : PGPrf (Γ.map NFm.pub) A.pub := by
  induction h with
  | hyp h => exact .hyp (List.mem_map_of_mem h)
  | iterZero a h => exact PGPrf.gateI (PGPrf.wrCong zero a h (.iterZero a h))
  | iterSucc c a h => exact PGPrf.gateI (PGPrf.wrCong (succ c) a h (.iterSucc c a h))
  | trOne h _ _ ih₁ ih₂ => exact PGPrf.gateI (PGPrf.trW h (PGPrf.gateE ih₁) (PGPrf.gateE ih₂))
  | qE t _ _ ih₁ ih₂ =>
    rw [NFm.pub_subst] at ih₂ ⊢
    exact .qE t ih₁ ih₂
  | dE _ _ ih₁ ih₂ =>
    rw [List.map_cons, NFm.map_pub_shift, NFm.pub_shift] at ih₂
    exact .dE ih₁ ih₂
  | @dICase _ Γ B t _ ih =>
    rw [List.map_cons, NFm.map_pub_shift, NFm.pub_shift] at ih
    simp only [NFm.pub_subst] at ih
    refine .dI B.pub t ?_
    rw [NFm.eta_pub, ← NFm.shift_subst_inst_zero]
    exact ih
  | @qIInd n Γ s t _ ih =>
    rw [List.map_cons, NFm.map_pub_shift, NFm.pub_subst] at ih
    -- equation induction on the wrapped matrix
    have hM : PGPrf (Γ.map NFm.pub) (.Q (.eq (Tm.wr s) (Tm.wr t))) := by
      refine PGPrf.qIProg _ _ ?_
      have c := ih.cut (Δ := NFm.eq (Tm.wr s) (Tm.wr t) :: (Γ.map NFm.pub).map NFm.shift)
        fun C hC => by
          rcases List.mem_cons.1 hC with rfl | hC
          · exact PGPrf.gateI PGPrf.hyp0
          · exact .hyp (List.mem_cons_of_mem _ hC)
      rw [← NFm.pub_subst] at c
      have c' : PGPrf (NFm.eq (Tm.wr s) (Tm.wr t) :: (Γ.map NFm.pub).map NFm.shift)
          (.eq (Tm.wr (Syn.subst (repl (succ (Syn.var 0))) s))
            (Tm.wr (Syn.subst (repl (succ (Syn.var 0))) t))) := PGPrf.gateE c
      show PGPrf _ (.eq (Syn.subst (repl (succ (Syn.var 0))) (Tm.wr s))
        (Syn.subst (repl (succ (Syn.var 0))) (Tm.wr t)))
      rw [Tm.subst_wr, Tm.subst_wr]
      exact c'
    -- the closure of the gated matrix, by cases
    show PGPrf (Γ.map NFm.pub) (.Q (NFm.eq s t).pub)
    refine PGPrf.qICases _ (NFm.pub_isEq _) ?_
    rw [← NFm.pub_subst, ← NFm.pub_subst, ← NFm.pub_shift]
    have b : PGPrf (((NFm.eq s t).subst (inst zero)).shift.pub :: (Γ.map NFm.pub).map NFm.shift)
        (.eq (Tm.wr (Syn.shift (Syn.subst (inst zero) s)))
          (Tm.wr (Syn.shift (Syn.subst (inst zero) t)))) := PGPrf.gateE PGPrf.hyp0
    have h0 : PGPrf (((NFm.eq s t).subst (inst zero)).shift.pub :: (Γ.map NFm.pub).map NFm.shift)
        ((NFm.eq (Tm.wr s) (Tm.wr t)).subst (repl zero)) := by
      rw [← NFm.shift_subst_inst_zero]
      show PGPrf _ (.eq (Syn.shift (Syn.subst (inst zero) (Tm.wr s)))
        (Syn.shift (Syn.subst (inst zero) (Tm.wr t))))
      rw [Tm.subst_wr, Tm.subst_wr, Tm.shift_wr, Tm.shift_wr]
      exact b
    have r : PGPrf (((NFm.eq s t).subst (inst zero)).shift.pub :: (Γ.map NFm.pub).map NFm.shift)
        (.eq (Syn.subst (repl (succ (Syn.var 0))) (Tm.wr s))
          (Syn.subst (repl (succ (Syn.var 0))) (Tm.wr t))) :=
      PGPrf.qStep (.eq (Tm.wr s) (Tm.wr t)) hM.shift.wk h0
    rw [Tm.subst_wr, Tm.subst_wr] at r
    exact PGPrf.gateI r

/-- **The guarded public language.**  The calculus with the root-determined
introduction and transport at iterator sources only derives the translation
of a sequent exactly when the kernel derives the sequent. -/
theorem pgprf_pub_iff : PGPrf (Γ.map NFm.pub) A.pub ↔ NPrf Γ A :=
  ⟨fun h => (NEquiv.pub A).mp (h.toNPrf.cut fun B hB => by
      obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hB
      exact (NEquiv.pub C).mpr (.hyp hC)), NPrf.toPG⟩

/-- The same calculus derives the translation of a sequent exactly when iPRA
proves its reading. -/
theorem pgprf_pub_iff_pra :
    PGPrf (Γ.map NFm.pub) A.pub ↔ (Γ.map NFm.toPRA ⊢[PRAAx] A.toPRA) :=
  pgprf_pub_iff.trans native_iff_pra

end LeanProofs.ConciseIPRA
