import ConciseIPRA.NativeMirror

/-!
# Substitution for a parameter in place of template transport

The package `Research/parameter_substitution` replaces transport in a supplied
term template by a fixed operation on three terms,

  `ψ(s, t, u) = u[t/s]` when `s` is a variable,
  `ψ(s, t, s) = t` and `ψ(s, t, u) = u` otherwise,

and one rule **Param**: from `s = t` and `u = r` infer `r = ψ(s, t, u)`.  A
proper subterm is replaced only when the source `s` is a variable.  For another
source the rule joins two equations with a common left-hand side, or reverses
the second premise.

`PPrf` is the kernel with Param in place of `Tr`, and `pprf_iff_nprf` proves
that it derives the same sequents.

* Param is an instance of `Tr`: replacement of the variable `x_i` in `u` is
  the template obtained from `u` by abstracting `x_i`.
* Conversely `Tr` in a template `h` is recovered through a *fresh alias*.
  Under the assumption `b = s` with `b` fresh, Param at the variable `b` turns
  `h(b) = h(b)` into `h(b) = h(s)`, and likewise into `h(b) = h(t)`, and the
  two are joined.  The alias is discharged by `PPrf.aliasE`: the formula
  `D_{x,y} (sel(y, s, x) = s)` is proved by cases with the witness `s`, and its
  elimination at `y = 1` gives `b = s` for the fresh `b`.

Param is not stable under substitution, since a substitution can turn a
variable source into a compound one.  It is stable under injective renaming
(`PPrf.ren`), which is all that the alias construction needs.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open Tm (zero succ iter)

variable {n m : ℕ}

open Classical

namespace Tm

/-- The fixed equality operation of Param. -/
noncomputable def psi (s t u : Tm n) : Tm n :=
  match s with
  | .var i => Syn.subst (Function.update Syn.var i t) u
  | _ => if u = s then t else u

theorem psi_var (i : Fin n) (t u : Tm n) :
    psi (Syn.var i) t u = Syn.subst (Function.update Syn.var i t) u := rfl

theorem psi_of_not_var {s : Tm n} (hs : ∀ i, s ≠ Syn.var i) (t u : Tm n) :
    psi s t u = if u = s then t else u := by
  cases s with
  | var i => exact absurd rfl (hs i)
  | _ => rfl

theorem psi_self (s t : Tm n) : psi s t s = t := by
  cases s with
  | var i =>
    show Syn.subst (Function.update Syn.var i t) (Syn.var i) = t
    rw [Syn.subst_var, Function.update_self]
  | _ => exact if_pos rfl

/-- A substitution instance of a term that is not a variable is not a
variable. -/
theorem subst_not_var {s : Tm n} (hs : ∀ i, s ≠ Syn.var i) (σ : Fin n → Tm m) :
    ∀ j, Syn.subst σ s ≠ Syn.var j := by
  intro j e
  cases s with
  | var i => exact hs i rfl
  | zero => change Tm.zero = Tm.var j at e; cases e
  | succ a => change Tm.succ _ = Tm.var j at e; cases e
  | iter c a h => change Tm.iter _ _ _ = Tm.var j at e; cases e

/-- Param commutes with injective renaming. -/
theorem psi_rn {ξ : Fin n → Fin m} (hξ : Function.Injective ξ) (s t u : Tm n) :
    Syn.subst (fun i => (Syn.var (ξ i) : Tm m)) (psi s t u)
      = psi (Syn.subst (fun i => (Syn.var (ξ i) : Tm m)) s)
          (Syn.subst (fun i => (Syn.var (ξ i) : Tm m)) t)
          (Syn.subst (fun i => (Syn.var (ξ i) : Tm m)) u) := by
  by_cases hs : ∃ i, s = Syn.var i
  · obtain ⟨i, rfl⟩ := hs
    rw [Syn.subst_var, psi_var, psi_var, Syn.subst_subst, Syn.subst_subst]
    refine congrArg (fun σ => Syn.subst σ u) (funext fun j => ?_)
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj, Function.update_of_ne (fun e => hj (hξ e))]
  · have hs' : ∀ i, s ≠ Syn.var i := fun i e => hs ⟨i, e⟩
    rw [psi_of_not_var hs', psi_of_not_var (subst_not_var hs' _)]
    by_cases e : u = s
    · rw [if_pos e, if_pos (by rw [e])]
    · rw [if_neg e, if_neg fun e' => e (Tm.ren_inj u hξ s (by
        rw [Tm.ren_eq_sub, Tm.ren_eq_sub]; exact e'))]

/-- Replacement of the fresh variable `0`. -/
theorem psi_var0 (s : Tm n) (h : Tm (n + 1)) :
    psi (Syn.var 0) (Syn.shift s) h = Syn.shift (Syn.subst (inst s) h) := by
  rw [psi_var, Syn.shift_subst]
  refine congrArg (fun σ => Syn.subst σ h) (funext fun i => ?_)
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp

/-- Replacement of the variable `i` is transport in the template that
abstracts it. -/
theorem subst_inst_abs (i : Fin n) (t u : Tm n) :
    Syn.subst (inst t)
        (Syn.subst (Function.update (fun j => (Syn.var j.succ : Tm (n + 1))) i (Syn.var 0)) u)
      = Syn.subst (Function.update Syn.var i t) u := by
  rw [Syn.subst_subst]
  refine congrArg (fun σ => Syn.subst σ u) (funext fun j => ?_)
  by_cases hj : j = i
  · subst hj; simp
  · simp [Function.update_of_ne hj]

end Tm

/-- The kernel with Param in place of transport in a template. -/
inductive PPrf : {n : ℕ} → List (NFm n) → NFm n → Prop
  | hyp {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (h : A ∈ Γ) : PPrf Γ A
  | iterZero {n : ℕ} {Γ : List (NFm n)} (a : Tm n) (h : Tm (n + 1)) :
      PPrf Γ (.eq (iter zero a h) a)
  | iterSucc {n : ℕ} {Γ : List (NFm n)} (c a : Tm n) (h : Tm (n + 1)) :
      PPrf Γ (.eq (iter (succ c) a h) (Syn.subst (inst (iter c a h)) h))
  /-- Param: from `s = t` and `u = r` infer `r = ψ(s, t, u)`. -/
  | param {n : ℕ} {Γ : List (NFm n)} {s t u r : Tm n}
      (h₁ : PPrf Γ (.eq s t)) (h₂ : PPrf Γ (.eq u r)) : PPrf Γ (.eq r (Tm.psi s t u))
  | qE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 1)} (t : Tm n)
      (h₁ : PPrf Γ (.Q B)) (h₂ : PPrf Γ (B.subst (inst zero))) : PPrf Γ (B.subst (inst t))
  | dE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 2)} {A : NFm n}
      (h₁ : PPrf Γ (.D B)) (h₂ : PPrf (.Q B :: Γ.map NFm.shift) A.shift) : PPrf Γ A
  | dICase {n : ℕ} {Γ : List (NFm n)} (B : NFm (n + 2)) (t : Tm n)
      (h : PPrf (((B.subst (up (inst t))).subst (inst zero)).shift :: Γ.map NFm.shift)
        ((B.subst (up (inst t))).subst (repl (succ (var 0))))) :
      PPrf Γ (.D B)
  | qIInd {n : ℕ} {Γ : List (NFm n)} (s₁ s₂ : Tm (n + 1))
      (h : PPrf (NFm.eq s₁ s₂ :: Γ.map NFm.shift)
        ((NFm.eq s₁ s₂).subst (repl (succ (var 0))))) :
      PPrf Γ (.Q (.eq s₁ s₂))

namespace PPrf

variable {Γ Δ : List (NFm n)} {A : NFm n}

/-- Param is an instance of transport in a template, of joining, or of
reversal. -/
theorem toNPrf (h : PPrf Γ A) : NPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | @param _ Γ s t u r _ _ ih₁ ih₂ =>
    by_cases hs : ∃ i, s = Syn.var i
    · obtain ⟨i, rfl⟩ := hs
      have k := NPrf.trOne
        (Syn.subst (Function.update (fun j => (Syn.var j.succ : Tm _)) i (Syn.var 0)) u) ih₁
        (u := r) (by
          rw [Tm.subst_inst_abs, Function.update_eq_self, Syn.subst_id]; exact ih₂)
      rwa [Tm.subst_inst_abs] at k
    · rw [Tm.psi_of_not_var fun i e => hs ⟨i, e⟩]
      by_cases e : u = s
      · subst e
        rw [if_pos rfl]
        exact .trOne (Syn.var 0) ih₁ ih₂
      · rw [if_neg e]
        exact NPrf.eqSymm ih₂
  | qE t _ _ ih₁ ih₂ => exact .qE t ih₁ ih₂
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dICase B t _ ih => exact .dICase B t ih
  | qIInd s₁ s₂ _ ih => exact .qIInd s₁ s₂ ih

theorem hyp0 : PPrf (A :: Γ) A := .hyp List.mem_cons_self

theorem weaken (h : PPrf Γ A) : ∀ {Δ : List (NFm n)}, Γ ⊆ Δ → PPrf Δ A := by
  induction h with
  | hyp h => intro Δ s; exact .hyp (s h)
  | iterZero a h => intro Δ _; exact .iterZero a h
  | iterSucc c a h => intro Δ _; exact .iterSucc c a h
  | param _ _ ih₁ ih₂ => intro Δ s; exact .param (ih₁ s) (ih₂ s)
  | qE t _ _ ih₁ ih₂ => intro Δ s; exact .qE t (ih₁ s) (ih₂ s)
  | dE _ _ ih₁ ih₂ =>
    intro Δ s
    exact .dE (ih₁ s) (ih₂ (List.cons_subset_cons _ (List.map_subset _ s)))
  | dICase B t _ ih =>
    intro Δ s
    exact .dICase B t (ih (List.cons_subset_cons _ (List.map_subset _ s)))
  | qIInd s₁ s₂ _ ih =>
    intro Δ s
    exact .qIInd s₁ s₂ (ih (List.cons_subset_cons _ (List.map_subset _ s)))

theorem wk {B : NFm n} (h : PPrf Γ A) : PPrf (B :: Γ) A :=
  h.weaken (List.subset_cons_self _ _)

/-- Injective renaming of the free variables of a derivation. -/
theorem ren (h : PPrf Γ A) : ∀ {m : ℕ} (ξ : Fin n → Fin m), Function.Injective ξ →
    PPrf (Γ.map fun B => B.subst fun i => (Syn.var (ξ i) : Tm m))
      (A.subst fun i => (Syn.var (ξ i) : Tm m)) := by
  induction h with
  | hyp h => intro m ξ _; exact .hyp (List.mem_map_of_mem h)
  | iterZero a h => intro m ξ _; exact .iterZero _ _
  | iterSucc c a h =>
    intro m ξ _
    simp only [NFm.subst_eq, Tm.subst_iter, Tm.subst_succ, Syn.subst_subst_inst]
    exact .iterSucc _ _ _
  | param _ _ ih₁ ih₂ =>
    intro m ξ hξ
    rw [NFm.subst_eq, Tm.psi_rn hξ]
    exact .param (ih₁ ξ hξ) (ih₂ ξ hξ)
  | qE t _ _ ih₁ ih₂ =>
    intro m ξ hξ
    have h₂ := ih₂ ξ hξ
    rw [NFm.subst_inst] at h₂ ⊢
    exact .qE _ (ih₁ ξ hξ) h₂
  | dE _ _ ih₁ ih₂ =>
    intro m ξ hξ
    have h := ih₂ (Tm.upRen ξ) (Tm.upRen_inj hξ)
    rw [← Tm.up_rn, List.map_cons, NFm.map_shift_subst, NFm.shift_subst_up] at h
    exact .dE (ih₁ ξ hξ) h
  | dICase B t _ ih =>
    intro m ξ hξ
    have h := ih (Tm.upRen ξ) (Tm.upRen_inj hξ)
    rw [← Tm.up_rn, List.map_cons, NFm.map_shift_subst, NFm.shift_subst_up, NFm.subst_inst,
      NFm.subst_repl_succ, NFm.subst_up_inst] at h
    exact .dICase _ _ h
  | qIInd s₁ s₂ _ ih =>
    intro m ξ hξ
    have h := ih (Tm.upRen ξ) (Tm.upRen_inj hξ)
    rw [← Tm.up_rn, List.map_cons, NFm.map_shift_subst, NFm.subst_repl_succ] at h
    exact .qIInd _ _ h

theorem shift (h : PPrf Γ A) : PPrf (Γ.map NFm.shift) A.shift :=
  h.ren Fin.succ (Fin.succ_injective _)

theorem cutLift (h : ∀ B ∈ Γ, PPrf Δ B) (C : NFm (n + 1)) :
    ∀ B ∈ C :: Γ.map NFm.shift, PPrf (C :: Δ.map NFm.shift) B := by
  intro B hB
  rcases List.mem_cons.1 hB with rfl | hB
  · exact hyp0
  · obtain ⟨B₀, hB₀, rfl⟩ := List.mem_map.1 hB
    exact (h B₀ hB₀).shift.wk

theorem cut (h : PPrf Γ A) : ∀ {Δ : List (NFm n)}, (∀ B ∈ Γ, PPrf Δ B) → PPrf Δ A := by
  induction h with
  | hyp h => intro Δ hΔ; exact hΔ _ h
  | iterZero a h => intro Δ _; exact .iterZero a h
  | iterSucc c a h => intro Δ _; exact .iterSucc c a h
  | param _ _ ih₁ ih₂ => intro Δ hΔ; exact .param (ih₁ hΔ) (ih₂ hΔ)
  | qE t _ _ ih₁ ih₂ => intro Δ hΔ; exact .qE t (ih₁ hΔ) (ih₂ hΔ)
  | dE _ _ ih₁ ih₂ => intro Δ hΔ; exact .dE (ih₁ hΔ) (ih₂ (cutLift hΔ _))
  | dICase B t _ ih => intro Δ hΔ; exact .dICase B t (ih (cutLift hΔ _))
  | qIInd s₁ s₂ _ ih => intro Δ hΔ; exact .qIInd s₁ s₂ (ih (cutLift hΔ _))

/-! ### Equality from joining at the root -/

/-- Joining: from `s = t` and `s = r` infer `r = t`. -/
theorem join {s t r : Tm n} (h₁ : PPrf Γ (.eq s t)) (h₂ : PPrf Γ (.eq s r)) :
    PPrf Γ (.eq r t) := by
  have h := PPrf.param h₁ h₂
  rwa [Tm.psi_self] at h

theorem eqRefl (t : Tm n) : PPrf Γ (.eq t t) :=
  join (.iterZero t (Syn.var 0)) (.iterZero t (Syn.var 0))

theorem eqSymm {s t : Tm n} (h : PPrf Γ (.eq s t)) : PPrf Γ (.eq t s) :=
  join (eqRefl s) h

theorem eqTrans {s t u : Tm n} (h₁ : PPrf Γ (.eq s t)) (h₂ : PPrf Γ (.eq t u)) :
    PPrf Γ (.eq s u) :=
  join h₂ (eqSymm h₁)

theorem selSucc (c a b : Tm n) : PPrf Γ (.eq (Tm.sel (succ c) a b) b) := by
  have h := PPrf.iterSucc (Γ := Γ) c a (Syn.shift b)
  rwa [Syn.subst_inst_shift] at h

/-! ### The fresh alias -/

/-- The matrix `sel(y, a, x) = a`, where `y` is the variable `0` and `x` the
variable `1`. -/
def aliasM (a : Tm n) : NFm (n + 2) :=
  .eq (Tm.sel (Syn.var 0) (Syn.shift (Syn.shift a)) (Syn.var 1)) (Syn.shift (Syn.shift a))

theorem aliasD (a : Tm n) : PPrf Γ (.D (aliasM a)) := by
  refine .dICase _ a ?_
  have e : ((aliasM a).subst (up (inst a))).subst (repl (succ (Syn.var 0)))
      = .eq (Tm.sel (succ (Syn.var 0)) (Syn.shift a) (Syn.shift a)) (Syn.shift a) := by
    simp [aliasM, Syn.subst_up_shift]
  rw [e]
  exact selSucc _ _ _

/-- **The fresh alias.**  An assumption `b = a` with `b` fresh may be
discharged. -/
theorem aliasE (a : Tm n)
    (h : PPrf (.eq (Syn.var 0) (Syn.shift a) :: Γ.map NFm.shift) A.shift) : PPrf Γ A := by
  refine .dE (aliasD a) ?_
  have e0 : (aliasM a).subst (inst zero)
      = .eq (Tm.sel zero (Syn.shift a) (Syn.var 0)) (Syn.shift a) := by
    simp [aliasM]
  have e1 : (aliasM a).subst (inst (succ zero))
      = .eq (Tm.sel (succ zero) (Syn.shift a) (Syn.var 0)) (Syn.shift a) := by
    simp [aliasM]
  have k : PPrf (.Q (aliasM a) :: Γ.map NFm.shift)
      ((aliasM a).subst (inst (succ zero))) := by
    refine .qE (succ zero) hyp0 ?_
    rw [e0]
    exact .iterZero _ _
  rw [e1] at k
  refine h.cut fun C hC => ?_
  rcases List.mem_cons.1 hC with rfl | hC
  · exact join k (selSucc zero _ _)
  · exact .hyp (List.mem_cons_of_mem _ hC)

/-- **Transport in a template from Param.**  From `s = t` and `h(s) = u` infer
`u = h(t)`. -/
theorem trOne (h : Tm (n + 1)) {s t u : Tm n} (e : PPrf Γ (.eq s t))
    (k : PPrf Γ (.eq (Syn.subst (inst s) h) u)) :
    PPrf Γ (.eq u (Syn.subst (inst t) h)) := by
  refine aliasE s ?_
  have hb : PPrf (.eq (Syn.var 0) (Syn.shift s) :: Γ.map NFm.shift)
      (.eq (Syn.var 0) (Syn.shift s)) := hyp0
  have es : PPrf (.eq (Syn.var 0) (Syn.shift s) :: Γ.map NFm.shift)
      (.eq (Syn.shift s) (Syn.shift t)) := e.shift.wk
  have ks : PPrf (.eq (Syn.var 0) (Syn.shift s) :: Γ.map NFm.shift)
      (.eq (Syn.shift (Syn.subst (inst s) h)) (Syn.shift u)) := k.shift.wk
  have hs := PPrf.param hb (eqRefl h)
  have ht := PPrf.param (eqTrans hb es) (eqRefl h)
  rw [Tm.psi_var0] at hs ht
  exact join (join ht hs) ks

end PPrf

variable {Γ : List (NFm n)} {A : NFm n}

theorem NPrf.toPPrf (h : NPrf Γ A) : PPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | trOne h _ _ ih₁ ih₂ => exact PPrf.trOne h ih₁ ih₂
  | qE t _ _ ih₁ ih₂ => exact .qE t ih₁ ih₂
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dICase B t _ ih => exact .dICase B t ih
  | qIInd s₁ s₂ _ ih => exact .qIInd s₁ s₂ ih

/-- **Parameter substitution is enough.**  The kernel with Param in place of
transport in a template derives the same sequents. -/
theorem pprf_iff_nprf : PPrf Γ A ↔ NPrf Γ A := ⟨PPrf.toNPrf, NPrf.toPPrf⟩

end LeanProofs.ConciseIPRA
