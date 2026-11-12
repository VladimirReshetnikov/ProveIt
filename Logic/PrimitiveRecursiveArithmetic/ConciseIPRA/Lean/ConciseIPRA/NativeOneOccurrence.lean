import ConciseIPRA.NativeMirror
import ConciseIPRA.NativeOneContext

/-!
# Replacement of one occurrence

`LPrf` is the calculus of the note on one-occurrence transport in the package
`Research/kernel_refinement` (`review/left_occurrence_transport.md`, and the
theorem "One occurrence suffices" of its report).  It is the kernel with
transport replaced by

  **LOR**: from `s = t` and `C[s] = r` infer `C[t] = r`,

where `C` is a term context with exactly one hole.  The hole may lie below
binders; plugging avoids capture.  The right side `r` is fixed.

A context is a term `C` with one more variable, the hole, at index `0`.
`Tm.Hole i C` says that the variable `i` occurs exactly once in `C`, and
`Tm.Free i x` that it does not occur.

`lprf_iff_nprf` proves that `LPrf` derives the same sequents as the kernel.
`UPrf` of `NativeOneContext` is the same rule with an arbitrary template, so
it is enough to derive that rule in `LPrf`.  `Reach s t x y` says that `y` is
obtained from `x` by finitely many replacements of one occurrence of `s` by
`t`.  It is a congruence for the term formers, below a binder as well
(`Reach.iterH`, where the hole of the context and the bound variable are
exchanged), so `h(s)` reaches `h(t)` for every template `h` (`Reach.subst`),
and every step of a chain is one application of LOR (`LPrf.ofReach`).  No
occurrence is counted and none is singled out as the first.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open Tm (zero succ iter)

variable {n m k : ℕ}

namespace Tm

/-- The variable `i` does not occur in the term. -/
inductive Free : {k : ℕ} → Fin k → Tm k → Prop
  | var {k : ℕ} {i j : Fin k} (h : j ≠ i) : Free i (.var j)
  | zero {k : ℕ} {i : Fin k} : Free i .zero
  | succ {k : ℕ} {i : Fin k} {c : Tm k} (hc : Free i c) : Free i (.succ c)
  | iter {k : ℕ} {i : Fin k} {c a : Tm k} {h : Tm (k + 1)} (hc : Free i c) (ha : Free i a)
      (hh : Free i.succ h) : Free i (.iter c a h)

/-- The variable `i` occurs exactly once in the term. -/
inductive Hole : {k : ℕ} → Fin k → Tm k → Prop
  | var {k : ℕ} (i : Fin k) : Hole i (.var i)
  | succ {k : ℕ} {i : Fin k} {c : Tm k} (hc : Hole i c) : Hole i (.succ c)
  | iterC {k : ℕ} {i : Fin k} {c a : Tm k} {h : Tm (k + 1)} (hc : Hole i c) (ha : Free i a)
      (hh : Free i.succ h) : Hole i (.iter c a h)
  | iterA {k : ℕ} {i : Fin k} {c a : Tm k} {h : Tm (k + 1)} (hc : Free i c) (ha : Hole i a)
      (hh : Free i.succ h) : Hole i (.iter c a h)
  | iterH {k : ℕ} {i : Fin k} {c a : Tm k} {h : Tm (k + 1)} (hc : Free i c) (ha : Free i a)
      (hh : Hole i.succ h) : Hole i (.iter c a h)

/-- A variable outside the range of a renaming does not occur in a renamed
term. -/
theorem free_ren (x : Tm k) : ∀ {m : ℕ} (ξ : Fin k → Fin m) (i : Fin m),
    (∀ j, ξ j ≠ i) → Free i (ren ξ x) := by
  induction x with
  | var j => intro m ξ i hξ; exact .var (hξ j)
  | zero => intro m ξ i _; exact .zero
  | succ c ih => intro m ξ i hξ; exact .succ (ih ξ i hξ)
  | iter c a h ihc iha ihh =>
    intro m ξ i hξ
    refine .iter (ihc ξ i hξ) (iha ξ i hξ) (ihh (upRen ξ) i.succ fun j => ?_)
    refine Fin.cases ?_ (fun j' => ?_) j
    · rw [upRen_zero]; exact (Fin.succ_ne_zero i).symm
    · rw [upRen_succ]; exact fun e => hξ j' (Fin.succ_inj.1 e)

theorem Free.ren {i : Fin k} {x : Tm k} (h : Free i x) :
    ∀ {m : ℕ} (ξ : Fin k → Fin m), Function.Injective ξ → Free (ξ i) (Tm.ren ξ x) := by
  induction h with
  | var hj => intro m ξ hξ; exact .var fun e => hj (hξ e)
  | zero => intro m ξ _; exact .zero
  | succ _ ih => intro m ξ hξ; exact .succ (ih ξ hξ)
  | iter _ _ _ ihc iha ihh =>
    intro m ξ hξ
    have h₃ := ihh (upRen ξ) (upRen_inj hξ)
    rw [upRen_succ] at h₃
    exact .iter (ihc ξ hξ) (iha ξ hξ) h₃

theorem Hole.ren {i : Fin k} {x : Tm k} (h : Hole i x) :
    ∀ {m : ℕ} (ξ : Fin k → Fin m), Function.Injective ξ → Hole (ξ i) (Tm.ren ξ x) := by
  induction h with
  | var i => intro m ξ _; exact .var _
  | succ _ ih => intro m ξ hξ; exact .succ (ih ξ hξ)
  | iterC _ ha hh ih =>
    intro m ξ hξ
    have h₃ := hh.ren (upRen ξ) (upRen_inj hξ)
    rw [upRen_succ] at h₃
    exact .iterC (ih ξ hξ) (ha.ren ξ hξ) h₃
  | iterA hc _ hh ih =>
    intro m ξ hξ
    have h₃ := hh.ren (upRen ξ) (upRen_inj hξ)
    rw [upRen_succ] at h₃
    exact .iterA (hc.ren ξ hξ) (ih ξ hξ) h₃
  | iterH hc ha _ ih =>
    intro m ξ hξ
    have h₃ := ih (upRen ξ) (upRen_inj hξ)
    rw [upRen_succ] at h₃
    exact .iterH (hc.ren ξ hξ) (ha.ren ξ hξ) h₃

/-- The hole does not occur in a term moved under it. -/
theorem free_shift (x : Tm k) : Free 0 (Syn.shift x) := by
  rw [shift_eq_ren]
  exact free_ren x Fin.succ 0 fun j => Fin.succ_ne_zero j

/-- The hole does not occur in a body moved under it. -/
theorem free_upShift (g : Tm (k + 1)) :
    Free 1 (Syn.subst (up fun i => (Syn.var i.succ : Tm (k + 1))) g) := by
  have e : Syn.subst (up fun i => (Syn.var i.succ : Tm (k + 1))) g
      = Tm.ren (upRen Fin.succ) g := by
    rw [Tm.up_rn]
    exact (ren_eq_sub g _).symm
  rw [e]
  refine free_ren g _ 1 fun j => ?_
  refine Fin.cases ?_ (fun j' => ?_) j
  · rw [upRen_zero]; exact fun e => Fin.succ_ne_zero (0 : Fin (k + 1)) e.symm
  · rw [upRen_succ]; exact fun e => Fin.succ_ne_zero j' (Fin.succ_inj.1 e)

/-- The exchange of the first two variables. -/
def sw : Fin (k + 2) → Fin (k + 2) := Fin.cases 1 (Fin.cases 0 fun j => j.succ.succ)

theorem sw_sw (i : Fin (k + 2)) : sw (sw i) = i := by
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun j => ?_) i) i <;> rfl

theorem sw_inj : Function.Injective (sw (k := k)) :=
  Function.LeftInverse.injective sw_sw

/-- A context in the scope of one binder, as the body of an iterator: the hole
and the bound variable are exchanged. -/
def swp (x : Tm (k + 2)) : Tm (k + 2) := ren sw x

theorem Hole.swp {C : Tm (k + 2)} (h : Hole 0 C) : Hole 1 (Tm.swp C) := h.ren sw sw_inj

theorem swp_inst (x : Tm k) (C : Tm (k + 2)) :
    Syn.subst (up (inst x)) (swp C) = Syn.subst (inst (Syn.shift x)) C := by
  have e : swp C = Syn.subst (fun i => (Syn.var (sw i) : Tm (k + 2))) C := ren_eq_sub C sw
  rw [e, Syn.subst_subst]
  congr 1
  funext i
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun j => ?_) i) i <;> simp [sw]

end Tm

/-- Derivability in the kernel with replacement of one occurrence in the left
side of an equation in place of transport. -/
inductive LPrf : {n : ℕ} → List (NFm n) → NFm n → Prop
  | hyp {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (h : A ∈ Γ) : LPrf Γ A
  | iterZero {n : ℕ} {Γ : List (NFm n)} (a : Tm n) (h : Tm (n + 1)) :
      LPrf Γ (.eq (iter zero a h) a)
  | iterSucc {n : ℕ} {Γ : List (NFm n)} (c a : Tm n) (h : Tm (n + 1)) :
      LPrf Γ (.eq (iter (succ c) a h) (Syn.subst (inst (iter c a h)) h))
  /-- LOR: from `s = t` and `C[s] = r` infer `C[t] = r`, for a context `C`
  with exactly one hole. -/
  | lor {n : ℕ} {Γ : List (NFm n)} (C : Tm (n + 1)) (hC : Tm.Hole 0 C) {s t r : Tm n}
      (h₁ : LPrf Γ (.eq s t)) (h₂ : LPrf Γ (.eq (Syn.subst (inst s) C) r)) :
      LPrf Γ (.eq (Syn.subst (inst t) C) r)
  | qE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 1)} (t : Tm n)
      (h₁ : LPrf Γ (.Q B)) (h₂ : LPrf Γ (B.subst (inst zero))) : LPrf Γ (B.subst (inst t))
  | dE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 2)} {A : NFm n}
      (h₁ : LPrf Γ (.D B)) (h₂ : LPrf (.Q B :: Γ.map NFm.shift) A.shift) : LPrf Γ A
  | dICase {n : ℕ} {Γ : List (NFm n)} (B : NFm (n + 2)) (t : Tm n)
      (h : LPrf (((B.subst (up (inst t))).subst (inst zero)).shift :: Γ.map NFm.shift)
        ((B.subst (up (inst t))).subst (repl (succ (var 0))))) :
      LPrf Γ (.D B)
  | qIInd {n : ℕ} {Γ : List (NFm n)} (s₁ s₂ : Tm (n + 1))
      (h : LPrf (NFm.eq s₁ s₂ :: Γ.map NFm.shift)
        ((NFm.eq s₁ s₂).subst (repl (succ (var 0))))) :
      LPrf Γ (.Q (.eq s₁ s₂))

/-- `Reach s t x y`: the term `y` is obtained from `x` by finitely many
replacements of one occurrence of `s` by `t`. -/
inductive Reach (s t : Tm n) : Tm n → Tm n → Prop
  | refl (x : Tm n) : Reach s t x x
  | step (C : Tm (n + 1)) (hC : Tm.Hole 0 C) :
      Reach s t (Syn.subst (inst s) C) (Syn.subst (inst t) C)
  | trans {x y z : Tm n} (h₁ : Reach s t x y) (h₂ : Reach s t y z) : Reach s t x z

namespace Reach

variable {s t x y : Tm n}

theorem succ (h : Reach s t x y) : Reach s t (succ x) (succ y) := by
  induction h with
  | refl x => exact .refl _
  | step C hC =>
    have k := Reach.step (s := s) (t := t) (Tm.succ C) (.succ hC)
    simpa only [Tm.subst_succ] using k
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- A replacement in the counter of an iterator. -/
theorem iterC (a : Tm n) (g : Tm (n + 1)) (h : Reach s t x y) :
    Reach s t (iter x a g) (iter y a g) := by
  induction h with
  | refl x => exact .refl _
  | step C hC =>
    have k := Reach.step (s := s) (t := t)
      (Tm.iter C (Syn.shift a) (Syn.subst (up fun i => Syn.var i.succ) g))
      (.iterC hC (Tm.free_shift a) (Tm.free_upShift g))
    simpa only [Tm.subst_iter, Syn.subst_inst_shift, Syn.subst_up_inst_up_shift] using k
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- A replacement in the seed of an iterator. -/
theorem iterA (c : Tm n) (g : Tm (n + 1)) (h : Reach s t x y) :
    Reach s t (iter c x g) (iter c y g) := by
  induction h with
  | refl x => exact .refl _
  | step C hC =>
    have k := Reach.step (s := s) (t := t)
      (Tm.iter (Syn.shift c) C (Syn.subst (up fun i => Syn.var i.succ) g))
      (.iterA (Tm.free_shift c) hC (Tm.free_upShift g))
    simpa only [Tm.subst_iter, Syn.subst_inst_shift, Syn.subst_up_inst_up_shift] using k
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- A replacement in the body of an iterator, below its binder. -/
theorem iterH (c a : Tm n) {x y : Tm (n + 1)} (h : Reach (Syn.shift s) (Syn.shift t) x y) :
    Reach s t (iter c a x) (iter c a y) := by
  induction h with
  | refl x => exact .refl _
  | step C hC =>
    have k := Reach.step (s := s) (t := t)
      (Tm.iter (Syn.shift c) (Syn.shift a) (Tm.swp C))
      (.iterH (Tm.free_shift c) (Tm.free_shift a) hC.swp)
    simpa only [Tm.subst_iter, Syn.subst_inst_shift, Tm.swp_inst] using k
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **Every template is a chain of single replacements.**  If two
substitutions differ only where one has `s` and the other `t`, their
instances of a term are connected. -/
theorem subst (h : Tm k) : ∀ {n : ℕ} (s t : Tm n) (σ τ : Fin k → Tm n),
    (∀ i, σ i = τ i ∨ (σ i = s ∧ τ i = t)) → Reach s t (Syn.subst σ h) (Syn.subst τ h) := by
  induction h with
  | var i =>
    intro n s t σ τ hσ
    rw [show Syn.subst σ (Tm.var i) = σ i from Syn.subst_var σ i,
      show Syn.subst τ (Tm.var i) = τ i from Syn.subst_var τ i]
    rcases hσ i with e | ⟨e₁, e₂⟩
    · rw [e]; exact .refl _
    · rw [e₁, e₂]
      have k := Reach.step (s := s) (t := t) (Syn.var 0) (Tm.Hole.var 0)
      simpa only [Syn.subst_var, Syn.inst_zero] using k
  | zero => intro n s t σ τ _; exact .refl _
  | succ c ih => intro n s t σ τ hσ; exact (ih s t σ τ hσ).succ
  | iter c a g ihc iha ihg =>
    intro n s t σ τ hσ
    rw [Tm.subst_iter, Tm.subst_iter]
    refine ((ihc s t σ τ hσ).iterC _ _).trans (((iha s t σ τ hσ).iterA _ _).trans
      (Reach.iterH _ _ (ihg (Syn.shift s) (Syn.shift t) (up σ) (up τ) fun i => ?_)))
    refine Fin.cases ?_ (fun j => ?_) i
    · exact .inl rfl
    · rcases hσ j with e | ⟨e₁, e₂⟩
      · left; rw [Syn.up_succ, Syn.up_succ, e]
      · right; exact ⟨by rw [Syn.up_succ, e₁], by rw [Syn.up_succ, e₂]⟩

end Reach

variable {Γ : List (NFm n)} {A : NFm n}

namespace LPrf

/-- Every step of a chain is one application of LOR. -/
theorem ofReach {s t x y : Tm n} (he : LPrf Γ (.eq s t)) (h : Reach s t x y) :
    ∀ r, LPrf Γ (.eq x r) → LPrf Γ (.eq y r) := by
  induction h with
  | refl x => exact fun r hr => hr
  | step C hC => exact fun r hr => .lor C hC he hr
  | trans _ _ ih₁ ih₂ => exact fun r hr => ih₂ r (ih₁ r hr)

/-- Transport in an arbitrary template, with the right side fixed. -/
theorem trL (h : Tm (n + 1)) {s t r : Tm n} (h₁ : LPrf Γ (.eq s t))
    (h₂ : LPrf Γ (.eq (Syn.subst (inst s) h) r)) : LPrf Γ (.eq (Syn.subst (inst t) h) r) :=
  ofReach h₁ (Reach.subst h s t (inst s) (inst t) fun i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact .inr ⟨rfl, rfl⟩
    · left; rw [Syn.inst_succ, Syn.inst_succ]) r h₂

theorem toUPrf (h : LPrf Γ A) : UPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | lor C _ _ _ ih₁ ih₂ => exact .trL C ih₁ ih₂
  | qE t _ _ ih₁ ih₂ => exact .qE t ih₁ ih₂
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dICase B t _ ih => exact .dICase B t ih
  | qIInd s t _ ih => exact .qIInd s t ih

end LPrf

theorem UPrf.toLPrf (h : UPrf Γ A) : LPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | trL h _ _ ih₁ ih₂ => exact LPrf.trL h ih₁ ih₂
  | qE t _ _ ih₁ ih₂ => exact .qE t ih₁ ih₂
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dICase B t _ ih => exact .dICase B t ih
  | qIInd s t _ ih => exact .qIInd s t ih

/-- Replacement of one occurrence and replacement in a template derive the
same sequents. -/
theorem lprf_iff_uprf : LPrf Γ A ↔ UPrf Γ A := ⟨LPrf.toUPrf, UPrf.toLPrf⟩

/-- **One occurrence suffices.**  The kernel with replacement of one
occurrence in the left side of an equation, in place of transport, derives
the same sequents. -/
theorem lprf_iff_nprf : LPrf Γ A ↔ NPrf Γ A := lprf_iff_uprf.trans uprf_iff_nprf

end LeanProofs.ConciseIPRA
