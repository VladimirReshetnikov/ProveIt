import ConciseIPRA.TeqArith

/-!
# The theory `T_UR` and its terms modulo provable equality

`T_UR` (`kern:def:U`) is `T_eq` with induction for literal equations replaced
by the rule of uniqueness of iteration

  from `Γ ⊢ f(S z) = h(f(z))` with `z` fresh infer `Γ ⊢ f(t) = I(t, f(0); u.h(u))`,

stated here as the axiom scheme `TurAx.ur`.  As for `T_eq` (`Lindenbaum`), the
type `U Γ` of terms modulo provable equality turns derivations of equations into
equations of Lean; the operations of terms descend to it.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm
open Tm (zero succ iter)

variable {n m : ℕ}

/-- The weakening of a body under the binder of the fresh variable. -/
abbrev Tm.wkb (h : Tm (n + 1)) : Tm (n + 2) := Syn.subst (up fun i => Syn.var i.succ) h

/-- The axioms of `T_UR`: those of `T_eq` with uniqueness of iteration in place of
induction. -/
inductive TurAx : Theory Tm
  | iterZero {n : ℕ} (a : Tm n) (h : Tm (n + 1)) : TurAx n (iter zero a h ≐ a)
  | iterSucc {n : ℕ} (c a : Tm n) (h : Tm (n + 1)) :
      TurAx n (iter (succ c) a h ≐ Syn.subst (inst (iter c a h)) h)
  | cover : TurAx 1 ((var 0 ≐ zero) ⋎ Fm.ex (var 1 ≐ succ (var 0)))
  | sep : TurAx 0 ((zero ≐ succ zero) ⟶ Fm.bot)
  | ur {n : ℕ} (f h : Tm (n + 1)) :
      TurAx n (Fm.all (Syn.subst (repl (succ (var 0))) f ≐ Syn.subst (inst f) (Tm.wkb h)) ⟶
        Fm.all (f ≐ iter (var 0) (Syn.shift (Syn.subst (inst zero) f)) (Tm.wkb h)))

namespace Tur

variable {Γ : List (Fm Tm n)}

theorem iterZero (a : Tm n) (h : Tm (n + 1)) : Γ ⊢[TurAx] iter zero a h ≐ a :=
  .axm (.iterZero a h)

theorem iterSucc (c a : Tm n) (h : Tm (n + 1)) :
    Γ ⊢[TurAx] iter (succ c) a h ≐ Syn.subst (inst (iter c a h)) h :=
  .axm (.iterSucc c a h)

theorem cover (t : Tm n) :
    Γ ⊢[TurAx] (t ≐ zero) ⋎ Fm.ex (Syn.shift t ≐ succ (var 0)) := by
  simpa using Prf.ax (Γ := Γ) TurAx.cover (fun _ => t)

theorem sep : Γ ⊢[TurAx] (zero ≐ succ zero) ⟶ Fm.bot := by
  simpa using Prf.ax (Γ := Γ) TurAx.sep Fin.elim0

theorem casesOn (t : Tm n) {ψ : Fm Tm n}
    (h0 : (t ≐ zero) :: Γ ⊢[TurAx] ψ)
    (hS : (Syn.shift t ≐ succ (var 0)) :: Γ.map Fm.shift ⊢[TurAx] ψ.shift) :
    Γ ⊢[TurAx] ψ :=
  .orE (cover t) h0 (.exE Prf.hyp0 (hS.weaken (List.cons_subset_cons _ (by simp))))

/-- **Uniqueness of iteration**, as a rule over an arbitrary context. -/
theorem ur (f h : Tm (n + 1)) (t : Tm n)
    (hs : Γ.map Fm.shift ⊢[TurAx]
      Syn.subst (repl (succ (var 0))) f ≐ Syn.subst (inst f) (Tm.wkb h)) :
    Γ ⊢[TurAx] Syn.subst (inst t) f ≐ iter t (Syn.subst (inst zero) f) h := by
  have k := Prf.allE t (.impE (.axm (.ur f h)) (.allI hs))
  simpa [Tm.wkb, Syn.subst_up_inst_up_shift] using k

theorem congr₁ {f : ∀ k, Tm k → Tm k} (hf : Sub₁ f) {a a' : Tm n}
    (ha : Γ ⊢[TurAx] a ≐ a') : Γ ⊢[TurAx] f n a ≐ f n a' := by
  simpa only [hf, Syn.subst_var, Syn.inst_zero] using Prf.eqCongr1 (f (n + 1) (var 0)) ha

theorem congr₂ {f : ∀ k, Tm k → Tm k → Tm k} (hf : Sub₂ f) {a a' b b' : Tm n}
    (ha : Γ ⊢[TurAx] a ≐ a') (hb : Γ ⊢[TurAx] b ≐ b') :
    Γ ⊢[TurAx] f n a b ≐ f n a' b' := by
  have h₁ := Prf.eqCongr1 (f (n + 1) (var 0) (shift b)) ha
  have h₂ := Prf.eqCongr1 (f (n + 1) (shift a') (var 0)) hb
  simp only [hf, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at h₁ h₂
  exact Prf.eqTrans h₁ h₂

theorem congr₃ {f : ∀ k, Tm k → Tm k → Tm k → Tm k} (hf : Sub₃ f) {a a' b b' c c' : Tm n}
    (ha : Γ ⊢[TurAx] a ≐ a') (hb : Γ ⊢[TurAx] b ≐ b') (hc : Γ ⊢[TurAx] c ≐ c') :
    Γ ⊢[TurAx] f n a b c ≐ f n a' b' c' := by
  have h₁ := Prf.eqCongr1 (f (n + 1) (var 0) (shift b) (shift c)) ha
  have h₂ := Prf.eqCongr1 (f (n + 1) (shift a') (var 0) (shift c)) hb
  have h₃ := Prf.eqCongr1 (f (n + 1) (shift a') (shift b') (var 0)) hc
  simp only [hf, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at h₁ h₂ h₃
  exact Prf.eqTrans (Prf.eqTrans h₁ h₂) h₃

theorem iterCongr (h : Tm (n + 1)) {c c' a a' : Tm n}
    (hc : Γ ⊢[TurAx] c ≐ c') (ha : Γ ⊢[TurAx] a ≐ a') :
    Γ ⊢[TurAx] Tm.iter c a h ≐ Tm.iter c' a' h := by
  have h₁ := Prf.eqCongr1
    (Tm.iter (var 0) (shift a) (Syn.subst (up (fun i => var i.succ)) h)) hc
  have h₂ := Prf.eqCongr1
    (Tm.iter (shift c') (var 0) (Syn.subst (up (fun i => var i.succ)) h)) ha
  simp only [Tm.subst_iter, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    Syn.subst_up_inst_up_shift] at h₁ h₂
  exact Prf.eqTrans h₁ h₂

end Tur

/-- Provable equality of terms in `T_UR`. -/
def turSetoid (Γ : List (Fm Tm n)) : Setoid (Tm n) where
  r a b := Γ ⊢[TurAx] a ≐ b
  iseqv := ⟨fun a => Prf.eqRefl a, fun h => Prf.eqSymm h, fun h₁ h₂ => Prf.eqTrans h₁ h₂⟩

/-- Terms modulo provable equality of `T_UR` in the context `Γ`. -/
def U (Γ : List (Fm Tm n)) : Type := Quotient (turSetoid Γ)

/-- A substitution sending the hypotheses of `Γ` into `Γ'`. -/
structure UExt (Γ : List (Fm Tm n)) (Γ' : List (Fm Tm m)) where
  σ : Fin n → Tm m
  sub : ∀ φ ∈ Γ, φ.subst σ ∈ Γ'

namespace U

variable {Γ : List (Fm Tm n)}

def mk (Γ : List (Fm Tm n)) (a : Tm n) : U Γ := Quotient.mk (turSetoid Γ) a

theorem sound {a b : Tm n} (h : Γ ⊢[TurAx] a ≐ b) : mk Γ a = mk Γ b := Quotient.sound h

theorem exact {a b : Tm n} (h : mk Γ a = mk Γ b) : Γ ⊢[TurAx] a ≐ b := Quotient.exact h

theorem ind {p : U Γ → Prop} (h : ∀ a, p (mk Γ a)) (x : U Γ) : p x := Quotient.ind h x

theorem ind₂ {p : U Γ → U Γ → Prop} (h : ∀ a b, p (mk Γ a) (mk Γ b)) (x y : U Γ) : p x y :=
  Quotient.inductionOn₂ x y h

theorem ind₃ {p : U Γ → U Γ → U Γ → Prop} (h : ∀ a b c, p (mk Γ a) (mk Γ b) (mk Γ c))
    (x y z : U Γ) : p x y z :=
  Quotient.inductionOn₃ x y z h

theorem hyp0 {a b : Tm n} : mk ((a ≐ b) :: Γ) a = mk ((a ≐ b) :: Γ) b := sound Prf.hyp0

def op₁ (f : ∀ k, Tm k → Tm k) (hf : Sub₁ f) : U Γ → U Γ :=
  Quotient.lift (fun a => mk Γ (f n a)) (fun _ _ h => sound (Tur.congr₁ hf h))

def op₂ (f : ∀ k, Tm k → Tm k → Tm k) (hf : Sub₂ f) : U Γ → U Γ → U Γ :=
  Quotient.lift₂ (fun a b => mk Γ (f n a b))
    (fun _ _ _ _ ha hb => sound (Tur.congr₂ hf ha hb))

def op₃ (f : ∀ k, Tm k → Tm k → Tm k → Tm k) (hf : Sub₃ f) (x y z : U Γ) : U Γ :=
  Quotient.lift
    (fun a => Quotient.lift₂ (fun b c => mk Γ (f n a b c))
      (fun _ _ _ _ hb hc => sound (Tur.congr₃ hf (Prf.eqRefl _) hb hc)) y z)
    (fun _ _ ha => Quotient.inductionOn₂ y z (fun b c =>
      sound (Tur.congr₃ hf ha (Prf.eqRefl b) (Prf.eqRefl c)))) x

instance : Zero (U Γ) := ⟨mk Γ Tm.zero⟩

instance : One (U Γ) := ⟨mk Γ Tm.one⟩

def succ : U Γ → U Γ := op₁ (fun _ => Tm.succ) (fun _ _ => rfl)

@[simp] theorem mk_zero : mk Γ Tm.zero = 0 := rfl

@[simp] theorem mk_one : mk Γ Tm.one = 1 := rfl

@[simp] theorem mk_succ (a : Tm n) : mk Γ (Tm.succ a) = succ (mk Γ a) := rfl

theorem one_eq : (1 : U Γ) = succ 0 := rfl

/-- The iterator with a fixed step term. -/
def iterate (h : Tm (n + 1)) : U Γ → U Γ → U Γ :=
  Quotient.lift₂ (fun c a => mk Γ (Tm.iter c a h))
    (fun _ _ _ _ hc ha => sound (Tur.iterCongr h hc ha))

/-- Instantiation of a step term. -/
def app (h : Tm (n + 1)) : U Γ → U Γ :=
  Quotient.lift (fun a => mk Γ (Syn.subst (inst a) h)) (fun _ _ e => sound (Prf.eqCongr1 h e))

theorem mk_iter (c a : Tm n) (h : Tm (n + 1)) :
    mk Γ (Tm.iter c a h) = iterate h (mk Γ c) (mk Γ a) := rfl

theorem app_mk (h : Tm (n + 1)) (a : Tm n) : app h (mk Γ a) = mk Γ (Syn.subst (inst a) h) := rfl

@[simp] theorem iterate_zero (h : Tm (n + 1)) (x : U Γ) : iterate h 0 x = x := by
  induction x using U.ind with | _ a => exact sound (Tur.iterZero a h)

@[simp] theorem iterate_succ (h : Tm (n + 1)) (c x : U Γ) :
    iterate h (succ c) x = app h (iterate h c x) := by
  induction c, x using U.ind₂ with | _ c a => exact sound (Tur.iterSucc c a h)

theorem absurd (h : (0 : U Γ) = 1) (x y : U Γ) : x = y := by
  induction x, y using U.ind₂ with | _ a b => exact sound (.botE _ (.impE Tur.sep (exact h)))

/-- **Uniqueness of iteration** on classes: a template whose value at `S z` is the body
at its value at `z` is the iteration of the body from its value at `0`.  The step is
found by `simp` when it is not given. -/
theorem ur (f h : Tm (n + 1)) (a : Tm n)
    (hs : mk (Γ.map Fm.shift) (Syn.subst (repl (Tm.succ (var 0))) f)
      = mk (Γ.map Fm.shift) (Syn.subst (inst f) (Tm.wkb h)) := by simp) :
    mk Γ (Syn.subst (inst a) f) = mk Γ (Tm.iter a (Syn.subst (inst Tm.zero) f) h) :=
  sound (Tur.ur f h a (exact hs))

end U

namespace UExt

variable {Γ : List (Fm Tm n)} {Γ' : List (Fm Tm m)}

theorem prf (e : UExt Γ Γ') {φ : Fm Tm n} (h : Γ ⊢[TurAx] φ) : Γ' ⊢[TurAx] φ.subst e.σ :=
  h.substWeaken e.σ (List.forall_mem_map.2 e.sub)

def map (e : UExt Γ Γ') : U Γ → U Γ' :=
  Quotient.lift (fun a => U.mk Γ' (Syn.subst e.σ a)) (fun _ _ h => U.sound (e.prf h))

@[simp] theorem map_zero (e : UExt Γ Γ') : e.map 0 = 0 := rfl

@[simp] theorem map_one (e : UExt Γ Γ') : e.map 1 = 1 := rfl

theorem map_op₁ (e : UExt Γ Γ') (f : ∀ k, Tm k → Tm k) (hf : Sub₁ f) (x : U Γ) :
    e.map (U.op₁ f hf x) = U.op₁ f hf (e.map x) := by
  induction x using U.ind with | _ a => exact congrArg (U.mk Γ') (hf e.σ a)

theorem map_op₂ (e : UExt Γ Γ') (f : ∀ k, Tm k → Tm k → Tm k) (hf : Sub₂ f) (x y : U Γ) :
    e.map (U.op₂ f hf x y) = U.op₂ f hf (e.map x) (e.map y) := by
  induction x, y using U.ind₂ with | _ a b => exact congrArg (U.mk Γ') (hf e.σ a b)

theorem map_op₃ (e : UExt Γ Γ') (f : ∀ k, Tm k → Tm k → Tm k → Tm k) (hf : Sub₃ f)
    (x y z : U Γ) : e.map (U.op₃ f hf x y z) = U.op₃ f hf (e.map x) (e.map y) (e.map z) := by
  induction x, y, z using U.ind₃ with | _ a b c => exact congrArg (U.mk Γ') (hf e.σ a b c)

@[simp] theorem map_succ (e : UExt Γ Γ') (x : U Γ) : e.map (U.succ x) = U.succ (e.map x) :=
  map_op₁ e (fun _ => Tm.succ) (fun _ _ => rfl) x

def wk (ψ : Fm Tm n) : UExt Γ (ψ :: Γ) where
  σ := var
  sub φ h := by rw [Fm.subst_id]; exact List.mem_cons_of_mem _ h

def shiftCons (ψ : Fm Tm (n + 1)) : UExt Γ (ψ :: Γ.map Fm.shift) where
  σ := fun i => var i.succ
  sub _ h := List.mem_cons_of_mem _ (List.mem_map_of_mem (f := Fm.shift) h)

theorem wk_map_mk (ψ : Fm Tm n) (a : Tm n) :
    (wk ψ : UExt Γ (ψ :: Γ)).map (U.mk Γ a) = U.mk (ψ :: Γ) a :=
  congrArg (U.mk (ψ :: Γ)) (Syn.subst_id a)

end UExt

namespace U

variable {Γ : List (Fm Tm n)}

/-- Proof of an equation by cases on a number: it is `0` or a successor in an
extension of the context. -/
theorem cases (x : U Γ) {p q : U Γ}
    (h0 : ∀ {m : ℕ} {Γ' : List (Fm Tm m)} (e : UExt Γ Γ'), e.map x = 0 → e.map p = e.map q)
    (hS : ∀ {m : ℕ} {Γ' : List (Fm Tm m)} (e : UExt Γ Γ') (z : U Γ'),
      e.map x = succ z → e.map p = e.map q) : p = q := by
  induction x, p, q using U.ind₃ with | _ a s t
  refine sound (Tur.casesOn a (exact ?_) (exact ?_))
  · have h := h0 (UExt.wk (a ≐ Tm.zero)) (by rw [UExt.wk_map_mk]; exact hyp0)
    rwa [UExt.wk_map_mk, UExt.wk_map_mk] at h
  · exact hS (UExt.shiftCons _) (mk _ (var 0)) hyp0

end U

end LeanProofs.ConciseIPRA
