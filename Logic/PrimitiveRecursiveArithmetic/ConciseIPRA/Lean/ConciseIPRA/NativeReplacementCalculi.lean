import ConciseIPRA.NativeAbstraction

/-!
# Calculi with a replacement rule in place of transport

Three calculi of the article (`kern:def:B`, `kern:thm:brep`, `kern:thm:tfree`),
equivalent to the kernel:

* `BPrf` (`B`): the kernel with transport replaced by backward replacement
  `bRep` (from `s = t` and `Rep_t^s(u) = r` infer `r = u`);
* `B7Prf` (`B₇`): the single introduction of `WPrf` with `bRep`, seven rules;
* `G7Prf` (`G₇`): the single introduction with the template-free replacement
  of `TPrf` (from `s = t` and `u = v` infer `v = Rep_s^t(u)`), seven rules.

The equality rules and the kernel's transport are derived from the first
computation and the replacement rule alone, generically over the classes
`BRKernel` and `TFKernel`, with a marker larger than the template; the
introductions of the kernel come from `WKernel` once transport and `QE` are
available.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open Tm (zero succ iter)

variable {n m : ℕ}

/-! ### Equality from the first computation and backward replacement -/

/-- The first computation equation and backward replacement. -/
class BRKernel (P : ∀ {n : ℕ}, List (NFm n) → NFm n → Prop) : Prop where
  iterZero : ∀ {n : ℕ} {Γ : List (NFm n)} (a : Tm n) (h : Tm (n + 1)),
    P Γ (.eq (iter zero a h) a)
  bRep : ∀ {n : ℕ} {Γ : List (NFm n)} {s t u r : Tm n}, P Γ (.eq s t) →
    P Γ (.eq (Tm.rpl t s Syn.var u) r) → P Γ (.eq r u)

namespace BRKernel

variable {P : ∀ {n : ℕ}, List (NFm n) → NFm n → Prop} [BRKernel @P] {Γ : List (NFm n)}

theorem join {s t r : Tm n} (h₁ : P Γ (.eq s t)) (h₂ : P Γ (.eq s r)) : P Γ (.eq r t) :=
  bRep h₁ (by rwa [Tm.rpl_root])

theorem eqRefl (a : Tm n) : P Γ (.eq a a) := join (iterZero a zero) (iterZero a zero)

theorem eqSymm {s t : Tm n} (h : P Γ (.eq s t)) : P Γ (.eq t s) := join (eqRefl s) h

theorem eqTrans {s t u : Tm n} (h₁ : P Γ (.eq s t)) (h₂ : P Γ (.eq t u)) : P Γ (.eq s u) :=
  join h₂ (eqSymm h₁)

theorem trOne (h : Tm (n + 1)) {s t u : Tm n} (h₁ : P Γ (.eq s t))
    (h₂ : P Γ (.eq (Syn.subst (inst s) h) u)) : P Γ (.eq u (Syn.subst (inst t) h)) := by
  have hK : P Γ (.eq (Tm.marker h s) s) := iterZero s _
  have k₁ : P Γ (.eq (Syn.subst (inst s) h) (Syn.subst (inst (Tm.marker h s)) h)) :=
    bRep (eqSymm hK) (by rw [Tm.rpl_marker]; exact eqRefl _)
  have k₂ : P Γ (.eq (Syn.subst (inst t) h) (Syn.subst (inst (Tm.marker h s)) h)) :=
    bRep (eqSymm (eqTrans hK h₁)) (by rw [Tm.rpl_marker]; exact eqRefl _)
  exact join (eqTrans k₁ (eqSymm k₂)) h₂

theorem trEq (a b : Tm (n + 1)) {s t : Tm n} (h₁ : P Γ (.eq s t))
    (h₂ : P Γ (.eq (Syn.subst (inst s) a) (Syn.subst (inst s) b))) :
    P Γ (.eq (Syn.subst (inst t) a) (Syn.subst (inst t) b)) :=
  trOne b h₁ (trOne a h₁ h₂)

end BRKernel

/-! ### Equality from the first computation and template-free replacement -/

/-- The first computation equation and template-free replacement. -/
class TFKernel (P : ∀ {n : ℕ}, List (NFm n) → NFm n → Prop) : Prop where
  iterZero : ∀ {n : ℕ} {Γ : List (NFm n)} (a : Tm n) (h : Tm (n + 1)),
    P Γ (.eq (iter zero a h) a)
  tf : ∀ {n : ℕ} {Γ : List (NFm n)} {s t u v : Tm n}, P Γ (.eq s t) → P Γ (.eq u v) →
    P Γ (.eq v (Tm.rep s t u))

namespace TFKernel

variable {P : ∀ {n : ℕ}, List (NFm n) → NFm n → Prop} [TFKernel @P] {Γ : List (NFm n)}

theorem eqRefl (a : Tm n) : P Γ (.eq a a) := by
  have h := tf (P := @P) (Γ := Γ) (iterZero a (Syn.var 0)) (iterZero a (Syn.var 0))
  rwa [Tm.rep_self] at h

theorem eqSymm {p q : Tm n} (h : P Γ (.eq p q)) : P Γ (.eq q p) := by
  have k := tf (iterZero p zero) h
  rwa [Tm.rep_small p _ p (by simp only [Tm.sz]; omega)] at k

theorem eqTrans {p q r : Tm n} (h₁ : P Γ (.eq p q)) (h₂ : P Γ (.eq q r)) : P Γ (.eq p r) := by
  have k := tf h₂ (eqSymm h₁)
  rwa [Tm.rep_self] at k

theorem trOne (h : Tm (n + 1)) {s t u : Tm n} (h₁ : P Γ (.eq s t))
    (h₂ : P Γ (.eq (Syn.subst (inst s) h) u)) : P Γ (.eq u (Syn.subst (inst t) h)) := by
  have congr : ∀ {x : Tm n}, P Γ (.eq (Tm.marker h s) x) →
      P Γ (.eq (Syn.subst (inst (Tm.marker h s)) h) (Syn.subst (inst x) h)) := fun e => by
    have k := tf e (eqRefl (Syn.subst (inst (Tm.marker h s)) h))
    rwa [Tm.rep_marker] at k
  have e₁ : P Γ (.eq (Tm.marker h s) s) := iterZero s _
  exact eqTrans (eqSymm h₂) (eqTrans (eqSymm (congr e₁)) (congr (eqTrans e₁ h₁)))

theorem trEq (a b : Tm (n + 1)) {s t : Tm n} (h₁ : P Γ (.eq s t))
    (h₂ : P Γ (.eq (Syn.subst (inst s) a) (Syn.subst (inst s) b))) :
    P Γ (.eq (Syn.subst (inst t) a) (Syn.subst (inst t) b)) :=
  trOne b h₁ (trOne a h₁ h₂)

end TFKernel

/-! ### The calculi -/

/-- `B`: the kernel with backward replacement in place of transport. -/
inductive BPrf : {n : ℕ} → List (NFm n) → NFm n → Prop
  | hyp {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (h : A ∈ Γ) : BPrf Γ A
  | iterZero {n : ℕ} {Γ : List (NFm n)} (a : Tm n) (h : Tm (n + 1)) :
      BPrf Γ (.eq (iter zero a h) a)
  | iterSucc {n : ℕ} {Γ : List (NFm n)} (c a : Tm n) (h : Tm (n + 1)) :
      BPrf Γ (.eq (iter (succ c) a h) (Syn.subst (inst (iter c a h)) h))
  | bRep {n : ℕ} {Γ : List (NFm n)} {s t u r : Tm n} (h₁ : BPrf Γ (.eq s t))
      (h₂ : BPrf Γ (.eq (Tm.rpl t s Syn.var u) r)) : BPrf Γ (.eq r u)
  | qE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 1)} (t : Tm n)
      (h₁ : BPrf Γ (.Q B)) (h₂ : BPrf Γ (B.subst (inst zero))) : BPrf Γ (B.subst (inst t))
  | dE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 2)} {A : NFm n}
      (h₁ : BPrf Γ (.D B)) (h₂ : BPrf (.Q B :: Γ.map NFm.shift) A.shift) : BPrf Γ A
  | dICase {n : ℕ} {Γ : List (NFm n)} (B : NFm (n + 2)) (t : Tm n)
      (h : BPrf (((B.subst (up (inst t))).subst (inst zero)).shift :: Γ.map NFm.shift)
        ((B.subst (up (inst t))).subst (repl (succ (var 0))))) :
      BPrf Γ (.D B)
  | qIInd {n : ℕ} {Γ : List (NFm n)} (s₁ s₂ : Tm (n + 1))
      (h : BPrf (NFm.eq s₁ s₂ :: Γ.map NFm.shift)
        ((NFm.eq s₁ s₂).subst (repl (succ (var 0))))) :
      BPrf Γ (.Q (.eq s₁ s₂))

/-- `B₇`: the single introduction with backward replacement. -/
inductive B7Prf : {n : ℕ} → List (NFm n) → NFm n → Prop
  | hyp {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (h : A ∈ Γ) : B7Prf Γ A
  | iterZero {n : ℕ} {Γ : List (NFm n)} (a : Tm n) (h : Tm (n + 1)) :
      B7Prf Γ (.eq (iter zero a h) a)
  | iterSucc {n : ℕ} {Γ : List (NFm n)} (c a : Tm n) (h : Tm (n + 1)) :
      B7Prf Γ (.eq (iter (succ c) a h) (Syn.subst (inst (iter c a h)) h))
  | bRep {n : ℕ} {Γ : List (NFm n)} {s t u r : Tm n} (h₁ : B7Prf Γ (.eq s t))
      (h₂ : B7Prf Γ (.eq (Tm.rpl t s Syn.var u) r)) : B7Prf Γ (.eq r u)
  | qE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 1)} (t : Tm n)
      (h₁ : B7Prf Γ (.Q B)) (h₂ : B7Prf Γ (B.subst (inst zero))) : B7Prf Γ (B.subst (inst t))
  | dE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 2)} {A : NFm n}
      (h₁ : B7Prf Γ (.D B)) (h₂ : B7Prf (.Q B :: Γ.map NFm.shift) A.shift) : B7Prf Γ A
  | dI {n : ℕ} {Γ : List (NFm n)} (B : NFm (n + 2)) (t : Tm n)
      (h : B7Prf ((B.subst (up (inst t))).subst (repl (NFm.start B t)) :: Γ.map NFm.shift)
        ((B.subst (up (inst t))).subst (repl (succ (var 0))))) :
      B7Prf Γ (.D B)

/-- `G₇`: the single introduction with template-free replacement. -/
inductive G7Prf : {n : ℕ} → List (NFm n) → NFm n → Prop
  | hyp {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (h : A ∈ Γ) : G7Prf Γ A
  | iterZero {n : ℕ} {Γ : List (NFm n)} (a : Tm n) (h : Tm (n + 1)) :
      G7Prf Γ (.eq (iter zero a h) a)
  | iterSucc {n : ℕ} {Γ : List (NFm n)} (c a : Tm n) (h : Tm (n + 1)) :
      G7Prf Γ (.eq (iter (succ c) a h) (Syn.subst (inst (iter c a h)) h))
  | tf {n : ℕ} {Γ : List (NFm n)} {s t u v : Tm n}
      (h₁ : G7Prf Γ (.eq s t)) (h₂ : G7Prf Γ (.eq u v)) : G7Prf Γ (.eq v (Tm.rep s t u))
  | qE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 1)} (t : Tm n)
      (h₁ : G7Prf Γ (.Q B)) (h₂ : G7Prf Γ (B.subst (inst zero))) : G7Prf Γ (B.subst (inst t))
  | dE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 2)} {A : NFm n}
      (h₁ : G7Prf Γ (.D B)) (h₂ : G7Prf (.Q B :: Γ.map NFm.shift) A.shift) : G7Prf Γ A
  | dI {n : ℕ} {Γ : List (NFm n)} (B : NFm (n + 2)) (t : Tm n)
      (h : G7Prf ((B.subst (up (inst t))).subst (repl (NFm.start B t)) :: Γ.map NFm.shift)
        ((B.subst (up (inst t))).subst (repl (succ (var 0))))) :
      G7Prf Γ (.D B)

instance : BRKernel @BPrf := ⟨fun a h => .iterZero a h, fun h₁ h₂ => .bRep h₁ h₂⟩
instance : BRKernel @B7Prf := ⟨fun a h => .iterZero a h, fun h₁ h₂ => .bRep h₁ h₂⟩
instance : BRKernel @APrf := ⟨fun a h => .iterZero a h, fun h₁ h₂ => .bRep h₁ h₂⟩
instance : TFKernel @G7Prf := ⟨fun a h => .iterZero a h, fun h₁ h₂ => .tf h₁ h₂⟩

instance : WKernel @B7Prf :=
  ⟨fun h => .hyp h, fun a h => .iterZero a h, fun a b => BRKernel.trEq a b,
    fun t h₁ h₂ => .qE t h₁ h₂, fun h₁ h₂ => .dE h₁ h₂, fun B t h => .dI B t h⟩

instance : WKernel @G7Prf :=
  ⟨fun h => .hyp h, fun a h => .iterZero a h, fun a b => TFKernel.trEq a b,
    fun t h₁ h₂ => .qE t h₁ h₂, fun h₁ h₂ => .dE h₁ h₂, fun B t h => .dI B t h⟩

variable {Γ : List (NFm n)} {A : NFm n}

/-- Backward replacement is transport in the kernel. -/
theorem NPrf.bRep {s t u r : Tm n} (h₁ : NPrf Γ (.eq s t))
    (h₂ : NPrf Γ (.eq (Tm.rpl t s Syn.var u) r)) : NPrf Γ (.eq r u) := by
  rw [Tm.rpl_var_eq_rep] at h₂
  exact NPrf.eqSymm (NPrf.eqTrans (NPrf.repEq u (NPrf.eqSymm h₁)) h₂)

/-- **`B` and the kernel derive the same sequents.** -/
theorem bprf_iff_nprf : BPrf Γ A ↔ NPrf Γ A := by
  constructor
  · intro h
    induction h with
    | hyp h => exact .hyp h
    | iterZero a h => exact .iterZero a h
    | iterSucc c a h => exact .iterSucc c a h
    | bRep _ _ ih₁ ih₂ => exact NPrf.bRep ih₁ ih₂
    | qE t _ _ ih₁ ih₂ => exact .qE t ih₁ ih₂
    | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
    | dICase B t _ ih => exact .dICase B t ih
    | qIInd s t _ ih => exact .qIInd s t ih
  · intro h
    induction h with
    | hyp h => exact .hyp h
    | iterZero a h => exact .iterZero a h
    | iterSucc c a h => exact .iterSucc c a h
    | trOne h _ _ ih₁ ih₂ => exact BRKernel.trOne h ih₁ ih₂
    | qE t _ _ ih₁ ih₂ => exact .qE t ih₁ ih₂
    | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
    | dICase B t _ ih => exact .dICase B t ih
    | qIInd s t _ ih => exact .qIInd s t ih

/-- **`B₇` and the kernel derive the same sequents.** -/
theorem b7prf_iff_nprf : B7Prf Γ A ↔ NPrf Γ A := by
  constructor
  · intro h
    induction h with
    | hyp h => exact .hyp h
    | iterZero a h => exact .iterZero a h
    | iterSucc c a h => exact .iterSucc c a h
    | bRep _ _ ih₁ ih₂ => exact NPrf.bRep ih₁ ih₂
    | qE t _ _ ih₁ ih₂ => exact .qE t ih₁ ih₂
    | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
    | dI B t _ ih => exact .ofDI B t ih
  · intro h
    induction h with
    | hyp h => exact .hyp h
    | iterZero a h => exact .iterZero a h
    | iterSucc c a h => exact .iterSucc c a h
    | trOne h _ _ ih₁ ih₂ => exact BRKernel.trOne h ih₁ ih₂
    | qE t _ _ ih₁ ih₂ => exact .qE t ih₁ ih₂
    | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
    | dICase B t _ ih => exact WKernel.dICase B t ih
    | qIInd s t _ ih => exact WKernel.qInd s t ih

/-- **`G₇` and the kernel derive the same sequents.** -/
theorem g7prf_iff_nprf : G7Prf Γ A ↔ NPrf Γ A := by
  constructor
  · intro h
    induction h with
    | hyp h => exact .hyp h
    | iterZero a h => exact .iterZero a h
    | iterSucc c a h => exact .iterSucc c a h
    | tf _ _ ih₁ ih₂ => exact NPrf.eqTrans (NPrf.eqSymm ih₂) (NPrf.repEq _ ih₁)
    | qE t _ _ ih₁ ih₂ => exact .qE t ih₁ ih₂
    | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
    | dI B t _ ih => exact .ofDI B t ih
  · intro h
    induction h with
    | hyp h => exact .hyp h
    | iterZero a h => exact .iterZero a h
    | iterSucc c a h => exact .iterSucc c a h
    | trOne h _ _ ih₁ ih₂ => exact TFKernel.trOne h ih₁ ih₂
    | qE t _ _ ih₁ ih₂ => exact .qE t ih₁ ih₂
    | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
    | dICase B t _ ih => exact WKernel.dICase B t ih
    | qIInd s t _ ih => exact WKernel.qInd s t ih

end LeanProofs.ConciseIPRA
