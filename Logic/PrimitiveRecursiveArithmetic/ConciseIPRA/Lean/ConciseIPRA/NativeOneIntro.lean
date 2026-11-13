import ConciseIPRA.NativeInherited

/-!
# One introduction rule

The kernel `NPrf` has two introduction rules: `dICase` (`D` by cases, for any
matrix) and `qIInd` (`Q` by progress, for a literal equation).  `WPrf` has one,

  `dI`: from `Γ, B(t, η) ⊢ B(t, S z)` with `z` fresh infer `D_{x,y} B`,

where the start `η` is read off the syntax of the conclusion and the witness:
`η = z` when `B` is a literal equation and `t` is the literal `0` (the progress
step), and `η = 0` otherwise (the case step).  There is no choice between two
rules, and `WPrf` has seven rules in all.

`wprf_iff_nprf` proves that `WPrf` derives the same sequents as the kernel.
This is the idea of the package `Research/witness_rule` ("one introduction
rule in place of the case/progress choice"), which the packages
`Research/guarded_core` and `Research/scope_and_closure` pursue by other
means; here it is stated for the kernel with equational transport.

* `Q` by progress is `dI` at a dummy witness coordinate and the witness `0`,
  followed by `dE`.
* `D` by cases is `dI` itself, except for a literal equation at the witness
  `0`.  That instance is recovered at the witness `I(0, 0; u. 0)`, which is
  provably `0` and not literally `0`: first `Q_y E(0, y)` by `dI` with a dummy
  witness coordinate, then `dI` for `E` at `I(0, 0; u. 0)`, with one transport
  of the hypothesis and one of the conclusion (`dICaseEqZero`).

No structural rule of `WPrf` is used.  Substitution is not admissible in it by
a direct induction, since it can turn a witness into the literal `0`.

The argument uses six rules, collected in the class `WKernel`, and is carried
out for every derivability predicate that has them.  `WPrf` is one instance;
`NativeMinimal` uses another.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open Tm (zero succ iter)

variable {n m : ℕ}

namespace NFm

/-- The start of the introduction rule: the fresh variable for a literal
equation at the literal witness `0`, and `0` otherwise. -/
def start : NFm (n + 2) → Tm n → Tm (n + 1)
  | .eq _ _, .zero => Syn.var 0
  | _, _ => zero

theorem start_eq_zero (a b : Tm (n + 2)) : start (.eq a b) (zero : Tm n) = Syn.var 0 := rfl

theorem start_of_not {B : NFm (n + 2)} {t : Tm n}
    (h : ¬((∃ a b, B = NFm.eq a b) ∧ t = zero)) : start B t = zero := by
  cases B with
  | eq a b => cases t <;> first | rfl | exact absurd ⟨⟨a, b, rfl⟩, rfl⟩ h
  | Q B => cases t <;> rfl
  | D B => cases t <;> rfl

theorem start_iter (B : NFm (n + 2)) (c a : Tm n) (h : Tm (n + 1)) :
    start B (iter c a h) = zero :=
  start_of_not fun h' => by cases h'.2

theorem subst_repl_var (A : NFm (n + 1)) : A.subst (repl (Syn.var 0)) = A :=
  A.subst_eq_self fun i => by refine Fin.cases ?_ (fun j => ?_) i <;> simp

/-- The substitution `y ↦ u`, `x ↦ s`, and two new variables below the rest. -/
def rho (s u : Tm (n + 2)) : Fin (n + 2) → Tm (n + 2) :=
  Fin.cases u (Fin.cases s (fun i => Syn.var i.succ.succ))

/-- The template of `rho` in its `x` coordinate. -/
def tau (u : Tm (n + 2)) : Fin (n + 2) → Tm (n + 3) :=
  Fin.cases (Syn.shift u) (Fin.cases (Syn.var 0) (fun i => Syn.var i.succ.succ.succ))

/-- An instance of a twice weakened matrix at the witness `c` and the value `u`. -/
theorem subst_weak_inst (A : NFm (n + 2)) (c : Tm (n + 1)) (u : Tm (n + 2)) :
    ((A.subst (up (up (fun i => Syn.var i.succ)))).subst (up (inst c))).subst (repl u)
      = A.subst (rho (Syn.shift c) u) := by
  rw [subst_subst, subst_subst]
  refine A.subst_ext (Fin.cases ?_ fun j => ?_)
  · simp [rho]
  · refine Fin.cases ?_ (fun l => ?_) j <;> simp [rho]

theorem subst_tau_inst (A : NFm (n + 2)) (s u : Tm (n + 2)) :
    (A.subst (tau u)).subst (inst s) = A.subst (rho s u) := by
  rw [subst_subst]
  refine A.subst_ext (Fin.cases ?_ fun j => ?_)
  · simp [rho, tau]
  · refine Fin.cases ?_ (fun l => ?_) j <;> simp [rho, tau]

/-- An instance of the closure `Q_y A(0, y)` under the two new variables. -/
theorem subst_closure_inst (A : NFm (n + 2)) (u : Tm (n + 2)) :
    (((A.subst (up (inst zero))).subst (up (fun i => Syn.var i.succ))).subst
      (up (fun i => Syn.var i.succ))).subst (inst u)
      = A.subst (rho zero u) := by
  rw [subst_subst, subst_subst, subst_subst]
  refine A.subst_ext (Fin.cases ?_ fun j => ?_)
  · simp [rho]
  · refine Fin.cases ?_ (fun l => ?_) j <;> simp [rho]

end NFm

/-- The rules that the single introduction uses: hypothesis, the first
computation equation, transport, `QE`, `DE` and the introduction `dI`. -/
class WKernel (P : ∀ {n : ℕ}, List (NFm n) → NFm n → Prop) : Prop where
  hyp : ∀ {n : ℕ} {Γ : List (NFm n)} {A : NFm n}, A ∈ Γ → P Γ A
  iterZero : ∀ {n : ℕ} {Γ : List (NFm n)} (a : Tm n) (h : Tm (n + 1)),
    P Γ (.eq (iter zero a h) a)
  trEq : ∀ {n : ℕ} {Γ : List (NFm n)} (a b : Tm (n + 1)) {s t : Tm n}, P Γ (.eq s t) →
    P Γ (.eq (Syn.subst (inst s) a) (Syn.subst (inst s) b)) →
    P Γ (.eq (Syn.subst (inst t) a) (Syn.subst (inst t) b))
  qE : ∀ {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 1)} (t : Tm n), P Γ (.Q B) →
    P Γ (B.subst (inst zero)) → P Γ (B.subst (inst t))
  dE : ∀ {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 2)} {A : NFm n}, P Γ (.D B) →
    P (.Q B :: Γ.map NFm.shift) A.shift → P Γ A
  dI : ∀ {n : ℕ} {Γ : List (NFm n)} (B : NFm (n + 2)) (t : Tm n),
    P ((B.subst (up (inst t))).subst (repl (NFm.start B t)) :: Γ.map NFm.shift)
      ((B.subst (up (inst t))).subst (repl (succ (Syn.var 0)))) → P Γ (.D B)

namespace WKernel

variable {P : ∀ {n : ℕ}, List (NFm n) → NFm n → Prop} [WKernel @P] {Γ : List (NFm n)}

theorem trE {a b : Tm (n + 1)} (H : NFm (n + 1)) (hH : H = .eq a b) {s t : Tm n}
    {A A' : NFm n} (h₁ : P Γ (.eq s t)) (hA : H.subst (inst s) = A)
    (hA' : H.subst (inst t) = A') (h₂ : P Γ A) : P Γ A' := by
  subst hH hA hA'
  exact trEq a b h₁ h₂

theorem eqRefl (t : Tm n) : P Γ (.eq t t) :=
  trE (.eq (Syn.var 0) (Syn.shift t)) rfl (iterZero t (Syn.var 0)) (by simp) (by simp)
    (iterZero t (Syn.var 0))

theorem eqSymm {s t : Tm n} (h : P Γ (.eq s t)) : P Γ (.eq t s) :=
  trE (.eq (Syn.var 0) (Syn.shift s)) rfl h (by simp) (by simp) (eqRefl s)

/-- `Q` by progress: the introduction at a dummy witness coordinate and the
witness `0`, followed by `dE`. -/
theorem qInd (s t : Tm (n + 1))
    (h : P (NFm.eq s t :: Γ.map NFm.shift) ((NFm.eq s t).subst (repl (succ (Syn.var 0))))) :
    P Γ (.Q (.eq s t)) := by
  have hD : P Γ (.D ((NFm.eq s t).subst (up (fun i => Syn.var i.succ)))) := by
    refine dI _ zero ?_
    rw [show (NFm.eq s t).subst (up (fun i => Syn.var i.succ))
        = .eq (Syn.subst (up (fun i => Syn.var i.succ)) s)
          (Syn.subst (up (fun i => Syn.var i.succ)) t) from rfl,
      NFm.start_eq_zero, NFm.subst_repl_var,
      show (NFm.eq (Syn.subst (up (fun i => Syn.var i.succ)) s)
        (Syn.subst (up (fun i => Syn.var i.succ)) t)).subst (up (inst zero)) = .eq s t from
      NFm.subst_dummy_inst (.eq s t) zero]
    exact h
  exact dE hD (hyp List.mem_cons_self)

/-- `Q` by cases, at a dummy witness coordinate. -/
theorem dDummy (B : NFm (n + 1))
    (h : P ((B.subst (inst zero)).shift :: Γ.map NFm.shift)
      (B.subst (repl (succ (Syn.var 0))))) :
    P Γ (.D (B.subst (up (fun i => Syn.var i.succ)))) := by
  refine dI _ (iter zero zero zero) ?_
  rw [NFm.start_iter, NFm.subst_dummy_inst, ← NFm.shift_subst_inst_zero]
  exact h

/-- **`D` by cases for a literal equation at the literal witness `0`.** -/
theorem dICaseEqZero (a b : Tm (n + 2))
    (h : P ((((NFm.eq a b).subst (up (inst zero))).subst (inst zero)).shift
        :: Γ.map NFm.shift)
      (((NFm.eq a b).subst (up (inst zero))).subst (repl (succ (Syn.var 0))))) :
    P Γ (.D (.eq a b)) := by
  -- `Q_y E(0, y)` as a hypothesis, under a new variable
  refine dE (dDummy _ h) ?_
  show P _ (NFm.D ((NFm.eq a b).subst (up (up (fun i => Syn.var i.succ)))))
  -- the introduction at the witness `I(0, 0; u. 0)`
  refine dI _ (iter zero zero zero) ?_
  rw [NFm.start_iter, NFm.subst_weak_inst, NFm.subst_weak_inst]
  have hc : Syn.shift (iter zero zero zero : Tm (n + 1)) = iter zero zero zero := by simp
  rw [hc]
  -- from `E(c, 0)` to `E(0, 0)`
  have h1 : P ((NFm.eq a b).subst (NFm.rho (iter zero zero zero) zero)
        :: (NFm.Q (((NFm.eq a b).subst (up (inst zero))).subst (up (fun i => Syn.var i.succ)))
          :: Γ.map NFm.shift).map NFm.shift)
      ((NFm.eq a b).subst (NFm.rho zero zero)) :=
    trE ((NFm.eq a b).subst (NFm.tau zero)) rfl (iterZero zero zero)
      (NFm.subst_tau_inst _ _ _) (NFm.subst_tau_inst _ _ _) (hyp List.mem_cons_self)
  -- the closure gives `E(0, S z)`
  have hq : P ((NFm.eq a b).subst (NFm.rho (iter zero zero zero) zero)
        :: (NFm.Q (((NFm.eq a b).subst (up (inst zero))).subst (up (fun i => Syn.var i.succ)))
          :: Γ.map NFm.shift).map NFm.shift)
      (.Q ((((NFm.eq a b).subst (up (inst zero))).subst (up (fun i => Syn.var i.succ))).subst
        (up (fun i => Syn.var i.succ)))) :=
    hyp (List.mem_cons_of_mem _ List.mem_cons_self)
  rw [← NFm.subst_closure_inst] at h1
  have h2 := qE (succ (Syn.var 0)) hq h1
  rw [NFm.subst_closure_inst] at h2
  -- from `E(0, S z)` to `E(c, S z)`
  exact trE ((NFm.eq a b).subst (NFm.tau (succ (Syn.var 0)))) rfl
    (eqSymm (iterZero zero zero)) (NFm.subst_tau_inst _ _ _) (NFm.subst_tau_inst _ _ _) h2

/-- **`D` by cases**, for every matrix and witness. -/
theorem dICase (B : NFm (n + 2)) (t : Tm n)
    (h : P (((B.subst (up (inst t))).subst (inst zero)).shift :: Γ.map NFm.shift)
      ((B.subst (up (inst t))).subst (repl (succ (Syn.var 0))))) : P Γ (.D B) := by
  by_cases hc : (∃ a b, B = NFm.eq a b) ∧ t = zero
  · obtain ⟨⟨a, b, rfl⟩, rfl⟩ := hc
    exact dICaseEqZero a b h
  · refine dI B t ?_
    rw [NFm.start_of_not hc, ← NFm.shift_subst_inst_zero]
    exact h

end WKernel

/-- Derivability with a single introduction rule. -/
inductive WPrf : {n : ℕ} → List (NFm n) → NFm n → Prop
  | hyp {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (h : A ∈ Γ) : WPrf Γ A
  | iterZero {n : ℕ} {Γ : List (NFm n)} (a : Tm n) (h : Tm (n + 1)) :
      WPrf Γ (.eq (iter zero a h) a)
  | iterSucc {n : ℕ} {Γ : List (NFm n)} (c a : Tm n) (h : Tm (n + 1)) :
      WPrf Γ (.eq (iter (succ c) a h) (Syn.subst (inst (iter c a h)) h))
  | trOne {n : ℕ} {Γ : List (NFm n)} (h : Tm (n + 1)) {s t u : Tm n}
      (h₁ : WPrf Γ (.eq s t)) (h₂ : WPrf Γ (.eq (Syn.subst (inst s) h) u)) :
      WPrf Γ (.eq u (Syn.subst (inst t) h))
  | qE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 1)} (t : Tm n)
      (h₁ : WPrf Γ (.Q B)) (h₂ : WPrf Γ (B.subst (inst zero))) : WPrf Γ (B.subst (inst t))
  | dE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 2)} {A : NFm n}
      (h₁ : WPrf Γ (.D B)) (h₂ : WPrf (.Q B :: Γ.map NFm.shift) A.shift) : WPrf Γ A
  /-- DI: from `B(t, η) ⊢ B(t, S z)` with `z` fresh infer `D_{x,y} B`, where
  `η = z` for a literal equation at the literal witness `0` and `η = 0`
  otherwise. -/
  | dI {n : ℕ} {Γ : List (NFm n)} (B : NFm (n + 2)) (t : Tm n)
      (h : WPrf ((B.subst (up (inst t))).subst (repl (NFm.start B t)) :: Γ.map NFm.shift)
        ((B.subst (up (inst t))).subst (repl (succ (var 0))))) :
      WPrf Γ (.D B)

instance : WKernel @WPrf :=
  ⟨fun h => .hyp h, fun a h => .iterZero a h,
    fun a b => fun h₁ h₂ => .trOne b h₁ (.trOne a h₁ h₂),
    fun t h₁ h₂ => .qE t h₁ h₂, fun h₁ h₂ => .dE h₁ h₂, fun B t h => .dI B t h⟩

variable {Γ : List (NFm n)} {A : NFm n}

/-- An instance of the single introduction rule is an instance of one of the
two introductions of the reports' calculus, both derived in the kernel. -/
theorem NPrf.ofDI (B : NFm (n + 2)) (t : Tm n)
    (h : NPrf ((B.subst (up (inst t))).subst (repl (NFm.start B t)) :: Γ.map NFm.shift)
      ((B.subst (up (inst t))).subst (repl (succ (Syn.var 0))))) : NPrf Γ (.D B) := by
  by_cases hc : (∃ a b, B = NFm.eq a b) ∧ t = zero
  · obtain ⟨⟨a, b, rfl⟩, rfl⟩ := hc
    rw [NFm.start_eq_zero, NFm.subst_repl_var] at h
    exact .dIProg a b zero h
  · rw [NFm.start_of_not hc, ← NFm.shift_subst_inst_zero] at h
    exact .dICase B t h

theorem WPrf.toNPrf (h : WPrf Γ A) : NPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | trOne h _ _ ih₁ ih₂ => exact .trOne h ih₁ ih₂
  | qE t _ _ ih₁ ih₂ => exact .qE t ih₁ ih₂
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dI B t _ ih => exact .ofDI B t ih

/-- Both introduction rules of the kernel are derived rules of `WPrf`. -/
theorem NPrf.toWPrf (h : NPrf Γ A) : WPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | trOne h _ _ ih₁ ih₂ => exact .trOne h ih₁ ih₂
  | qE t _ _ ih₁ ih₂ => exact .qE t ih₁ ih₂
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dICase B t _ ih => exact WKernel.dICase B t ih
  | qIInd s t _ ih => exact WKernel.qInd s t ih

/-- **One introduction rule suffices**: `WPrf` and the kernel derive the same
sequents. -/
theorem wprf_iff_nprf : WPrf Γ A ↔ NPrf Γ A := ⟨WPrf.toNPrf, NPrf.toWPrf⟩

end LeanProofs.ConciseIPRA
