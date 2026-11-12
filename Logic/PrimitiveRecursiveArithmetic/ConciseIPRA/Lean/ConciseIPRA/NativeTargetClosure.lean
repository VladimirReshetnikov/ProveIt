import ConciseIPRA.NativeProgressiveEmbedding

/-!
# The target-directed closure

`TQPrf` is the calculus of the package `Research/target_closure`.  It has the
rules of the uniform calculus `RPrf` of `NativeProgressive` except for the
elimination of `Q`, which supplies one target term and no orbit term:

  `QE`: from `Q_y B` and `B(δ_B(t))` infer `B(t)`,

where `δ_B(t) = r` when `B` is a literal equation and `t` is literally `S r`,
and `δ_B(t) = 0` otherwise.  At an equation a successor target asks for the
predecessor instance, which is one step of progress, and every other target
asks for the instance at zero.

`tqprf_iff_rprf` proves that `TQPrf` and `RPrf` derive the same sequents, on
the same formulas.  Only the elimination of `Q` is translated.

* From `TQPrf` to `RPrf`: a step is the orbit elimination with the
  initializer `1` and `I(z, 1; v.S v) = S z`; a target that is not a successor
  is the orbit elimination from `0`, with the redex removed by the Leibniz
  rule of `RPrf`.
* From `RPrf` to `TQPrf`: at a compound matrix the orbit term is itself a
  target.  At an equation, `E(a)` gives `E(I(a, c; v.S v))` by an equation
  induction on `c` inside `TQPrf` (`TQPrf.orbit`), with `0 + a = a` and
  `S x + y = S (x + y)` proved by the same induction.

Equation induction in `TQPrf` (`TQPrf.eqInd`) uses the target `I(0, t; u.0)`,
which is not a successor and equals `t` by the first computation equation.

Derivations of `TQPrf` are stable under renaming but not under substitution,
since a substitution can turn a target into a successor.

With `rprf_emb_iff` this gives `tqprf_emb_iff`: the kernel derives a sequent
exactly when `TQPrf` derives its padded translation.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm
open Tm (zero succ iter)

variable {n m k : ℕ}

/-- The literal predecessor of a term: `r` for `S r`, and `0` otherwise. -/
def Tm.lpred : {n : ℕ} → Tm n → Tm n
  | _, .succ r => r
  | _, _ => zero

theorem Tm.up_rn_var (ξ : Fin n → Fin m) :
    up (fun i => (Syn.var (ξ i) : Tm m)) = fun i => Syn.var (Tm.upRen ξ i) := by
  refine funext (Fin.cases ?_ fun j => ?_) <;> simp

theorem Tm.lpred_rn (t : Tm n) (ξ : Fin n → Fin m) :
    (Syn.subst (fun i => (Syn.var (ξ i) : Tm m)) t).lpred
      = Syn.subst (fun i => (Syn.var (ξ i) : Tm m)) t.lpred := by
  cases t <;> rfl

namespace NFm

/-- The source of the target-directed elimination. -/
def delta {k : ℕ} (B : NFm k) (t : Tm n) : Tm n := if B.isEq then t.lpred else zero

theorem delta_rn {k k' : ℕ} (B : NFm k) (τ : Fin k → Tm k') (ξ : Fin n → Fin m) (t : Tm n) :
    Syn.subst (fun i => (Syn.var (ξ i) : Tm m)) (delta B t)
      = delta (B.subst τ) (Syn.subst (fun i => (Syn.var (ξ i) : Tm m)) t) := by
  unfold delta
  rw [isEq_subst]
  cases B.isEq
  · rfl
  · exact (Tm.lpred_rn t ξ).symm

theorem delta_of_ne {k : ℕ} {B : NFm k} (h : B.isEq = false) (t : Tm n) : delta B t = zero := by
  simp [delta, h]

theorem delta_succ {k : ℕ} {B : NFm k} (h : B.isEq = true) (r : Tm n) :
    delta B (succ r) = r := by
  simp [delta, h, Tm.lpred]

theorem delta_iter {k : ℕ} (B : NFm k) (c a : Tm n) (h : Tm (n + 1)) :
    delta B (Tm.iter c a h) = zero := by
  unfold delta
  cases B.isEq <;> rfl

end NFm

/-- Derivability with the target-directed elimination of `Q`. -/
inductive TQPrf : {n : ℕ} → List (NFm n) → NFm n → Prop
  | hyp {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (h : A ∈ Γ) : TQPrf Γ A
  | iterZero {n : ℕ} {Γ : List (NFm n)} (a : Tm n) (h : Tm (n + 1)) :
      TQPrf Γ (.eq (iter zero a h) a)
  | iterSucc {n : ℕ} {Γ : List (NFm n)} (c a : Tm n) (h : Tm (n + 1)) :
      TQPrf Γ (.eq (iter (succ c) a h) (Syn.subst (inst (iter c a h)) h))
  | trEq {n : ℕ} {Γ : List (NFm n)} (p q : Tm (n + 1)) {s t : Tm n} (h₁ : TQPrf Γ (.eq s t))
      (h₂ : TQPrf Γ (.eq (Syn.subst (inst s) p) (Syn.subst (inst s) q))) :
      TQPrf Γ (.eq (Syn.subst (inst t) p) (Syn.subst (inst t) q))
  /-- `QE`: from `Q_y B` and `B(δ_B(t))` infer `B(t)`. -/
  | qE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 1)} (t : Tm n) (h₁ : TQPrf Γ (.Q B))
      (h₂ : TQPrf Γ (B.subst (inst (NFm.delta B t)))) : TQPrf Γ (B.subst (inst t))
  | dE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 2)} {A : NFm n} (h₁ : TQPrf Γ (.D B))
      (h₂ : TQPrf (.Q B :: Γ.map NFm.shift) A.shift) : TQPrf Γ A
  | dI {n : ℕ} {Γ : List (NFm n)} (B : NFm (n + 2)) (t : Tm n)
      (h : TQPrf ((B.subst (up (inst t))).subst (repl (NFm.eta B (Syn.var 0)))
          :: Γ.map NFm.shift)
        ((B.subst (up (inst t))).subst (repl (succ (var 0))))) : TQPrf Γ (.D B)

namespace TQPrf

variable {Γ Δ : List (NFm n)} {A : NFm n}

theorem hyp0 : TQPrf (A :: Γ) A := .hyp List.mem_cons_self

/-! ### Structural rules -/

theorem weaken (h : TQPrf Γ A) : ∀ {Δ : List (NFm n)}, Γ ⊆ Δ → TQPrf Δ A := by
  induction h with
  | hyp h => intro Δ s; exact .hyp (s h)
  | iterZero a h => intro Δ _; exact .iterZero a h
  | iterSucc c a h => intro Δ _; exact .iterSucc c a h
  | trEq p q _ _ ih₁ ih₂ => intro Δ s; exact .trEq p q (ih₁ s) (ih₂ s)
  | qE t _ _ ih₁ ih₂ => intro Δ s; exact .qE t (ih₁ s) (ih₂ s)
  | dE _ _ ih₁ ih₂ =>
    intro Δ s
    exact .dE (ih₁ s) (ih₂ (List.cons_subset_cons _ (List.map_subset _ s)))
  | dI B t _ ih =>
    intro Δ s
    exact .dI B t (ih (List.cons_subset_cons _ (List.map_subset _ s)))

theorem wk {B : NFm n} (h : TQPrf Γ A) : TQPrf (B :: Γ) A :=
  h.weaken (List.subset_cons_self _ _)

/-- Renaming of the free variables of a derivation.  A renaming keeps a target
a successor or not a successor; a substitution need not. -/
theorem ren (h : TQPrf Γ A) : ∀ {m : ℕ} (ξ : Fin n → Fin m),
    TQPrf (Γ.map fun B => B.subst fun i => (Syn.var (ξ i) : Tm m))
      (A.subst fun i => (Syn.var (ξ i) : Tm m)) := by
  induction h with intro m ξ
  | hyp h => exact .hyp (List.mem_map_of_mem h)
  | iterZero a h => exact .iterZero _ _
  | iterSucc c a h =>
    simp only [NFm.subst_eq, Tm.subst_iter, Tm.subst_succ, Syn.subst_subst_inst]
    exact .iterSucc _ _ _
  | trEq p q _ _ ih₁ ih₂ =>
    have h₂ := ih₂ ξ
    simp only [NFm.subst_eq, Syn.subst_subst_inst] at h₂ ⊢
    exact .trEq _ _ (ih₁ ξ) h₂
  | @qE _ Γ B t _ _ ih₁ ih₂ =>
    have h₂ := ih₂ ξ
    rw [NFm.subst_inst, NFm.delta_rn B (up fun i => (Syn.var (ξ i) : Tm m)) ξ t] at h₂
    rw [NFm.subst_inst]
    exact .qE _ (ih₁ ξ) h₂
  | dE _ _ ih₁ ih₂ =>
    have h := ih₂ (Tm.upRen ξ)
    rw [List.map_cons, ← Tm.up_rn_var, NFm.map_shift_subst, NFm.shift_subst_up] at h
    exact .dE (ih₁ ξ) h
  | @dI _ Γ B t _ ih =>
    have h := ih (Tm.upRen ξ)
    rw [List.map_cons, ← Tm.up_rn_var, NFm.map_shift_subst,
      NFm.subst_repl_up_comm _ (NFm.eta B (Syn.var 0)), NFm.subst_repl_succ, NFm.subst_up_inst,
      NFm.eta_subst B (up (up fun i => (Syn.var (ξ i) : Tm m)))
        (up fun i => (Syn.var (ξ i) : Tm m)) (Syn.var 0)] at h
    simp only [Syn.subst_var, Syn.up_zero] at h
    exact .dI _ _ h

theorem shift (h : TQPrf Γ A) : TQPrf (Γ.map NFm.shift) A.shift := h.ren Fin.succ

/-! ### Equality -/

theorem trE {a b : Tm (n + 1)} (H : NFm (n + 1)) (hH : H = .eq a b) {s t : Tm n}
    {A A' : NFm n} (h₁ : TQPrf Γ (.eq s t)) (hA : H.subst (inst s) = A)
    (hA' : H.subst (inst t) = A') (h₂ : TQPrf Γ A) : TQPrf Γ A' := by
  subst hH hA hA'
  exact .trEq a b h₁ h₂

theorem eqRefl (t : Tm n) : TQPrf Γ (.eq t t) :=
  trE (.eq (Syn.var 0) (Syn.shift t)) rfl (.iterZero t (Syn.var 0)) (by simp) (by simp)
    (.iterZero t (Syn.var 0))

theorem eqSymm {s t : Tm n} (h : TQPrf Γ (.eq s t)) : TQPrf Γ (.eq t s) :=
  trE (.eq (Syn.var 0) (Syn.shift s)) rfl h (by simp) (by simp) (eqRefl s)

theorem eqTrans {s t u : Tm n} (h₁ : TQPrf Γ (.eq s t)) (h₂ : TQPrf Γ (.eq t u)) :
    TQPrf Γ (.eq s u) :=
  trE (.eq (Syn.shift s) (Syn.var 0)) rfl h₂ (by simp) (by simp) h₁

theorem eqCongr (h : Tm (n + 1)) {s t : Tm n} (e : TQPrf Γ (.eq s t)) :
    TQPrf Γ (.eq (Syn.subst (inst s) h) (Syn.subst (inst t) h)) :=
  trE (A := .eq (Syn.subst (inst s) h) (Syn.subst (inst s) h))
    (.eq (Syn.shift (Syn.subst (inst s) h)) h) rfl e (by simp) (by simp) (eqRefl _)

/-- Transport in a template that is a literal equation. -/
theorem trF (H : NFm (n + 1)) (hH : H.isEq = true) {s t : Tm n} (h₁ : TQPrf Γ (.eq s t))
    (h₂ : TQPrf Γ (H.subst (inst s))) : TQPrf Γ (H.subst (inst t)) := by
  cases H with
  | eq a b => exact .trEq a b h₁ h₂
  | Q B => cases hH
  | D B => cases hH

/-! ### The two closure interfaces and induction -/

/-- Introduction of `Q` at a literal equation, by progress. -/
theorem qIE (B : NFm (n + 1)) (hB : B.isEq = true)
    (h : TQPrf (B :: Γ.map NFm.shift) (B.subst (repl (succ (Syn.var 0))))) : TQPrf Γ (.Q B) := by
  have hD : TQPrf Γ (.D (B.subst (up fun i => Syn.var i.succ))) := by
    refine .dI _ zero ?_
    rw [NFm.subst_dummy_inst,
      NFm.eta_of_eq (B := B.subst (up fun i => Syn.var i.succ))
        (by rw [NFm.isEq_subst]; exact hB), NFm.subst_repl_var]
    exact h
  refine .dE hD ?_
  show TQPrf (.Q (B.subst (up fun i => Syn.var i.succ)) :: Γ.map NFm.shift)
    (.Q (B.subst (up fun i => Syn.var i.succ)))
  exact hyp0

/-- One step of progress: the elimination at a successor target. -/
theorem oneStep {B : NFm (n + 1)} (hB : B.isEq = true) (t : Tm n) (h₁ : TQPrf Γ (.Q B))
    (h₂ : TQPrf Γ (B.subst (inst t))) : TQPrf Γ (B.subst (inst (succ t))) :=
  .qE (succ t) h₁ (by rw [NFm.delta_succ hB]; exact h₂)

/-- Closure at an arbitrary target, from the instance at zero: the target
`I(0, t; u.0)` is not a successor, and it is `t` by the first computation
equation. -/
theorem anyTarget {B : NFm (n + 1)} (hB : B.isEq = true) (t : Tm n) (h₁ : TQPrf Γ (.Q B))
    (h₂ : TQPrf Γ (B.subst (inst zero))) : TQPrf Γ (B.subst (inst t)) :=
  trF B hB (.iterZero t zero)
    (.qE (Tm.iter zero t zero) h₁ (by rw [NFm.delta_iter]; exact h₂))

/-- **Equation induction with the target-directed elimination.** -/
theorem eqInd (s t : Tm (n + 1)) (u : Tm n) (h0 : TQPrf Γ ((NFm.eq s t).subst (inst zero)))
    (hS : TQPrf (NFm.eq s t :: Γ.map NFm.shift)
      ((NFm.eq s t).subst (repl (succ (Syn.var 0))))) :
    TQPrf Γ ((NFm.eq s t).subst (inst u)) :=
  anyTarget rfl u (qIE _ rfl hS) h0

/-- `0 + y = y`. -/
theorem zeroAdd (y : Tm n) : TQPrf Γ (.eq (Tm.add zero y) y) :=
  eqInd (Γ := Γ) (Tm.add zero (Syn.var 0)) (Syn.var 0) y
    (TQPrf.iterZero zero (succ (Syn.var 0)))
    (eqTrans (TQPrf.iterSucc (Syn.var 0) zero (succ (Syn.var 0)))
      (eqCongr (succ (Syn.var 0)) hyp0))

/-- `S x + y = S (x + y)`. -/
theorem succAdd (x y : Tm n) : TQPrf Γ (.eq (Tm.add (succ x) y) (succ (Tm.add x y))) := by
  have k := eqInd (Γ := Γ) (Tm.add (succ (Syn.shift x)) (Syn.var 0))
    (succ (Tm.add (Syn.shift x) (Syn.var 0))) y
    (by
      simp only [NFm.subst_eq, Tm.subst_add, Tm.subst_succ, Syn.subst_var, Syn.inst_zero,
        Syn.subst_inst_shift]
      exact eqTrans (TQPrf.iterZero (succ x) (succ (Syn.var 0)))
        (eqSymm (eqCongr (succ (Syn.var 0)) (TQPrf.iterZero x (succ (Syn.var 0))))))
    (by
      simp only [NFm.subst_eq, Tm.subst_add, Tm.subst_succ, Syn.subst_var, Syn.repl_zero,
        Syn.subst_repl_shift]
      exact eqTrans (TQPrf.iterSucc (Syn.var 0) (succ (Syn.shift x)) (succ (Syn.var 0)))
        (eqTrans (eqCongr (succ (Syn.var 0)) hyp0)
          (eqSymm (eqCongr (succ (Syn.var 0))
            (TQPrf.iterSucc (Syn.var 0) (Syn.shift x) (succ (Syn.var 0)))))))
  simp only [NFm.subst_eq, Tm.subst_add, Tm.subst_succ, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift] at k
  exact k

/-- **The orbit elimination at an equation.**  From `Q_y E` and `E(a)` infer
`E(I(a, c; v.S v))`, by an equation induction on `c`. -/
theorem orbit (s t : Tm (n + 1)) (a c : Tm n) (h₁ : TQPrf Γ (.Q (.eq s t)))
    (h₂ : TQPrf Γ ((NFm.eq s t).subst (inst a))) :
    TQPrf Γ ((NFm.eq s t).subst (inst (Tm.add c a))) := by
  have ed : ∀ u : Tm n,
      Syn.subst (inst u) (Tm.add (Syn.var 0) (Syn.shift a)) = Tm.add u a := fun u => by simp
  have ed' : Syn.subst (repl (succ (Syn.var 0))) (Tm.add (Syn.var 0) (Syn.shift a))
      = Tm.add (succ (Syn.var 0)) (Syn.shift a) := by simp [Syn.subst_repl_shift]
  rw [← ed c, ← NFm.subst_repl_inst]
  show TQPrf Γ ((NFm.eq (Syn.subst (repl (Tm.add (Syn.var 0) (Syn.shift a))) s)
    (Syn.subst (repl (Tm.add (Syn.var 0) (Syn.shift a))) t)).subst (inst c))
  refine eqInd _ _ c ?_ ?_
  · show TQPrf Γ (((NFm.eq s t).subst (repl (Tm.add (Syn.var 0) (Syn.shift a)))).subst
      (inst zero))
    rw [NFm.subst_repl_inst, ed]
    exact trF (NFm.eq s t) rfl (eqSymm (zeroAdd a)) h₂
  · show TQPrf ((NFm.eq s t).subst (repl (Tm.add (Syn.var 0) (Syn.shift a)))
        :: Γ.map NFm.shift)
      (((NFm.eq s t).subst (repl (Tm.add (Syn.var 0) (Syn.shift a)))).subst
        (repl (succ (Syn.var 0))))
    have hQ : TQPrf ((NFm.eq s t).subst (repl (Tm.add (Syn.var 0) (Syn.shift a)))
          :: Γ.map NFm.shift)
        (.Q ((NFm.eq s t).subst (up fun i => Syn.var i.succ))) := h₁.shift.wk
    have hs := oneStep (B := (NFm.eq s t).subst (up fun i => Syn.var i.succ)) rfl
      (Tm.add (Syn.var 0) (Syn.shift a)) hQ (by rw [NFm.subst_dummy_up_inst]; exact hyp0)
    rw [NFm.subst_repl_repl, ed']
    have k := trF ((NFm.eq s t).subst (up fun i => Syn.var i.succ)) rfl
      (eqSymm (succAdd (Syn.var 0) (Syn.shift a))) hs
    rw [NFm.subst_dummy_up_inst] at k
    exact k

/-! ### The two translations -/

/-- Every derivation with the target-directed elimination is a derivation of
the uniform calculus. -/
theorem toR (h : TQPrf Γ A) : RPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | trEq p q _ _ ih₁ ih₂ => exact .trEq p q ih₁ ih₂
  | @qE _ Γ B t _ _ ih₁ ih₂ =>
    cases hB : B.isEq
    · rw [NFm.delta_of_ne hB] at ih₂
      have q := RPrf.qE zero t ih₁ (by rw [NFm.eta_of_ne hB]; exact ih₂)
      rw [NFm.eta_of_ne hB] at q
      exact RPrf.tr B (RPrf.iterZero t (succ (Syn.var 0))) q
    · have key : ∀ u : Tm _, RPrf Γ (B.subst (inst zero)) → RPrf Γ (B.subst (inst u)) := by
        intro u h0
        have q := RPrf.qE zero u ih₁ (by rw [NFm.eta_of_eq hB]; exact h0)
        rw [NFm.eta_of_eq hB] at q
        exact RPrf.trF B hB (RPrf.iterZero u (succ (Syn.var 0))) q
      rw [NFm.delta, hB] at ih₂
      cases t with
      | succ r =>
        have q := RPrf.qE r (succ zero) ih₁ (by rw [NFm.eta_of_eq hB]; exact ih₂)
        rw [NFm.eta_of_eq hB] at q
        exact RPrf.trF B hB (RPrf.addOne r) q
      | _ => exact key _ ih₂
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dI B t _ ih => exact .dI B t ih

end TQPrf

/-- Every derivation of the uniform calculus is a derivation with the
target-directed elimination. -/
theorem RPrf.toTQ {Γ : List (NFm n)} {A : NFm n} (h : RPrf Γ A) : TQPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | trEq p q _ _ ih₁ ih₂ => exact .trEq p q ih₁ ih₂
  | @qE _ Γ B a c _ _ ih₁ ih₂ =>
    cases B with
    | eq s t => exact TQPrf.orbit s t a c ih₁ ih₂
    | Q B' => exact .qE _ ih₁ ih₂
    | D B' => exact .qE _ ih₁ ih₂
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dI B t _ ih => exact .dI B t ih

variable {Γ : List (NFm n)} {A : NFm n}

/-- **The target-directed and the orbit elimination.**  The two calculi derive
the same sequents. -/
theorem tqprf_iff_rprf : TQPrf Γ A ↔ RPrf Γ A := ⟨TQPrf.toR, RPrf.toTQ⟩

/-- The kernel derives a sequent exactly when the calculus with the
target-directed elimination derives its padded translation. -/
theorem tqprf_emb_iff : TQPrf (Γ.map NFm.emb) A.emb ↔ NPrf Γ A :=
  tqprf_iff_rprf.trans rprf_emb_iff

/-- Soundness for the progressive reading. -/
theorem TQPrf.toNPrf (h : TQPrf Γ A) : NPrf (Γ.map NFm.rd) A.rd := h.toR.toNPrf

/-- The calculus with the target-directed elimination is consistent. -/
theorem tqprf_consistent : ¬ TQPrf ([] : List (NFm 0)) NFm.bot := fun h =>
  rprf_consistent h.toR

end LeanProofs.ConciseIPRA
