import ConciseIPRA.NativeVariableSubstitution

/-!
# Six rules on full normal forms

`F6Prf` is the calculus of the packages `Research/full_normalization` and
`Research/computation_normal`: on full normal forms, with no computation rule,

  Hyp, Refl, Tr, QE, DE, and one introduction of `D`,

whose mode is read off the matrix and the witness: progress for a literal
equation at the literal witness `0`, cases otherwise (`NFm.start`).
`f6prf_iff_nprf` proves that the kernel derives a sequent exactly when `F6Prf`
derives its full normal form.

The two introductions of the kernel are recovered as follows.

* `QI` by progress for an equation `E` is the introduction of
  `D_{x,y} E(y)` at the literal `0`, in progress mode, followed by `DE`.
* `DI` by cases at a witness that is not the literal `0`, or for a matrix that
  is not an equation, is the introduction in case mode.
* `DI` by cases for an equation at a witness whose normal form is the literal
  `0` cannot be made at that witness, which selects progress, and on full
  normal forms no other term is provably `0`.  It is made in two steps.  With
  `T(x) = sel(x, 0, 0)`, whose instance at `1` has the normal form `0`, the
  formula `D_{x,y} B(T(x), y)` is introduced at the witness `1`, in case mode,
  from the given premise.  It is opened at a fresh `b`, and `D_{x,y} B` is
  introduced at the witness `T(b)`, which is neutral, from the opened closure
  by `QE`.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm
open Tm (zero succ iter)

variable {n m : ℕ}

/-- The kernel on full normal forms with one introduction rule. -/
inductive F6Prf : {n : ℕ} → List (NFm n) → NFm n → Prop
  | hyp {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (h : A ∈ Γ) : F6Prf Γ A
  | refl {n : ℕ} {Γ : List (NFm n)} (t : Tm n) : F6Prf Γ (.eq t.full t.full)
  | trOne {n : ℕ} {Γ : List (NFm n)} (h : Tm (n + 1)) {s t u : Tm n}
      (h₁ : F6Prf Γ (.eq s t)) (h₂ : F6Prf Γ (.eq (Syn.subst (inst s) h).full u)) :
      F6Prf Γ (.eq u (Syn.subst (inst t) h).full)
  | qE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 1)} (t : Tm n)
      (h₁ : F6Prf Γ (.Q B)) (h₂ : F6Prf Γ (B.subst (inst zero)).full) :
      F6Prf Γ (B.subst (inst t)).full
  | dE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 2)} {A : NFm n}
      (h₁ : F6Prf Γ (.D B)) (h₂ : F6Prf (.Q B :: Γ.map NFm.shift) A.shift) : F6Prf Γ A
  /-- The introduction: from `B(t, η) ⊢ B(t, S z)` infer `D_{x,y} B`, where `η`
  is the fresh `z` for a literal equation at the literal `0`, and `0`
  otherwise. -/
  | dI {n : ℕ} {Γ : List (NFm n)} (B : NFm (n + 2)) (t : Tm n) (hB : B.full = B)
      (ht : t.full = t)
      (h : F6Prf (((B.subst (up (inst t))).subst (repl (NFm.start B t))).full
          :: Γ.map NFm.shift)
        ((B.subst (up (inst t))).subst (repl (succ (var 0)))).full) :
      F6Prf Γ (.D B)

/-- The term `sel(x, 0, 0)`, whose instance at `1` has the normal form `0`. -/
def Tm.tz : Tm (n + 1) := Tm.sel (Syn.var 0) zero zero

theorem Tm.tz_one : (Syn.subst (inst (succ zero)) (Tm.tz : Tm (n + 1))).full = zero := by
  simp only [Tm.tz, Tm.subst_sel, Syn.subst_var, Syn.inst_zero, Tm.subst_zero]
  exact Tm.full_sel_succ' (c := succ zero) (x := zero) rfl

theorem Tm.tz_full_ne : (Tm.tz : Tm (n + 1)).full ≠ zero := fun e => by
  have e' : (Tm.iter (Tm.var 0) Tm.zero Tm.zero : Tm (n + 1)) = Tm.zero := e
  cases e'

namespace NFm

theorem subst_dummy_up_up_inst (B : NFm (n + 2)) (w : Tm (n + 1)) :
    (B.subst (up (up fun i => Syn.var i.succ))).subst (up (inst w)) = B.subst (up (repl w)) := by
  rw [subst_subst, Syn.up_comp]
  refine congrArg (fun r => B.subst (up r)) (funext (Fin.cases ?_ fun j => ?_)) <;> simp

/-- The instance of the shifted matrix at the witness `1` is the instance of
the matrix at a witness with the normal form `0`. -/
theorem full_tz_inst (B : NFm (n + 2)) {t : Tm n} (ht : t.full = zero) {k : ℕ}
    (ρ : Fin (n + 1) → Tm k) :
    (((B.subst (up (repl Tm.tz))).full.subst (up (inst (succ zero)))).subst ρ).full
      = ((B.subst (up (inst t))).subst ρ).full := by
  rw [full_subst_congr (A' := (B.subst (up (repl Tm.tz))).subst (up (inst (succ zero))))
    (σ' := ρ) (full_subst_congr (full_idem _) fun _ => rfl) (fun _ => rfl),
    subst_subst B (up (repl Tm.tz)) (up (inst (succ zero))), Syn.up_comp]
  refine full_subst_congr (full_subst_congr rfl (Tm.full_up_congr fun i => ?_)) fun _ => rfl
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [Syn.repl_zero, Syn.inst_zero, Tm.tz_one, ht]
  · simp

/-- The instance of the weakened matrix at the neutral witness, and the
instance of the opened closure, are one formula. -/
theorem full_tz_goal (B : NFm (n + 2)) {k : ℕ} (ρ : Fin (n + 2) → Tm k) :
    (((B.subst (up (up fun i => Syn.var i.succ))).subst (up (inst (Tm.tz : Tm (n + 1)).full))).subst
        ρ).full
      = ((B.subst (up (repl Tm.tz))).subst ρ).full := by
  rw [subst_dummy_up_up_inst]
  refine full_subst_congr (full_subst_congr rfl (Tm.full_up_congr fun i => ?_)) fun _ => rfl
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · rfl

end NFm

namespace F6Prf

variable {Γ : List (NFm n)} {A : NFm n}

/-- Every rule is a derived rule of the kernel, up to normal forms. -/
theorem toNPrf (h : F6Prf Γ A) : NPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | refl t => exact NPrf.eqRefl _
  | trOne h _ _ ih₁ ih₂ =>
    exact NPrf.eqTrans (.trOne h ih₁ (NPrf.eqTrans (NPrf.eqFull _) ih₂)) (NPrf.eqFull _)
  | qE t _ _ ih₁ ih₂ => exact (equivFull _).mp (.qE t ih₁ ((equivFull _).mpr ih₂))
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dI B t _ _ _ ih =>
    exact .ofDI B t ((equivFull _).mpr
      (NPrf.cut1 ((equivFull _).mp NPrf.hyp0) (NPrf.wkUnder ih)))

/-- `DI` by cases for an equation at a witness with the normal form `0`, in
two steps through the matrix `B(sel(x, 0, 0), y)`. -/
theorem dIZero (B : NFm (n + 2)) (hB : B.full = B) {t : Tm n} (ht : t.full = zero)
    (h : F6Prf (((B.subst (up (inst t))).subst (inst zero)).full.shift :: Γ.map NFm.shift)
      ((B.subst (up (inst t))).subst (repl (succ (Syn.var 0)))).full) : F6Prf Γ (.D B) := by
  have hD : F6Prf Γ (.D (B.subst (up (repl Tm.tz))).full) := by
    refine .dI _ (succ zero) (NFm.full_idem _) rfl ?_
    rw [NFm.start_of_not (fun k => by cases k.2), NFm.full_tz_inst B ht,
      NFm.full_tz_inst B ht, ← NFm.shift_subst_inst_zero, NFm.full_shift]
    exact h
  refine .dE hD ?_
  have hB'' : (B.subst (up (up fun i => Syn.var i.succ))).full
      = B.subst (up (up fun i => Syn.var i.succ)) := by
    rw [Tm.up_rn Fin.succ, Tm.up_rn, NFm.full_rn, hB]
  show F6Prf _ (.D (B.subst (up (up fun i => Syn.var i.succ))))
  refine .dI _ (Tm.tz : Tm (n + 1)).full hB'' (Tm.full_idem _) ?_
  rw [NFm.start_of_not (fun k => Tm.tz_full_ne k.2), NFm.full_tz_goal, NFm.full_tz_goal]
  have e : ∀ c : Tm (n + 2),
      (((B.subst (up (repl Tm.tz))).full.subst (up fun i => Syn.var i.succ)).subst (inst c)).full
        = ((B.subst (up (repl Tm.tz))).subst (repl c)).full := by
    intro c
    rw [NFm.subst_dummy_up_inst]
    exact NFm.full_subst_congr (NFm.full_idem _) fun _ => rfl
  have hQ : F6Prf (((B.subst (up (repl Tm.tz))).subst (repl zero)).full
        :: (NFm.Q (B.subst (up (repl Tm.tz))).full :: Γ.map NFm.shift).map NFm.shift)
      (.Q ((B.subst (up (repl Tm.tz))).full.subst (up fun i => Syn.var i.succ))) :=
    .hyp (List.mem_cons_of_mem _ (List.mem_map_of_mem List.mem_cons_self))
  have r := F6Prf.qE (succ (Syn.var 0)) hQ (by
    rw [e]
    exact .hyp List.mem_cons_self)
  rwa [e] at r

end F6Prf

variable {Γ : List (NFm n)} {A : NFm n}

/-- Every derivation of the kernel on full normal forms is a derivation with
the single introduction. -/
theorem FNPrf.toF6 (h : FNPrf Γ A) : F6Prf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | refl t => exact .refl t
  | trOne h _ _ ih₁ ih₂ => exact .trOne h ih₁ ih₂
  | qE t _ _ ih₁ ih₂ => exact .qE t ih₁ ih₂
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | @dICase _ Γ B t hB _ ih =>
    by_cases hc : (∃ a b, B = NFm.eq a b) ∧ t.full = zero
    · exact F6Prf.dIZero B hB hc.2 ih
    · refine .dI B t.full hB (Tm.full_idem t) ?_
      have e : ∀ {k : ℕ} (ρ : Fin (_ + 1) → Tm k),
          ((B.subst (up (inst t.full))).subst ρ).full = ((B.subst (up (inst t))).subst ρ).full :=
        fun ρ => NFm.full_subst_congr
          (NFm.full_subst_congr rfl (Tm.full_up_congr (Tm.full_inst t))) fun _ => rfl
      rw [NFm.start_of_not hc, e, e, ← NFm.shift_subst_inst_zero, NFm.full_shift]
      exact ih
  | @qIInd _ Γ s₁ s₂ h₁ h₂ _ ih =>
    have hD : F6Prf Γ (.D (.eq (Syn.subst (up fun i => Syn.var i.succ) s₁)
        (Syn.subst (up fun i => Syn.var i.succ) s₂))) := by
      refine .dI _ zero ?_ rfl ?_
      · show NFm.full ((NFm.eq s₁ s₂).subst (up fun i => Syn.var i.succ)) = _
        rw [Tm.up_rn Fin.succ, NFm.full_rn]
        simp only [NFm.full, h₁, h₂, NFm.subst_eq]
      · rw [NFm.start_eq_zero]
        have e : (NFm.eq (Syn.subst (up fun i => Syn.var i.succ) s₁)
              (Syn.subst (up fun i => Syn.var i.succ) s₂)).subst (up (inst zero))
            = NFm.eq s₁ s₂ := NFm.subst_dummy_inst (.eq s₁ s₂) zero
        rw [e, NFm.subst_repl_var]
        simp only [NFm.full, h₁, h₂]
        exact ih
    refine .dE hD ?_
    exact .hyp List.mem_cons_self

/-- **Six rules on full normal forms.**  The kernel derives a sequent exactly
when the calculus with Hyp, Refl, Tr, QE, DE and one introduction derives its
full normal form. -/
theorem f6prf_iff_nprf : F6Prf (Γ.map NFm.full) A.full ↔ NPrf Γ A := by
  constructor
  · intro h
    refine (equivFull A).mpr (h.toNPrf.cut fun B hB => ?_)
    obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hB
    exact (equivFull C).mp (.hyp hC)
  · intro h
    exact (fnprf_iff_nprf.2 h).toF6

end LeanProofs.ConciseIPRA
