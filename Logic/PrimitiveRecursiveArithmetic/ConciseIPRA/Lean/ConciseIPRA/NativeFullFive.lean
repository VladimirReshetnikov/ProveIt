import ConciseIPRA.NativeFullSix
import ConciseIPRA.NativeWitnessDischarge

/-!
# Five rules on full normal forms

Two reductions on full normal forms combine.  Name replaces transport and the
elimination of `D` (`NativeWitnessDischarge`), and one introduction whose mode
is read off the matrix and the witness replaces the two introductions
(`NativeFullSix`).  `N5Prf` has both:

  Hyp, Refl, Name, QE, and one introduction of `D`.

There is no computation rule, no transport, and no separate elimination of
`D`.  Contexts are lists of formulas, and `Q` stays in the language.
`n5prf_iff_nprf` proves that the kernel derives a sequent exactly when `N5Prf`
derives its full normal form.

The proof translates the six-rule calculus with Name, `NMPrf`: its two
introductions are recovered from the single one exactly as in
`NativeFullSix`, with the elimination of `D` given by Name at the fresh
variable itself.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm
open Tm (zero succ iter)

variable {n m : ℕ}

/-- Five rules on full normal forms. -/
inductive N5Prf : {n : ℕ} → List (NFm n) → NFm n → Prop
  | hyp {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (h : A ∈ Γ) : N5Prf Γ A
  | refl {n : ℕ} {Γ : List (NFm n)} (t : Tm n) : N5Prf Γ (.eq t.full t.full)
  /-- Name: from `D_{x,y} B`, and from `b = t` and `F` in the context opened at
  a fresh `b`, infer `F[t/b]`, which does not mention `b`. -/
  | name {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 2)} {A : NFm n} (F : NFm (n + 1))
      (t : Tm (n + 1)) (h₁ : N5Prf Γ (.D B))
      (h₂ : N5Prf (.Q B :: Γ.map NFm.shift) (.eq (Syn.var 0) t))
      (h₃ : N5Prf (.Q B :: Γ.map NFm.shift) F) (hA : (F.subst (repl t)).full = A.shift) :
      N5Prf Γ A
  | qE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 1)} (t : Tm n)
      (h₁ : N5Prf Γ (.Q B)) (h₂ : N5Prf Γ (B.subst (inst zero)).full) :
      N5Prf Γ (B.subst (inst t)).full
  /-- The introduction: from `B(t, η) ⊢ B(t, S z)` infer `D_{x,y} B`, where `η`
  is the fresh `z` for a literal equation at the literal `0`, and `0`
  otherwise. -/
  | dI {n : ℕ} {Γ : List (NFm n)} (B : NFm (n + 2)) (t : Tm n) (hB : B.full = B)
      (ht : t.full = t)
      (h : N5Prf (((B.subst (up (inst t))).subst (repl (NFm.start B t))).full
          :: Γ.map NFm.shift)
        ((B.subst (up (inst t))).subst (repl (succ (var 0)))).full) :
      N5Prf Γ (.D B)

namespace N5Prf

variable {Γ : List (NFm n)} {A : NFm n}

/-- Every rule is a derived rule of the kernel, up to normal forms. -/
theorem toNPrf (h : N5Prf Γ A) : NPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | refl t => exact NPrf.eqRefl _
  | @name _ Γ B A F t _ _ _ hA ih₁ ih₂ ih₃ =>
    refine .dE ih₁ ?_
    have tr := NPrf.tr (F.subst (Fin.cases (Syn.var 0) fun i => Syn.var i.succ.succ)) ih₂
      (by rw [NFm.subst_hole_inst, NFm.subst_repl_var]; exact ih₃)
    rw [NFm.subst_hole_inst] at tr
    rw [← hA]
    exact (equivFull _).mp tr
  | qE t _ _ ih₁ ih₂ => exact (equivFull _).mp (.qE t ih₁ ((equivFull _).mpr ih₂))
  | dI B t _ _ _ ih =>
    exact .ofDI B t ((equivFull _).mpr
      (NPrf.cut1 ((equivFull _).mp NPrf.hyp0) (NPrf.wkUnder ih)))

/-- `DE`, by Name at the fresh variable itself. -/
theorem dE {B : NFm (n + 2)} (h₁ : N5Prf Γ (.D B))
    (h₂ : N5Prf (.Q B :: Γ.map NFm.shift) A.shift) (hA : A.full = A) : N5Prf Γ A := by
  have r := N5Prf.refl (Γ := .Q B :: Γ.map NFm.shift) (Syn.var 0)
  rw [Tm.full_var] at r
  refine .name A.shift (Syn.var 0) h₁ r h₂ ?_
  rw [NFm.subst_repl_var, NFm.full_shift, hA]

/-- `DI` by cases for an equation at a witness with the normal form `0`. -/
theorem dIZero (B : NFm (n + 2)) (hB : B.full = B) {t : Tm n} (ht : t.full = zero)
    (h : N5Prf (((B.subst (up (inst t))).subst (inst zero)).full.shift :: Γ.map NFm.shift)
      ((B.subst (up (inst t))).subst (repl (succ (Syn.var 0)))).full) : N5Prf Γ (.D B) := by
  have hD : N5Prf Γ (.D (B.subst (up (repl Tm.tz))).full) := by
    refine .dI _ (succ zero) (NFm.full_idem _) rfl ?_
    rw [NFm.start_of_not (fun k => by cases k.2), NFm.full_tz_inst B ht,
      NFm.full_tz_inst B ht, ← NFm.shift_subst_inst_zero, NFm.full_shift]
    exact h
  refine dE hD ?_ (congrArg NFm.D hB)
  have hB'' : (B.subst (up (up fun i => Syn.var i.succ))).full
      = B.subst (up (up fun i => Syn.var i.succ)) := by
    rw [Tm.up_rn Fin.succ, Tm.up_rn, NFm.full_rn, hB]
  show N5Prf _ (.D (B.subst (up (up fun i => Syn.var i.succ))))
  refine .dI _ (Tm.tz : Tm (n + 1)).full hB'' (Tm.full_idem _) ?_
  rw [NFm.start_of_not (fun k => Tm.tz_full_ne k.2), NFm.full_tz_goal, NFm.full_tz_goal]
  have e : ∀ c : Tm (n + 2),
      (((B.subst (up (repl Tm.tz))).full.subst (up fun i => Syn.var i.succ)).subst (inst c)).full
        = ((B.subst (up (repl Tm.tz))).subst (repl c)).full := by
    intro c
    rw [NFm.subst_dummy_up_inst]
    exact NFm.full_subst_congr (NFm.full_idem _) fun _ => rfl
  have hQ : N5Prf (((B.subst (up (repl Tm.tz))).subst (repl zero)).full
        :: (NFm.Q (B.subst (up (repl Tm.tz))).full :: Γ.map NFm.shift).map NFm.shift)
      (.Q ((B.subst (up (repl Tm.tz))).full.subst (up fun i => Syn.var i.succ))) :=
    .hyp (List.mem_cons_of_mem _ (List.mem_map_of_mem List.mem_cons_self))
  have r := N5Prf.qE (succ (Syn.var 0)) hQ (by
    rw [e]
    exact .hyp List.mem_cons_self)
  rwa [e] at r

end N5Prf

variable {Γ : List (NFm n)} {A : NFm n}

/-- Every derivation of the six-rule calculus with Name is a derivation with
five rules. -/
theorem NMPrf.toN5 (h : NMPrf Γ A) : N5Prf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | refl t => exact .refl t
  | name F t _ _ _ hA ih₁ ih₂ ih₃ => exact .name F t ih₁ ih₂ ih₃ hA
  | qE t _ _ ih₁ ih₂ => exact .qE t ih₁ ih₂
  | @dICase _ Γ B t hB _ ih =>
    by_cases hc : (∃ a b, B = NFm.eq a b) ∧ t.full = zero
    · exact N5Prf.dIZero B hB hc.2 ih
    · refine .dI B t.full hB (Tm.full_idem t) ?_
      have e : ∀ {k : ℕ} (ρ : Fin (_ + 1) → Tm k),
          ((B.subst (up (inst t.full))).subst ρ).full = ((B.subst (up (inst t))).subst ρ).full :=
        fun ρ => NFm.full_subst_congr
          (NFm.full_subst_congr rfl (Tm.full_up_congr (Tm.full_inst t))) fun _ => rfl
      rw [NFm.start_of_not hc, e, e, ← NFm.shift_subst_inst_zero, NFm.full_shift]
      exact ih
  | @qIInd _ Γ s₁ s₂ h₁ h₂ _ ih =>
    have hD : N5Prf Γ (.D (.eq (Syn.subst (up fun i => Syn.var i.succ) s₁)
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
    refine N5Prf.dE hD ?_ (by simp only [NFm.full, h₁, h₂])
    exact .hyp List.mem_cons_self

/-- **Five rules.**  The kernel derives a sequent exactly when the calculus
with Hyp, Refl, Name, QE and one introduction derives its full normal form. -/
theorem n5prf_iff_nprf : N5Prf (Γ.map NFm.full) A.full ↔ NPrf Γ A := by
  constructor
  · intro h
    refine (equivFull A).mpr (h.toNPrf.cut fun B hB => ?_)
    obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hB
    exact (equivFull C).mp (.hyp hC)
  · intro h
    exact (nmprf_iff_nprf.2 h).toN5

/-- The five-rule calculus proves the full normal form of a sequent exactly
when iPRA proves its reading. -/
theorem n5prf_iff_pra :
    N5Prf (Γ.map NFm.full) A.full ↔ (Γ.map NFm.toPRA ⊢[PRAAx] A.toPRA) :=
  n5prf_iff_nprf.trans native_iff_pra

end LeanProofs.ConciseIPRA
