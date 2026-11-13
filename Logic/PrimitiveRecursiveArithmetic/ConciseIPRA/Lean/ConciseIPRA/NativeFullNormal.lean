import ConciseIPRA.FullNormalization
import ConciseIPRA.NativeBiInterpretation

/-!
# No computation rule: the kernel on full normal forms

When terms are kept in full normal form, both computation equations of the
iterator hold by syntax: the two sides of each have the same normal form.
`FNPrf` is the kernel without either computation rule, on full normal forms.
It has reflexivity in their place, and every rule normalizes its conclusion:

  Hyp, Refl, Tr, QE, DE, DI by cases, QI by progress.

`fnprf_iff_nprf` proves that the kernel derives a sequent exactly when `FNPrf`
derives its full normal form.  This is the kernel form of the calculi of
`Research/full_normalization` and `Research/computation_normal`; their single
witness-selected introduction is not treated here.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm
open Tm (zero succ iter)

variable {n m : ℕ}

/-- Derivability in the kernel without computation rules, on full normal
forms. -/
inductive FNPrf : {n : ℕ} → List (NFm n) → NFm n → Prop
  | hyp {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (h : A ∈ Γ) : FNPrf Γ A
  | refl {n : ℕ} {Γ : List (NFm n)} (t : Tm n) : FNPrf Γ (.eq t.full t.full)
  | trOne {n : ℕ} {Γ : List (NFm n)} (h : Tm (n + 1)) {s t u : Tm n}
      (h₁ : FNPrf Γ (.eq s t)) (h₂ : FNPrf Γ (.eq (Syn.subst (inst s) h).full u)) :
      FNPrf Γ (.eq u (Syn.subst (inst t) h).full)
  | qE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 1)} (t : Tm n)
      (h₁ : FNPrf Γ (.Q B)) (h₂ : FNPrf Γ (B.subst (inst zero)).full) :
      FNPrf Γ (B.subst (inst t)).full
  | dE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 2)} {A : NFm n}
      (h₁ : FNPrf Γ (.D B)) (h₂ : FNPrf (.Q B :: Γ.map NFm.shift) A.shift) : FNPrf Γ A
  | dICase {n : ℕ} {Γ : List (NFm n)} (B : NFm (n + 2)) (t : Tm n) (hB : B.full = B)
      (h : FNPrf (((B.subst (up (inst t))).subst (inst zero)).full.shift :: Γ.map NFm.shift)
        ((B.subst (up (inst t))).subst (repl (succ (var 0)))).full) :
      FNPrf Γ (.D B)
  | qIInd {n : ℕ} {Γ : List (NFm n)} (s₁ s₂ : Tm (n + 1)) (h₁ : s₁.full = s₁)
      (h₂ : s₂.full = s₂)
      (h : FNPrf (NFm.eq s₁ s₂ :: Γ.map NFm.shift)
        ((NFm.eq s₁ s₂).subst (repl (succ (var 0)))).full) :
      FNPrf Γ (.Q (.eq s₁ s₂))

variable {Γ : List (NFm n)} {A : NFm n}

/-- Every rule is a derived rule of the kernel, up to normal forms. -/
theorem FNPrf.toNPrf (h : FNPrf Γ A) : NPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | refl t => exact NPrf.eqRefl _
  | trOne h _ _ ih₁ ih₂ =>
    exact NPrf.eqTrans (.trOne h ih₁ (NPrf.eqTrans (NPrf.eqFull _) ih₂)) (NPrf.eqFull _)
  | qE t _ _ ih₁ ih₂ => exact (equivFull _).mp (.qE t ih₁ ((equivFull _).mpr ih₂))
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dICase B t _ _ ih =>
    exact .dICase B t ((equivFull _).mpr
      (NPrf.cut1 ((equivFull _).shift.mp NPrf.hyp0) (NPrf.wkUnder ih)))
  | qIInd s₁ s₂ _ _ _ ih => exact .qIInd s₁ s₂ ((equivFull _).mpr ih)

/-- The successor computation holds by syntax on full normal forms. -/
theorem Tm.full_iterSucc (c a : Tm n) (h : Tm (n + 1)) :
    (Syn.subst (inst (iter c a h)) h).full = (iter (succ c) a h).full := by
  rw [Tm.full_subst]
  show Tm.nbe h _ = Tm.nbe h (Fin.cases (iter c a h).full Tm.var)
  refine congrArg (fun r => Tm.nbe h r) (funext (Fin.cases ?_ fun j => ?_)) <;> rfl

/-- Every kernel derivation becomes a derivation without computation rules
when its formulas are normalized. -/
theorem NPrf.toFN (h : NPrf Γ A) : FNPrf (Γ.map NFm.full) A.full := by
  induction h with
  | hyp h => exact .hyp (List.mem_map_of_mem h)
  | iterZero a h => exact .refl a
  | iterSucc c a h =>
    show FNPrf _ (.eq (iter (succ c) a h).full (Syn.subst (inst (iter c a h)) h).full)
    rw [Tm.full_iterSucc]
    exact .refl _
  | @trOne _ Γ h s t u _ _ ih₁ ih₂ =>
    have h₂ : FNPrf (Γ.map NFm.full)
        (.eq (Syn.subst (inst s.full) h.full).full u.full) := by
      rw [Tm.full_subst_congr (Tm.full_idem h) (Tm.full_inst s)]
      exact ih₂
    have r := FNPrf.trOne h.full ih₁ h₂
    rw [Tm.full_subst_congr (Tm.full_idem h) (Tm.full_inst t)] at r
    exact r
  | @qE _ Γ B t _ _ ih₁ ih₂ =>
    have h₂ : FNPrf (Γ.map NFm.full) (B.full.subst (inst zero)).full := by
      rw [NFm.full_subst_congr (σ' := inst zero) (NFm.full_idem B) (fun _ => rfl)]
      exact ih₂
    have r := FNPrf.qE t.full ih₁ h₂
    rw [NFm.full_subst_congr (NFm.full_idem B) (Tm.full_inst t)] at r
    exact r
  | dE _ _ ih₁ ih₂ =>
    rw [List.map_cons, NFm.map_full_shift, NFm.full_shift] at ih₂
    exact .dE ih₁ ih₂
  | @dICase _ _ B t _ ih =>
    refine .dICase B.full t.full (NFm.full_idem B) ?_
    rw [List.map_cons, NFm.map_full_shift, NFm.full_shift] at ih
    have e : (B.full.subst (up (inst t.full))).full = (B.subst (up (inst t))).full :=
      NFm.full_subst_congr (NFm.full_idem B) (Tm.full_up_congr (Tm.full_inst t))
    rw [NFm.full_subst_congr (σ' := inst zero) e (fun _ => rfl),
      NFm.full_subst_congr (σ' := repl (succ (Syn.var 0))) e (fun _ => rfl)]
    exact ih
  | @qIInd _ _ s₁ s₂ _ ih =>
    refine .qIInd s₁.full s₂.full (Tm.full_idem s₁) (Tm.full_idem s₂) ?_
    rw [List.map_cons, NFm.map_full_shift] at ih
    rw [NFm.full_subst_congr (A' := .eq s₁ s₂) (σ' := repl (succ (Syn.var 0)))
      (by simp only [NFm.full, Tm.full_idem]) (fun _ => rfl)]
    exact ih

/-- **Both computation rules can be moved into the syntax.**  The kernel
derives a sequent exactly when the calculus without computation rules derives
its full normal form. -/
theorem fnprf_iff_nprf : FNPrf (Γ.map NFm.full) A.full ↔ NPrf Γ A :=
  ⟨fun h => (equivFull A).mpr (h.toNPrf.cut fun B hB => by
      obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hB
      exact (equivFull C).mp (.hyp hC)), NPrf.toFN⟩

/-- On fully normal sequents the two calculi derive the same. -/
theorem fnprf_iff_nprf_of_normal (hΓ : ∀ B ∈ Γ, B.full = B) (hA : A.full = A) :
    FNPrf Γ A ↔ NPrf Γ A := by
  have e : Γ.map NFm.full = Γ := by
    rw [List.map_congr_left hΓ, List.map_id']
  rw [← fnprf_iff_nprf, e, hA]

/-- The calculus without computation rules proves the full normal form of a
sequent exactly when iPRA proves its reading. -/
theorem fnprf_iff_pra :
    FNPrf (Γ.map NFm.full) A.full ↔ (Γ.map NFm.toPRA ⊢[PRAAx] A.toPRA) :=
  fnprf_iff_nprf.trans native_iff_pra

end LeanProofs.ConciseIPRA
