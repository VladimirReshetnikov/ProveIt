import ConciseIPRA.NativeModels
import ConciseIPRA.TeqParity

/-!
# Transport from the literal `0`, with the equivalence rules, is incomplete

`disch:prop:zero-refl`.  `Z0Prf` is the kernel with transport replaced by

  `Tr₀`: from `0 = t` and `F(0)` infer `F(t)`, for every formula template `F`,

and with reflexivity, symmetry and transitivity added.  Read an equation `s = t`
over the natural numbers as "both are `0` or both are not" (`zsem`): this is an
equivalence relation that relates the two sides of each computation equation, and
`Tr₀` is valid because `0 = t` forces the value of `t` to be `0`.  The progress
and case rules are valid as for the standard reading.  So `Z0Prf` derives only
sequents valid in this reading, and it derives neither `1 = 2 ⊢ 0 = 1` nor
`⊢ Q_y (A(y) = B(y))` with `A(y) = I(y, 2; u.N(u))`, `B(y) = I(y, 1; u.N(u))` and
the parity `N`; the kernel derives both (`zero_refl_separation`).
-/

namespace LeanProofs.ConciseIPRA

open Syn
open Tm (zero succ iter)

variable {n : ℕ}

/-- `N⁰`: transport from the literal `0` in every formula template, with the
equivalence rules. -/
inductive Z0Prf : {n : ℕ} → List (NFm n) → NFm n → Prop
  | hyp {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (h : A ∈ Γ) : Z0Prf Γ A
  | iterZero {n : ℕ} {Γ : List (NFm n)} (a : Tm n) (h : Tm (n + 1)) :
      Z0Prf Γ (.eq (iter zero a h) a)
  | iterSucc {n : ℕ} {Γ : List (NFm n)} (c a : Tm n) (h : Tm (n + 1)) :
      Z0Prf Γ (.eq (iter (succ c) a h) (Syn.subst (inst (iter c a h)) h))
  | tr0 {n : ℕ} {Γ : List (NFm n)} (F : NFm (n + 1)) {t : Tm n}
      (h₁ : Z0Prf Γ (.eq zero t)) (h₂ : Z0Prf Γ (F.subst (inst zero))) : Z0Prf Γ (F.subst (inst t))
  | refl {n : ℕ} {Γ : List (NFm n)} (t : Tm n) : Z0Prf Γ (.eq t t)
  | symm {n : ℕ} {Γ : List (NFm n)} {s t : Tm n} (h : Z0Prf Γ (.eq s t)) : Z0Prf Γ (.eq t s)
  | trans {n : ℕ} {Γ : List (NFm n)} {r s t : Tm n} (h₁ : Z0Prf Γ (.eq r s))
      (h₂ : Z0Prf Γ (.eq s t)) : Z0Prf Γ (.eq r t)
  | qE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 1)} (t : Tm n)
      (h₁ : Z0Prf Γ (.Q B)) (h₂ : Z0Prf Γ (B.subst (inst zero))) : Z0Prf Γ (B.subst (inst t))
  | dE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 2)} {A : NFm n}
      (h₁ : Z0Prf Γ (.D B)) (h₂ : Z0Prf (.Q B :: Γ.map NFm.shift) A.shift) : Z0Prf Γ A
  | dICase {n : ℕ} {Γ : List (NFm n)} (B : NFm (n + 2)) (t : Tm n)
      (h : Z0Prf (((B.subst (up (inst t))).subst (inst zero)).shift :: Γ.map NFm.shift)
        ((B.subst (up (inst t))).subst (repl (succ (var 0))))) :
      Z0Prf Γ (.D B)
  | qIInd {n : ℕ} {Γ : List (NFm n)} (s₁ s₂ : Tm (n + 1))
      (h : Z0Prf (NFm.eq s₁ s₂ :: Γ.map NFm.shift)
        ((NFm.eq s₁ s₂).subst (repl (succ (var 0))))) :
      Z0Prf Γ (.Q (.eq s₁ s₂))

/-- The reading: an equation holds when both sides are `0` or both are not. -/
def zsem : Sem := { Sem.std with eqv := fun a b => (a = 0 ↔ b = 0) }

theorem zsem_sound : zsem.Sound { Rules.all with trOne := false } :=
  { Sem.std_sound _ with
    iterZero := fun _ _ _ => Iff.rfl
    iterSucc := fun _ _ _ _ => Iff.rfl
    trOne := fun e => absurd e (by decide)
    qIInd := fun _ f g H h0 y => by
      induction y with
      | zero => exact h0
      | succ z ih => exact H z ih }

variable {Γ : List (NFm n)} {A : NFm n}

/-- **Soundness** of `N⁰` for the reading `zsem`. -/
theorem Z0Prf.sound (h : Z0Prf Γ A) :
    ∀ ρ : Fin n → ℕ, (∀ X ∈ Γ, X.sat zsem ρ) → A.sat zsem ρ := by
  have hS := zsem_sound
  induction h with
  | hyp h => intro ρ hΓ; exact hΓ _ h
  | iterZero a h => intro ρ _; exact hS.iterZero rfl _ _
  | iterSucc c a h =>
    intro ρ _
    show zsem.eqv _ ((Syn.subst (inst (iter c a h)) h).val zsem ρ)
    rw [Tm.val_subst, Tm.val_inst]
    exact hS.iterSucc rfl _ _ _
  | @tr0 _ Γ F t _ _ ih₁ ih₂ =>
    intro ρ hΓ
    have h₁ : (0 = 0 ↔ t.val zsem ρ = 0) := ih₁ ρ hΓ
    have h₂ := ih₂ ρ hΓ
    rw [NFm.sat_inst] at h₂ ⊢
    rw [show t.val zsem ρ = 0 from h₁.1 rfl]
    exact h₂
  | refl t => intro ρ _; exact Iff.rfl
  | symm _ ih => intro ρ hΓ; exact (ih ρ hΓ).symm
  | trans _ _ ih₁ ih₂ => intro ρ hΓ; exact (ih₁ ρ hΓ).trans (ih₂ ρ hΓ)
  | @qE _ Γ B t _ _ ih₁ ih₂ =>
    intro ρ hΓ
    have h₂ := ih₂ ρ hΓ
    rw [NFm.sat_inst] at h₂ ⊢
    exact hS.qE rfl _ _ (ih₁ ρ hΓ) h₂
  | @dE _ Γ B A _ _ ih₁ ih₂ =>
    intro ρ hΓ
    refine hS.dE rfl _ _ (ih₁ ρ hΓ) fun b hq => ?_
    rw [← NFm.sat_shift zsem A b ρ]
    refine ih₂ (Fin.cases b ρ) fun X hX => ?_
    rcases List.mem_cons.1 hX with rfl | hX
    · exact hq
    · obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
      rw [NFm.sat_shift]
      exact hΓ Y hY
  | @dICase _ Γ B t _ ih =>
    intro ρ hΓ
    refine hS.dICase rfl _ (t.val zsem ρ) fun z h0 => ?_
    have h := ih (Fin.cases z ρ) fun X hX => by
      rcases List.mem_cons.1 hX with rfl | hX
      · rw [NFm.sat_shift, NFm.sat_inst, NFm.sat_up_inst]
        exact h0
      · obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
        rw [NFm.sat_shift]
        exact hΓ Y hY
    rw [NFm.sat_repl, NFm.sat_up_inst] at h
    exact h
  | @qIInd _ Γ s₁ s₂ _ ih =>
    intro ρ hΓ
    refine hS.qIInd rfl (fun y => s₁.val zsem (Fin.cases y ρ)) (fun y => s₂.val zsem (Fin.cases y ρ))
      fun z hz => ?_
    have h := ih (Fin.cases z ρ) fun X hX => by
      rcases List.mem_cons.1 hX with rfl | hX
      · exact hz
      · obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
        rw [NFm.sat_shift]
        exact hΓ Y hY
    simp only [NFm.subst_eq, NFm.sat, Tm.val_subst, Tm.val_repl] at h
    exact h

/-- `A(y) = I(y, 2; u.N(u))`. -/
def zrA : Tm 1 := iter (var 0) (succ (succ zero)) (Tm.par (var 0))

/-- `B(y) = I(y, 1; u.N(u))`. -/
def zrB : Tm 1 := iter (var 0) (succ zero) (Tm.par (var 0))

/-- `Z0Prf` derives neither separating sequent. -/
theorem z0prf_not_one_two : ¬ Z0Prf [NFm.eq (succ zero : Tm 0) (succ (succ zero))]
    (.eq zero (succ zero)) := fun h => by
  have k := h.sound (fun i => i.elim0) fun X hX => by
    rcases List.mem_singleton.1 hX with rfl
    show ((1 : ℕ) = 0 ↔ (2 : ℕ) = 0)
    decide
  exact absurd (k.1 rfl) (by decide)

theorem z0prf_not_q : ¬ Z0Prf ([] : List (NFm 0)) (.Q (.eq zrA zrB)) := fun h => by
  have k := h.sound (fun i => i.elim0) (fun _ hX => nomatch hX)
  have h0 : (zrA.val zsem (Fin.cases 0 fun i => i.elim0) = 0 ↔
      zrB.val zsem (Fin.cases 0 fun i => i.elim0) = 0) := by decide
  have k1 : (zrA.val zsem (Fin.cases 1 fun i => i.elim0) = 0 ↔
      zrB.val zsem (Fin.cases 1 fun i => i.elim0) = 0) := k h0 1
  exact absurd k1 (by decide)

namespace NPrf

variable {Γ : List (NFm n)}

theorem zf_zero : NPrf Γ (.eq (Tm.zf (zero : Tm n)) (succ zero)) := by
  simpa [Tm.zf, Tm.sel, Tm.one] using NPrf.iterZero (Γ := Γ) (succ zero) (Syn.shift (zero : Tm n))

theorem zf_succ (c : Tm n) : NPrf Γ (.eq (Tm.zf (succ c)) zero) := by
  simpa [Tm.zf, Tm.sel, Tm.one] using NPrf.iterSucc (Γ := Γ) c (succ zero) (Syn.shift (zero : Tm n))

theorem par_one : NPrf Γ (.eq (Tm.par (succ (zero : Tm n))) (succ zero)) := by
  have h₁ : NPrf Γ (.eq (Tm.par (succ (zero : Tm n))) (Tm.zf (iter zero zero (Tm.zf (var 0))))) := by
    simpa [Tm.par] using NPrf.iterSucc (Γ := Γ) zero zero (Tm.zf (var 0))
  have h₂ : NPrf Γ (.eq (Tm.zf (iter zero zero (Tm.zf (var 0)))) (Tm.zf (zero : Tm n))) := by
    simpa using NPrf.eqCongr (Tm.zf (var 0)) (NPrf.iterZero (Γ := Γ) zero (Tm.zf (var 0)))
  exact NPrf.eqTrans h₁ (NPrf.eqTrans h₂ zf_zero)

theorem par_two : NPrf Γ (.eq (Tm.par (succ (succ (zero : Tm n)))) zero) := by
  have h₁ : NPrf Γ (.eq (Tm.par (succ (succ (zero : Tm n)))) (Tm.zf (Tm.par (succ zero)))) := by
    simpa [Tm.par] using NPrf.iterSucc (Γ := Γ) (succ zero) zero (Tm.zf (var 0))
  have h₂ : NPrf Γ (.eq (Tm.zf (Tm.par (succ (zero : Tm n)))) (Tm.zf (succ zero))) := by
    simpa using NPrf.eqCongr (Tm.zf (var 0)) (par_one (Γ := Γ))
  exact NPrf.eqTrans h₁ (NPrf.eqTrans h₂ (zf_succ zero))

end NPrf

/-- **The separation** (`disch:prop:zero-refl`): the kernel derives `1 = 2 ⊢ 0 = 1` and
`⊢ Q_y (A(y) = B(y))`; transport from the literal `0` with the equivalence rules
derives neither. -/
theorem zero_refl_separation :
    NPrf [NFm.eq (succ zero : Tm 0) (succ (succ zero))] (.eq zero (succ zero))
      ∧ NPrf ([] : List (NFm 0)) (.Q (.eq zrA zrB))
      ∧ ¬ Z0Prf [NFm.eq (succ zero : Tm 0) (succ (succ zero))] (.eq zero (succ zero))
      ∧ ¬ Z0Prf ([] : List (NFm 0)) (.Q (.eq zrA zrB)) := by
  refine ⟨?_, ?_, z0prf_not_one_two, z0prf_not_q⟩
  · have e := NPrf.eqCongr (Tm.par (var 0)) (NPrf.hyp0 (Γ := []) (A := NFm.eq (succ zero : Tm 0)
      (succ (succ zero))))
    simp only [Tm.subst_par, Syn.subst_var, Syn.inst_zero] at e
    exact NPrf.eqSymm (NPrf.eqTrans (NPrf.eqSymm NPrf.par_one) (NPrf.eqTrans e NPrf.par_two))
  · refine .qIInd zrA zrB ?_
    have hA := NPrf.iterSucc (Γ := [NFm.eq zrA zrB]) (var 0) (succ (succ zero)) (Tm.par (var 0))
    have hB := NPrf.iterSucc (Γ := [NFm.eq zrA zrB]) (var 0) (succ zero) (Tm.par (var 0))
    have e := NPrf.eqCongr (Γ := [NFm.eq zrA zrB]) (Tm.par (var 0)) NPrf.hyp0
    simp only [Tm.subst_par, Syn.subst_var, Syn.inst_zero] at hA hB e
    simp only [zrA, zrB, NFm.subst_eq, Tm.subst_iter, Syn.subst_var, Syn.repl_zero, Tm.subst_succ,
      Tm.subst_zero, Tm.subst_par, Syn.up_zero, List.map_nil]
    exact NPrf.eqTrans hA (NPrf.eqTrans e (NPrf.eqSymm hB))

end LeanProofs.ConciseIPRA
