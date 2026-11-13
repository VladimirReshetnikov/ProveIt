import ConciseIPRA.NativeZeroNormal
import ConciseIPRA.NativeDiagonal

/-!
# Six rules on zero-normal terms: the reflexive-base introduction

`NRPrf` is the calculus of the package `Research/reflexive_base`, on the
zero-normal syntax of `NativeZeroNormal`: hypothesis, successor computation,
transport in one term, `QE`, `DE`, and one introduction

  `dI`: from `Γ, B(t, η) ⊢ B(t, S z)` with `z` fresh infer `D_{x,y} B`,

where `η = z` exactly when the normalized zero instance `B(t, 0)` is literally
of the form `r = r`, and `η = 0` otherwise.  Every substitution of a rule is
followed by the contraction `nf`.  There is no zero computation rule and only
one introduction: six rules.

* `nrprf_iff_nprf`: `NPrf Γ A ↔ NRPrf (Γ.map fnf) (fnf A)`;
* `NRPrf.normal`: only zero-normal formulas from zero-normal hypotheses;
* `nrprf_iff_pra`: the bi-interpretation with iPRA transfers.

Completeness translates the calculus `GPrf` of `NativeDiagonal` rule by rule
(`GPrf.toNR`).  The two mode tests differ: a matrix can have a reflexive
normalized base without being diagonal.  The translation therefore carries the
invariant that every hypothesis of the source is a hypothesis of the target
*or literally reflexive*: a reflexive hypothesis is never needed, since a use
of it is a use of reflexivity.  With this invariant no cut rule of `NRPrf` is
required.  A diagonal matrix always has the base `0 = 0` after normalization,
so its progress mode is the same in both calculi.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open Tm (zero succ iter)
open scoped Fm
open ZeroNormalization

variable {n m : ℕ}

namespace NFm

/-- A literal equation with identical sides. -/
def IsRefl (X : NFm n) : Prop := ∃ r, X = .eq r r

theorem IsRefl.shift {X : NFm n} (h : X.IsRefl) : X.shift.IsRefl := by
  obtain ⟨r, rfl⟩ := h
  exact ⟨Syn.shift r, rfl⟩

open Classical in
/-- The start of the reflexive-base introduction: the fresh variable when the
normalized zero instance of the matrix is reflexive, `0` otherwise. -/
noncomputable def rstart (B : NFm (n + 2)) (t : Tm n) : Tm (n + 1) :=
  if IsRefl (fnf ((B.subst (up (inst t))).subst (inst zero))) then Syn.var 0 else zero

theorem rstart_congr (B : NFm (n + 2)) (t : Tm n) : rstart (fnf B) (nf t) = rstart B t := by
  have e : fnf ((fnf B).subst (up (inst (nf t)))) = fnf (B.subst (up (inst t))) :=
    fnf_subst_congr (fnf_idempotent B) (nf_up_congr (nf_inst t))
  unfold rstart
  rw [fnf_subst_congr (σ' := inst zero) e (fun _ => rfl)]

theorem nf_diagTerm {s : Tm (n + 2)} (hs : s.isDiag = true) (t : Tm n) :
    nf (Syn.subst (inst zero) (Syn.subst (up (inst t)) s)) = zero := by
  cases s with
  | var i => exact Bool.noConfusion hs
  | zero => exact Bool.noConfusion hs
  | succ t => exact Bool.noConfusion hs
  | iter c a h =>
    have hc : c.isV0 = true ∧ a.isV0 = true := by simpa [Tm.isDiag] using hs
    rw [Tm.eq_var0 hc.1, Tm.eq_var0 hc.2]
    rfl

/-- The normalized base of a diagonal matrix is `0 = 0`. -/
theorem fnf_diagBase {B : NFm (n + 2)} (hB : B.isDiag = true) (t : Tm n) :
    fnf ((B.subst (up (inst t))).subst (inst zero)) = .eq zero zero := by
  cases B with
  | eq s₁ s₂ =>
    have h : s₁.isDiag = true ∧ s₂.isDiag = true := by simpa [NFm.isDiag] using hB
    simp only [NFm.subst_eq, fnf, nf_diagTerm h.1, nf_diagTerm h.2]
  | Q B => exact Bool.noConfusion hB
  | D B => exact Bool.noConfusion hB

/-- The invariant of the translation, under one more variable. -/
theorem liftRefl {Γ Δ : List (NFm n)} (s : ∀ C ∈ Γ.map fnf, C ∈ Δ ∨ C.IsRefl) :
    ∀ C ∈ (Γ.map NFm.shift).map fnf, C ∈ Δ.map NFm.shift ∨ C.IsRefl := by
  intro C hC
  rw [map_fnf_shift] at hC
  obtain ⟨C₀, hC₀, rfl⟩ := List.mem_map.1 hC
  rcases s C₀ hC₀ with h | h
  · exact .inl (List.mem_map_of_mem h)
  · exact .inr h.shift

end NFm

/-- Derivability on zero-normal terms with the reflexive-base introduction. -/
inductive NRPrf : {n : ℕ} → List (NFm n) → NFm n → Prop
  | hyp {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (h : A ∈ Γ) : NRPrf Γ A
  | iterSucc {n : ℕ} {Γ : List (NFm n)} (c a : Tm n) (h : Tm (n + 1)) :
      NRPrf Γ (fnf (.eq (iter (succ c) a h) (Syn.subst (inst (iter c a h)) h)))
  | trOne {n : ℕ} {Γ : List (NFm n)} (h : Tm (n + 1)) {s t u : Tm n}
      (h₁ : NRPrf Γ (.eq s t)) (h₂ : NRPrf Γ (.eq (nf (Syn.subst (inst s) h)) u)) :
      NRPrf Γ (.eq u (nf (Syn.subst (inst t) h)))
  | qE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 1)} (t : Tm n)
      (h₁ : NRPrf Γ (.Q B)) (h₂ : NRPrf Γ (fnf (B.subst (inst zero)))) :
      NRPrf Γ (fnf (B.subst (inst t)))
  | dE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 2)} {A : NFm n}
      (h₁ : NRPrf Γ (.D B)) (h₂ : NRPrf (.Q B :: Γ.map NFm.shift) A.shift) : NRPrf Γ A
  /-- DI: from `B(t, η) ⊢ B(t, S z)` infer `D_{x,y} B`, where `η = z` when the
  normalized `B(t, 0)` is literally `r = r` and `η = 0` otherwise. -/
  | dI {n : ℕ} {Γ : List (NFm n)} (B : NFm (n + 2)) (t : Tm n) (hB : fnf B = B)
      (h : NRPrf (fnf ((B.subst (up (inst t))).subst (repl (NFm.rstart B t)))
          :: Γ.map NFm.shift)
        (fnf ((B.subst (up (inst t))).subst (repl (succ (var 0)))))) :
      NRPrf Γ (.D B)

variable {Γ : List (NFm n)} {A : NFm n}

namespace NRPrf

/-- Every rule is a derived rule of the kernel, up to normal forms. -/
theorem toNPrf (h : NRPrf Γ A) : NPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | iterSucc c a h => exact (equivFnf _).mp (.iterSucc c a h)
  | trOne h _ _ ih₁ ih₂ =>
    exact NPrf.eqTrans (.trOne h ih₁ (NPrf.eqTrans (eqNf _) ih₂)) (eqNf _)
  | qE t _ _ ih₁ ih₂ => exact (equivFnf _).mp (.qE t ih₁ ((equivFnf _).mpr ih₂))
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | @dI _ Γ B t _ _ ih =>
    have h' : NPrf ((B.subst (up (inst t))).subst (repl (NFm.rstart B t)) :: Γ.map NFm.shift)
        ((B.subst (up (inst t))).subst (repl (succ (Syn.var 0)))) :=
      (equivFnf _).mpr (NPrf.cut1 ((equivFnf _).mp NPrf.hyp0) (NPrf.wkUnder ih))
    by_cases hr : NFm.IsRefl (fnf ((B.subst (up (inst t))).subst (inst zero)))
    · rw [NFm.rstart, if_pos hr, NFm.subst_repl_var0] at h'
      cases B with
      | eq s₁ s₂ => exact .dIProg s₁ s₂ t h'
      | Q B => obtain ⟨r, e⟩ := hr; simp [fnf] at e
      | D B => obtain ⟨r, e⟩ := hr; simp [fnf] at e
    · rw [NFm.rstart, if_neg hr, ← NFm.shift_subst_inst_zero] at h'
      exact .dICase B t h'

/-- Reflexivity at a normal form, from successor computation. -/
theorem reflNf (t : Tm n) : NRPrf Γ (.eq (nf t) (nf t)) := by
  have e := NRPrf.iterSucc (Γ := Γ) zero (nf t) (Syn.var 0)
  simp only [fnf, nf_iter, nf_succ, nf_zero, nf_var, smartI_succ, smartI_zero, nf_idempotent,
    Syn.subst_var, Syn.inst_zero] at e
  have r := NRPrf.trOne (Syn.var 0) (u := nf t) e (by
    simpa only [nf_iter, nf_succ, nf_zero, nf_var, smartI_succ, nf_idempotent, Syn.subst_var,
      Syn.inst_zero] using e)
  simpa only [Syn.subst_var, Syn.inst_zero, nf_idempotent] using r

/-- From zero-normal hypotheses only zero-normal formulas are derivable. -/
theorem normal (h : NRPrf Γ A) : (∀ B ∈ Γ, fnf B = B) → fnf A = A := by
  induction h with
  | hyp h => exact fun hΓ => hΓ _ h
  | iterSucc c a h => exact fun _ => fnf_idempotent _
  | trOne h _ _ _ ih₂ =>
    intro hΓ
    have e := ih₂ hΓ
    simp only [fnf, NFm.eq.injEq] at e
    simp only [fnf, nf_idempotent, e.2]
  | qE t _ _ _ _ => exact fun _ => fnf_idempotent _
  | @dE _ Γ B A _ _ ih₁ ih₂ =>
    intro hΓ
    have hB : fnf B = B := by
      have e := ih₁ hΓ
      simpa only [fnf, NFm.D.injEq] using e
    have e := ih₂ fun C hC => by
      rcases List.mem_cons.1 hC with rfl | hC
      · simp only [fnf, hB]
      · obtain ⟨C₀, hC₀, rfl⟩ := List.mem_map.1 hC
        rw [fnf_shift, hΓ C₀ hC₀]
    rw [fnf_shift] at e
    have e' := congrArg (fun X : NFm _ => X.subst (inst zero)) e
    simpa only [NFm.subst_inst_shift] using e'
  | dI B t hB _ _ => exact fun _ => by simp only [fnf, hB]

end NRPrf

/-- Every derivation with the diagonal introduction becomes a derivation with
the reflexive-base introduction when its formulas are normalized.  Hypotheses
that are literally reflexive may be dropped. -/
theorem GPrf.toNR (h : GPrf Γ A) :
    ∀ {Δ : List (NFm n)}, (∀ C ∈ Γ.map fnf, C ∈ Δ ∨ C.IsRefl) → NRPrf Δ (fnf A) := by
  induction h with
  | @hyp _ Γ A h =>
    intro Δ s
    rcases s _ (List.mem_map_of_mem (f := fnf) h) with h' | ⟨r, e⟩
    · exact .hyp h'
    · cases A with
      | eq a b =>
        simp only [fnf, NFm.eq.injEq] at e
        show NRPrf Δ (.eq (nf a) (nf b))
        rw [e.2, ← e.1]
        exact NRPrf.reflNf a
      | Q B => simp [fnf] at e
      | D B => simp [fnf] at e
  | iterZero a h => intro Δ _; exact NRPrf.reflNf a
  | iterSucc c a h => intro Δ _; exact .iterSucc c a h
  | @trOne _ Γ h s t u _ _ ih₁ ih₂ =>
    intro Δ hΔ
    have h₂ : NRPrf Δ (.eq (nf (Syn.subst (inst (nf s)) (nf h))) (nf u)) := by
      rw [nf_subst_congr (nf_idempotent h) (nf_inst s)]
      exact ih₂ hΔ
    have r := NRPrf.trOne (nf h) (ih₁ hΔ) h₂
    rw [nf_subst_congr (nf_idempotent h) (nf_inst t)] at r
    exact r
  | @qE _ Γ B t _ _ ih₁ ih₂ =>
    intro Δ hΔ
    have h₂ : NRPrf Δ (fnf ((fnf B).subst (inst zero))) := by
      rw [fnf_subst_congr (σ' := inst zero) (fnf_idempotent B) (fun _ => rfl)]
      exact ih₂ hΔ
    have r := NRPrf.qE (nf t) (ih₁ hΔ) h₂
    rw [fnf_subst_congr (fnf_idempotent B) (nf_inst t)] at r
    exact r
  | @dE _ Γ B A _ _ ih₁ ih₂ =>
    intro Δ hΔ
    refine .dE (ih₁ hΔ) ?_
    have h := ih₂ (Δ := .Q (fnf B) :: Δ.map NFm.shift) fun C hC => by
      rw [List.map_cons] at hC
      rcases List.mem_cons.1 hC with rfl | hC
      · exact .inl List.mem_cons_self
      · rcases NFm.liftRefl hΔ C hC with h | h
        · exact .inl (List.mem_cons_of_mem _ h)
        · exact .inr h
    rw [fnf_shift] at h
    exact h
  | @dI _ Γ B t _ ih =>
    intro Δ hΔ
    have e : fnf ((fnf B).subst (up (inst (nf t)))) = fnf (B.subst (up (inst t))) :=
      fnf_subst_congr (fnf_idempotent B) (nf_up_congr (nf_inst t))
    refine .dI (fnf B) (nf t) (fnf_idempotent B) ?_
    rw [NFm.rstart_congr, fnf_subst_congr (σ' := repl (succ (Syn.var 0))) e (fun _ => rfl),
      fnf_subst_congr (σ' := repl (NFm.rstart B t)) e (fun _ => rfl)]
    refine ih fun C hC => ?_
    rw [List.map_cons] at hC
    rcases List.mem_cons.1 hC with rfl | hC
    · by_cases hd : B.isDiag = true
      · -- a diagonal matrix: both tests choose the progress mode
        have hr : NFm.IsRefl (fnf ((B.subst (up (inst t))).subst (inst zero))) :=
          ⟨zero, NFm.fnf_diagBase hd t⟩
        rw [NFm.dstart, if_pos hd, NFm.rstart, if_pos hr]
        exact .inl List.mem_cons_self
      · rw [NFm.dstart, if_neg hd]
        by_cases hr : NFm.IsRefl (fnf ((B.subst (up (inst t))).subst (inst zero)))
        · -- the case hypothesis is literally reflexive and can be dropped
          right
          rw [← NFm.shift_subst_inst_zero, fnf_shift]
          exact hr.shift
        · rw [NFm.rstart, if_neg hr]
          exact .inl List.mem_cons_self
    · rcases NFm.liftRefl hΔ C hC with h | h
      · exact .inl (List.mem_cons_of_mem _ h)
      · exact .inr h

/-- **Six rules on zero-normal terms.**  The kernel derives a sequent exactly
when the calculus with the reflexive-base introduction derives its zero-normal
form. -/
theorem nrprf_iff_nprf : NRPrf (Γ.map fnf) (fnf A) ↔ NPrf Γ A :=
  ⟨fun h => (equivFnf A).mpr (h.toNPrf.cut fun B hB => by
      obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hB
      exact (equivFnf C).mp (.hyp hC)), fun h => h.toGPrf.toNR fun _ hC => .inl hC⟩

/-- The same calculus proves the zero-normal form of a sequent exactly when
iPRA proves its reading. -/
theorem nrprf_iff_pra : NRPrf (Γ.map fnf) (fnf A) ↔ (Γ.map NFm.toPRA ⊢[PRAAx] A.toPRA) :=
  nrprf_iff_nprf.trans native_iff_pra

end LeanProofs.ConciseIPRA
