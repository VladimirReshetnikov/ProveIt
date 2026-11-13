import ConciseIPRA.NativeExportClauses
import ConciseIPRA.NativeEvalDischarge

/-!
# Use at the newest parameter

`XNPrf` is the calculus `𝒳_ν` of the article (`wit:def:xnu`, from the package
`export_specialization`): the inferred-discharge calculus `XCPrf` with Use
restricted to the newest parameter of the scope (the variable `0`, or `0` in an
empty scope), and with reflexivity a rule at every term.  The introduction
keeps an arbitrary witness, and the discharge is unchanged.

`xnprf_iff_xcprf`: with the reflexivity clause, `XNPrf` and `XCPrf` derive the
same formulas; hence `xnprf_iff_nprf_of_qfree`.

A Use of a clause at a term `t` is recovered from the name formula
`Nm_t = D_{x,y} (sel(y, 0, x) = sel(y, 0, t))`: it is introduced at the
witness `t` by one reflexivity step, its discharge at a fresh `b` selects `t`
(the rows at `b` are `0 = 0` and `b = t`), and in the branch the clause is
used at `b`, which is the newest parameter there.  Since a new parameter
changes which one is the newest, the translation carries a renaming and an
extension of the context through the induction.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open Tm (zero succ iter)

variable {n m : ℕ}

/-- The newest parameter of a scope: the variable `0`, or `0` in an empty scope. -/
def Tm.newest : (n : ℕ) → Tm n
  | 0 => zero
  | _ + 1 => Syn.var 0

/-- Derivability with Use at the newest parameter. -/
inductive XNPrf : {n : ℕ} → List (UCl n) → NFm n → Prop
  | refl {n : ℕ} {Γ : List (UCl n)} (t : Tm n) : XNPrf Γ (.eq t.full t.full)
  | use {n : ℕ} {Γ : List (UCl n)} {c : UCl n} (hc : c ∈ Γ)
      (h : ∀ A, c.ante = some A → XNPrf Γ A) :
      XNPrf Γ (c.cons.subst (inst (Tm.newest n))).full
  | intro {n : ℕ} {Γ : List (UCl n)} (B : NFm (n + 2)) (t : Tm n) (hB : B.full = B)
      (hQ : B.QFree) (ht : t.full = t)
      (h : XNPrf (UCl.asm ((B.subst (up (inst t))).subst (repl (NFm.start B t))).full
          :: Γ.map UCl.shift)
        ((B.subst (up (inst t))).subst (repl (succ (var 0)))).full) :
      XNPrf Γ (.D B)
  | dis {n : ℕ} {Γ : List (UCl n)} {B : NFm (n + 2)} {A : NFm n} (F : NFm (n + 1))
      (h₁ : XNPrf Γ (.D B)) (h₂ : XNPrf (UCl.clo B :: Γ.map UCl.shift) F)
      (hA : (F.subst (repl (NFm.owit B))).full = A.shift) : XNPrf Γ A

/-! ### Soundness -/

theorem XNPrf.toXC {Γ : List (UCl n)} {A : NFm n} (h : XNPrf Γ A) :
    UCl.refl ∈ Γ → XCPrf Γ A := by
  induction h with
  | refl t => exact fun hr => XCPrf.refl hr t
  | use hc _ ih => exact fun hr => .use _ hc fun A hA => ih A hA hr
  | intro B t hB hQ ht _ ih =>
    intro hr
    refine .intro B t hB hQ ht (ih (List.mem_cons_of_mem _ ?_))
    rw [← UCl.refl_shift]; exact List.mem_map_of_mem hr
  | dis F _ _ hA ih₁ ih₂ =>
    intro hr
    refine .dis F (ih₁ hr) (ih₂ (List.mem_cons_of_mem _ ?_)) hA
    rw [← UCl.refl_shift]; exact List.mem_map_of_mem hr

/-! ### The name formula -/

theorem Tm.full_sel_zero (b : Tm n) : Tm.full (iter zero zero (Syn.shift b)) = zero := by
  simp [Tm.full, Tm.nbe, Tm.recV]

theorem Tm.full_sel_succ (b z : Tm n) : Tm.full (iter (succ z) zero (Syn.shift b)) = Tm.full b := by
  simp [Tm.full, Tm.nbe, Tm.recV, Tm.nbe_ren, Tm.shift_eq_ren]
  rfl

/-- The matrix of the name formula of `t`, `sel(y, 0, x) = sel(y, 0, t)`. -/
def NFm.nmRaw (t : Tm n) : NFm (n + 2) :=
  .eq (iter (Syn.var 0) zero (Syn.shift (Syn.var (Fin.succ 0))))
    (iter (Syn.var 0) zero (Syn.shift (Syn.shift (Syn.shift t))))

/-- The name formula `D_{x,y} nm(t)`, its matrix in full normal form. -/
noncomputable def NFm.nm (t : Tm n) : NFm (n + 2) := (NFm.nmRaw t).full

theorem NFm.nm_full (t : Tm n) : (NFm.nm t).full = NFm.nm t := NFm.full_idem _

theorem NFm.nm_qfree (t : Tm n) : (NFm.nm t).QFree := trivial

theorem NFm.nm_subst_full (t : Tm n) (σ : Fin (n + 2) → Tm m) :
    ((NFm.nm t).subst σ).full = ((NFm.nmRaw t).subst σ).full :=
  NFm.full_subst_congr (NFm.full_idem _) fun _ => rfl

/-- The step of the introduction of the name formula at the witness `t` is
`t = t`, moved under the fresh variable. -/
theorem NFm.nm_step (t : Tm n) :
    (((NFm.nm t).subst (up (inst t))).subst (repl (succ (Syn.var 0)))).full
      = .eq (Syn.shift t).full (Syn.shift t).full := by
  rw [NFm.full_subst_congr (σ' := repl (succ (Syn.var 0))) (NFm.nm_subst_full t (up (inst t)))
    fun _ => rfl]
  simp only [NFm.nmRaw, NFm.subst_eq, NFm.full, Tm.subst_iter, Tm.subst_zero, Syn.subst_var,
    Syn.subst_up_shift, Syn.up_zero, Syn.up_succ, Syn.inst_zero, Syn.repl_zero,
    Syn.subst_inst_shift, Syn.subst_repl_shift]
  rw [Tm.full_sel_succ]

/-- The rows of the name formula at a fresh variable select `t`. -/
theorem NFm.nm_otest {t : Tm n} (ht : t.full = t) : NFm.OTest (NFm.nm t) (Syn.shift t) := by
  constructor
  · rw [NFm.nm_subst_full]
    simp only [NFm.nmRaw, NFm.subst_eq, NFm.full, Tm.subst_iter, Tm.subst_zero, Syn.subst_var,
      Syn.subst_up_shift, Syn.inst_zero, Syn.inst_succ, Syn.subst_inst_shift]
    rw [Tm.full_sel_zero, Tm.full_sel_zero]
  · rw [NFm.nm_subst_full]
    simp only [NFm.nmRaw, NFm.subst_eq, NFm.full, Tm.subst_iter, Tm.subst_zero,
      Syn.subst_var, Syn.subst_up_shift, Syn.inst_zero, Syn.inst_succ, Syn.subst_inst_shift]
    rw [Tm.full_sel_succ, Tm.full_sel_succ]
    simp [ht]
    rfl

/-- `Nm_t` is derivable in every context, by one introduction at the witness
`t` and one reflexivity step. -/
theorem XNPrf.nm {Γ : List (UCl n)} {t : Tm n} (ht : t.full = t) : XNPrf Γ (.D (NFm.nm t)) :=
  .intro _ t (NFm.nm_full t) (NFm.nm_qfree t) ht (by rw [NFm.nm_step]; exact .refl _)

/-! ### From `𝒳` to `𝒳_ν` -/

/-- **Completeness**, with a renaming and an extension of the context carried
through the induction: a Use of a clause at a term `t` becomes a discharge of
the name formula of `t` around a Use of the clause at the fresh, newest
variable. -/
theorem XCPrf.toXN {Γ : List (UCl n)} {A : NFm n} (h : XCPrf Γ A) :
    ∀ {m : ℕ} (ξ : Fin n → Fin m) (Δ : List (UCl m)), (∀ c ∈ Γ, c.rn ξ ∈ Δ) →
      XNPrf Δ (A.subst fun i => (Syn.var (ξ i) : Tm m)) := by
  induction h with intro m ξ Δ R
  | @use _ Γ c t hc _ ih =>
    have hN : XNPrf Δ (.D (NFm.nm (Syn.subst (fun i => (Syn.var (ξ i) : Tm m)) t).full)) :=
      XNPrf.nm (Tm.full_idem _)
    refine .dis _ hN (XNPrf.use (c := (c.rn ξ).shift)
      (List.mem_cons_of_mem _ (List.mem_map_of_mem (R c hc))) fun A hA => ?_) ?_
    · cases hca : c.ante with
      | none => simp [UCl.rn, UCl.shift, hca] at hA
      | some A₀ =>
        simp only [UCl.rn, UCl.shift, hca, Option.map_some, Option.some.injEq] at hA
        subst hA
        rw [NFm.rn_shift]
        exact ih A₀ hca (fun i => (ξ i).succ) _ (UCl.liftRn R _)
    · rw [NFm.owit_eq (NFm.nm_otest (Tm.full_idem _)),
        NFm.full_subst_congr (σ' := repl (Syn.shift
          (Syn.subst (fun i => (Syn.var (ξ i) : Tm m)) t).full)) (NFm.full_idem _) fun _ => rfl,
        ← NFm.full_rn, ← NFm.full_shift]
      simp only [UCl.rn, UCl.shift, NFm.shift, NFm.subst_subst]
      refine NFm.full_subst_congr rfl fun i => ?_
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Tm.newest, Syn.up_zero, Syn.subst_var, Syn.inst_zero,
          Syn.repl_zero, Tm.full_shift, Tm.full_rn, Tm.full_idem]
        rfl
      · simp
  | @intro _ Γ B t hB hQ ht _ ih =>
    have eX : (((B.subst (up (inst t))).subst (repl (NFm.start B t))).full).subst
          (fun i => (Syn.var (Tm.upRen ξ i) : Tm (m + 1)))
        = (((B.subst (up (up fun i => (Syn.var (ξ i) : Tm m)))).subst
            (up (inst (Syn.subst (fun i => (Syn.var (ξ i) : Tm m)) t)))).subst
          (repl (NFm.start (B.subst (up (up fun i => (Syn.var (ξ i) : Tm m))))
            (Syn.subst (fun i => (Syn.var (ξ i) : Tm m)) t)))).full := by
      rw [← NFm.full_rn, ← Tm.up_rn, NFm.subst_repl_up _ (NFm.start B t), NFm.subst_up_inst,
        ← NFm.start_rn]
    have k := ih (Tm.upRen ξ) _ (UCl.liftUp R (by rw [UCl.asm_rn, eX]))
    rw [← NFm.full_rn, ← Tm.up_rn, NFm.subst_repl_succ, NFm.subst_up_inst] at k
    refine .intro _ _ ?_ ((NFm.qfree_subst _ _).2 hQ) ?_ k
    · rw [Tm.up_rn ξ, Tm.up_rn, NFm.full_rn, hB]
    · rw [Tm.full_rn, ht]
  | @dis _ Γ B A F _ _ hA ih₁ ih₂ =>
    have h₂ := ih₂ (Tm.upRen ξ) (UCl.clo (B.subst (up (up fun i => (Syn.var (ξ i) : Tm m))))
        :: Δ.map UCl.shift)
      (UCl.liftUp R (by
        show (UCl.clo B).subst _ = _
        rw [UCl.clo_subst_rn, Tm.up_rn ξ]))
    rw [← Tm.up_rn] at h₂
    refine .dis (F.subst (up fun i => (Syn.var (ξ i) : Tm m))) (ih₁ ξ Δ R) h₂ ?_
    rw [NFm.owit_rn, ← NFm.subst_repl_up, Tm.up_rn, NFm.full_rn, hA, ← Tm.up_rn,
      NFm.shift_subst_up]

variable {Γ : List (UCl n)} {A : NFm n}

/-- **Use at the newest parameter suffices**: with the reflexivity clause,
`𝒳_ν` and `𝒳` derive the same formulas. -/
theorem xnprf_iff_xcprf (hr : UCl.refl ∈ Γ) : XNPrf Γ A ↔ XCPrf Γ A := by
  refine ⟨fun h => h.toXC hr, fun h => ?_⟩
  have k := h.toXN id Γ fun c hc => by rw [UCl.rn_id]; exact hc
  rwa [show (fun i => (Syn.var (id i) : Tm n)) = Syn.var from rfl, NFm.subst_id] at k

/-- On `Q`-free sequents `𝒳_ν` derives exactly what the kernel derives, up to
full normal forms. -/
theorem xnprf_iff_nprf_of_qfree {Γ : List (NFm n)} (hΓ : ∀ X ∈ Γ, X.QFree) (hA : A.QFree) :
    XNPrf (UCl.refl :: Γ.map fun X => UCl.asm X.full) A.full ↔ NPrf Γ A :=
  (xnprf_iff_xcprf List.mem_cons_self).trans (xcprf_iff_nprf_of_qfree hΓ hA)

end LeanProofs.ConciseIPRA
