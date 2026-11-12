import ConciseIPRA.NativeFullNormal

/-!
# Opening with an inferred witness

The packages `Research/inferred_witness`, `Research/deterministic_opening`,
`Research/first_instance` and `Research/clause_discharge` change the
elimination of `D_{x,y} B`.  On full normal forms, the rule inspects two rows
of the matrix at the fresh `b`: if `B(b, 0)` is literally `0 = 0` and `B(b, 1)`
is literally `b = r`, it opens the closure at `r`, and otherwise at `b`.  No
replacement term and no equality proof are supplied; `r` may mention `b`.

`NFm.owit B` is the selected witness, and `FOPrf` is the kernel on full normal
forms (`FNPrf`) with this opening in place of `DE`.  `foprf_iff_nprf` proves
that the kernel derives a sequent exactly when `FOPrf` derives its full normal
form.

* The opening is sound: when the test selects `r`, the closure at `b` has a
  true base, so its instance at `1` is `b = r`, and the closure at `r` follows
  by transport (`NPrf.owitQ`).
* For completeness a kernel derivation is translated under an arbitrary
  substitution (`NPrf.toFO`).  At `DE`, the branch is translated under the
  substitution that sends the fresh variable to the selected witness of the
  normalized matrix, whatever that witness is.  No case distinction on the
  test and no substitution lemma for `FOPrf` are needed, although the test is
  not stable under substitution.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm
open Tm (zero succ iter)

variable {n m : ℕ}

namespace NFm

/-- The rows that select the witness `r`: `B(b, 0)` is `0 = 0` and `B(b, 1)`
is `b = r`, as full normal forms. -/
def OTest (B : NFm (n + 2)) (r : Tm (n + 1)) : Prop :=
  (B.subst (inst zero)).full = .eq zero zero
    ∧ (B.subst (inst (succ zero))).full = .eq (Syn.var 0) r

open Classical in
/-- The witness at which `D_{x,y} B` is opened: the term read off the matrix,
or the fresh variable. -/
noncomputable def owit (B : NFm (n + 2)) : Tm (n + 1) :=
  if h : ∃ r, OTest B r then h.choose else Syn.var 0

theorem owit_spec {B : NFm (n + 2)} (h : ∃ r, OTest B r) : OTest B (owit B) := by
  rw [owit, dif_pos h]
  exact h.choose_spec

theorem owit_neg {B : NFm (n + 2)} (h : ¬∃ r, OTest B r) : owit B = Syn.var 0 := by
  rw [owit, dif_neg h]

theorem subst_hole_inst (X : NFm (n + 1)) (x : Tm (n + 1)) :
    (X.subst (Fin.cases (Syn.var 0) fun i => Syn.var i.succ.succ)).subst (inst x)
      = X.subst (repl x) := by
  rw [subst_subst]
  refine X.subst_ext fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem map_shift_subst_full (Γ : List (NFm n)) (σ : Fin n → Tm m) :
    (Γ.map NFm.shift).map (fun X => (X.subst (up σ)).full)
      = (Γ.map fun X => (X.subst σ).full).map NFm.shift := by
  rw [List.map_map, List.map_map]
  refine List.map_congr_left fun X _ => ?_
  show (X.shift.subst (up σ)).full = _
  rw [NFm.shift_subst_up, NFm.full_shift]
  rfl

end NFm

/-- The closure at the selected witness follows from the closure at the fresh
variable. -/
theorem NPrf.owitQ (B : NFm (n + 2)) {Δ : List (NFm (n + 1))} (hQ : NPrf Δ (.Q B)) :
    NPrf Δ (.Q (B.subst (up (repl (NFm.owit B)))).full) := by
  by_cases h : ∃ r, NFm.OTest B r
  · obtain ⟨e0, e1⟩ := NFm.owit_spec h
    have base : NPrf Δ (B.subst (inst zero)) :=
      (equivFull _).mpr (by rw [e0]; exact NPrf.eqRefl zero)
    have row : NPrf Δ (.eq (Syn.var 0) (NFm.owit B)) := by
      have k := (equivFull _).mp (NPrf.qE (succ zero) hQ base)
      rwa [e1] at k
    have tr := NPrf.tr ((NFm.Q B).subst (Fin.cases (Syn.var 0) fun i => Syn.var i.succ.succ))
      row (by rw [NFm.subst_hole_inst, NFm.subst_repl_var]; exact hQ)
    rw [NFm.subst_hole_inst] at tr
    exact (equivFull (.Q (B.subst (up (repl (NFm.owit B)))))).mp tr
  · have e : B.subst (up (repl (Syn.var 0))) = B := by
      rw [show (repl (Syn.var 0) : Fin (n + 1) → Tm (n + 1)) = Syn.var from
        funext fun i => by refine Fin.cases ?_ (fun j => ?_) i <;> simp, Syn.up_var,
        NFm.subst_id]
    rw [NFm.owit_neg h, e]
    exact (equivFull (.Q B)).mp hQ

/-- The kernel on full normal forms with the opening at an inferred witness in
place of `DE`. -/
inductive FOPrf : {n : ℕ} → List (NFm n) → NFm n → Prop
  | hyp {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (h : A ∈ Γ) : FOPrf Γ A
  | refl {n : ℕ} {Γ : List (NFm n)} (t : Tm n) : FOPrf Γ (.eq t.full t.full)
  | trOne {n : ℕ} {Γ : List (NFm n)} (h : Tm (n + 1)) {s t u : Tm n}
      (h₁ : FOPrf Γ (.eq s t)) (h₂ : FOPrf Γ (.eq (Syn.subst (inst s) h).full u)) :
      FOPrf Γ (.eq u (Syn.subst (inst t) h).full)
  | qE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 1)} (t : Tm n)
      (h₁ : FOPrf Γ (.Q B)) (h₂ : FOPrf Γ (B.subst (inst zero)).full) :
      FOPrf Γ (B.subst (inst t)).full
  /-- Open: from `D_{x,y} B` and a derivation of `A` from the closure of `B` at
  the witness read off its rows, infer `A`. -/
  | dO {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 2)} {A : NFm n} (h₁ : FOPrf Γ (.D B))
      (h₂ : FOPrf (.Q (B.subst (up (repl (NFm.owit B)))).full :: Γ.map NFm.shift) A.shift) :
      FOPrf Γ A
  | dICase {n : ℕ} {Γ : List (NFm n)} (B : NFm (n + 2)) (t : Tm n) (hB : B.full = B)
      (h : FOPrf (((B.subst (up (inst t))).subst (inst zero)).full.shift :: Γ.map NFm.shift)
        ((B.subst (up (inst t))).subst (repl (succ (var 0)))).full) :
      FOPrf Γ (.D B)
  | qIInd {n : ℕ} {Γ : List (NFm n)} (s₁ s₂ : Tm (n + 1)) (h₁ : s₁.full = s₁)
      (h₂ : s₂.full = s₂)
      (h : FOPrf (NFm.eq s₁ s₂ :: Γ.map NFm.shift)
        ((NFm.eq s₁ s₂).subst (repl (succ (var 0)))).full) :
      FOPrf Γ (.Q (.eq s₁ s₂))

variable {Γ : List (NFm n)} {A : NFm n}

/-- Every rule is a derived rule of the kernel, up to normal forms. -/
theorem FOPrf.toNPrf (h : FOPrf Γ A) : NPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | refl t => exact NPrf.eqRefl _
  | trOne h _ _ ih₁ ih₂ =>
    exact NPrf.eqTrans (.trOne h ih₁ (NPrf.eqTrans (NPrf.eqFull _) ih₂)) (NPrf.eqFull _)
  | qE t _ _ ih₁ ih₂ => exact (equivFull _).mp (.qE t ih₁ ((equivFull _).mpr ih₂))
  | @dO _ Γ B A _ _ ih₁ ih₂ =>
    exact .dE ih₁ (NPrf.cut1 (NPrf.owitQ B NPrf.hyp0) (NPrf.wkUnder ih₂))
  | dICase B t _ _ ih =>
    exact .dICase B t ((equivFull _).mpr
      (NPrf.cut1 ((equivFull _).shift.mp NPrf.hyp0) (NPrf.wkUnder ih)))
  | qIInd s₁ s₂ _ _ _ ih => exact .qIInd s₁ s₂ ((equivFull _).mpr ih)

/-- Every kernel derivation, under any substitution, becomes a derivation with
the opening at an inferred witness when its formulas are normalized. -/
theorem NPrf.toFO (h : NPrf Γ A) : ∀ {m : ℕ} (σ : Fin n → Tm m),
    FOPrf (Γ.map fun X => (X.subst σ).full) (A.subst σ).full := by
  induction h with
  | hyp h =>
    intro m σ
    exact .hyp (List.mem_map_of_mem (f := fun X => (X.subst σ).full) h)
  | iterZero a h => intro m σ; exact .refl (Syn.subst σ a)
  | iterSucc c a h =>
    intro m σ
    simp only [NFm.subst_eq, NFm.full, Tm.subst_iter, Tm.subst_succ, Syn.subst_subst_inst]
    rw [Tm.full_iterSucc]
    exact .refl _
  | @trOne _ Γ h s t u _ _ ih₁ ih₂ =>
    intro m σ
    have h₁ := ih₁ σ
    have h₂ := ih₂ σ
    simp only [NFm.subst_eq, NFm.full, Syn.subst_subst_inst] at h₁ h₂ ⊢
    have k := FOPrf.trOne (Syn.subst (up σ) h) h₁ (by
      rw [Tm.full_subst_congr rfl (Tm.full_inst (Syn.subst σ s))]
      exact h₂)
    rwa [Tm.full_subst_congr rfl (Tm.full_inst (Syn.subst σ t))] at k
  | @qE _ Γ B t _ _ ih₁ ih₂ =>
    intro m σ
    have h₂ := ih₂ σ
    rw [NFm.subst_inst] at h₂ ⊢
    have k := FOPrf.qE (B := (B.subst (up σ)).full) (Syn.subst σ t) (ih₁ σ) (by
      rw [NFm.full_subst_congr (σ' := inst zero) (NFm.full_idem _) (fun _ => rfl)]
      exact h₂)
    rwa [NFm.full_subst_congr (σ' := inst (Syn.subst σ t)) (NFm.full_idem _)
      (fun _ => rfl)] at k
  | @dE n' Γ B A _ _ ih₁ ih₂ =>
    intro m σ
    refine .dO (B := (B.subst (up (up σ))).full) (ih₁ σ) ?_
    have h₂ := ih₂ fun i =>
      Syn.subst (repl (NFm.owit (B.subst (up (up σ))).full)) (up σ i)
    have e₁ : ∀ X : NFm n', (X.shift.subst fun i =>
          Syn.subst (repl (NFm.owit (B.subst (up (up σ))).full)) (up σ i)).full
        = (X.subst σ).full.shift := by
      intro X
      rw [← NFm.full_shift]
      refine congrArg NFm.full ?_
      unfold NFm.shift
      rw [NFm.subst_subst, NFm.subst_subst]
      refine X.subst_ext fun i => ?_
      simp
      rfl
    have hΓ : (Γ.map NFm.shift).map (fun X => (X.subst fun i =>
          Syn.subst (repl (NFm.owit (B.subst (up (up σ))).full)) (up σ i)).full)
        = (Γ.map fun X => (X.subst σ).full).map NFm.shift := by
      rw [List.map_map, List.map_map]
      exact List.map_congr_left fun X _ => e₁ X
    have hB : ((NFm.Q B).subst fun i =>
          Syn.subst (repl (NFm.owit (B.subst (up (up σ))).full)) (up σ i)).full
        = .Q ((B.subst (up (up σ))).full.subst
            (up (repl (NFm.owit (B.subst (up (up σ))).full)))).full := by
      show NFm.Q (B.subst (up _)).full = _
      rw [NFm.full_subst_congr (A' := B.subst (up (up σ)))
        (σ' := up (repl (NFm.owit (B.subst (up (up σ))).full))) (NFm.full_idem _)
        (fun _ => rfl), NFm.subst_subst, Syn.up_comp]
    simp only [List.map_cons] at h₂
    rw [hΓ, hB, e₁] at h₂
    exact h₂
  | @dICase _ Γ B t _ ih =>
    intro m σ
    have h := ih (up σ)
    refine .dICase (B.subst (up (up σ))).full (Syn.subst σ t) (NFm.full_idem _) ?_
    have e : ∀ {k : ℕ} (ρ : Fin (m + 1) → Tm k),
        (((B.subst (up (up σ))).full.subst (up (inst (Syn.subst σ t)))).subst ρ).full
          = (((B.subst (up (up σ))).subst (up (inst (Syn.subst σ t)))).subst ρ).full :=
      fun ρ => NFm.full_subst_congr
        (NFm.full_subst_congr (NFm.full_idem _) fun _ => rfl) fun _ => rfl
    rw [e, e]
    simp only [List.map_cons] at h
    rw [NFm.map_shift_subst_full, NFm.shift_subst_up, NFm.full_shift, NFm.subst_inst,
      NFm.subst_repl_succ, NFm.subst_up_inst] at h
    exact h
  | @qIInd _ Γ s₁ s₂ _ ih =>
    intro m σ
    have h := ih (up σ)
    refine .qIInd (Syn.subst (up σ) s₁).full (Syn.subst (up σ) s₂).full (Tm.full_idem _)
      (Tm.full_idem _) ?_
    simp only [List.map_cons] at h
    rw [NFm.map_shift_subst_full, NFm.subst_repl_succ] at h
    rw [NFm.full_subst_congr (A' := (NFm.eq s₁ s₂).subst (up σ))
      (σ' := repl (succ (Syn.var 0))) (by simp only [NFm.subst_eq, NFm.full, Tm.full_idem])
      (fun _ => rfl)]
    exact h

/-- **Opening with an inferred witness.**  The kernel derives a sequent exactly
when the calculus on full normal forms with that opening in place of `DE`
derives its full normal form. -/
theorem foprf_iff_nprf : FOPrf (Γ.map NFm.full) A.full ↔ NPrf Γ A := by
  constructor
  · intro h
    refine (equivFull A).mpr (h.toNPrf.cut fun B hB => ?_)
    obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hB
    exact (equivFull C).mp (.hyp hC)
  · intro h
    have k := h.toFO Syn.var
    rw [NFm.subst_id, List.map_congr_left (g := NFm.full)
      (fun X _ => by rw [NFm.subst_id])] at k
    exact k

end LeanProofs.ConciseIPRA
