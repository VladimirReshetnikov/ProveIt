import ConciseIPRA.NativeVariableQE
import ConciseIPRA.NativeWitnessShape

/-!
# Introduction at a variable, and a name for every term

`DNPrf` is the kernel in which the introduction of `D` by cases takes no
term: its witness is a variable (`dIVar`).  In exchange there is one axiom
scheme, *every term has a name* (`name`):

  `D_{x,y} (sel(y, a, x) = a)`

for every term `a`.  Opened at a fresh `b` and used at `y = 1`, that formula
gives `b = a`.  This is the naming matrix of the package
`deterministic_introduction`, in the form of the alias matrix `NFm.aliasM` of
`NativeParameter`.

* `dnprf_iff_nprf : DNPrf Γ A ↔ NPrf Γ A`.

The introduction at an arbitrary term `t` is recovered as in the package:
name `t` by a fresh variable `b`, introduce at `b`, and move the two
instances of the matrix between `b` and `t` by the Leibniz rule
(`DNPrf.dIEq`, `DNPrf.dICase`).  The calculus is closed under renaming, not
under substitution, so the Leibniz rule is proved for the derivability of two
instances over one context, without substitution into a derivation
(`DNPrf.leibniz`).  The introduction of `Q` by cases for a compound matrix
needs a dummy witness; in a scope without variables it is the variable that a
name of `0` provides (`DNPrf.qI`).

Without the axiom the introduction at variables is incomplete, and so is the
introduction at the literal `0` (`NativeWitnessShape`).  For the calculus
`DWPrf z true` of that module, with variables (and `0` if `z`) as witnesses
and no axiom, completeness is exactly the derivability of the names
(`dwprf_complete_iff_names`).  The package selects
the variable deterministically (the newest parameter, or `0` in an empty
scope, with priority for a literal naming matrix); that refinement is not
formalized here.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open Tm (zero succ iter)

variable {n m k : ℕ}

theorem NFm.aliasM_subst (a : Tm n) (σ : Fin n → Tm m) :
    (NFm.aliasM a).subst (up (up σ)) = NFm.aliasM (Syn.subst σ a) := by
  simp [NFm.aliasM, Syn.subst_up_shift]

/-- The kernel with the introduction at a variable and a name for every
term. -/
inductive DNPrf : {n : ℕ} → List (NFm n) → NFm n → Prop
  | hyp {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (h : A ∈ Γ) : DNPrf Γ A
  | iterZero {n : ℕ} {Γ : List (NFm n)} (a : Tm n) (h : Tm (n + 1)) :
      DNPrf Γ (.eq (iter zero a h) a)
  | iterSucc {n : ℕ} {Γ : List (NFm n)} (c a : Tm n) (h : Tm (n + 1)) :
      DNPrf Γ (.eq (iter (succ c) a h) (Syn.subst (inst (iter c a h)) h))
  | trOne {n : ℕ} {Γ : List (NFm n)} (h : Tm (n + 1)) {s t u : Tm n}
      (h₁ : DNPrf Γ (.eq s t)) (h₂ : DNPrf Γ (.eq (Syn.subst (inst s) h) u)) :
      DNPrf Γ (.eq u (Syn.subst (inst t) h))
  | qE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 1)} (t : Tm n)
      (h₁ : DNPrf Γ (.Q B)) (h₂ : DNPrf Γ (B.subst (inst zero))) : DNPrf Γ (B.subst (inst t))
  | dE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 2)} {A : NFm n}
      (h₁ : DNPrf Γ (.D B)) (h₂ : DNPrf (.Q B :: Γ.map NFm.shift) A.shift) : DNPrf Γ A
  /-- Every term has a name. -/
  | name {n : ℕ} {Γ : List (NFm n)} (a : Tm n) : DNPrf Γ (.D (NFm.aliasM a))
  /-- DI by cases at a variable. -/
  | dIVar {n : ℕ} {Γ : List (NFm n)} (B : NFm (n + 2)) (i : Fin n)
      (h : DNPrf (((B.subst (up (inst (var i)))).subst (inst zero)).shift :: Γ.map NFm.shift)
        ((B.subst (up (inst (var i)))).subst (repl (succ (var 0))))) :
      DNPrf Γ (.D B)
  | qIInd {n : ℕ} {Γ : List (NFm n)} (s₁ s₂ : Tm (n + 1))
      (h : DNPrf (NFm.eq s₁ s₂ :: Γ.map NFm.shift)
        ((NFm.eq s₁ s₂).subst (repl (succ (var 0))))) :
      DNPrf Γ (.Q (.eq s₁ s₂))

namespace DNPrf

variable {Γ Δ : List (NFm n)} {A : NFm n}

theorem selSucc (c a b : Tm n) : DNPrf Γ (.eq (Tm.sel (succ c) a b) b) := by
  have h := DNPrf.iterSucc (Γ := Γ) c a (Syn.shift b)
  rwa [Syn.subst_inst_shift] at h

theorem toNPrf (h : DNPrf Γ A) : NPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | trOne h _ _ ih₁ ih₂ => exact .trOne h ih₁ ih₂
  | qE t _ _ ih₁ ih₂ => exact .qE t ih₁ ih₂
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | name a =>
    refine .dICase _ a ?_
    rw [NFm.aliasM_step]
    exact NPrf.selSucc _ _ _
  | dIVar B i _ ih => exact .dICase B _ ih
  | qIInd s₁ s₂ _ ih => exact .qIInd s₁ s₂ ih

theorem hyp0 : DNPrf (A :: Γ) A := .hyp List.mem_cons_self

theorem weaken (h : DNPrf Γ A) : ∀ {Δ : List (NFm n)}, Γ ⊆ Δ → DNPrf Δ A := by
  induction h with intro Δ s
  | hyp h => exact .hyp (s h)
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | trOne h _ _ ih₁ ih₂ => exact .trOne h (ih₁ s) (ih₂ s)
  | qE t _ _ ih₁ ih₂ => exact .qE t (ih₁ s) (ih₂ s)
  | dE _ _ ih₁ ih₂ => exact .dE (ih₁ s) (ih₂ (List.cons_subset_cons _ (List.map_subset _ s)))
  | name a => exact .name a
  | dIVar B i _ ih => exact .dIVar B i (ih (List.cons_subset_cons _ (List.map_subset _ s)))
  | qIInd s₁ s₂ _ ih =>
    exact .qIInd s₁ s₂ (ih (List.cons_subset_cons _ (List.map_subset _ s)))

theorem wk {B : NFm n} (h : DNPrf Γ A) : DNPrf (B :: Γ) A :=
  h.weaken (List.subset_cons_self _ _)

/-- Renaming of the free variables of a derivation. -/
theorem ren (h : DNPrf Γ A) : ∀ {m : ℕ} (ξ : Fin n → Fin m),
    DNPrf (Γ.map fun B => B.subst fun i => (Syn.var (ξ i) : Tm m))
      (A.subst fun i => (Syn.var (ξ i) : Tm m)) := by
  induction h with intro m ξ
  | hyp h => exact .hyp (List.mem_map_of_mem h)
  | iterZero a h => exact .iterZero _ _
  | iterSucc c a h =>
    simp only [NFm.subst_eq, Tm.subst_iter, Tm.subst_succ, Syn.subst_subst_inst]
    exact .iterSucc _ _ _
  | trOne h _ _ ih₁ ih₂ =>
    have h₂ := ih₂ ξ
    simp only [NFm.subst_eq, Syn.subst_subst_inst] at h₂ ⊢
    exact .trOne _ (ih₁ ξ) h₂
  | qE t _ _ ih₁ ih₂ =>
    have h₂ := ih₂ ξ
    rw [NFm.subst_inst] at h₂ ⊢
    exact .qE _ (ih₁ ξ) h₂
  | dE _ _ ih₁ ih₂ =>
    have h := ih₂ (Tm.upRen ξ)
    rw [← Tm.up_rn, List.map_cons, NFm.map_shift_subst, NFm.shift_subst_up] at h
    exact .dE (ih₁ ξ) h
  | name a =>
    rw [NFm.subst_D, NFm.aliasM_subst]
    exact .name _
  | dIVar B i _ ih =>
    have h := ih (Tm.upRen ξ)
    rw [← Tm.up_rn, List.map_cons, NFm.map_shift_subst, NFm.shift_subst_up, NFm.subst_inst,
      NFm.subst_repl_succ, NFm.subst_up_inst] at h
    exact .dIVar _ (ξ i) h
  | qIInd s₁ s₂ _ ih =>
    have h := ih (Tm.upRen ξ)
    rw [← Tm.up_rn, List.map_cons, NFm.map_shift_subst, NFm.subst_repl_succ] at h
    exact .qIInd _ _ h

theorem shift (h : DNPrf Γ A) : DNPrf (Γ.map NFm.shift) A.shift := h.ren Fin.succ

theorem cutLift (h : ∀ B ∈ Γ, DNPrf Δ B) (C : NFm (n + 1)) :
    ∀ B ∈ C :: Γ.map NFm.shift, DNPrf (C :: Δ.map NFm.shift) B := by
  intro B hB
  rcases List.mem_cons.1 hB with rfl | hB
  · exact hyp0
  · obtain ⟨B₀, hB₀, rfl⟩ := List.mem_map.1 hB
    exact (h B₀ hB₀).shift.wk

theorem cut (h : DNPrf Γ A) : ∀ {Δ : List (NFm n)}, (∀ B ∈ Γ, DNPrf Δ B) → DNPrf Δ A := by
  induction h with intro Δ hΔ
  | hyp h => exact hΔ _ h
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | trOne h _ _ ih₁ ih₂ => exact .trOne h (ih₁ hΔ) (ih₂ hΔ)
  | qE t _ _ ih₁ ih₂ => exact .qE t (ih₁ hΔ) (ih₂ hΔ)
  | dE _ _ ih₁ ih₂ => exact .dE (ih₁ hΔ) (ih₂ (cutLift hΔ _))
  | name a => exact .name a
  | dIVar B i _ ih => exact .dIVar B i (ih (cutLift hΔ _))
  | qIInd s₁ s₂ _ ih => exact .qIInd s₁ s₂ (ih (cutLift hΔ _))

/-! ### Equality -/

theorem eqRefl (t : Tm n) : DNPrf Γ (.eq t t) :=
  .trOne (Syn.var 0) (.iterZero t (Syn.var 0)) (.iterZero t (Syn.var 0))

theorem eqSymm {s t : Tm n} (h : DNPrf Γ (.eq s t)) : DNPrf Γ (.eq t s) :=
  .trOne (Syn.var 0) (eqRefl s) h

/-- Transport in an equation template, with the template and its two instances
named. -/
theorem trE {a b : Tm (n + 1)} (H : NFm (n + 1)) (hH : H = .eq a b) {s t : Tm n}
    {A A' : NFm n} (h₁ : DNPrf Γ (.eq s t)) (hA : H.subst (inst s) = A)
    (hA' : H.subst (inst t) = A') (h₂ : DNPrf Γ A) : DNPrf Γ A' := by
  subst hH hA hA'
  exact .trOne b h₁ (.trOne a h₁ h₂)

/-- The simultaneous Leibniz rule for an equation. -/
theorem leibnizEq (a b : Tm k) (σ σ' : Fin k → Tm n)
    (he : ∀ i, DNPrf Γ (.eq (σ i) (σ' i)))
    (h : DNPrf Γ ((NFm.eq a b).subst σ)) : DNPrf Γ ((NFm.eq a b).subst σ') := by
  have key : ∀ j, j ≤ k →
      DNPrf Γ ((NFm.eq a b).subst fun i => if i.val < j then σ' i else σ i) := by
    intro j
    induction j with
    | zero => intro _; simpa using h
    | succ j ih =>
      intro hj
      have hj' := ih (Nat.le_of_succ_le hj)
      refine trE ((NFm.eq a b).subst fun i => if i.val = j then Syn.var 0
          else Syn.shift (if i.val < j then σ' i else σ i)) rfl (he ⟨j, hj⟩) ?_ ?_ hj'
      · rw [NFm.subst_subst]
        refine NFm.subst_ext _ fun i => ?_
        by_cases hi : i.val = j
        · subst hi; simp
        · simp [hi]
      · rw [NFm.subst_subst]
        refine NFm.subst_ext _ fun i => ?_
        by_cases hi : i.val = j
        · subst hi; simp
        · have hlt : i.val < j + 1 ↔ i.val < j := by omega
          simp [hi, hlt]
  have h' := key k le_rfl
  simpa using h'

/-- Equal substitutions stay equal under a binder. -/
theorem upEq {σ σ' : Fin k → Tm n} (he : ∀ i, DNPrf Γ (.eq (σ i) (σ' i))) :
    ∀ i, DNPrf (Γ.map NFm.shift) (.eq (up σ i) (up σ' i)) := by
  refine Fin.cases ?_ fun j => ?_
  · exact eqRefl _
  · rw [up_succ, up_succ]
    exact (he j).shift

/-- Equal substitutions extended by equal terms. -/
theorem casesEq {σ σ' : Fin k → Tm n} {s s' : Tm n} (h : DNPrf Γ (.eq s s'))
    (he : ∀ i, DNPrf Γ (.eq (σ i) (σ' i))) :
    ∀ i, DNPrf Γ (.eq ((Fin.cases s σ : Fin (k + 1) → Tm n) i)
      ((Fin.cases s' σ' : Fin (k + 1) → Tm n) i)) := by
  refine Fin.cases ?_ fun j => ?_
  · exact h
  · simpa only [Fin.cases_succ] using he j

/-! ### The name of a term, and `Q` by cases -/

/-- **The fresh alias.**  An assumption `b = a` with `b` fresh may be
discharged: `b` is the name of `a`. -/
theorem aliasE (a : Tm n)
    (h : DNPrf (.eq (Syn.var 0) (Syn.shift a) :: Γ.map NFm.shift) A.shift) : DNPrf Γ A := by
  refine .dE (.name a) ?_
  have k : DNPrf (.Q (NFm.aliasM a) :: Γ.map NFm.shift)
      ((NFm.aliasM a).subst (inst (succ zero))) := by
    refine .qE (succ zero) hyp0 ?_
    rw [NFm.aliasM_inst]
    exact .iterZero _ _
  rw [NFm.aliasM_inst] at k
  refine h.cut fun C hC => ?_
  rcases List.mem_cons.1 hC with rfl | hC
  · exact .trOne (Syn.var 0) k (selSucc zero _ _)
  · exact .hyp (List.mem_cons_of_mem _ hC)

/-- Introduction of `Q` by cases.  The auxiliary `D` has a dummy witness: the
variable that a name of `0` provides. -/
theorem qI (B : NFm (n + 1))
    (h : DNPrf ((B.subst (inst zero)).shift :: Γ.map NFm.shift)
      (B.subst (repl (succ (Syn.var 0))))) : DNPrf Γ (.Q B) := by
  refine .dE (.name zero) ?_
  have hD : DNPrf (.Q (NFm.aliasM zero) :: Γ.map NFm.shift)
      (.D ((B.subst (up fun i => Syn.var i.succ)).subst (up fun i => Syn.var i.succ))) := by
    refine .dIVar _ 0 ?_
    rw [NFm.subst_dummy_inst]
    have h' := h.ren (Tm.upRen Fin.succ)
    rw [← Tm.up_rn, List.map_cons, NFm.map_shift_subst, NFm.shift_subst_up, NFm.subst_inst,
      NFm.subst_repl_succ] at h'
    exact h'.weaken (List.cons_subset_cons _ (List.map_subset _ (List.subset_cons_self _ _)))
  refine .dE hD ?_
  exact hyp0

/-! ### The Leibniz rule -/

/-- `QE` for the matrix `B` with a change of the parameters, from the Leibniz
rule for `B`. -/
theorem qELeib {B : NFm (k + 1)}
    (ih : ∀ {n : ℕ} {Γ : List (NFm n)} (σ σ' : Fin (k + 1) → Tm n),
      (∀ i, DNPrf Γ (.eq (σ i) (σ' i))) → DNPrf Γ (B.subst σ) → DNPrf Γ (B.subst σ'))
    {ρ ρ' : Fin k → Tm n} (he : ∀ i, DNPrf Γ (.eq (ρ i) (ρ' i))) (t : Tm n)
    (hQ : DNPrf Γ (.Q (B.subst (up ρ))))
    (h0 : DNPrf Γ (B.subst (Fin.cases zero ρ'))) :
    DNPrf Γ (B.subst (Fin.cases t ρ')) := by
  have base := ih _ _ (casesEq (eqRefl zero) fun i => eqSymm (he i)) h0
  have hv := DNPrf.qE t hQ (by rw [NFm.subst_up_cases]; exact base)
  rw [NFm.subst_up_cases] at hv
  exact ih _ _ (casesEq (eqRefl t) he) hv

/-- **The simultaneous Leibniz rule**, for the derivability of two instances
over one context. -/
theorem leibniz (A : NFm k) : ∀ {n : ℕ} {Γ : List (NFm n)} (σ σ' : Fin k → Tm n),
    (∀ i, DNPrf Γ (.eq (σ i) (σ' i))) → DNPrf Γ (A.subst σ) → DNPrf Γ (A.subst σ') := by
  induction A with intro n Γ σ σ' he h
  | eq a b => exact leibnizEq a b σ σ' he h
  | Q B ih =>
    rw [NFm.subst_Q] at h ⊢
    refine qI _ ?_
    rw [NFm.subst_up_repl, NFm.shift_subst_up_zero]
    refine qELeib ih (ρ := fun i => Syn.shift (σ i)) (fun i => (he i).shift.wk)
      (succ (Syn.var 0)) ?_ hyp0
    rw [← NFm.shift_Q_up]
    exact h.shift.wk
  | D B ih =>
    rw [NFm.subst_D] at h ⊢
    refine .dE h ?_
    show DNPrf _ (.D ((B.subst (up (up σ'))).subst (up (up fun i => Syn.var i.succ))))
    refine .dIVar _ 0 ?_
    rw [NFm.subst_upup_inst_var, NFm.subst_up_repl, NFm.shift_subst_up_zero]
    refine qELeib ih (ρ := fun i => Syn.shift (up σ i))
      (fun i => ((upEq he i).wk).shift.wk) (succ (Syn.var 0)) ?_ hyp0
    rw [← NFm.shift_Q_up]
    exact .hyp (List.mem_cons_of_mem _ (List.mem_map_of_mem List.mem_cons_self))

/-! ### The introduction at an arbitrary term -/

/-- DI by cases at a term that a variable names. -/
theorem dIEq (B : NFm (n + 2)) (i : Fin n) {t : Tm n} (e : DNPrf Γ (.eq (Syn.var i) t))
    (h : DNPrf (((B.subst (up (inst t))).subst (inst zero)).shift :: Γ.map NFm.shift)
      ((B.subst (up (inst t))).subst (repl (succ (Syn.var 0))))) : DNPrf Γ (.D B) := by
  refine .dIVar B i ?_
  rw [NFm.subst_up_repl, NFm.shift_subst_up_zero] at h ⊢
  have he : ∀ (X : NFm (n + 1)) (j : Fin (n + 1)), DNPrf (X :: Γ.map NFm.shift)
      (.eq (Syn.shift (inst (Syn.var i) j)) (Syn.shift (inst t j))) := by
    intro X
    refine Fin.cases ?_ fun j => ?_
    · exact e.shift.wk
    · exact eqRefl _
  have h0 := leibniz B _ _ (casesEq (eqRefl zero) (he _)) hyp0
  have h1 := h.cut fun C hC => by
    rcases List.mem_cons.1 hC with rfl | hC
    · exact h0
    · exact .hyp (List.mem_cons_of_mem _ hC)
  exact leibniz B _ _ (casesEq (eqRefl _) fun j => eqSymm (he _ j)) h1

/-- **DI by cases at an arbitrary term**: name the term by a fresh variable
and introduce at that variable. -/
theorem dICase (B : NFm (n + 2)) (t : Tm n)
    (h : DNPrf (((B.subst (up (inst t))).subst (inst zero)).shift :: Γ.map NFm.shift)
      ((B.subst (up (inst t))).subst (repl (succ (Syn.var 0))))) : DNPrf Γ (.D B) := by
  refine aliasE t ?_
  show DNPrf _ (.D (B.subst (up (up fun i => Syn.var i.succ))))
  refine dIEq _ 0 hyp0 ?_
  have h' := h.ren (Tm.upRen Fin.succ)
  rw [← Tm.up_rn, List.map_cons, NFm.map_shift_subst, NFm.shift_subst_up, NFm.subst_inst,
    NFm.subst_repl_succ, NFm.subst_up_inst] at h'
  exact h'.weaken (List.cons_subset_cons _ (List.map_subset _ (List.subset_cons_self _ _)))

end DNPrf

variable {Γ : List (NFm n)} {A : NFm n}

theorem NPrf.toDNPrf (h : NPrf Γ A) : DNPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | trOne h _ _ ih₁ ih₂ => exact .trOne h ih₁ ih₂
  | qE t _ _ ih₁ ih₂ => exact .qE t ih₁ ih₂
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dICase B t _ ih => exact DNPrf.dICase B t ih
  | qIInd s₁ s₂ _ ih => exact .qIInd s₁ s₂ ih

/-- **The introduction at a variable is enough, given a name for every
term.** -/
theorem dnprf_iff_nprf : DNPrf Γ A ↔ NPrf Γ A := ⟨DNPrf.toNPrf, NPrf.toDNPrf⟩

/-- A derivation with the naming scheme, in the calculus with variables as
witnesses, once that calculus derives the names. -/
theorem DNPrf.toDW {z : Bool}
    (hN : ∀ {n : ℕ} (Γ : List (NFm n)) (a : Tm n), DWPrf z true Γ (.D (NFm.aliasM a)))
    (h : DNPrf Γ A) : DWPrf z true Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | trOne h _ _ ih₁ ih₂ => exact .trOne h ih₁ ih₂
  | qE t _ _ ih₁ ih₂ => exact .qE t ih₁ ih₂
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | name a => exact hN _ a
  | dIVar B i _ ih => exact .dICase B (Syn.var i) (show true = true from rfl) ih
  | qIInd s₁ s₂ _ ih => exact .qIInd s₁ s₂ ih

/-- **Without the naming scheme, the introduction at a variable (and at `0`
if `z`) is complete exactly when it derives a name for every term.** -/
theorem dwprf_complete_iff_names (z : Bool) :
    (∀ {n : ℕ} (Γ : List (NFm n)) (A : NFm n), DWPrf z true Γ A ↔ NPrf Γ A)
      ↔ ∀ {n : ℕ} (Γ : List (NFm n)) (a : Tm n), DWPrf z true Γ (.D (NFm.aliasM a)) :=
  ⟨fun h {_} Γ a => (h Γ _).2 (DNPrf.name a).toNPrf,
    fun hN {_} _ _ => ⟨DWPrf.toNPrf, fun h => (NPrf.toDNPrf h).toDW hN⟩⟩

end LeanProofs.ConciseIPRA
