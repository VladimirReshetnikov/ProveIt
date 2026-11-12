import ConciseIPRA.NativeProgressiveRules

/-!
# The Leibniz rule in the uniform calculus

Transport along an equation is primitive in `RPrf` for equations only.  This
module derives it for every formula: substitutions that are provably equal
give interderivable instances (`RPrf.leibnizIn`, `RPrf.leibniz`, `RPrf.tr`).

The proof is by induction on the formula, as for the kernel (`NativeEq`), with
congruence rules for `Q` and `D` over a context.  The two readings of a binder
need two arguments.

* At a compound matrix the binder is the conditional closure.  Its
  elimination gives the instance at `I(0, c; v.S v)`, not at `c`; the redex is
  removed by the Leibniz rule for the matrix, which is the induction
  hypothesis (`REquivIn.red`).
* At a literal equation the binder is progressivity.  One step from `E(z)` is
  the elimination with the source `z` and the initializer `1`, which gives
  `E(I(z, 1; v.S v))`, and `I(z, 1; v.S v) = S z` (`RPrf.addOne`).
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm
open Tm (zero succ iter)

variable {n m k : ℕ}

namespace NFm

theorem eta_of_eq {k : ℕ} {B : NFm k} (h : B.isEq = true) (a : Tm n) : eta B a = a := by
  simp [eta, h]

theorem eta_of_ne {k : ℕ} {B : NFm k} (h : B.isEq = false) (a : Tm n) : eta B a = zero := by
  simp [eta, h]

end NFm

/-- Interderivability of two formulas over a context, in the uniform
calculus. -/
def REquivIn (Γ : List (NFm n)) (A B : NFm n) : Prop := RPrf (A :: Γ) B ∧ RPrf (B :: Γ) A

namespace RPrf

variable {Γ : List (NFm n)}

/-- Transport in a template that is a literal equation. -/
theorem trF (H : NFm (n + 1)) (hH : H.isEq = true) {s t : Tm n} (h₁ : RPrf Γ (.eq s t))
    (h₂ : RPrf Γ (H.subst (inst s))) : RPrf Γ (H.subst (inst t)) := by
  cases H with
  | eq a b => exact .trEq a b h₁ h₂
  | Q B => cases hH
  | D B => cases hH

/-- Introduction of `Q` at a compound matrix, by cases. -/
theorem qIC (B : NFm (n + 1)) (hB : B.isEq = false)
    (h : RPrf ((B.subst (inst zero)).shift :: Γ.map NFm.shift)
      (B.subst (repl (succ (Syn.var 0))))) : RPrf Γ (.Q B) := by
  have hD : RPrf Γ (.D (B.subst (up fun i => Syn.var i.succ))) := by
    refine .dI _ zero ?_
    rw [NFm.subst_dummy_inst,
      NFm.eta_of_ne (B := B.subst (up fun i => Syn.var i.succ))
        (by rw [NFm.isEq_subst]; exact hB), ← NFm.shift_subst_inst_zero]
    exact h
  refine .dE hD ?_
  show RPrf (.Q (B.subst (up fun i => Syn.var i.succ)) :: Γ.map NFm.shift)
    (.Q (B.subst (up fun i => Syn.var i.succ)))
  exact hyp0

/-- Introduction of `Q` at a literal equation, by progress. -/
theorem qIE (B : NFm (n + 1)) (hB : B.isEq = true)
    (h : RPrf (B :: Γ.map NFm.shift) (B.subst (repl (succ (Syn.var 0))))) : RPrf Γ (.Q B) := by
  have hD : RPrf Γ (.D (B.subst (up fun i => Syn.var i.succ))) := by
    refine .dI _ zero ?_
    rw [NFm.subst_dummy_inst,
      NFm.eta_of_eq (B := B.subst (up fun i => Syn.var i.succ))
        (by rw [NFm.isEq_subst]; exact hB), NFm.subst_repl_var]
    exact h
  refine .dE hD ?_
  show RPrf (.Q (B.subst (up fun i => Syn.var i.succ)) :: Γ.map NFm.shift)
    (.Q (B.subst (up fun i => Syn.var i.succ)))
  exact hyp0

end RPrf

namespace REquivIn

variable {Γ : List (NFm n)} {A B : NFm n}

theorem symm (e : REquivIn Γ A B) : REquivIn Γ B A := ⟨e.2, e.1⟩

theorem mp (e : REquivIn Γ A B) {Δ : List (NFm n)} (hΔ : Γ ⊆ Δ) (h : RPrf Δ A) : RPrf Δ B :=
  .cut1 h (e.1.weaken (List.cons_subset_cons _ hΔ))

theorem mpr (e : REquivIn Γ A B) {Δ : List (NFm n)} (hΔ : Γ ⊆ Δ) (h : RPrf Δ B) : RPrf Δ A :=
  e.symm.mp hΔ h

/-- Replacement of the bound variable, over a context that does not mention
it. -/
theorem substRepl {B B' : NFm (n + 1)} (e : REquivIn (Γ.map NFm.shift) B B') (c : Tm (n + 1)) :
    REquivIn (Γ.map NFm.shift) (B.subst (repl c)) (B'.subst (repl c)) := by
  have h₁ := e.1.subst (repl c)
  have h₂ := e.2.subst (repl c)
  rw [List.map_cons, NFm.map_shift_subst_repl] at h₁ h₂
  exact ⟨h₁, h₂⟩

/-- The step of the congruence rules at compound matrices. -/
theorem qStepC {B B' : NFm (n + 1)} (hB : B.isEq = false)
    (e : REquivIn (Γ.map NFm.shift) B B')
    (r : ∀ {Δ : List (NFm (n + 1))} (c : Tm (n + 1)),
      RPrf Δ (B.subst (repl (Tm.add c zero))) → RPrf Δ (B.subst (repl c)))
    {Δ : List (NFm (n + 1))} (hΔ : Γ.map NFm.shift ⊆ Δ) :
    RPrf ((B'.subst (inst zero)).shift :: (NFm.Q B).shift :: Δ)
      (B'.subst (repl (succ (Syn.var 0)))) := by
  have hΔ' : ∀ X Y : NFm (n + 1), Γ.map NFm.shift ⊆ X :: Y :: Δ := fun _ _ _ hA =>
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hΔ hA))
  have hBu : (B.subst (up fun i => Syn.var i.succ)).isEq = false := by
    rw [NFm.isEq_subst]; exact hB
  have h0 : RPrf ((B'.subst (inst zero)).shift :: (NFm.Q B).shift :: Δ)
      ((B.subst (up fun i => Syn.var i.succ)).subst
        (inst (NFm.eta (B.subst (up fun i => Syn.var i.succ)) (zero : Tm (n + 1))))) := by
    rw [NFm.eta_of_ne hBu, NFm.subst_dummy_up_inst, NFm.shift_subst_inst_zero]
    exact (e.substRepl zero).mpr (hΔ' _ _) RPrf.hyp0
  have hQ : RPrf ((B'.subst (inst zero)).shift :: (NFm.Q B).shift :: Δ)
      (.Q (B.subst (up fun i => Syn.var i.succ))) :=
    .hyp (List.mem_cons_of_mem _ List.mem_cons_self)
  have q := RPrf.qE zero (succ (Syn.var 0)) hQ h0
  rw [NFm.eta_of_ne hBu, NFm.subst_dummy_up_inst] at q
  exact (e.substRepl _).mp (hΔ' _ _) (r _ q)

/-- The step of the congruence rules at literal equations. -/
theorem qStepE {B B' : NFm (n + 1)} (hB : B.isEq = true)
    (e : REquivIn (Γ.map NFm.shift) B B') {Δ : List (NFm (n + 1))}
    (hΔ : Γ.map NFm.shift ⊆ Δ) :
    RPrf (B' :: (NFm.Q B).shift :: Δ) (B'.subst (repl (succ (Syn.var 0)))) := by
  have hΔ' : ∀ X Y : NFm (n + 1), Γ.map NFm.shift ⊆ X :: Y :: Δ := fun _ _ _ hA =>
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hΔ hA))
  have hBu : (B.subst (up fun i => Syn.var i.succ)).isEq = true := by
    rw [NFm.isEq_subst]; exact hB
  have h0 : RPrf (B' :: (NFm.Q B).shift :: Δ)
      ((B.subst (up fun i => Syn.var i.succ)).subst
        (inst (NFm.eta (B.subst (up fun i => Syn.var i.succ)) (Syn.var 0 : Tm (n + 1))))) := by
    rw [NFm.eta_of_eq hBu, NFm.subst_up_inst_var]
    exact e.mpr (hΔ' _ _) RPrf.hyp0
  have hQ : RPrf (B' :: (NFm.Q B).shift :: Δ) (.Q (B.subst (up fun i => Syn.var i.succ))) :=
    .hyp (List.mem_cons_of_mem _ List.mem_cons_self)
  have q := RPrf.qE (Syn.var 0) (succ zero) hQ h0
  rw [NFm.eta_of_eq hBu] at q
  have q' := RPrf.trF (B.subst (up fun i => Syn.var i.succ)) hBu (RPrf.addOne (Syn.var 0)) q
  rw [NFm.subst_dummy_up_inst] at q'
  exact (e.substRepl _).mp (hΔ' _ _) q'

/-- `Q` respects interderivability of compound matrices. -/
theorem QC {B B' : NFm (n + 1)} (hB : B.isEq = false) (hB' : B'.isEq = false)
    (e : REquivIn (Γ.map NFm.shift) B B')
    (r : ∀ {Δ : List (NFm (n + 1))} (c : Tm (n + 1)),
      RPrf Δ (B.subst (repl (Tm.add c zero))) → RPrf Δ (B.subst (repl c)))
    (r' : ∀ {Δ : List (NFm (n + 1))} (c : Tm (n + 1)),
      RPrf Δ (B'.subst (repl (Tm.add c zero))) → RPrf Δ (B'.subst (repl c))) :
    REquivIn Γ (.Q B) (.Q B') :=
  ⟨RPrf.qIC _ hB' (qStepC hB e r (List.Subset.refl _)),
    RPrf.qIC _ hB (qStepC hB' e.symm r' (List.Subset.refl _))⟩

/-- `Q` respects interderivability of literal equations. -/
theorem QE {B B' : NFm (n + 1)} (hB : B.isEq = true) (hB' : B'.isEq = true)
    (e : REquivIn (Γ.map NFm.shift) B B') : REquivIn Γ (.Q B) (.Q B') :=
  ⟨RPrf.qIE _ hB' (qStepE hB e (List.Subset.refl _)),
    RPrf.qIE _ hB (qStepE hB' e.symm (List.Subset.refl _))⟩

theorem dStepC {B B' : NFm (n + 2)} (hB : B.isEq = false) (hB' : B'.isEq = false)
    (e : REquivIn ((Γ.map NFm.shift).map NFm.shift) B B')
    (r : ∀ {Δ : List (NFm (n + 2))} (c : Tm (n + 2)),
      RPrf Δ (B.subst (repl (Tm.add c zero))) → RPrf Δ (B.subst (repl c))) :
    RPrf (.D B :: Γ) (.D B') := by
  refine .dE RPrf.hyp0 ?_
  show RPrf _ (.D (B'.subst (up (up fun i => Syn.var i.succ))))
  refine .dI _ (Syn.var 0) ?_
  rw [NFm.subst_upup_inst_var,
    NFm.eta_of_ne (B := B'.subst (up (up fun i => Syn.var i.succ)))
      (by rw [NFm.isEq_subst]; exact hB'), ← NFm.shift_subst_inst_zero]
  exact qStepC hB e r (List.map_subset _ (List.map_subset _ (List.subset_cons_self _ _)))

theorem dStepE {B B' : NFm (n + 2)} (hB : B.isEq = true) (hB' : B'.isEq = true)
    (e : REquivIn ((Γ.map NFm.shift).map NFm.shift) B B') : RPrf (.D B :: Γ) (.D B') := by
  refine .dE RPrf.hyp0 ?_
  show RPrf _ (.D (B'.subst (up (up fun i => Syn.var i.succ))))
  refine .dI _ (Syn.var 0) ?_
  rw [NFm.subst_upup_inst_var,
    NFm.eta_of_eq (B := B'.subst (up (up fun i => Syn.var i.succ)))
      (by rw [NFm.isEq_subst]; exact hB'), NFm.subst_repl_var]
  exact qStepE hB e (List.map_subset _ (List.map_subset _ (List.subset_cons_self _ _)))

/-- Removal of the redex `I(0, c; v.S v)` in the bound variable of a matrix
whose instances obey the Leibniz rule. -/
theorem red {j p : ℕ} {C : NFm (j + 1)}
    (L : ∀ {q : ℕ} {Γ : List (NFm q)} (σ σ' : Fin (j + 1) → Tm q),
      (∀ i, RPrf Γ (.eq (σ i) (σ' i))) → REquivIn Γ (C.subst σ) (C.subst σ'))
    (τ : Fin j → Tm p) {Δ : List (NFm (p + 1))} (c : Tm (p + 1))
    (h : RPrf Δ ((C.subst (up τ)).subst (repl (Tm.add c zero)))) :
    RPrf Δ ((C.subst (up τ)).subst (repl c)) := by
  rw [NFm.subst_subst] at h ⊢
  refine (L _ _ fun i => ?_).mp (List.Subset.refl _) h
  refine Fin.cases ?_ (fun l => ?_) i
  · simp only [up_zero, Syn.subst_var, repl_zero]
    exact RPrf.iterZero c (succ (Syn.var 0))
  · rw [up_succ, Syn.subst_repl_shift, Syn.subst_repl_shift]
    exact RPrf.eqRefl _

end REquivIn

namespace RPrf

variable {Γ : List (NFm n)}

/-- Equal substitutions stay equal under a binder. -/
theorem upEq {σ σ' : Fin k → Tm n} (he : ∀ i, RPrf Γ (.eq (σ i) (σ' i))) :
    ∀ i, RPrf (Γ.map NFm.shift) (.eq (up σ i) (up σ' i)) := by
  refine Fin.cases ?_ fun j => ?_
  · exact eqRefl _
  · rw [up_succ, up_succ]
    exact (he j).shift

/-- Substitutions that are provably equal give interderivable instances. -/
theorem leibnizIn (A : NFm k) : ∀ {n : ℕ} {Γ : List (NFm n)} (σ σ' : Fin k → Tm n),
    (∀ i, RPrf Γ (.eq (σ i) (σ' i))) → REquivIn Γ (A.subst σ) (A.subst σ') := by
  induction A with intro n Γ σ σ' he
  | eq a b =>
    exact ⟨leibnizEq a b σ σ' (fun i => (he i).wk) hyp0,
      leibnizEq a b σ' σ (fun i => eqSymm (he i).wk) hyp0⟩
  | Q B ih =>
    have e := ih (up σ) (up σ') (upEq he)
    cases hB : B.isEq
    · exact REquivIn.QC (by rw [NFm.isEq_subst]; exact hB) (by rw [NFm.isEq_subst]; exact hB) e
        (fun c h => REquivIn.red ih σ c h) (fun c h => REquivIn.red ih σ' c h)
    · exact REquivIn.QE (by rw [NFm.isEq_subst]; exact hB) (by rw [NFm.isEq_subst]; exact hB) e
  | D B ih =>
    have e := ih (up (up σ)) (up (up σ')) (upEq (upEq he))
    cases hB : B.isEq
    · exact ⟨REquivIn.dStepC (by rw [NFm.isEq_subst]; exact hB)
          (by rw [NFm.isEq_subst]; exact hB) e (fun c h => REquivIn.red ih (up σ) c h),
        REquivIn.dStepC (by rw [NFm.isEq_subst]; exact hB)
          (by rw [NFm.isEq_subst]; exact hB) e.symm (fun c h => REquivIn.red ih (up σ') c h)⟩
    · exact ⟨REquivIn.dStepE (by rw [NFm.isEq_subst]; exact hB)
          (by rw [NFm.isEq_subst]; exact hB) e,
        REquivIn.dStepE (by rw [NFm.isEq_subst]; exact hB)
          (by rw [NFm.isEq_subst]; exact hB) e.symm⟩

/-- **The simultaneous Leibniz rule in the uniform calculus.** -/
theorem leibniz (A : NFm k) (σ σ' : Fin k → Tm n) (he : ∀ i, RPrf Γ (.eq (σ i) (σ' i)))
    (h : RPrf Γ (A.subst σ)) : RPrf Γ (A.subst σ') :=
  (leibnizIn A σ σ' he).mp (List.Subset.refl _) h

/-- Transport in an arbitrary formula template. -/
theorem tr (H : NFm (n + 1)) {s t : Tm n} (h₁ : RPrf Γ (.eq s t))
    (h₂ : RPrf Γ (H.subst (inst s))) : RPrf Γ (H.subst (inst t)) :=
  leibniz H (inst s) (inst t) (fun i => Fin.cases h₁ (fun j => by
    rw [inst_succ, inst_succ]; exact eqRefl _) i) h₂

end RPrf

end LeanProofs.ConciseIPRA
