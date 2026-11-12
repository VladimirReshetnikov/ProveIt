import ConciseIPRA.NativeVariableSubstitution

/-!
# Substitution for the newest variable only

`Research/variable_substitution` observes that the source of its equality rule
can be restricted to the newest variable.  With de Bruijn indices the newest
variable is the index `0`, and `V0Prf` is the calculus `VSPrf` of
`NativeVariableSubstitution` with its rule restricted to that index:

  from `x₀ = t` and `u = v` infer `v = u[t/x₀]`.

`v0prf_iff_nprf` proves that the kernel derives a sequent exactly when `V0Prf`
derives its full normal form.

The restricted rule is not stable under renaming, since a renaming moves the
index `0`.  The proof does not need that stability.  The naming packet
substitutes only for the witness it has just opened, which is the newest
variable there, and the translation of kernel derivations is made under an
arbitrary substitution and into an arbitrary larger context, so that no
derivation of `V0Prf` is ever renamed or weakened.  The matrix of the packet,
its rows and the context lemmas are those of `NativeVariableSubstitution`.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm
open Tm (zero succ iter)

variable {n m : ℕ}

/-- The kernel on full normal forms whose only equality rule substitutes for
the newest variable. -/
inductive V0Prf : {n : ℕ} → List (NFm n) → NFm n → Prop
  | hyp {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (h : A ∈ Γ) : V0Prf Γ A
  | refl {n : ℕ} {Γ : List (NFm n)} (t : Tm n) : V0Prf Γ (.eq t.full t.full)
  /-- From `x = t`, for the newest variable `x`, and `u = v` infer
  `v = u[t/x]`. -/
  | vsub0 {n : ℕ} {Γ : List (NFm (n + 1))} {t u v : Tm (n + 1)}
      (h₁ : V0Prf Γ (.eq (Syn.var 0) t)) (h₂ : V0Prf Γ (.eq u v)) :
      V0Prf Γ (.eq v (Syn.subst (Function.update Syn.var 0 t) u).full)
  | qE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 1)} (t : Tm n)
      (h₁ : V0Prf Γ (.Q B)) (h₂ : V0Prf Γ (B.subst (inst zero)).full) :
      V0Prf Γ (B.subst (inst t)).full
  | dE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 2)} {A : NFm n}
      (h₁ : V0Prf Γ (.D B)) (h₂ : V0Prf (.Q B :: Γ.map NFm.shift) A.shift) : V0Prf Γ A
  | dICase {n : ℕ} {Γ : List (NFm n)} (B : NFm (n + 2)) (t : Tm n) (hB : B.full = B)
      (h : V0Prf (((B.subst (up (inst t))).subst (inst zero)).full.shift :: Γ.map NFm.shift)
        ((B.subst (up (inst t))).subst (repl (succ (var 0)))).full) :
      V0Prf Γ (.D B)
  | qIInd {n : ℕ} {Γ : List (NFm n)} (s₁ s₂ : Tm (n + 1)) (h₁ : s₁.full = s₁)
      (h₂ : s₂.full = s₂)
      (h : V0Prf (NFm.eq s₁ s₂ :: Γ.map NFm.shift)
        ((NFm.eq s₁ s₂).subst (repl (succ (var 0)))).full) :
      V0Prf Γ (.Q (.eq s₁ s₂))

namespace V0Prf

variable {Γ : List (NFm n)} {A : NFm n}

/-- Every rule is a derived rule of the kernel, up to normal forms. -/
theorem toNPrf (h : V0Prf Γ A) : NPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | refl t => exact NPrf.eqRefl _
  | @vsub0 _ Γ t u v _ _ ih₁ ih₂ =>
    have k := NPrf.trOne
      (Syn.subst (Function.update (fun j => (Syn.var j.succ : Tm _)) 0 (Syn.var 0)) u) ih₁
      (u := v) (by
        rw [Tm.subst_inst_abs, Function.update_eq_self, Syn.subst_id]; exact ih₂)
    rw [Tm.subst_inst_abs] at k
    exact NPrf.eqTrans k (NPrf.eqFull _)
  | qE t _ _ ih₁ ih₂ => exact (equivFull _).mp (.qE t ih₁ ((equivFull _).mpr ih₂))
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dICase B t _ _ ih =>
    exact .dICase B t ((equivFull _).mpr
      (NPrf.cut1 ((equivFull _).shift.mp NPrf.hyp0) (NPrf.wkUnder ih)))
  | qIInd s₁ s₂ _ _ _ ih => exact .qIInd s₁ s₂ ((equivFull _).mpr ih)

/-- Introduction of `Q` by cases, for a normal matrix. -/
theorem qI (B : NFm (n + 1)) (hB : B.full = B)
    (h : V0Prf ((B.subst (inst zero)).full.shift :: Γ.map NFm.shift)
      (B.subst (repl (succ (Syn.var 0)))).full) : V0Prf Γ (.Q B) := by
  have hB' : (B.subst (up fun i => Syn.var i.succ)).full
      = B.subst (up fun i => Syn.var i.succ) := by
    rw [Tm.up_rn Fin.succ, NFm.full_rn, hB]
  have hD : V0Prf Γ (.D (B.subst (up fun i => Syn.var i.succ))) := by
    refine .dICase _ zero hB' ?_
    rw [NFm.subst_dummy_inst]
    exact h
  refine .dE hD ?_
  show V0Prf (.Q (B.subst (up fun i => Syn.var i.succ)) :: Γ.map NFm.shift)
    (.Q (B.subst (up fun i => Syn.var i.succ)))
  exact .hyp List.mem_cons_self

/-- Numerical cases, for a normal matrix. -/
theorem cases (B : NFm (n + 1)) (hB : B.full = B) (t : Tm n)
    (h0 : V0Prf Γ (B.subst (inst zero)).full)
    (hS : V0Prf ((B.subst (inst zero)).full.shift :: Γ.map NFm.shift)
      (B.subst (repl (succ (Syn.var 0)))).full) : V0Prf Γ (B.subst (inst t)).full :=
  .qE t (qI B hB hS) h0

/-- **The naming packet.**  Transport, from the two given equations under one
and under two fresh variables. -/
theorem packet (S T U : Tm n) (H : Tm (n + 1))
    (he : ∀ X : NFm (n + 1),
      V0Prf (X :: Γ.map NFm.shift) (.eq (Syn.shift S.full) (Syn.shift T.full)))
    (hk : ∀ (X : NFm (n + 1)) (Y : NFm (n + 2)),
      V0Prf (Y :: (X :: Γ.map NFm.shift).map NFm.shift)
        (.eq (Syn.shift (Syn.shift (Syn.subst (inst S) H).full)) (Syn.shift (Syn.shift U.full)))) :
    V0Prf Γ (.eq U.full (Syn.subst (inst T) H).full) := by
  have hD : V0Prf Γ (.D (NFm.pkt H T U).full) := by
    refine .dICase _ S (NFm.full_idem _) ?_
    have eA : (((NFm.pkt H T U).full.subst (up (inst S))).subst (repl (succ (Syn.var 0)))).full
        = ((NFm.pktF S T U (Syn.subst (inst S) H)).full.subst
            (inst (Tm.npar (succ (Syn.var 0))))).full := by
      rw [NFm.full_subst_congr (A' := (NFm.pkt H T U).subst (up (inst S)))
          (σ' := repl (succ (Syn.var 0)))
          (NFm.full_subst_congr (NFm.full_idem _) fun _ => rfl) (fun _ => rfl),
        NFm.pkt_wit,
        NFm.full_subst_congr (A' := NFm.pktF S T U (Syn.subst (inst S) H))
          (σ' := inst (Tm.npar (succ (Syn.var 0)))) (NFm.full_idem _) (fun _ => rfl),
        NFm.pktF_inst]
      show NFm.eq (Tm.full _) (Tm.full _) = NFm.eq (Tm.full _) (Tm.full _)
      rw [Tm.full_sel_succ' (c := succ (Syn.var 0)) (x := Syn.var 0) rfl,
        Tm.full_sel_succ' (c := succ (Syn.var 0)) (x := Syn.var 0) rfl]
    rw [eA]
    refine cases _ (NFm.full_idem _) _ ?_ ?_
    · rw [NFm.full_subst_congr (A' := NFm.pktF S T U (Syn.subst (inst S) H)) (σ' := inst zero)
        (NFm.full_idem _) (fun _ => rfl), NFm.pktF_zero]
      exact he _
    · rw [NFm.full_subst_congr (A' := NFm.pktF S T U (Syn.subst (inst S) H))
        (σ' := repl (succ (Syn.var 0))) (NFm.full_idem _) (fun _ => rfl), NFm.pktF_succ]
      exact hk _ _
  refine .dE hD ?_
  have base : V0Prf (.Q (NFm.pkt H T U).full :: Γ.map NFm.shift)
      ((NFm.pkt H T U).full.subst (inst zero)).full := by
    rw [NFm.full_subst_congr (A' := NFm.pkt H T U) (σ' := inst zero) (NFm.full_idem _)
      (fun _ => rfl), NFm.pkt_row0]
    exact .refl zero
  have r1 := V0Prf.qE (succ zero) (.hyp List.mem_cons_self) base
  rw [NFm.full_subst_congr (A' := NFm.pkt H T U) (σ' := inst (succ zero)) (NFm.full_idem _)
    (fun _ => rfl), NFm.pkt_row1] at r1
  have r2 := V0Prf.qE (succ (succ zero)) (.hyp List.mem_cons_self) base
  rw [NFm.full_subst_congr (A' := NFm.pkt H T U) (σ' := inst (succ (succ zero)))
    (NFm.full_idem _) (fun _ => rfl), NFm.pkt_row2] at r2
  have k := V0Prf.vsub0 r2 r1
  have e : (Syn.subst (Function.update Syn.var 0 (Syn.shift T.full)) H.full).full
      = Syn.shift (Syn.subst (inst T) H).full := by
    rw [Tm.full_subst_congr (t' := H) (σ' := Function.update Syn.var 0 (Syn.shift T))
      (Tm.full_idem H) (fun i => by
        by_cases hi : i = 0
        · subst hi; simp
        · simp [Function.update_of_ne hi]),
      ← Tm.psi_var, Tm.psi_var0, Tm.full_shift]
  rw [e] at k
  exact k

end V0Prf

variable {Γ : List (NFm n)} {A : NFm n}

/-- Every kernel derivation, under any substitution and in any larger context,
becomes a derivation with substitution for the newest variable only. -/
theorem NPrf.toV0 (h : NPrf Γ A) : ∀ {m : ℕ} (σ : Fin n → Tm m) (Δ : List (NFm m)),
    (∀ X ∈ Γ, (X.subst σ).full ∈ Δ) → V0Prf Δ (A.subst σ).full := by
  induction h with
  | hyp h => intro m σ Δ hs; exact .hyp (hs _ h)
  | iterZero a h => intro m σ Δ _; exact .refl (Syn.subst σ a)
  | iterSucc c a h =>
    intro m σ Δ _
    simp only [NFm.subst_eq, NFm.full, Tm.subst_iter, Tm.subst_succ, Syn.subst_subst_inst]
    rw [Tm.full_iterSucc]
    exact .refl _
  | @trOne _ Γ h s t u _ _ ih₁ ih₂ =>
    intro m σ Δ hs
    simp only [NFm.subst_eq, NFm.full, Syn.subst_subst_inst]
    refine V0Prf.packet (Syn.subst σ s) (Syn.subst σ t) (Syn.subst σ u) (Syn.subst (up σ) h)
      (fun X => ?_) (fun X Y => ?_)
    · have k := ih₁ (fun i => Syn.shift (σ i)) _ (NFm.liftShift hs X)
      simp only [NFm.subst_eq, NFm.full, ← Syn.shift_subst, Tm.full_shift] at k
      exact k
    · have k := ih₂ (fun i => Syn.shift (Syn.shift (σ i))) _
        (NFm.liftShift (NFm.liftShift hs X) Y)
      rw [NFm.subst_shift_fun (σ := fun i => Syn.shift (σ i)), NFm.subst_shift_fun,
        NFm.full_shift, NFm.full_shift] at k
      simp only [NFm.subst_eq, NFm.full, Syn.subst_subst_inst] at k
      exact k
  | @qE _ Γ B t _ _ ih₁ ih₂ =>
    intro m σ Δ hs
    have h₂ := ih₂ σ Δ hs
    rw [NFm.subst_inst] at h₂ ⊢
    have k := V0Prf.qE (B := (B.subst (up σ)).full) (Syn.subst σ t) (ih₁ σ Δ hs) (by
      rw [NFm.full_subst_congr (σ' := inst zero) (NFm.full_idem _) (fun _ => rfl)]
      exact h₂)
    rwa [NFm.full_subst_congr (σ' := inst (Syn.subst σ t)) (NFm.full_idem _)
      (fun _ => rfl)] at k
  | @dE _ Γ B A _ _ ih₁ ih₂ =>
    intro m σ Δ hs
    refine .dE (B := (B.subst (up (up σ))).full) (ih₁ σ Δ hs) ?_
    have k := ih₂ (up σ) _ (NFm.liftFull hs (.Q B) _ rfl)
    rwa [NFm.shift_subst_up, NFm.full_shift] at k
  | @dICase _ Γ B t _ ih =>
    intro m σ Δ hs
    refine .dICase (B.subst (up (up σ))).full (Syn.subst σ t) (NFm.full_idem _) ?_
    have e : ∀ {k : ℕ} (ρ : Fin (m + 1) → Tm k),
        (((B.subst (up (up σ))).full.subst (up (inst (Syn.subst σ t)))).subst ρ).full
          = (((B.subst (up (up σ))).subst (up (inst (Syn.subst σ t)))).subst ρ).full :=
      fun ρ => NFm.full_subst_congr
        (NFm.full_subst_congr (NFm.full_idem _) fun _ => rfl) fun _ => rfl
    rw [e, e]
    have k := ih (up σ) _ (NFm.liftFull hs _ _ (by
      rw [NFm.shift_subst_up, NFm.full_shift, NFm.subst_inst, NFm.subst_up_inst]))
    rwa [NFm.subst_repl_succ, NFm.subst_up_inst] at k
  | @qIInd _ Γ s₁ s₂ _ ih =>
    intro m σ Δ hs
    refine .qIInd (Syn.subst (up σ) s₁).full (Syn.subst (up σ) s₂).full (Tm.full_idem _)
      (Tm.full_idem _) ?_
    rw [NFm.full_subst_congr (A' := (NFm.eq s₁ s₂).subst (up σ))
      (σ' := repl (succ (Syn.var 0))) (by simp only [NFm.subst_eq, NFm.full, Tm.full_idem])
      (fun _ => rfl)]
    have k := ih (up σ) _ (NFm.liftFull hs (.eq s₁ s₂) _ rfl)
    rwa [NFm.subst_repl_succ] at k

/-- **Substitution for the newest variable is enough.**  The kernel derives a
sequent exactly when the calculus on full normal forms whose only equality rule
substitutes for the newest variable derives its full normal form. -/
theorem v0prf_iff_nprf : V0Prf (Γ.map NFm.full) A.full ↔ NPrf Γ A := by
  constructor
  · intro h
    refine (equivFull A).mpr (h.toNPrf.cut fun B hB => ?_)
    obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hB
    exact (equivFull C).mp (.hyp hC)
  · intro h
    have k := h.toV0 Syn.var (Γ.map NFm.full) fun X hX => by
      rw [NFm.subst_id]; exact List.mem_map_of_mem hX
    rwa [NFm.subst_id] at k

end LeanProofs.ConciseIPRA
