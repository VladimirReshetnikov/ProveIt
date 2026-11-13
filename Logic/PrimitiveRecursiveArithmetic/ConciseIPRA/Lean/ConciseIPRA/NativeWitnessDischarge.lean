import ConciseIPRA.NativeVariableSubstitution

/-!
# Equality at the discharge of a witness

The package `Research/witness_discharge` has one rule, Name, in place of both
equality transport and the elimination of `D`, on full normal forms:

  prove `D_{x,y} B`; in the context opened at a fresh `b` prove `b = t` and
  `F`; export `F[t/b]`, provided it does not mention `b`.

With `t = b` this is the ordinary elimination.  `NMPrf` is the kernel on full
normal forms with Name in place of transport and `DE`: six rules, Hyp, Refl,
Name, `QE`, `DI` by cases and `QI` by progress.  `nmprf_iff_nprf` proves that
the kernel derives a sequent exactly when `NMPrf` derives its full normal form.

Transport is recovered by the naming packet of `NativeVariableSubstitution`:
the rows of the opened packet give `b = t` and `h(b) = u`, and Name exports
`h(t) = u`.  That is transport without the crossing; applied to the template
`x` and a reflexive equation it is symmetry, and the transport of the kernel
follows.  The translation is made under an arbitrary substitution and into an
arbitrary larger context, so the equations to be turned round are available
under the fresh variables that the packet needs.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm
open Tm (zero succ iter)

variable {n m : ℕ}

/-- The kernel on full normal forms with Name in place of transport and
`DE`. -/
inductive NMPrf : {n : ℕ} → List (NFm n) → NFm n → Prop
  | hyp {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (h : A ∈ Γ) : NMPrf Γ A
  | refl {n : ℕ} {Γ : List (NFm n)} (t : Tm n) : NMPrf Γ (.eq t.full t.full)
  /-- Name: from `D_{x,y} B`, and from `b = t` and `F` in the context opened at
  a fresh `b`, infer `F[t/b]`, which does not mention `b`. -/
  | name {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 2)} {A : NFm n} (F : NFm (n + 1))
      (t : Tm (n + 1)) (h₁ : NMPrf Γ (.D B))
      (h₂ : NMPrf (.Q B :: Γ.map NFm.shift) (.eq (Syn.var 0) t))
      (h₃ : NMPrf (.Q B :: Γ.map NFm.shift) F) (hA : (F.subst (repl t)).full = A.shift) :
      NMPrf Γ A
  | qE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 1)} (t : Tm n)
      (h₁ : NMPrf Γ (.Q B)) (h₂ : NMPrf Γ (B.subst (inst zero)).full) :
      NMPrf Γ (B.subst (inst t)).full
  | dICase {n : ℕ} {Γ : List (NFm n)} (B : NFm (n + 2)) (t : Tm n) (hB : B.full = B)
      (h : NMPrf (((B.subst (up (inst t))).subst (inst zero)).full.shift :: Γ.map NFm.shift)
        ((B.subst (up (inst t))).subst (repl (succ (var 0)))).full) :
      NMPrf Γ (.D B)
  | qIInd {n : ℕ} {Γ : List (NFm n)} (s₁ s₂ : Tm (n + 1)) (h₁ : s₁.full = s₁)
      (h₂ : s₂.full = s₂)
      (h : NMPrf (NFm.eq s₁ s₂ :: Γ.map NFm.shift)
        ((NFm.eq s₁ s₂).subst (repl (succ (var 0)))).full) :
      NMPrf Γ (.Q (.eq s₁ s₂))

theorem Tm.full_var (i : Fin n) : (Syn.var i : Tm n).full = Syn.var i :=
  show Tm.nbe (Tm.var i) Tm.var = Tm.var i from rfl

namespace NMPrf

variable {Γ : List (NFm n)} {A : NFm n}

/-- Every rule is a derived rule of the kernel, up to normal forms. -/
theorem toNPrf (h : NMPrf Γ A) : NPrf Γ A := by
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
  | dICase B t _ _ ih =>
    exact .dICase B t ((equivFull _).mpr
      (NPrf.cut1 ((equivFull _).shift.mp NPrf.hyp0) (NPrf.wkUnder ih)))
  | qIInd s₁ s₂ _ _ _ ih => exact .qIInd s₁ s₂ ((equivFull _).mpr ih)

/-- `DE`, by Name at the fresh variable itself. -/
theorem dE {B : NFm (n + 2)} (h₁ : NMPrf Γ (.D B))
    (h₂ : NMPrf (.Q B :: Γ.map NFm.shift) A.shift) (hA : A.full = A) : NMPrf Γ A := by
  have r := NMPrf.refl (Γ := .Q B :: Γ.map NFm.shift) (Syn.var 0)
  rw [Tm.full_var] at r
  refine .name A.shift (Syn.var 0) h₁ r h₂ ?_
  rw [NFm.subst_repl_var, NFm.full_shift, hA]

/-- Introduction of `Q` by cases, for a normal matrix. -/
theorem qI (B : NFm (n + 1)) (hB : B.full = B)
    (h : NMPrf ((B.subst (inst zero)).full.shift :: Γ.map NFm.shift)
      (B.subst (repl (succ (Syn.var 0)))).full) : NMPrf Γ (.Q B) := by
  have hB' : (B.subst (up fun i => Syn.var i.succ)).full
      = B.subst (up fun i => Syn.var i.succ) := by
    rw [Tm.up_rn Fin.succ, NFm.full_rn, hB]
  have hD : NMPrf Γ (.D (B.subst (up fun i => Syn.var i.succ))) := by
    refine .dICase _ zero hB' ?_
    rw [NFm.subst_dummy_inst]
    exact h
  refine dE hD ?_ (congrArg NFm.Q hB)
  show NMPrf (.Q (B.subst (up fun i => Syn.var i.succ)) :: Γ.map NFm.shift)
    (.Q (B.subst (up fun i => Syn.var i.succ)))
  exact .hyp List.mem_cons_self

/-- Numerical cases, for a normal matrix. -/
theorem cases (B : NFm (n + 1)) (hB : B.full = B) (t : Tm n)
    (h0 : NMPrf Γ (B.subst (inst zero)).full)
    (hS : NMPrf ((B.subst (inst zero)).full.shift :: Γ.map NFm.shift)
      (B.subst (repl (succ (Syn.var 0)))).full) : NMPrf Γ (B.subst (inst t)).full :=
  .qE t (qI B hB hS) h0

/-- **The naming packet with Name.**  Transport without the crossing, from the
two given equations under one and under two fresh variables. -/
theorem packet (S T U : Tm n) (H : Tm (n + 1))
    (he : ∀ X : NFm (n + 1),
      NMPrf (X :: Γ.map NFm.shift) (.eq (Syn.shift S.full) (Syn.shift T.full)))
    (hk : ∀ (X : NFm (n + 1)) (Y : NFm (n + 2)),
      NMPrf (Y :: (X :: Γ.map NFm.shift).map NFm.shift)
        (.eq (Syn.shift (Syn.shift (Syn.subst (inst S) H).full)) (Syn.shift (Syn.shift U.full)))) :
    NMPrf Γ (.eq (Syn.subst (inst T) H).full U.full) := by
  have hD : NMPrf Γ (.D (NFm.pkt H T U).full) := by
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
  have base : NMPrf (.Q (NFm.pkt H T U).full :: Γ.map NFm.shift)
      ((NFm.pkt H T U).full.subst (inst zero)).full := by
    rw [NFm.full_subst_congr (A' := NFm.pkt H T U) (σ' := inst zero) (NFm.full_idem _)
      (fun _ => rfl), NFm.pkt_row0]
    exact .refl zero
  have r1 := NMPrf.qE (succ zero) (.hyp List.mem_cons_self) base
  rw [NFm.full_subst_congr (A' := NFm.pkt H T U) (σ' := inst (succ zero)) (NFm.full_idem _)
    (fun _ => rfl), NFm.pkt_row1] at r1
  have r2 := NMPrf.qE (succ (succ zero)) (.hyp List.mem_cons_self) base
  rw [NFm.full_subst_congr (A' := NFm.pkt H T U) (σ' := inst (succ (succ zero)))
    (NFm.full_idem _) (fun _ => rfl), NFm.pkt_row2] at r2
  refine .name (.eq H.full (Syn.shift U.full)) (Syn.shift T.full) hD r2 r1 ?_
  rw [NFm.full_subst_congr (A' := .eq H (Syn.shift U)) (σ' := repl (Syn.shift T))
      (by simp only [NFm.full, Tm.full_idem, Tm.full_shift]) (fun i => by
        refine Fin.cases ?_ (fun j => ?_) i
        · simp
        · rfl),
    ← NFm.shift_subst_inst, NFm.full_shift]
  simp only [NFm.subst_eq, NFm.full, Syn.subst_inst_shift]

end NMPrf

variable {Γ : List (NFm n)} {A : NFm n}

/-- Every kernel derivation, under any substitution and in any larger context,
becomes a derivation with Name. -/
theorem NPrf.toNM (h : NPrf Γ A) : ∀ {m : ℕ} (σ : Fin n → Tm m) (Δ : List (NFm m)),
    (∀ X ∈ Γ, (X.subst σ).full ∈ Δ) → NMPrf Δ (A.subst σ).full := by
  induction h with
  | hyp h => intro m σ Δ hs; exact .hyp (hs _ h)
  | iterZero a h => intro m σ Δ _; exact .refl (Syn.subst σ a)
  | iterSucc c a h =>
    intro m σ Δ _
    simp only [NFm.subst_eq, NFm.full, Tm.subst_iter, Tm.subst_succ, Syn.subst_subst_inst]
    rw [Tm.full_iterSucc]
    exact .refl _
  | @trOne n' Γ h s t u _ _ ih₁ ih₂ =>
    intro m σ Δ hs
    simp only [NFm.subst_eq, NFm.full, Syn.subst_subst_inst]
    -- transport without the crossing, under every substitution
    have unc : ∀ {m' : ℕ} (τ : Fin n' → Tm m') (Δ' : List (NFm m')),
        (∀ X ∈ Γ, (X.subst τ).full ∈ Δ') →
        NMPrf Δ' (.eq (Syn.subst (inst (Syn.subst τ t)) (Syn.subst (up τ) h)).full
          (Syn.subst τ u).full) := by
      intro m' τ Δ' hs'
      refine NMPrf.packet (Syn.subst τ s) (Syn.subst τ t) (Syn.subst τ u)
        (Syn.subst (up τ) h) (fun X => ?_) (fun X Y => ?_)
      · have k := ih₁ (fun i => Syn.shift (τ i)) _ (NFm.liftShift hs' X)
        simp only [NFm.subst_eq, NFm.full, ← Syn.shift_subst, Tm.full_shift] at k
        exact k
      · have k := ih₂ (fun i => Syn.shift (Syn.shift (τ i))) _
          (NFm.liftShift (NFm.liftShift hs' X) Y)
        rw [NFm.subst_shift_fun (σ := fun i => Syn.shift (τ i)), NFm.subst_shift_fun,
          NFm.full_shift, NFm.full_shift] at k
        simp only [NFm.subst_eq, NFm.full, Syn.subst_subst_inst] at k
        exact k
    -- symmetry, by the packet at the template `x`
    have k := NMPrf.packet (Γ := Δ)
      (Syn.subst (inst (Syn.subst σ t)) (Syn.subst (up σ) h)) (Syn.subst σ u)
      (Syn.subst (inst (Syn.subst σ t)) (Syn.subst (up σ) h)) (Syn.var 0)
      (fun X => by
        have k' := unc (fun i => Syn.shift (σ i)) _ (NFm.liftShift hs X)
        rw [← Syn.subst_subst_inst, ← Syn.shift_subst, ← Syn.shift_subst, Tm.full_shift,
          Tm.full_shift, Syn.subst_subst_inst] at k'
        exact k')
      (fun X Y => by
        have r := NMPrf.refl (Γ := Y :: (X :: Δ.map NFm.shift).map NFm.shift)
          (Syn.shift (Syn.shift (Syn.subst (inst (Syn.subst σ t)) (Syn.subst (up σ) h))))
        rw [Tm.full_shift, Tm.full_shift] at r
        simpa only [Syn.subst_var, Syn.inst_zero] using r)
    simpa only [Syn.subst_var, Syn.inst_zero] using k
  | @qE _ Γ B t _ _ ih₁ ih₂ =>
    intro m σ Δ hs
    have h₂ := ih₂ σ Δ hs
    rw [NFm.subst_inst] at h₂ ⊢
    have k := NMPrf.qE (B := (B.subst (up σ)).full) (Syn.subst σ t) (ih₁ σ Δ hs) (by
      rw [NFm.full_subst_congr (σ' := inst zero) (NFm.full_idem _) (fun _ => rfl)]
      exact h₂)
    rwa [NFm.full_subst_congr (σ' := inst (Syn.subst σ t)) (NFm.full_idem _)
      (fun _ => rfl)] at k
  | @dE _ Γ B A _ _ ih₁ ih₂ =>
    intro m σ Δ hs
    refine NMPrf.dE (B := (B.subst (up (up σ))).full) (ih₁ σ Δ hs) ?_ (NFm.full_idem _)
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

/-- **Equality at the discharge of a witness.**  The kernel derives a sequent
exactly when the six-rule calculus with Name derives its full normal form. -/
theorem nmprf_iff_nprf : NMPrf (Γ.map NFm.full) A.full ↔ NPrf Γ A := by
  constructor
  · intro h
    refine (equivFull A).mpr (h.toNPrf.cut fun B hB => ?_)
    obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hB
    exact (equivFull C).mp (.hyp hC)
  · intro h
    have k := h.toNM Syn.var (Γ.map NFm.full) fun X hX => by
      rw [NFm.subst_id]; exact List.mem_map_of_mem hX
    rwa [NFm.subst_id] at k

end LeanProofs.ConciseIPRA
