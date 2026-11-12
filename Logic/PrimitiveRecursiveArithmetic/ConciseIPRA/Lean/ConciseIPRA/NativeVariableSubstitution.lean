import ConciseIPRA.NativeInferredWitness
import ConciseIPRA.NativeParameter

/-!
# Equality by substitution for a variable only

The package `Research/variable_substitution` has one equality rule, on full
normal forms:

  from `x = t`, for a variable `x`, and `u = v` infer `v = u[t/x]`.

There is no transport in a template and no joining of two equations with a
common side.  `VSPrf` is the kernel on full normal forms (`FNPrf`) with this
rule in place of transport, and `vsprf_iff_nprf` proves that the kernel derives
a sequent exactly when `VSPrf` derives its full normal form.

Transport from `s = t` and `h(s) = u` to `u = h(t)` is recovered by a *naming
packet*.  The matrix

  `B(x, y) = (sel(y, 0, sel(P(y), x, h(x))) = sel(y, 0, sel(P(y), t, u)))`,

with `P` the parity iterator, has three rows as full normal forms: `0 = 0` at
`y = 0`, `h(x) = u` at `y = 1` and `x = t` at `y = 2`.  `D_{x,y} B` is
introduced at the witness `s`, by numerical cases on the parity of the fresh
variable, from the two given equations.  It is opened at a fresh `b`; its rows
give `h(b) = u` and `b = t`, and one substitution for the variable `b` gives
`u = h(t)`.

The translation of kernel derivations is made under an arbitrary substitution
and into an arbitrary larger context (`NPrf.toVS`), so that no weakening,
renaming or cut of `VSPrf` derivations is needed.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm
open Tm (zero succ iter)

variable {n m : ℕ}

namespace Tm

theorem full_sel_zero' {c a b : Tm n} (hc : full c = zero) : full (sel c a b) = full a := by
  show recV (nbe c Tm.var) (nbe a Tm.var) _ _ = _
  rw [show nbe c Tm.var = zero from hc]
  rfl

theorem full_sel_succ' {c x a b : Tm n} (hc : full c = succ x) : full (sel c a b) = full b := by
  show recV (nbe c Tm.var) (nbe a Tm.var) (fun v => nbe (Syn.shift b) (Fin.cases v Tm.var)) _ = _
  rw [show nbe c Tm.var = succ x from hc]
  show nbe (Syn.shift b) (Fin.cases _ Tm.var) = _
  rw [shift_eq_ren, nbe_ren]
  simp only [Fin.cases_succ]
  rfl

theorem full_npar_one : full (npar (succ zero) : Tm n) = succ zero := rfl

theorem full_npar_two : full (npar (succ (succ zero)) : Tm n) = zero := rfl

theorem subst_hole1 (H : Tm (n + 1)) (c : Tm (n + 1)) :
    Syn.subst (inst c) (Syn.subst (Fin.cases (Syn.var 1) fun i => Syn.var i.succ.succ) H) = H := by
  rw [Syn.subst_subst]
  refine (congrArg (fun r => Syn.subst r H) (funext fun i => ?_)).trans (Syn.subst_id H)
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem subst_hole2 (H : Tm (n + 1)) (S : Tm n) (r : Tm (n + 1)) :
    Syn.subst (repl r) (Syn.subst (up (inst S))
        (Syn.subst (Fin.cases (Syn.var 1) fun i => Syn.var i.succ.succ) H))
      = Syn.shift (Syn.subst (inst S) H) := by
  rw [Syn.subst_subst, Syn.subst_subst, Syn.shift_subst]
  refine congrArg (fun ρ => Syn.subst ρ H) (funext fun i => ?_)
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

end Tm

namespace NFm

/-- The matrix of the naming packet. -/
def pkt (H : Tm (n + 1)) (T U : Tm n) : NFm (n + 2) :=
  .eq (Tm.sel (Syn.var 0) zero (Tm.sel (Tm.npar (Syn.var 0)) (Syn.var 1)
        (Syn.subst (Fin.cases (Syn.var 1) fun i => Syn.var i.succ.succ) H)))
    (Tm.sel (Syn.var 0) zero (Tm.sel (Tm.npar (Syn.var 0)) (Syn.shift (Syn.shift T))
        (Syn.shift (Syn.shift U))))

/-- The matrix of the numerical cases that introduce the packet. -/
def pktF (S T U HS : Tm n) : NFm (n + 2) :=
  .eq (Tm.sel (Syn.var 0) (Syn.shift (Syn.shift S)) (Syn.shift (Syn.shift HS)))
    (Tm.sel (Syn.var 0) (Syn.shift (Syn.shift T)) (Syn.shift (Syn.shift U)))

theorem pkt_inst (H : Tm (n + 1)) (T U : Tm n) (c : Tm (n + 1)) :
    (pkt H T U).subst (inst c)
      = .eq (Tm.sel c zero (Tm.sel (Tm.npar c) (Syn.var 0) H))
          (Tm.sel c zero (Tm.sel (Tm.npar c) (Syn.shift T) (Syn.shift U))) := by
  simp [pkt, Tm.subst_hole1]

theorem pkt_row0 (H : Tm (n + 1)) (T U : Tm n) :
    ((pkt H T U).subst (inst zero)).full = .eq zero zero := by
  rw [pkt_inst]
  rfl

theorem pkt_row1 (H : Tm (n + 1)) (T U : Tm n) :
    ((pkt H T U).subst (inst (succ zero))).full = .eq H.full (Syn.shift U.full) := by
  rw [pkt_inst]
  show NFm.eq (Tm.full _) (Tm.full _) = _
  rw [Tm.full_sel_succ' (c := succ zero) (x := zero) rfl,
    Tm.full_sel_succ' (c := succ zero) (x := zero) rfl,
    Tm.full_sel_succ' (c := Tm.npar (succ zero)) (x := zero) Tm.full_npar_one,
    Tm.full_sel_succ' (c := Tm.npar (succ zero)) (x := zero) Tm.full_npar_one, Tm.full_shift]

theorem pkt_row2 (H : Tm (n + 1)) (T U : Tm n) :
    ((pkt H T U).subst (inst (succ (succ zero)))).full
      = .eq (Syn.var 0) (Syn.shift T.full) := by
  rw [pkt_inst]
  show NFm.eq (Tm.full _) (Tm.full _) = _
  rw [Tm.full_sel_succ' (c := succ (succ zero)) (x := succ zero) rfl,
    Tm.full_sel_succ' (c := succ (succ zero)) (x := succ zero) rfl,
    Tm.full_sel_zero' (c := Tm.npar (succ (succ zero))) Tm.full_npar_two,
    Tm.full_sel_zero' (c := Tm.npar (succ (succ zero))) Tm.full_npar_two, Tm.full_shift]
  rfl

theorem pkt_wit (H : Tm (n + 1)) (S T U : Tm n) :
    ((pkt H T U).subst (up (inst S))).subst (repl (succ (Syn.var 0)))
      = .eq (Tm.sel (succ (Syn.var 0)) zero (Tm.sel (Tm.npar (succ (Syn.var 0)))
            (Syn.shift S) (Syn.shift (Syn.subst (inst S) H))))
          (Tm.sel (succ (Syn.var 0)) zero (Tm.sel (Tm.npar (succ (Syn.var 0)))
            (Syn.shift T) (Syn.shift U))) := by
  simp [pkt, Tm.subst_hole2, Syn.subst_up_shift]

theorem pktF_inst (S T U HS : Tm n) (q : Tm (n + 1)) :
    (pktF S T U HS).subst (inst q)
      = .eq (Tm.sel q (Syn.shift S) (Syn.shift HS)) (Tm.sel q (Syn.shift T) (Syn.shift U)) := by
  simp [pktF]

theorem pktF_zero (S T U HS : Tm n) :
    ((pktF S T U HS).subst (inst zero)).full = .eq (Syn.shift S.full) (Syn.shift T.full) := by
  rw [pktF_inst]
  show NFm.eq (Tm.full (Syn.shift S)) (Tm.full (Syn.shift T)) = _
  rw [Tm.full_shift, Tm.full_shift]

theorem pktF_succ (S T U HS : Tm n) :
    ((pktF S T U HS).subst (repl (succ (Syn.var 0)))).full
      = .eq (Syn.shift (Syn.shift HS.full)) (Syn.shift (Syn.shift U.full)) := by
  have e : (pktF S T U HS).subst (repl (succ (Syn.var 0)))
      = .eq (Tm.sel (succ (Syn.var 0)) (Syn.shift (Syn.shift S)) (Syn.shift (Syn.shift HS)))
          (Tm.sel (succ (Syn.var 0)) (Syn.shift (Syn.shift T)) (Syn.shift (Syn.shift U))) := by
    simp [pktF]
  rw [e]
  show NFm.eq (Tm.full _) (Tm.full _) = _
  rw [Tm.full_sel_succ' (c := succ (Syn.var 0)) (x := Syn.var 0) rfl,
    Tm.full_sel_succ' (c := succ (Syn.var 0)) (x := Syn.var 0) rfl, Tm.full_shift,
    Tm.full_shift, Tm.full_shift, Tm.full_shift]

theorem subst_shift_fun (X : NFm n) (σ : Fin n → Tm m) :
    X.subst (fun i => Syn.shift (σ i)) = (X.subst σ).shift := by
  unfold NFm.shift
  rw [NFm.subst_subst]
  rfl

end NFm

/-- The kernel on full normal forms with substitution for a variable as its
only equality rule. -/
inductive VSPrf : {n : ℕ} → List (NFm n) → NFm n → Prop
  | hyp {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (h : A ∈ Γ) : VSPrf Γ A
  | refl {n : ℕ} {Γ : List (NFm n)} (t : Tm n) : VSPrf Γ (.eq t.full t.full)
  /-- From `x = t` and `u = v` infer `v = u[t/x]`. -/
  | vsub {n : ℕ} {Γ : List (NFm n)} {i : Fin n} {t u v : Tm n}
      (h₁ : VSPrf Γ (.eq (Syn.var i) t)) (h₂ : VSPrf Γ (.eq u v)) :
      VSPrf Γ (.eq v (Syn.subst (Function.update Syn.var i t) u).full)
  | qE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 1)} (t : Tm n)
      (h₁ : VSPrf Γ (.Q B)) (h₂ : VSPrf Γ (B.subst (inst zero)).full) :
      VSPrf Γ (B.subst (inst t)).full
  | dE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 2)} {A : NFm n}
      (h₁ : VSPrf Γ (.D B)) (h₂ : VSPrf (.Q B :: Γ.map NFm.shift) A.shift) : VSPrf Γ A
  | dICase {n : ℕ} {Γ : List (NFm n)} (B : NFm (n + 2)) (t : Tm n) (hB : B.full = B)
      (h : VSPrf (((B.subst (up (inst t))).subst (inst zero)).full.shift :: Γ.map NFm.shift)
        ((B.subst (up (inst t))).subst (repl (succ (var 0)))).full) :
      VSPrf Γ (.D B)
  | qIInd {n : ℕ} {Γ : List (NFm n)} (s₁ s₂ : Tm (n + 1)) (h₁ : s₁.full = s₁)
      (h₂ : s₂.full = s₂)
      (h : VSPrf (NFm.eq s₁ s₂ :: Γ.map NFm.shift)
        ((NFm.eq s₁ s₂).subst (repl (succ (var 0)))).full) :
      VSPrf Γ (.Q (.eq s₁ s₂))

namespace VSPrf

variable {Γ : List (NFm n)} {A : NFm n}

/-- Every rule is a derived rule of the kernel, up to normal forms. -/
theorem toNPrf (h : VSPrf Γ A) : NPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | refl t => exact NPrf.eqRefl _
  | @vsub _ Γ i t u v _ _ ih₁ ih₂ =>
    have k := NPrf.trOne
      (Syn.subst (Function.update (fun j => (Syn.var j.succ : Tm _)) i (Syn.var 0)) u) ih₁
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
    (h : VSPrf ((B.subst (inst zero)).full.shift :: Γ.map NFm.shift)
      (B.subst (repl (succ (Syn.var 0)))).full) : VSPrf Γ (.Q B) := by
  have hB' : (B.subst (up fun i => Syn.var i.succ)).full
      = B.subst (up fun i => Syn.var i.succ) := by
    rw [Tm.up_rn Fin.succ, NFm.full_rn, hB]
  have hD : VSPrf Γ (.D (B.subst (up fun i => Syn.var i.succ))) := by
    refine .dICase _ zero hB' ?_
    rw [NFm.subst_dummy_inst]
    exact h
  refine .dE hD ?_
  show VSPrf (.Q (B.subst (up fun i => Syn.var i.succ)) :: Γ.map NFm.shift)
    (.Q (B.subst (up fun i => Syn.var i.succ)))
  exact .hyp List.mem_cons_self

/-- Numerical cases, for a normal matrix. -/
theorem cases (B : NFm (n + 1)) (hB : B.full = B) (t : Tm n)
    (h0 : VSPrf Γ (B.subst (inst zero)).full)
    (hS : VSPrf ((B.subst (inst zero)).full.shift :: Γ.map NFm.shift)
      (B.subst (repl (succ (Syn.var 0)))).full) : VSPrf Γ (B.subst (inst t)).full :=
  .qE t (qI B hB hS) h0

/-- **The naming packet.**  Transport, from the two given equations under one
and under two fresh variables. -/
theorem packet (S T U : Tm n) (H : Tm (n + 1))
    (he : ∀ X : NFm (n + 1),
      VSPrf (X :: Γ.map NFm.shift) (.eq (Syn.shift S.full) (Syn.shift T.full)))
    (hk : ∀ (X : NFm (n + 1)) (Y : NFm (n + 2)),
      VSPrf (Y :: (X :: Γ.map NFm.shift).map NFm.shift)
        (.eq (Syn.shift (Syn.shift (Syn.subst (inst S) H).full)) (Syn.shift (Syn.shift U.full)))) :
    VSPrf Γ (.eq U.full (Syn.subst (inst T) H).full) := by
  have hD : VSPrf Γ (.D (NFm.pkt H T U).full) := by
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
  have base : VSPrf (.Q (NFm.pkt H T U).full :: Γ.map NFm.shift)
      ((NFm.pkt H T U).full.subst (inst zero)).full := by
    rw [NFm.full_subst_congr (A' := NFm.pkt H T U) (σ' := inst zero) (NFm.full_idem _)
      (fun _ => rfl), NFm.pkt_row0]
    exact .refl zero
  have r1 := VSPrf.qE (succ zero) (.hyp List.mem_cons_self) base
  rw [NFm.full_subst_congr (A' := NFm.pkt H T U) (σ' := inst (succ zero)) (NFm.full_idem _)
    (fun _ => rfl), NFm.pkt_row1] at r1
  have r2 := VSPrf.qE (succ (succ zero)) (.hyp List.mem_cons_self) base
  rw [NFm.full_subst_congr (A' := NFm.pkt H T U) (σ' := inst (succ (succ zero)))
    (NFm.full_idem _) (fun _ => rfl), NFm.pkt_row2] at r2
  have k := VSPrf.vsub r2 r1
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

end VSPrf

variable {Γ : List (NFm n)} {A : NFm n}

/-- The context invariant under one more variable and one more formula. -/
theorem NFm.liftFull {Γ : List (NFm n)} {σ : Fin n → Tm m} {Δ : List (NFm m)}
    (hs : ∀ X ∈ Γ, (X.subst σ).full ∈ Δ) (Y : NFm (n + 1)) (Y' : NFm (m + 1))
    (hY : (Y.subst (up σ)).full = Y') :
    ∀ X ∈ Y :: Γ.map NFm.shift, (X.subst (up σ)).full ∈ Y' :: Δ.map NFm.shift := by
  intro X hX
  rcases List.mem_cons.1 hX with rfl | hX
  · rw [hY]; exact List.mem_cons_self
  · obtain ⟨Z, hZ, rfl⟩ := List.mem_map.1 hX
    rw [NFm.shift_subst_up, NFm.full_shift]
    exact List.mem_cons_of_mem _ (List.mem_map_of_mem (hs Z hZ))

/-- The context invariant under one more variable, for a shifted
substitution. -/
theorem NFm.liftShift {Γ : List (NFm n)} {σ : Fin n → Tm m} {Δ : List (NFm m)}
    (hs : ∀ X ∈ Γ, (X.subst σ).full ∈ Δ) (W : NFm (m + 1)) :
    ∀ X ∈ Γ, (X.subst fun i => Syn.shift (σ i)).full ∈ W :: Δ.map NFm.shift := by
  intro X hX
  rw [NFm.subst_shift_fun, NFm.full_shift]
  exact List.mem_cons_of_mem _ (List.mem_map_of_mem (hs X hX))

/-- Every kernel derivation, under any substitution and in any larger context,
becomes a derivation with substitution for a variable only. -/
theorem NPrf.toVS (h : NPrf Γ A) : ∀ {m : ℕ} (σ : Fin n → Tm m) (Δ : List (NFm m)),
    (∀ X ∈ Γ, (X.subst σ).full ∈ Δ) → VSPrf Δ (A.subst σ).full := by
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
    refine VSPrf.packet (Syn.subst σ s) (Syn.subst σ t) (Syn.subst σ u) (Syn.subst (up σ) h)
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
    have k := VSPrf.qE (B := (B.subst (up σ)).full) (Syn.subst σ t) (ih₁ σ Δ hs) (by
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

/-- **Substitution for a variable is enough.**  The kernel derives a sequent
exactly when the calculus on full normal forms whose only equality rule
substitutes for a variable derives its full normal form. -/
theorem vsprf_iff_nprf : VSPrf (Γ.map NFm.full) A.full ↔ NPrf Γ A := by
  constructor
  · intro h
    refine (equivFull A).mpr (h.toNPrf.cut fun B hB => ?_)
    obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hB
    exact (equivFull C).mp (.hyp hC)
  · intro h
    have k := h.toVS Syn.var (Γ.map NFm.full) fun X hX => by
      rw [NFm.subst_id]; exact List.mem_map_of_mem hX
    rwa [NFm.subst_id] at k

end LeanProofs.ConciseIPRA
