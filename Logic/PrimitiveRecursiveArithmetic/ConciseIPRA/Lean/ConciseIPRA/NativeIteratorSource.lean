import ConciseIPRA.NativePublicD
import ConciseIPRA.NativePublicNecessary

/-!
# Transport at iterator sources alone

`TIPrf` is the kernel with one change: transport is allowed at iterator
sources only.  Its two introductions are those of the kernel.  With `RDPrf`
(the root-determined introduction, unrestricted transport) and `PGPrf` (both
restrictions) it completes the picture of `NativePublic`:

|          | introduction     | transport sources |
| -------- | ---------------- | ----------------- |
| kernel   | cases, progress  | all               |
| `RDPrf`  | root-determined  | all               |
| `TIPrf`  | cases, progress  | iterators         |
| `PGPrf`  | root-determined  | iterators         |

* `PGPrf.toTI`: `TIPrf` contains `PGPrf`.  The root-determined introduction
  at a literal equation is `Q` by progress followed by the introduction by
  cases.
* `tiprf_pub_iff`, `tiprf_pubD_iff`: on a public language `TIPrf` derives the
  translation of a sequent exactly when the kernel derives the sequent.
* `tiprf_not_trans`, `tiprf_strictly_weaker`: on arbitrary sequents it is
  strictly weaker; `x = y, y = z ⊢ x = z` between variables is not derivable.
  The reading with colours of `NativePublicNecessary` is sound for the two
  introductions of the kernel as well (`TIPrf.sound`).

So the loss of transitivity is caused by the source restriction alone, and
the loss of the introduction by cases of a raw equation by the
root-determined introduction alone (`NativeRootDetermined`).
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm
open Tm (zero succ iter)

variable {n m : ℕ}

/-- The kernel with transport at iterator sources only. -/
inductive TIPrf : {n : ℕ} → List (NFm n) → NFm n → Prop
  | hyp {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (h : A ∈ Γ) : TIPrf Γ A
  | iterZero {n : ℕ} {Γ : List (NFm n)} (a : Tm n) (h : Tm (n + 1)) :
      TIPrf Γ (.eq (iter zero a h) a)
  | iterSucc {n : ℕ} {Γ : List (NFm n)} (c a : Tm n) (h : Tm (n + 1)) :
      TIPrf Γ (.eq (iter (succ c) a h) (Syn.subst (inst (iter c a h)) h))
  | trI {n : ℕ} {Γ : List (NFm n)} (h : Tm (n + 1)) (c a : Tm n) (g : Tm (n + 1)) {t u : Tm n}
      (h₁ : TIPrf Γ (.eq (iter c a g) t))
      (h₂ : TIPrf Γ (.eq (Syn.subst (inst (iter c a g)) h) u)) :
      TIPrf Γ (.eq u (Syn.subst (inst t) h))
  | qE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 1)} (t : Tm n)
      (h₁ : TIPrf Γ (.Q B)) (h₂ : TIPrf Γ (B.subst (inst zero))) : TIPrf Γ (B.subst (inst t))
  | dE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 2)} {A : NFm n}
      (h₁ : TIPrf Γ (.D B)) (h₂ : TIPrf (.Q B :: Γ.map NFm.shift) A.shift) : TIPrf Γ A
  | dICase {n : ℕ} {Γ : List (NFm n)} (B : NFm (n + 2)) (t : Tm n)
      (h : TIPrf (((B.subst (up (inst t))).subst (inst zero)).shift :: Γ.map NFm.shift)
        ((B.subst (up (inst t))).subst (repl (succ (var 0))))) :
      TIPrf Γ (.D B)
  | qIInd {n : ℕ} {Γ : List (NFm n)} (s₁ s₂ : Tm (n + 1))
      (h : TIPrf (NFm.eq s₁ s₂ :: Γ.map NFm.shift)
        ((NFm.eq s₁ s₂).subst (repl (succ (var 0))))) :
      TIPrf Γ (.Q (.eq s₁ s₂))

namespace TIPrf

variable {Γ : List (NFm n)} {A : NFm n}

theorem toNPrf (h : TIPrf Γ A) : NPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | trI h c a g _ _ ih₁ ih₂ => exact .trOne h ih₁ ih₂
  | qE t _ _ ih₁ ih₂ => exact .qE t ih₁ ih₂
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dICase B t _ ih => exact .dICase B t ih
  | qIInd s t _ ih => exact .qIInd s t ih

theorem hyp0 : TIPrf (A :: Γ) A := .hyp List.mem_cons_self

theorem weaken (h : TIPrf Γ A) : ∀ {Δ : List (NFm n)}, Γ ⊆ Δ → TIPrf Δ A := by
  induction h with
  | hyp h => intro Δ s; exact .hyp (s h)
  | iterZero a h => intro Δ _; exact .iterZero a h
  | iterSucc c a h => intro Δ _; exact .iterSucc c a h
  | trI h c a g _ _ ih₁ ih₂ => intro Δ s; exact .trI h c a g (ih₁ s) (ih₂ s)
  | qE t _ _ ih₁ ih₂ => intro Δ s; exact .qE t (ih₁ s) (ih₂ s)
  | dE _ _ ih₁ ih₂ =>
    intro Δ s
    exact .dE (ih₁ s) (ih₂ (List.cons_subset_cons _ (List.map_subset _ s)))
  | dICase B t _ ih =>
    intro Δ s
    exact .dICase B t (ih (List.cons_subset_cons _ (List.map_subset _ s)))
  | qIInd s₁ s₂ _ ih =>
    intro Δ s
    exact .qIInd s₁ s₂ (ih (List.cons_subset_cons _ (List.map_subset _ s)))

theorem wk {B : NFm n} (h : TIPrf Γ A) : TIPrf (B :: Γ) A :=
  h.weaken (List.subset_cons_self _ _)

/-- Substitution of terms for the free variables of a derivation: a source
stays an iterator. -/
theorem subst (h : TIPrf Γ A) : ∀ {m : ℕ} (σ : Fin n → Tm m),
    TIPrf (Γ.map fun B => B.subst σ) (A.subst σ) := by
  induction h with intro m σ
  | hyp h => exact .hyp (List.mem_map_of_mem h)
  | iterZero a h => exact .iterZero _ _
  | iterSucc c a h =>
    simp only [NFm.subst_eq, Tm.subst_iter, Tm.subst_succ, Syn.subst_subst_inst]
    exact .iterSucc _ _ _
  | trI h c a g _ _ ih₁ ih₂ =>
    have h₁ := ih₁ σ
    have h₂ := ih₂ σ
    simp only [NFm.subst_eq, Syn.subst_subst_inst, Tm.subst_iter] at h₁ h₂ ⊢
    exact .trI _ _ _ _ h₁ h₂
  | qE t _ _ ih₁ ih₂ =>
    have h₂ := ih₂ σ
    rw [NFm.subst_inst] at h₂ ⊢
    exact .qE _ (ih₁ σ) h₂
  | dE _ _ ih₁ ih₂ =>
    have h := ih₂ (up σ)
    rw [List.map_cons, NFm.map_shift_subst, NFm.shift_subst_up] at h
    exact .dE (ih₁ σ) h
  | dICase B t _ ih =>
    have h := ih (up σ)
    rw [List.map_cons, NFm.map_shift_subst, NFm.shift_subst_up, NFm.subst_inst,
      NFm.subst_repl_succ, NFm.subst_up_inst] at h
    exact .dICase _ _ h
  | qIInd s₁ s₂ _ ih =>
    have h := ih (up σ)
    rw [List.map_cons, NFm.map_shift_subst, NFm.subst_repl_succ] at h
    exact .qIInd (Syn.subst (up σ) s₁) (Syn.subst (up σ) s₂) h

theorem shift (h : TIPrf Γ A) : TIPrf (Γ.map NFm.shift) A.shift := h.subst _

/-- From the base and a closure moved under a fresh variable, the successor
instance. -/
theorem qStep (B : NFm (n + 1)) {Δ : List (NFm (n + 1))} (hQ : TIPrf Δ (NFm.Q B).shift)
    (h0 : TIPrf Δ (B.subst (repl zero))) : TIPrf Δ (B.subst (repl (succ (Syn.var 0)))) := by
  rw [← NFm.subst_dummy_up_inst] at h0 ⊢
  exact .qE (succ (Syn.var 0)) hQ h0

/-- The root-determined introduction is a derived rule: at a literal equation
it is `Q` by progress followed by the introduction by cases. -/
theorem ofDIEta (B : NFm (n + 2)) (t : Tm n)
    (h : TIPrf ((B.subst (up (inst t))).subst (repl (NFm.eta B (Syn.var 0))) :: Γ.map NFm.shift)
      ((B.subst (up (inst t))).subst (repl (succ (Syn.var 0))))) : TIPrf Γ (.D B) := by
  cases B with
  | eq a b =>
    rw [show NFm.eta (NFm.eq a b) (Syn.var 0 : Tm (n + 1)) = Syn.var 0 from rfl,
      NFm.subst_repl_var] at h
    have hQ := TIPrf.qIInd (Syn.subst (up (inst t)) a) (Syn.subst (up (inst t)) b) h
    refine .dICase (.eq a b) t ?_
    refine qStep _ hQ.shift.wk ?_
    rw [← NFm.shift_subst_inst_zero]
    exact hyp0
  | Q B' =>
    refine .dICase _ t ?_
    rw [NFm.shift_subst_inst_zero]
    exact h
  | D B' =>
    refine .dICase _ t ?_
    rw [NFm.shift_subst_inst_zero]
    exact h

end TIPrf

variable {Γ : List (NFm n)} {A : NFm n}

/-- `TIPrf` contains the calculus with both restrictions. -/
theorem PGPrf.toTI (h : PGPrf Γ A) : TIPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | trI h c a g _ _ ih₁ ih₂ => exact .trI h c a g ih₁ ih₂
  | qE t _ _ ih₁ ih₂ => exact .qE t ih₁ ih₂
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dI B t _ ih => exact .ofDIEta B t ih

/-- **On a public language transport at iterator sources is enough**, with the
two introductions of the kernel. -/
theorem tiprf_pub_iff (g : Gating) : TIPrf (Γ.map (NFm.pub g)) (A.pub g) ↔ NPrf Γ A :=
  ⟨fun h => (pgprf_pub_iff g).mp ((pgprf_pub_iff g).mpr
      ((NEquiv.pub g A).mp (h.toNPrf.cut fun B hB => by
        obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hB
        exact (NEquiv.pub g C).mpr (.hyp hC)))), fun h => ((pgprf_pub_iff g).mpr h).toTI⟩

/-- The same on the language without `Q`. -/
theorem tiprf_pubD_iff : TIPrf (Γ.map NFm.pubD) A.pubD ↔ NPrf Γ A :=
  ⟨fun h => (NEquiv.pubD A).mp (h.toNPrf.cut fun B hB => by
      obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hB
      exact (NEquiv.pubD C).mpr (.hyp hC)), fun h => (pgprf_pubD_iff.mpr h).toTI⟩

open Colour in
/-- Every rule of `TIPrf` is sound for the reading with colours. -/
theorem TIPrf.sound (h : TIPrf Γ A) : ∀ ρ : Fin n → V, (∀ C ∈ Γ, T C ρ) → T A ρ := by
  induction h with
  | hyp h => intro ρ hΓ; exact hΓ _ h
  | iterZero a g =>
    intro ρ _
    refine .inl ?_
    rw [tval_fst, tval_fst]
    exact NPrf.sound_std (Γ := []) (.iterZero a g) _ (fun _ hX => nomatch hX)
  | iterSucc c a g =>
    intro ρ _
    refine .inl ?_
    rw [tval_fst, tval_fst]
    exact NPrf.sound_std (Γ := []) (.iterSucc c a g) _ (fun _ hX => nomatch hX)
  | trI h c a g _ _ ih₁ ih₂ =>
    intro ρ hΓ
    exact tr_sound h rfl (ih₁ ρ hΓ) (ih₂ ρ hΓ)
  | @qE _ Γ B t _ _ ih₁ ih₂ =>
    intro ρ hΓ
    have h0 := ih₂ ρ hΓ
    rw [T_inst] at h0 ⊢
    exact T_mono_first B (tval t ρ) ρ (ih₁ ρ hΓ h0 (tval t ρ).1)
  | @dE _ Γ B A _ _ ih₁ ih₂ =>
    intro ρ hΓ
    obtain ⟨d, hd⟩ := ih₁ ρ hΓ
    have k := ih₂ (Fin.cases (d, 0) ρ) (by
      intro C hC
      rcases List.mem_cons.1 hC with rfl | hC
      · exact hd
      · obtain ⟨C₀, hC₀, rfl⟩ := List.mem_map.1 hC
        rw [T_shift]
        exact hΓ _ hC₀)
    rwa [T_shift] at k
  | @dICase n Γ B t _ ih =>
    intro ρ hΓ
    have hΓ' : ∀ (e : ℕ), ∀ C ∈ Γ.map NFm.shift, T C (Fin.cases (e, 0) ρ) := by
      intro e C hC
      obtain ⟨C₀, hC₀, rfl⟩ := List.mem_map.1 hC
      rw [T_shift]
      exact hΓ _ hC₀
    refine ⟨(tval t ρ).1, fun h0 e => ?_⟩
    cases e with
    | zero => exact h0
    | succ e =>
      cases hB : B.isEq with
      | false =>
        have c := ih (Fin.cases (e, 0) ρ) (by
          intro C hC
          rcases List.mem_cons.1 hC with rfl | hC
          · rw [T_shift, T_inst, T_up_inst]
            exact (T_recolor_second B hB _ _ _).mp h0
          · exact hΓ' e C hC)
        rw [T_repl, T_up_inst] at c
        exact (T_recolor_second B hB _ _ _).mpr c
      | true =>
        obtain ⟨a, b, rfl⟩ : ∃ a b, B = NFm.eq a b := by
          cases B with
          | eq a b => exact ⟨a, b, rfl⟩
          | Q B' => cases hB
          | D B' => cases hB
        have c := ih (Fin.cases (e, 0) ρ) (by
          intro C hC
          rcases List.mem_cons.1 hC with rfl | hC
          · rw [T_shift, T_inst, T_up_inst]
            exact T_eq_mono_second (0, 0) (tval t ρ) ρ h0
          · exact hΓ' e C hC)
        rw [T_repl, T_up_inst] at c
        exact T_eq_back c h0
  | @qIInd n Γ s t _ ih =>
    intro ρ hΓ h0 d
    induction d with
    | zero => exact h0
    | succ d ihd =>
      have c := ih (Fin.cases (d, 0) ρ) (by
        intro C hC
        rcases List.mem_cons.1 hC with rfl | hC
        · exact ihd
        · obtain ⟨C₀, hC₀, rfl⟩ := List.mem_map.1 hC
          rw [T_shift]
          exact hΓ _ hC₀)
      rw [T_repl] at c
      exact c

open Colour in
/-- **Transitivity between variables is not derivable** with transport at
iterator sources only, even with both introductions of the kernel. -/
theorem tiprf_not_trans :
    ¬ TIPrf [NFm.eq (Syn.var 0 : Tm 3) (Syn.var 1), NFm.eq (Syn.var 1) (Syn.var 2)]
      (.eq (Syn.var 0) (Syn.var 2)) := by
  intro h
  have k := h.sound (fun i => ((i : ℕ), (i : ℕ) + 1)) (by
    intro C hC
    rcases List.mem_cons.1 hC with rfl | hC
    · exact .inr (.inl ⟨rfl, rfl⟩)
    · rcases List.mem_cons.1 hC with rfl | hC
      · exact .inr (.inr (.inr (.inl ⟨rfl, rfl⟩)))
      · exact nomatch hC)
  rcases (show (0 : ℕ) = 2 ∨ H 1 3 from k) with e | e
  · exact absurd e (by decide)
  · rcases e with ⟨_, e⟩ | ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ <;> exact absurd e (by decide)

/-- **The source restriction alone is strictly weaker on arbitrary
sequents.** -/
theorem tiprf_strictly_weaker :
    ∃ (Γ : List (NFm 3)) (A : NFm 3), NPrf Γ A ∧ ¬ TIPrf Γ A :=
  ⟨_, _, NPrf.eqTrans (.hyp List.mem_cons_self)
    (.hyp (List.mem_cons_of_mem _ List.mem_cons_self)), tiprf_not_trans⟩

end LeanProofs.ConciseIPRA
