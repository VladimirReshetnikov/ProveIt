import ConciseIPRA.NativePublic

/-!
# The root-determined introduction alone

`RDPrf` is the kernel with the root-determined introduction in place of its
two introductions (progress at a literal equation, cases at a compound
matrix) and with *unrestricted* transport.  It contains `PGPrf` of
`NativePublic`, whose transport is restricted to iterator sources.

* On a public language the root-determined introduction is complete, with or
  without a restriction of the sources: `rdprf_pub_iff`.
* On arbitrary formulas it is not, whatever the sources:
  `rdprf_not_cases` shows that `RDPrf` does not derive `D_{x,y} (y = 1)`,
  which the kernel derives by cases (`nprf_cases_example`).  Hence
  `rdprf_strictly_weaker`, and the same for every calculus between `PGPrf`
  and `RDPrf`, in particular for the restriction "no literal `0` as a
  source" of the guarded packages.

The proof is the *progressive* reading of the formulas over the natural
numbers (`Prog.T`): a closure over a literal equation is read as
progressivity, `∀ z (E(z) → E(S z))`, and a closure over a compound matrix
as `B(0) → ∀ y B(y)`.  Every rule of `RDPrf` is sound for it
(`RDPrf.sound`): the introduction at an equation is literally progress, and
`QE` at an equation is induction from the base.  The introduction by cases of
an equation is not sound for it: `y = 1` fails at `0`, so the case step is
vacuous, but `y = 1` is not progressive.

Together with `NativePublicNecessary` this separates the two restrictions:
iterator sources lose transitivity of raw equations, and the root-determined
introduction loses the introduction by cases of raw equations.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm
open Tm (zero succ iter)

variable {n m : ℕ}

/-- Derivability with the root-determined introduction and unrestricted
transport. -/
inductive RDPrf : {n : ℕ} → List (NFm n) → NFm n → Prop
  | hyp {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (h : A ∈ Γ) : RDPrf Γ A
  | iterZero {n : ℕ} {Γ : List (NFm n)} (a : Tm n) (h : Tm (n + 1)) :
      RDPrf Γ (.eq (iter zero a h) a)
  | iterSucc {n : ℕ} {Γ : List (NFm n)} (c a : Tm n) (h : Tm (n + 1)) :
      RDPrf Γ (.eq (iter (succ c) a h) (Syn.subst (inst (iter c a h)) h))
  | trOne {n : ℕ} {Γ : List (NFm n)} (h : Tm (n + 1)) {s t u : Tm n}
      (h₁ : RDPrf Γ (.eq s t)) (h₂ : RDPrf Γ (.eq (Syn.subst (inst s) h) u)) :
      RDPrf Γ (.eq u (Syn.subst (inst t) h))
  | qE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 1)} (t : Tm n)
      (h₁ : RDPrf Γ (.Q B)) (h₂ : RDPrf Γ (B.subst (inst zero))) : RDPrf Γ (B.subst (inst t))
  | dE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 2)} {A : NFm n}
      (h₁ : RDPrf Γ (.D B)) (h₂ : RDPrf (.Q B :: Γ.map NFm.shift) A.shift) : RDPrf Γ A
  | dI {n : ℕ} {Γ : List (NFm n)} (B : NFm (n + 2)) (t : Tm n)
      (h : RDPrf ((B.subst (up (inst t))).subst (repl (NFm.eta B (Syn.var 0)))
          :: Γ.map NFm.shift)
        ((B.subst (up (inst t))).subst (repl (succ (var 0))))) : RDPrf Γ (.D B)

variable {Γ : List (NFm n)} {A : NFm n}

theorem PGPrf.toRD (h : PGPrf Γ A) : RDPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | trI h c a g _ _ ih₁ ih₂ => exact .trOne h ih₁ ih₂
  | qE t _ _ ih₁ ih₂ => exact .qE t ih₁ ih₂
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dI B t _ ih => exact .dI B t ih

theorem RDPrf.toNPrf (h : RDPrf Γ A) : NPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | trOne h _ _ ih₁ ih₂ => exact .trOne h ih₁ ih₂
  | qE t _ _ ih₁ ih₂ => exact .qE t ih₁ ih₂
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dI B t _ ih => exact .ofDIEta B t ih

/-- **On a public language the root-determined introduction is complete**,
with unrestricted transport as well. -/
theorem rdprf_pub_iff (g : Gating) : RDPrf (Γ.map (NFm.pub g)) (A.pub g) ↔ NPrf Γ A :=
  ⟨fun h => (NEquiv.pub g A).mp (h.toNPrf.cut fun B hB => by
      obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hB
      exact (NEquiv.pub g C).mpr (.hyp hC)), fun h => (h.toPG g).toRD⟩

namespace Prog

/-- The closure of a property of numbers: progressivity at a literal equation,
the conditional closure otherwise. -/
def clo (e : Bool) (P : ℕ → Prop) : Prop :=
  (e = true → ∀ z, P z → P (z + 1)) ∧ (e = false → P 0 → ∀ d, P d)

/-- The progressive reading over the natural numbers. -/
def T : {n : ℕ} → NFm n → (Fin n → ℕ) → Prop
  | _, .eq a b, ρ => a.val .std ρ = b.val .std ρ
  | _, .Q B, ρ => clo B.isEq fun y => T B (Fin.cases y ρ)
  | _, .D B, ρ => ∃ x, clo B.isEq fun y => T B (Fin.cases y (Fin.cases x ρ))

theorem T_subst (A : NFm n) : ∀ {m : ℕ} (σ : Fin n → Tm m) (ρ : Fin m → ℕ),
    T (A.subst σ) ρ = T A fun i => (σ i).val .std ρ := by
  induction A with intro m σ ρ
  | eq s t => simp only [NFm.subst_eq, T, Tm.val_subst]
  | Q B ih => simp only [NFm.subst_Q, T, ih, Tm.val_up, NFm.isEq_subst]
  | D B ih => simp only [NFm.subst_D, T, ih, Tm.val_up, NFm.isEq_subst]

theorem T_shift (A : NFm n) (b : ℕ) (ρ : Fin n → ℕ) : T A.shift (Fin.cases b ρ) = T A ρ := by
  unfold NFm.shift
  rw [T_subst]
  rfl

theorem T_inst (B : NFm (n + 1)) (t : Tm n) (ρ : Fin n → ℕ) :
    T (B.subst (inst t)) ρ = T B (Fin.cases (t.val .std ρ) ρ) := by
  rw [T_subst, Tm.val_inst]

theorem T_repl (B : NFm (n + 1)) (s : Tm (n + 1)) (z : ℕ) (ρ : Fin n → ℕ) :
    T (B.subst (repl s)) (Fin.cases z ρ) = T B (Fin.cases (s.val .std (Fin.cases z ρ)) ρ) := by
  rw [T_subst, Tm.val_repl]

theorem T_up_inst (B : NFm (n + 2)) (t : Tm n) (y : ℕ) (ρ : Fin n → ℕ) :
    T (B.subst (up (inst t))) (Fin.cases y ρ)
      = T B (Fin.cases y (Fin.cases (t.val .std ρ) ρ)) := by
  rw [T_subst, Tm.val_up, Tm.val_inst]

end Prog

open Prog in
/-- Every rule of `RDPrf` is sound for the progressive reading. -/
theorem RDPrf.sound (h : RDPrf Γ A) : ∀ ρ : Fin n → ℕ, (∀ C ∈ Γ, T C ρ) → T A ρ := by
  induction h with
  | hyp h => intro ρ hΓ; exact hΓ _ h
  | iterZero a g =>
    intro ρ _
    exact NPrf.sound_std (Γ := []) (.iterZero a g) ρ (fun _ hX => nomatch hX)
  | iterSucc c a g =>
    intro ρ _
    exact NPrf.sound_std (Γ := []) (.iterSucc c a g) ρ (fun _ hX => nomatch hX)
  | @trOne _ Γ h s t u _ _ ih₁ ih₂ =>
    intro ρ hΓ
    have e₁ : s.val .std ρ = t.val .std ρ := ih₁ ρ hΓ
    have e₂ : (Syn.subst (inst s) h).val .std ρ = u.val .std ρ := ih₂ ρ hΓ
    show u.val .std ρ = (Syn.subst (inst t) h).val .std ρ
    rw [Tm.val_subst, Tm.val_inst] at e₂ ⊢
    rw [← e₁]
    exact e₂.symm
  | @qE _ Γ B t _ _ ih₁ ih₂ =>
    intro ρ hΓ
    have h0 := ih₂ ρ hΓ
    rw [T_inst] at h0 ⊢
    have hq : clo B.isEq fun y => T B (Fin.cases y ρ) := ih₁ ρ hΓ
    cases hB : B.isEq with
    | true =>
      -- induction from the base
      have all : ∀ d : ℕ, T B (Fin.cases d ρ) := fun d => by
        induction d with
        | zero => exact h0
        | succ d ihd => exact hq.1 hB d ihd
      exact all _
    | false => exact hq.2 hB h0 _
  | @dE _ Γ B A _ _ ih₁ ih₂ =>
    intro ρ hΓ
    obtain ⟨x, hx⟩ := ih₁ ρ hΓ
    have k := ih₂ (Fin.cases x ρ) (by
      intro C hC
      rcases List.mem_cons.1 hC with rfl | hC
      · exact hx
      · obtain ⟨C₀, hC₀, rfl⟩ := List.mem_map.1 hC
        rw [T_shift]
        exact hΓ _ hC₀)
    rwa [T_shift] at k
  | @dI n Γ B t _ ih =>
    intro ρ hΓ
    have hΓ' : ∀ (z : ℕ), ∀ C ∈ Γ.map NFm.shift, T C (Fin.cases z ρ) := by
      intro z C hC
      obtain ⟨C₀, hC₀, rfl⟩ := List.mem_map.1 hC
      rw [T_shift]
      exact hΓ _ hC₀
    refine ⟨t.val .std ρ, fun hB z hz => ?_, fun hB h0 d => ?_⟩
    · -- a literal equation: the premise is progress
      have he : NFm.eta B (Syn.var 0 : Tm (n + 1)) = Syn.var 0 := by
        unfold NFm.eta
        rw [hB]
        rfl
      have c := ih (Fin.cases z ρ) (by
        intro C hC
        rcases List.mem_cons.1 hC with rfl | hC
        · rw [he, NFm.subst_repl_var, T_up_inst]
          exact hz
        · exact hΓ' z C hC)
      rw [T_repl, T_up_inst] at c
      exact c
    · -- a compound matrix: cases
      have he : NFm.eta B (Syn.var 0 : Tm (n + 1)) = zero := by
        unfold NFm.eta
        rw [hB]
        rfl
      cases d with
      | zero => exact h0
      | succ d =>
        have c := ih (Fin.cases d ρ) (by
          intro C hC
          rcases List.mem_cons.1 hC with rfl | hC
          · rw [he, T_repl, T_up_inst]
            exact h0
          · exact hΓ' d C hC)
        rw [T_repl, T_up_inst] at c
        exact c

/-- The kernel derives `D_{x,y} (y = 1)` by cases: its base `0 = 1` is absurd. -/
theorem nprf_cases_example :
    NPrf ([] : List (NFm 0)) (.D (.eq (Syn.var 0) (succ zero))) := by
  refine .dICase _ zero ?_
  simp only [NFm.subst_eq, NFm.shift, Syn.subst_var, Syn.up_zero, Syn.inst_zero, Syn.repl_zero,
    Tm.subst_succ, Tm.subst_zero, List.map_nil]
  exact NPrf.botEq (.hyp List.mem_cons_self) _ _

/-- **The introduction by cases of an equation is not derivable** from the
root-determined introduction, with unrestricted transport. -/
theorem rdprf_not_cases :
    ¬ RDPrf ([] : List (NFm 0)) (.D (.eq (Syn.var 0) (succ zero))) := by
  intro h
  obtain ⟨x, hx⟩ := h.sound Fin.elim0 (fun _ hC => nomatch hC)
  have k : (1 : ℕ) + 1 = 0 + 1 := hx.1 rfl 1 rfl
  exact absurd k (by decide)

/-- **The root-determined introduction is strictly weaker on arbitrary
formulas**, whatever the transport sources. -/
theorem rdprf_strictly_weaker : ∃ A : NFm 0, NPrf [] A ∧ ¬ RDPrf [] A :=
  ⟨_, nprf_cases_example, rdprf_not_cases⟩

/-- The same for the calculus with transport at iterator sources only. -/
theorem pgprf_not_cases :
    ¬ PGPrf ([] : List (NFm 0)) (.D (.eq (Syn.var 0) (succ zero))) := fun h =>
  rdprf_not_cases h.toRD

end LeanProofs.ConciseIPRA
