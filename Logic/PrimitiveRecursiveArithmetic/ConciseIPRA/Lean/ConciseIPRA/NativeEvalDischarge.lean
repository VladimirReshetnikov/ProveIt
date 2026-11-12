import ConciseIPRA.NativeUniformClauses

/-!
# Evaluation at the discharge of a witness

The raw calculus of the package `evaluation_discharge`: three inference
families on raw iterator terms with clause contexts.  `E3Prf` has Use and
Intro of the uniform clause calculus `VPrf`, and one rule in place of the two
cases of Eval and of the elimination of `D`:

  from `D_{x,y} B`, and from `E` and `F` under the clause of a fresh `b`,
  infer `ρ_E(F)`, provided `b` does not occur in it.

`ρ_E(F)` is one deterministic evaluation step (`Rho`):

* `ρ_{s = t}(I(0, s; u.h) = r)` is `r = t`;
* `ρ_{I(c, a; u.h) = t}(I(S c, a; u.h) = r)` is `r = h[t/u]`;
* `ρ_E(F)` is `F` in every other case.

`Rho E F R` is the graph of `ρ`; it is functional (`Rho.functional`) and, the
case distinction being decidable only classically here, total
(`Rho.total`).

`e3prf_iff_vprf : E3Prf Γ A ↔ VPrf Γ A` for every clause context, so with the
reflexivity clause `e3prf_iff_nprf_of_qfree`.

From `VPrf`: an elimination is a discharge with the auxiliary formula
`Θ = D_{x,y} (0 = 0)`, which is compound and so selects the identity; an Eval
step is a discharge of `Θ` whose two branches are the premises moved under the
fresh variable.  `E3Prf` is not shown closed under renaming first: the
translation carries a renaming and an extension of the context
(`VPrf.toE3`), as in the package's induction on the original derivation.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open Tm (zero succ iter)

variable {n m : ℕ}

/-- The graph of the evaluation step `ρ_E(F)`. -/
inductive Rho : {n : ℕ} → NFm n → NFm n → NFm n → Prop
  | zeroCase {n : ℕ} (h : Tm (n + 1)) {s t r : Tm n} :
      Rho (.eq s t) (.eq (iter zero s h) r) (.eq r t)
  | succCase {n : ℕ} {c a : Tm n} {h : Tm (n + 1)} {t r : Tm n} :
      Rho (.eq (iter c a h) t) (.eq (iter (succ c) a h) r) (.eq r (Syn.subst (inst t) h))
  | idCase {n : ℕ} {E F : NFm n}
      (hz : ∀ (s t r : Tm n) (h : Tm (n + 1)),
        ¬(E = .eq s t ∧ F = .eq (iter zero s h) r))
      (hs : ∀ (c a t r : Tm n) (h : Tm (n + 1)),
        ¬(E = .eq (iter c a h) t ∧ F = .eq (iter (succ c) a h) r)) :
      Rho E F F

/-- The evaluation step is deterministic. -/
theorem Rho.functional {E F R R' : NFm n} (h : Rho E F R) (h' : Rho E F R') : R = R' := by
  cases h with
  | zeroCase g =>
    cases h' with
    | zeroCase g' => rfl
    | idCase hz _ => exact absurd ⟨rfl, rfl⟩ (hz _ _ _ _)
  | succCase =>
    cases h' with
    | succCase => rfl
    | idCase _ hs => exact absurd ⟨rfl, rfl⟩ (hs _ _ _ _ _)
  | idCase hz hs =>
    cases h' with
    | zeroCase g => exact absurd ⟨rfl, rfl⟩ (hz _ _ _ _)
    | succCase => exact absurd ⟨rfl, rfl⟩ (hs _ _ _ _ _)
    | idCase _ _ => rfl

/-- The evaluation step is defined on every pair of formulas. -/
theorem Rho.total (E F : NFm n) : ∃ R, Rho E F R := by
  classical
  by_cases hz : ∃ (s t r : Tm n) (h : Tm (n + 1)), E = .eq s t ∧ F = .eq (iter zero s h) r
  · obtain ⟨s, t, r, h, rfl, rfl⟩ := hz
    exact ⟨_, .zeroCase h⟩
  · by_cases hs : ∃ (c a t r : Tm n) (h : Tm (n + 1)),
        E = .eq (iter c a h) t ∧ F = .eq (iter (succ c) a h) r
    · obtain ⟨c, a, t, r, h, rfl, rfl⟩ := hs
      exact ⟨_, .succCase⟩
    · exact ⟨F, .idCase (fun s t r h k => hz ⟨s, t, r, h, k⟩)
        (fun c a t r h k => hs ⟨c, a, t, r, h, k⟩)⟩

/-- Derivability with Use, Intro and the evaluating discharge. -/
inductive E3Prf : {n : ℕ} → List (UCl n) → NFm n → Prop
  | use {n : ℕ} {Γ : List (UCl n)} {c : UCl n} (t : Tm n) (hc : c ∈ Γ)
      (h : ∀ A, c.ante = some A → E3Prf Γ A) : E3Prf Γ (c.cons.subst (inst t))
  | intro {n : ℕ} {Γ : List (UCl n)} (B : NFm (n + 2)) (t : Tm n) (hB : B.QFree)
      (h : E3Prf (UCl.asm ((B.subst (up (inst t))).subst (repl (NFm.start B t)))
          :: Γ.map UCl.shift)
        ((B.subst (up (inst t))).subst (repl (succ (var 0))))) :
      E3Prf Γ (.D B)
  /-- Evaluate and discharge: the conclusion `ρ_E(F)` does not mention the
  fresh variable. -/
  | discharge {n : ℕ} {Γ : List (UCl n)} {B : NFm (n + 2)} {E F : NFm (n + 1)} {A : NFm n}
      (h₁ : E3Prf Γ (.D B))
      (hE : E3Prf (⟨some (B.subst (inst zero)), B⟩ :: Γ.map UCl.shift) E)
      (hF : E3Prf (⟨some (B.subst (inst zero)), B⟩ :: Γ.map UCl.shift) F)
      (hρ : Rho E F A.shift) : E3Prf Γ A

/-- Every derivation is a derivation of the uniform clause calculus: evaluate
inside the scope of the witness, then eliminate. -/
theorem E3Prf.toVPrf {Γ : List (UCl n)} {A : NFm n} (h : E3Prf Γ A) : VPrf Γ A := by
  induction h with
  | use t hc _ ih => exact .use t hc ih
  | intro B t hB _ ih => exact .intro B t hB ih
  | @discharge _ Γ B E F A _ _ _ hρ ih₁ ihE ihF =>
    refine .elim ih₁ ?_
    generalize A.shift = R at hρ ⊢
    cases hρ with
    | zeroCase h => exact .evalZero h ihE ihF
    | succCase => exact .evalSucc ihE ihF
    | idCase _ _ => exact ihF

/-- `Θ = D_{x,y} (0 = 0)` is derivable in every context. -/
theorem E3Prf.theta {Γ : List (UCl n)} : E3Prf Γ (.D (.eq zero zero)) := by
  refine .intro _ zero trivial ?_
  exact E3Prf.use (c := UCl.asm (.eq zero zero)) zero List.mem_cons_self
    (fun A hA => by cases hA)

/-! ### Renaming of clauses -/

namespace NFm

theorem rn_shift (A : NFm n) (ξ : Fin n → Fin m) :
    (A.subst fun i => (Syn.var (ξ i) : Tm m)).shift
      = A.subst fun i => (Syn.var (ξ i).succ : Tm (m + 1)) := by
  rw [NFm.shift, NFm.subst_subst]
  simp only [Syn.subst_var]

theorem rn_bsh (B : NFm (n + 1)) (ξ : Fin n → Fin m) :
    (B.subst (up fun i => (Syn.var (ξ i) : Tm m))).subst (up fun i => Syn.var i.succ)
      = B.subst (up fun i => (Syn.var (ξ i).succ : Tm (m + 1))) := by
  rw [NFm.subst_subst]
  refine B.subst_ext (Fin.cases ?_ fun j => ?_) <;> simp [Syn.shift]

end NFm

namespace UCl

/-- Renaming of the free variables of a clause. -/
def rn (ξ : Fin n → Fin m) (c : UCl n) : UCl m :=
  ⟨c.ante.map fun A => A.subst fun i => (Syn.var (ξ i) : Tm m),
    c.cons.subst (up fun i => (Syn.var (ξ i) : Tm m))⟩

theorem rn_id (c : UCl n) : c.rn id = c := by
  obtain ⟨a, b⟩ := c
  cases a <;> simp [rn, Syn.up_var, NFm.subst_id]

theorem rn_shift (ξ : Fin n → Fin m) (c : UCl n) :
    (c.rn ξ).shift = c.rn fun i => (ξ i).succ := by
  obtain ⟨a, b⟩ := c
  cases a <;> simp only [rn, shift, Option.map_none, Option.map_some, NFm.rn_shift, NFm.rn_bsh]

theorem shift_rn (ξ : Fin n → Fin m) (c : UCl n) :
    c.shift.rn (Tm.upRen ξ) = (c.rn ξ).shift := by
  obtain ⟨a, b⟩ := c
  cases a <;>
    simp only [rn, shift, Option.map_none, Option.map_some, ← Tm.up_rn, NFm.shift_subst_up,
      NFm.subst_dummy_comm]

theorem asm_rn (X : NFm n) (ξ : Fin n → Fin m) :
    (asm X).rn ξ = asm (X.subst fun i => (Syn.var (ξ i) : Tm m)) := by
  simp only [rn, asm, Option.map_none, NFm.shift_subst_up]

/-- A renaming of a context into another one, under one more variable and one
more clause. -/
theorem liftRn {Γ : List (UCl n)} {Δ : List (UCl m)} {ξ : Fin n → Fin m}
    (R : ∀ c ∈ Γ, c.rn ξ ∈ Δ) (c₀ : UCl (m + 1)) :
    ∀ c ∈ Γ, c.rn (fun i => (ξ i).succ) ∈ c₀ :: Δ.map UCl.shift := fun c hc =>
  List.mem_cons_of_mem _ (by rw [← rn_shift]; exact List.mem_map_of_mem (R c hc))

/-- The same for a context that was itself moved under a variable. -/
theorem liftUp {Γ : List (UCl n)} {Δ : List (UCl m)} {ξ : Fin n → Fin m}
    (R : ∀ c ∈ Γ, c.rn ξ ∈ Δ) {c₀ : UCl (n + 1)} {d₀ : UCl (m + 1)}
    (h₀ : c₀.rn (Tm.upRen ξ) = d₀) :
    ∀ c ∈ c₀ :: Γ.map UCl.shift, c.rn (Tm.upRen ξ) ∈ d₀ :: Δ.map UCl.shift := by
  intro c hc
  rcases List.mem_cons.1 hc with rfl | hc
  · exact List.mem_cons.2 (.inl h₀)
  · obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
    rw [shift_rn]
    exact List.mem_cons_of_mem _ (List.mem_map_of_mem (R c' hc'))

end UCl

/-- **From the uniform clause calculus**, with a renaming and an extension of
the context carried through the induction. -/
theorem VPrf.toE3 {Γ : List (UCl n)} {A : NFm n} (h : VPrf Γ A) :
    ∀ {m : ℕ} (ξ : Fin n → Fin m) (Δ : List (UCl m)), (∀ c ∈ Γ, c.rn ξ ∈ Δ) →
      E3Prf Δ (A.subst fun i => (Syn.var (ξ i) : Tm m)) := by
  induction h with intro m ξ Δ R
  | @use _ Γ c t hc _ ih =>
    rw [NFm.subst_inst]
    refine .use (c := c.rn ξ) _ (R c hc) fun A' hA' => ?_
    cases hca : c.ante with
    | none => rw [UCl.rn, hca] at hA'; cases hA'
    | some A₀ => rw [UCl.rn, hca] at hA'; cases hA'; exact ih A₀ hca ξ Δ R
  | @evalZero _ Γ h a t r _ _ ih₁ ih₂ =>
    refine .discharge E3Prf.theta (ih₁ _ _ (UCl.liftRn R _)) (ih₂ _ _ (UCl.liftRn R _)) ?_
    rw [NFm.rn_shift]
    simp only [NFm.subst_eq, Tm.subst_iter, Tm.subst_zero]
    exact .zeroCase _
  | @evalSucc _ Γ c a h t r _ _ ih₁ ih₂ =>
    refine .discharge E3Prf.theta (ih₁ _ _ (UCl.liftRn R _)) (ih₂ _ _ (UCl.liftRn R _)) ?_
    rw [NFm.rn_shift]
    simp only [NFm.subst_eq, Tm.subst_iter, Tm.subst_succ, Syn.subst_subst_inst]
    exact .succCase
  | @elim _ Γ B A _ _ ih₁ ih₂ =>
    refine .discharge (B := B.subst (up (up fun i => (Syn.var (ξ i) : Tm m)))) (ih₁ ξ Δ R)
      E3Prf.theta (ih₂ (Tm.upRen ξ) _ (UCl.liftUp R ?_)) ?_
    · simp only [UCl.rn, Option.map_some, ← Tm.up_rn, NFm.subst_inst]
      rfl
    · rw [← Tm.up_rn, NFm.shift_subst_up]
      exact .idCase (fun _ _ _ _ k => by cases k.1) (fun _ _ _ _ _ k => by cases k.1)
  | @intro _ Γ B t hB _ ih =>
    have eX : ((B.subst (up (inst t))).subst (repl (NFm.start B t))).subst
          (fun i => (Syn.var (Tm.upRen ξ i) : Tm (m + 1)))
        = ((B.subst (up (up fun i => (Syn.var (ξ i) : Tm m)))).subst
            (up (inst (Syn.subst (fun i => (Syn.var (ξ i) : Tm m)) t)))).subst
          (repl (NFm.start (B.subst (up (up fun i => (Syn.var (ξ i) : Tm m))))
            (Syn.subst (fun i => (Syn.var (ξ i) : Tm m)) t))) := by
      rw [← Tm.up_rn, NFm.subst_repl_up _ (NFm.start B t), NFm.subst_up_inst, ← NFm.start_rn]
    have k := ih (Tm.upRen ξ) _ (UCl.liftUp R (by rw [UCl.asm_rn, eX]))
    rw [← Tm.up_rn, NFm.subst_repl_succ, NFm.subst_up_inst] at k
    exact .intro _ _ ((NFm.qfree_subst _ _).2 hB) k

variable {Γ : List (UCl n)} {A : NFm n}

/-- **Evaluation at the discharge is the uniform clause calculus**, on every
clause context. -/
theorem e3prf_iff_vprf : E3Prf Γ A ↔ VPrf Γ A := by
  refine ⟨E3Prf.toVPrf, fun h => ?_⟩
  have k := h.toE3 id Γ fun c hc => by rw [UCl.rn_id]; exact hc
  rwa [show (fun i => (Syn.var (id i) : Tm n)) = Syn.var from rfl, NFm.subst_id] at k

/-- **On `Q`-free sequents, with the reflexivity clause, the three families
derive exactly what the kernel derives.** -/
theorem e3prf_iff_nprf_of_qfree {Γ : List (NFm n)} {A : NFm n} (hΓ : ∀ X ∈ Γ, X.QFree)
    (hA : A.QFree) : E3Prf (UCl.refl :: Γ.map UCl.asm) A ↔ NPrf Γ A :=
  e3prf_iff_vprf.trans (vprf_iff_nprf_of_qfree hΓ hA)

end LeanProofs.ConciseIPRA
