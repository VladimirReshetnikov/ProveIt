import ConciseIPRA.NativeEvalDischarge
import ConciseIPRA.NativeClausalDiagonal

/-!
# Partial evaluation at the discharge

The three-family calculus `PD` of the article (`claus:def:pd`, from the
package `476_byte_presentation`).  It differs from the evaluating discharge
`E3Prf` in two places:

* the introduction is the diagonal one of `KPrf`: its start is read off the
  matrix alone (`NFm.dstart`), not off the witness;
* the evaluation step is partial (`RhoPlus`, `ρ⁺`): the zero row and the
  successor row of `ρ`, and the identity only when the auxiliary formula `E`
  has root `D`; every other pair of formulas is outside its domain.

`K^u` (`KUPrf`) is the uniform clause calculus `VPrf` with the diagonal
introduction.  The theorems:

* `pdprf_iff_kuprf : PDPrf Γ A ↔ KUPrf Γ A` on every clause context;
* `kuprf_iff_kprf`: with the reflexivity clause, `K^u` and the diagonal clause
  calculus `KPrf` derive the same formulas from the same assumptions;
* hence `pdprf_iff_nprf_of_qfree`: on `Q`-free sequents `PD` derives exactly
  what the kernel derives.

The proofs are those of `NativeEvalDischarge` and `NativeUniformClauses`, with
the diagonal start and the row `D` of `ρ⁺` in place of the identity case.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open Tm (zero succ iter)

variable {n m : ℕ}

/-- The graph of the partial evaluation step `ρ⁺_E(F)`. -/
inductive RhoPlus : {n : ℕ} → NFm n → NFm n → NFm n → Prop
  | zeroCase {n : ℕ} (h : Tm (n + 1)) {s t r : Tm n} :
      RhoPlus (.eq s t) (.eq (iter zero s h) r) (.eq r t)
  | succCase {n : ℕ} {c a : Tm n} {h : Tm (n + 1)} {t r : Tm n} :
      RhoPlus (.eq (iter c a h) t) (.eq (iter (succ c) a h) r) (.eq r (Syn.subst (inst t) h))
  /-- The row `D`: an auxiliary formula with root `D` leaves `F` unchanged. -/
  | dCase {n : ℕ} (C : NFm (n + 2)) (F : NFm n) : RhoPlus (.D C) F F

/-- `ρ⁺` is contained in `ρ`. -/
theorem RhoPlus.toRho {E F R : NFm n} : RhoPlus E F R → Rho E F R
  | .zeroCase h => .zeroCase h
  | .succCase => .succCase
  | .dCase _ _ => .idCase (fun _ _ _ _ k => by cases k.1) (fun _ _ _ _ _ k => by cases k.1)

/-- `K^u`: uniform clause use with the diagonal introduction. -/
inductive KUPrf : {n : ℕ} → List (UCl n) → NFm n → Prop
  | use {n : ℕ} {Γ : List (UCl n)} {c : UCl n} (t : Tm n) (hc : c ∈ Γ)
      (h : ∀ A, c.ante = some A → KUPrf Γ A) : KUPrf Γ (c.cons.subst (inst t))
  | evalZero {n : ℕ} {Γ : List (UCl n)} (h : Tm (n + 1)) {a t r : Tm n}
      (h₁ : KUPrf Γ (.eq a t)) (h₂ : KUPrf Γ (.eq (iter zero a h) r)) : KUPrf Γ (.eq r t)
  | evalSucc {n : ℕ} {Γ : List (UCl n)} {c a : Tm n} {h : Tm (n + 1)} {t r : Tm n}
      (h₁ : KUPrf Γ (.eq (iter c a h) t)) (h₂ : KUPrf Γ (.eq (iter (succ c) a h) r)) :
      KUPrf Γ (.eq r (Syn.subst (inst t) h))
  | elim {n : ℕ} {Γ : List (UCl n)} {B : NFm (n + 2)} {A : NFm n} (h₁ : KUPrf Γ (.D B))
      (h₂ : KUPrf (⟨some (B.subst (inst zero)), B⟩ :: Γ.map UCl.shift) A.shift) : KUPrf Γ A
  | intro {n : ℕ} {Γ : List (UCl n)} (B : NFm (n + 2)) (t : Tm n) (hB : B.QFree)
      (h : KUPrf (UCl.asm ((B.subst (up (inst t))).subst (repl (NFm.dstart B)))
          :: Γ.map UCl.shift)
        ((B.subst (up (inst t))).subst (repl (succ (var 0))))) :
      KUPrf Γ (.D B)

/-- `PD`: Use, the diagonal Intro, and the discharge with partial evaluation. -/
inductive PDPrf : {n : ℕ} → List (UCl n) → NFm n → Prop
  | use {n : ℕ} {Γ : List (UCl n)} {c : UCl n} (t : Tm n) (hc : c ∈ Γ)
      (h : ∀ A, c.ante = some A → PDPrf Γ A) : PDPrf Γ (c.cons.subst (inst t))
  | intro {n : ℕ} {Γ : List (UCl n)} (B : NFm (n + 2)) (t : Tm n) (hB : B.QFree)
      (h : PDPrf (UCl.asm ((B.subst (up (inst t))).subst (repl (NFm.dstart B)))
          :: Γ.map UCl.shift)
        ((B.subst (up (inst t))).subst (repl (succ (var 0))))) :
      PDPrf Γ (.D B)
  | discharge {n : ℕ} {Γ : List (UCl n)} {B : NFm (n + 2)} {E F : NFm (n + 1)} {A : NFm n}
      (h₁ : PDPrf Γ (.D B))
      (hE : PDPrf (⟨some (B.subst (inst zero)), B⟩ :: Γ.map UCl.shift) E)
      (hF : PDPrf (⟨some (B.subst (inst zero)), B⟩ :: Γ.map UCl.shift) F)
      (hρ : RhoPlus E F A.shift) : PDPrf Γ A

/-! ### From `PD` to `K^u` -/

/-- Evaluate inside the scope of the witness, then eliminate. -/
theorem PDPrf.toKU {Γ : List (UCl n)} {A : NFm n} (h : PDPrf Γ A) : KUPrf Γ A := by
  induction h with
  | use t hc _ ih => exact .use t hc ih
  | intro B t hB _ ih => exact .intro B t hB ih
  | @discharge _ Γ B E F A _ _ _ hρ ih₁ ihE ihF =>
    refine .elim ih₁ ?_
    generalize A.shift = R at hρ ⊢
    cases hρ with
    | zeroCase h => exact .evalZero h ihE ihF
    | succCase => exact .evalSucc ihE ihF
    | dCase _ _ => exact ihF

/-- `Θ = D_{x,y} (0 = 0)` is derivable in every context: the matrix is not
diagonal, so the introduction at the witness `0` is in the mode of cases. -/
theorem PDPrf.theta {Γ : List (UCl n)} : PDPrf Γ (.D (.eq zero zero)) := by
  refine .intro _ zero trivial ?_
  exact PDPrf.use (c := UCl.asm (.eq zero zero)) zero List.mem_cons_self
    (fun A hA => by cases hA)

/-! ### From `K^u` to `PD` -/

/-- With a renaming and an extension of the context carried through the
induction: an elimination is a discharge with the auxiliary formula `Θ` in the
row `D`; an Eval step is a discharge of `Θ` whose branches are the premises
moved under the fresh variable. -/
theorem KUPrf.toPD {Γ : List (UCl n)} {A : NFm n} (h : KUPrf Γ A) :
    ∀ {m : ℕ} (ξ : Fin n → Fin m) (Δ : List (UCl m)), (∀ c ∈ Γ, c.rn ξ ∈ Δ) →
      PDPrf Δ (A.subst fun i => (Syn.var (ξ i) : Tm m)) := by
  induction h with intro m ξ Δ R
  | @use _ Γ c t hc _ ih =>
    rw [NFm.subst_inst]
    refine .use (c := c.rn ξ) _ (R c hc) fun A' hA' => ?_
    cases hca : c.ante with
    | none => rw [UCl.rn, hca] at hA'; cases hA'
    | some A₀ => rw [UCl.rn, hca] at hA'; cases hA'; exact ih A₀ hca ξ Δ R
  | @evalZero _ Γ h a t r _ _ ih₁ ih₂ =>
    refine .discharge PDPrf.theta (ih₁ _ _ (UCl.liftRn R _)) (ih₂ _ _ (UCl.liftRn R _)) ?_
    rw [NFm.rn_shift]
    simp only [NFm.subst_eq, Tm.subst_iter, Tm.subst_zero]
    exact .zeroCase _
  | @evalSucc _ Γ c a h t r _ _ ih₁ ih₂ =>
    refine .discharge PDPrf.theta (ih₁ _ _ (UCl.liftRn R _)) (ih₂ _ _ (UCl.liftRn R _)) ?_
    rw [NFm.rn_shift]
    simp only [NFm.subst_eq, Tm.subst_iter, Tm.subst_succ, Syn.subst_subst_inst]
    exact .succCase
  | @elim _ Γ B A _ _ ih₁ ih₂ =>
    refine .discharge (B := B.subst (up (up fun i => (Syn.var (ξ i) : Tm m)))) (ih₁ ξ Δ R)
      PDPrf.theta (ih₂ (Tm.upRen ξ) _ (UCl.liftUp R ?_)) ?_
    · simp only [UCl.rn, Option.map_some, ← Tm.up_rn, NFm.subst_inst]
      rfl
    · rw [← Tm.up_rn, NFm.shift_subst_up]
      exact .dCase _ _
  | @intro _ Γ B t hB _ ih =>
    have eX : ((B.subst (up (inst t))).subst (repl (NFm.dstart B))).subst
          (fun i => (Syn.var (Tm.upRen ξ i) : Tm (m + 1)))
        = ((B.subst (up (up fun i => (Syn.var (ξ i) : Tm m)))).subst
            (up (inst (Syn.subst (fun i => (Syn.var (ξ i) : Tm m)) t)))).subst
          (repl (NFm.dstart (B.subst (up (up fun i => (Syn.var (ξ i) : Tm m)))))) := by
      rw [← Tm.up_rn, NFm.subst_repl_up _ (NFm.dstart B), NFm.subst_up_inst, ← NFm.dstart_subst]
    have k := ih (Tm.upRen ξ) _ (UCl.liftUp R (by rw [UCl.asm_rn, eX]))
    rw [← Tm.up_rn, NFm.subst_repl_succ, NFm.subst_up_inst] at k
    exact .intro _ _ ((NFm.qfree_subst _ _).2 hB) k

/-- **Partial evaluation at the discharge is `K^u`**, on every clause
context. -/
theorem pdprf_iff_kuprf {Γ : List (UCl n)} {A : NFm n} : PDPrf Γ A ↔ KUPrf Γ A := by
  refine ⟨PDPrf.toKU, fun h => ?_⟩
  have k := h.toPD id Γ fun c hc => by rw [UCl.rn_id]; exact hc
  rwa [show (fun i => (Syn.var (id i) : Tm n)) = Syn.var from rfl, NFm.subst_id] at k

/-! ### `K^u` and the diagonal clause calculus -/

/-- Every derivation of `K^u` is a derivation of `KPrf`, a use of the
reflexivity clause being the reflexivity rule. -/
theorem KUPrf.toKPrf {Δ : List (UCl n)} {A : NFm n} (h : KUPrf Δ A) :
    ∀ {Γ : List (Cl n)}, (∀ c ∈ Δ, c = UCl.refl ∨ c.toCl ∈ Γ) → KPrf Γ A := by
  induction h with intro Γ s
  | @use _ Δ c t hc _ ih =>
    rcases s c hc with rfl | hm
    · exact .refl t
    · obtain ⟨a, b⟩ := c
      cases a with
      | none => exact .use (c := ⟨.eq zero zero, b⟩) t hm (.refl zero)
      | some A => exact .use (c := ⟨A, b⟩) t hm (ih A rfl s)
  | evalZero h _ _ ih₁ ih₂ => exact .evalZero h (ih₁ s) (ih₂ s)
  | evalSucc _ _ ih₁ ih₂ => exact .evalSucc (ih₁ s) (ih₂ s)
  | elim _ _ ih₁ ih₂ => exact .elim (ih₁ s) (ih₂ (UCl.liftToCl s _))
  | intro B t hB _ ih => exact .intro B t hB (ih (UCl.liftToCl s _))

/-- Every derivation of `KPrf` is a derivation of `K^u`, once the reflexivity
clause is in the context. -/
theorem KPrf.toKU {Γ : List (Cl n)} {A : NFm n} (h : KPrf Γ A) :
    ∀ {Δ : List (UCl n)}, UCl.refl ∈ Δ →
      (∀ c ∈ Γ, ∃ d ∈ Δ, d.cons = c.cons ∧ ∀ A, d.ante = some A → A = c.ante) → KUPrf Δ A := by
  induction h with
  | refl t =>
    intro Δ hr _
    exact KUPrf.use (c := UCl.refl) t hr (fun A hA => by cases hA)
  | evalZero h _ _ ih₁ ih₂ => intro Δ hr s; exact .evalZero h (ih₁ hr s) (ih₂ hr s)
  | evalSucc _ _ ih₁ ih₂ => intro Δ hr s; exact .evalSucc (ih₁ hr s) (ih₂ hr s)
  | @use _ Γ c t hc _ ih =>
    intro Δ hr s
    obtain ⟨d, hd, hdc, hda⟩ := s c hc
    rw [← hdc]
    exact .use t hd (fun A hA => by rw [hda A hA]; exact ih hr s)
  | elim _ _ ih₁ ih₂ =>
    intro Δ hr s
    refine .elim (ih₁ hr s) (ih₂ (List.mem_cons_of_mem _ ?_) (UCl.liftOfCl s _ _ rfl ?_))
    · rw [← UCl.refl_shift]; exact List.mem_map_of_mem hr
    · intro A hA; exact (Option.some.inj hA).symm
  | intro B t hB _ ih =>
    intro Δ hr s
    refine .intro B t hB (ih (List.mem_cons_of_mem _ ?_) (UCl.liftOfCl s _ _ rfl ?_))
    · rw [← UCl.refl_shift]; exact List.mem_map_of_mem hr
    · intro A hA; cases hA

variable {Γ : List (NFm n)} {A : NFm n}

/-- **Uniform clauses with the diagonal introduction**: with the reflexivity
clause `K^u` and `KPrf` derive the same formulas from the same assumptions. -/
theorem kuprf_iff_kprf : KUPrf (UCl.refl :: Γ.map UCl.asm) A ↔ KPrf (Γ.map Cl.asm) A := by
  constructor
  · intro h
    refine h.toKPrf fun c hc => ?_
    rcases List.mem_cons.1 hc with rfl | hc
    · exact .inl rfl
    · obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hc
      exact .inr (List.mem_map_of_mem (f := Cl.asm) hX)
  · intro h
    refine h.toKU List.mem_cons_self fun c hc => ?_
    obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hc
    exact ⟨UCl.asm X, List.mem_cons_of_mem _ (List.mem_map_of_mem hX), rfl,
      fun A hA => by cases hA⟩

/-- On `Q`-free sequents `K^u` derives exactly what the kernel derives. -/
theorem kuprf_iff_nprf_of_qfree (hΓ : ∀ X ∈ Γ, X.QFree) (hA : A.QFree) :
    KUPrf (UCl.refl :: Γ.map UCl.asm) A ↔ NPrf Γ A :=
  kuprf_iff_kprf.trans (kprf_iff_nprf_of_qfree hΓ hA)

/-- **On `Q`-free sequents, with the reflexivity clause, `PD` derives exactly
what the kernel derives.** -/
theorem pdprf_iff_nprf_of_qfree (hΓ : ∀ X ∈ Γ, X.QFree) (hA : A.QFree) :
    PDPrf (UCl.refl :: Γ.map UCl.asm) A ↔ NPrf Γ A :=
  pdprf_iff_kuprf.trans (kuprf_iff_nprf_of_qfree hΓ hA)

end LeanProofs.ConciseIPRA
