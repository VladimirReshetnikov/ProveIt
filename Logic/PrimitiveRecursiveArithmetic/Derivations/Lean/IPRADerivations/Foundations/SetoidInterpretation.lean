import IPRADerivations.Core.Basic

/-!
# Interpretation through numerical presentations

Packet: `foundations/ipra_local_global`, `paper/02_logic.tex`, Definition `def:presented-sort` ("A numerical
presentation of a sort") and Proposition `prop:setoid-interpretation` ("Interpretation through numerical
presentations"): replace source equality by a relation `E`, source operations by their numerical
interpretations, and sorted quantifiers by relativized ones,

  `(∀ x A)^I = ∀ x (D(x) → A^I)`,   `(∃ x A)^I = ∃ x (D(x) ∧ A^I)`;

if the interpreted source axioms are derivable, every intuitionistic first-order derivation from those axioms
has an interpreted derivation, with domain assumptions for its free variables.

This is the general embedding interface for abstract structures: a sort is presented by a domain formula `D`
and an equivalence `E` that need not be decidable (regular names with their equality, presented groups,
categories given by codes of objects and morphisms, …).

Here the source is any first-order theory `Ax` over any syntax `T` (one sort; the atoms are equations, as in
`ConciseIPRA`), and the target any theory `Ax'` over any syntax `T'`; iPRA is the instance `T' = PTm`,
`Ax' = PRAAx`. A presentation (`Presentation`) consists of

* a term translation `f` that fixes variables and commutes with substitution (operations are interpreted
  by fixed numerical terms);
* a domain formula `D(a)` and an equality formula `E(a, b)`;
* the contracts, as rules at arbitrary contexts: `closed` (interpreted terms stay in the domain),
  `congr` (interpreted terms respect `E`), `refl`, `symm`, `trans` (`E` is an equivalence on `D`), and
  `axioms` (each interpreted axiom is derivable under domain assumptions for its variables).

Derived:

* `tr`: the relativized translation; `tr_subst`, `tr_shift`: it commutes with substitution;
* `cong` (the formula induction of the proof): `E`-equivalent arguments in the domain give equivalent
  interpreted formulas, `A^I[τ] → A^I[τ′]`;
* `sound` (`prop:setoid-interpretation`): if `Γ ⊢ A` in the source, then
  `Γ^I, D(x₀), …, D(x_{n−1}) ⊢ A^I` in the target.
-/

namespace LeanProofs.IPRA.Foundations.SetoidInterpretation

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm

variable {T T' : ℕ → Type} [Syn T] [Syn T']

/-! ## Domain and equality formulas -/

/-- `D(a)`. -/
def dom (D : Fm T' 1) {n : ℕ} (a : T' n) : Fm T' n := D.subst (fun _ => a)

/-- `E(a, b)`. -/
def eqv (E : Fm T' 2) {n : ℕ} (a b : T' n) : Fm T' n := E.subst ![a, b]

theorem dom_subst (D : Fm T' 1) {n m : ℕ} (a : T' n) (τ : Fin n → T' m) :
    (dom D a).subst τ = dom D (Syn.subst τ a) := by
  simp [dom, Fm.subst_subst]

theorem eqv_subst (E : Fm T' 2) {n m : ℕ} (a b : T' n) (τ : Fin n → T' m) :
    (eqv E a b).subst τ = eqv E (Syn.subst τ a) (Syn.subst τ b) := by
  simp only [eqv, Fm.subst_subst]
  congr 1; funext i; fin_cases i <;> simp

theorem dom_shift (D : Fm T' 1) {n : ℕ} (a : T' n) : (dom D a).shift = dom D (Syn.shift a) := by
  simp [Fm.shift, dom_subst, Syn.shift]

theorem eqv_shift (E : Fm T' 2) {n : ℕ} (a b : T' n) :
    (eqv E a b).shift = eqv E (Syn.shift a) (Syn.shift b) := by
  simp [Fm.shift, eqv_subst, Syn.shift]

/-- The domain assumptions `D(x₀), …, D(x_{n−1})` for the free variables. -/
def domCtx (D : Fm T' 1) (n : ℕ) : List (Fm T' n) := List.ofFn (fun i : Fin n => dom D (Syn.var i))

/-! ## The relativized translation -/

/-- `A^I`: equations by `E`, quantifiers relativized to `D`. -/
def tr (f : ∀ n, T n → T' n) (D : Fm T' 1) (E : Fm T' 2) : {n : ℕ} → Fm T n → Fm T' n
  | _, .eq s t => eqv E (f _ s) (f _ t)
  | _, .bot => .bot
  | _, .and φ ψ => .and (tr f D E φ) (tr f D E ψ)
  | _, .or φ ψ => .or (tr f D E φ) (tr f D E ψ)
  | _, .imp φ ψ => .imp (tr f D E φ) (tr f D E ψ)
  | _, .all φ => .all (.imp (dom D (Syn.var 0)) (tr f D E φ))
  | _, .ex φ => .ex (.and (dom D (Syn.var 0)) (tr f D E φ))

/-- A numerical presentation of a sort for the source theory `Ax` in the target theory `Ax'`. -/
structure Presentation (Ax : Theory T) (Ax' : Theory T') where
  f : ∀ n, T n → T' n
  D : Fm T' 1
  E : Fm T' 2
  f_var : ∀ {n : ℕ} (i : Fin n), f n (Syn.var i) = Syn.var i
  f_subst : ∀ {n m : ℕ} (σ : Fin n → T m) (t : T n),
    f m (Syn.subst σ t) = Syn.subst (fun i => f m (σ i)) (f n t)
  closed : ∀ {n m : ℕ} {Δ : List (Fm T' m)} (t : T n) (τ : Fin n → T' m),
    (∀ i, Δ ⊢[Ax'] dom D (τ i)) → (Δ ⊢[Ax'] dom D (Syn.subst τ (f n t)))
  congr : ∀ {n m : ℕ} {Δ : List (Fm T' m)} (t : T n) (τ τ' : Fin n → T' m),
    (∀ i, Δ ⊢[Ax'] dom D (τ i)) → (∀ i, Δ ⊢[Ax'] dom D (τ' i)) →
      (∀ i, Δ ⊢[Ax'] eqv E (τ i) (τ' i)) →
        (Δ ⊢[Ax'] eqv E (Syn.subst τ (f n t)) (Syn.subst τ' (f n t)))
  refl : ∀ {m : ℕ} {Δ : List (Fm T' m)} {a : T' m}, (Δ ⊢[Ax'] dom D a) → (Δ ⊢[Ax'] eqv E a a)
  symm : ∀ {m : ℕ} {Δ : List (Fm T' m)} {a b : T' m}, (Δ ⊢[Ax'] dom D a) → (Δ ⊢[Ax'] dom D b) →
    (Δ ⊢[Ax'] eqv E a b) → (Δ ⊢[Ax'] eqv E b a)
  trans : ∀ {m : ℕ} {Δ : List (Fm T' m)} {a b c : T' m}, (Δ ⊢[Ax'] dom D a) → (Δ ⊢[Ax'] dom D b) →
    (Δ ⊢[Ax'] dom D c) → (Δ ⊢[Ax'] eqv E a b) → (Δ ⊢[Ax'] eqv E b c) → (Δ ⊢[Ax'] eqv E a c)
  axioms : ∀ {k : ℕ} {φ : Fm T k}, Ax k φ → (domCtx D k ⊢[Ax'] tr f D E φ)

variable {Ax : Theory T} {Ax' : Theory T'} (P : Presentation Ax Ax')

/-! ## Substitution -/

theorem f_up {n m : ℕ} (σ : Fin n → T m) :
    (fun i => P.f (m + 1) (Syn.up σ i)) = Syn.up (fun i => P.f m (σ i)) := by
  refine funext (Fin.cases ?_ fun j => ?_)
  · simp [P.f_var]
  · simp [Syn.shift, P.f_subst, P.f_var]

theorem f_inst {n : ℕ} (t : T n) : (fun i => P.f n (Syn.inst t i)) = Syn.inst (P.f n t) := by
  refine funext (Fin.cases ?_ fun j => ?_)
  · simp
  · simp [P.f_var]

theorem tr_subst {n : ℕ} (φ : Fm T n) :
    ∀ {m : ℕ} (σ : Fin n → T m), tr P.f P.D P.E (φ.subst σ) = (tr P.f P.D P.E φ).subst (fun i => P.f m (σ i)) := by
  induction φ with
  | eq s t => intro m σ; simp [tr, eqv_subst, P.f_subst]
  | bot => intro m σ; rfl
  | and φ ψ ih₁ ih₂ => intro m σ; simp [tr, ih₁, ih₂]
  | or φ ψ ih₁ ih₂ => intro m σ; simp [tr, ih₁, ih₂]
  | imp φ ψ ih₁ ih₂ => intro m σ; simp [tr, ih₁, ih₂]
  | all φ ih => intro m σ; simp [tr, ih, dom_subst, f_up]
  | ex φ ih => intro m σ; simp [tr, ih, dom_subst, f_up]

theorem tr_shift {n : ℕ} (φ : Fm T n) : tr P.f P.D P.E φ.shift = (tr P.f P.D P.E φ).shift := by
  simp only [Fm.shift, tr_subst, P.f_var]

/-! ## Congruence of interpreted formulas -/

section Lift

variable {k m : ℕ} {Δ : List (Fm T' m)} {X : Fm T' m} {χ : Fm T' (m + 1)}

theorem lift_dom {τ : Fin k → T' m} (h0 : (χ :: (X :: Δ).map Fm.shift) ⊢[Ax'] dom P.D (Syn.var 0))
    (hd : ∀ i, Δ ⊢[Ax'] dom P.D (τ i)) : ∀ i, (χ :: (X :: Δ).map Fm.shift) ⊢[Ax'] dom P.D (Syn.up τ i) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using h0
  · have a := ((hd j).wk (ψ := X)).shift
    rw [dom_shift] at a
    simpa using a.wk

theorem lift_eqv {τ τ' : Fin k → T' m} (h0 : (χ :: (X :: Δ).map Fm.shift) ⊢[Ax'] dom P.D (Syn.var 0))
    (he : ∀ i, Δ ⊢[Ax'] eqv P.E (τ i) (τ' i)) :
    ∀ i, (χ :: (X :: Δ).map Fm.shift) ⊢[Ax'] eqv P.E (Syn.up τ i) (Syn.up τ' i) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using P.refl h0
  · have a := ((he j).wk (ψ := X)).shift
    rw [eqv_shift] at a
    simpa using a.wk

end Lift

/-- `E`-equivalent arguments in the domain give equivalent interpreted formulas. -/
theorem cong {k : ℕ} (φ : Fm T k) : ∀ {m : ℕ} {Δ : List (Fm T' m)} {τ τ' : Fin k → T' m},
    (∀ i, Δ ⊢[Ax'] dom P.D (τ i)) → (∀ i, Δ ⊢[Ax'] dom P.D (τ' i)) →
      (∀ i, Δ ⊢[Ax'] eqv P.E (τ i) (τ' i)) →
        (Δ ⊢[Ax'] (tr P.f P.D P.E φ).subst τ ⟶ (tr P.f P.D P.E φ).subst τ') := by
  induction φ with
  | eq s t =>
    intro m Δ τ τ' hd hd' he
    simp only [tr, eqv_subst]
    exact .impI (P.trans (P.closed s τ' hd').wk (P.closed s τ hd).wk (P.closed t τ' hd').wk
      (P.symm (P.closed s τ hd).wk (P.closed s τ' hd').wk (P.congr s τ τ' hd hd' he).wk)
      (P.trans (P.closed s τ hd).wk (P.closed t τ hd).wk (P.closed t τ' hd').wk Prf.hyp0
        (P.congr t τ τ' hd hd' he).wk))
  | bot => intro m Δ τ τ' _ _ _; exact .impI Prf.hyp0
  | and φ ψ ih₁ ih₂ =>
    intro m Δ τ τ' hd hd' he
    simp only [tr, Fm.subst_and]
    exact .impI (.andI (.impE (ih₁ hd hd' he).wk (.andE₁ Prf.hyp0))
      (.impE (ih₂ hd hd' he).wk (.andE₂ Prf.hyp0)))
  | or φ ψ ih₁ ih₂ =>
    intro m Δ τ τ' hd hd' he
    simp only [tr, Fm.subst_or]
    exact .impI (.orE Prf.hyp0 (.orI₁ (.impE (ih₁ hd hd' he).wk.wk Prf.hyp0))
      (.orI₂ (.impE (ih₂ hd hd' he).wk.wk Prf.hyp0)))
  | imp φ ψ ih₁ ih₂ =>
    intro m Δ τ τ' hd hd' he
    simp only [tr, Fm.subst_imp]
    have he' : ∀ i, Δ ⊢[Ax'] eqv P.E (τ' i) (τ i) := fun i => P.symm (hd i) (hd' i) (he i)
    exact .impI (.impI (.impE (ih₂ hd hd' he).wk.wk
      (.impE Prf.hyp1 (.impE (ih₁ hd' hd he').wk.wk Prf.hyp0))))
  | all φ ih =>
    intro m Δ τ τ' hd hd' he
    simp only [tr, Fm.subst_all, Fm.subst_imp, dom_subst, Syn.subst_var, Syn.up_zero]
    refine .impI (.allI (.impI ?_))
    have h0 : (dom P.D (Syn.var 0) :: ((Fm.all (dom P.D (Syn.var 0) ⟶
        (tr P.f P.D P.E φ).subst (Syn.up τ))) :: Δ).map Fm.shift) ⊢[Ax'] dom P.D (Syn.var 0) := Prf.hyp0
    have hx := Prf.impE (Prf.allOpen Prf.hyp0).wk h0
    exact .impE (ih (lift_dom P h0 hd) (lift_dom P h0 hd') (lift_eqv P h0 he)) hx
  | ex φ ih =>
    intro m Δ τ τ' hd hd' he
    simp only [tr, Fm.subst_ex, Fm.subst_and, dom_subst, Syn.subst_var, Syn.up_zero]
    refine .impI (.exE Prf.hyp0 ?_)
    have h0 : ((dom P.D (Syn.var 0) ⋏ (tr P.f P.D P.E φ).subst (Syn.up τ)) ::
        ((Fm.ex (dom P.D (Syn.var 0) ⋏ (tr P.f P.D P.E φ).subst (Syn.up τ))) :: Δ).map Fm.shift) ⊢[Ax']
        dom P.D (Syn.var 0) := .andE₁ Prf.hyp0
    have hx := ih (lift_dom P h0 hd) (lift_dom P h0 hd') (lift_eqv P h0 he)
    rw [Fm.shift, Fm.subst_ex]
    refine .exI (Syn.var 0) ?_
    rw [Fm.subst_up_succ_inst]
    exact .andI h0 (.impE hx (.andE₂ Prf.hyp0))

/-! ## Soundness -/

/-- The interpreted context with the domain assumptions. -/
def ctx {n : ℕ} (Γ : List (Fm T n)) : List (Fm T' n) := Γ.map (tr P.f P.D P.E) ++ domCtx P.D n

theorem dom_var {n : ℕ} (Γ : List (Fm T n)) (j : Fin n) :
    ctx P Γ ⊢[Ax'] dom P.D (Syn.var j) :=
  .hyp (List.mem_append_right _ (List.mem_ofFn.2 ⟨j, rfl⟩))

theorem dom_term {n : ℕ} (Γ : List (Fm T n)) (t : T n) : ctx P Γ ⊢[Ax'] dom P.D (P.f n t) := by
  simpa using P.closed t Syn.var (dom_var P Γ)

/-- The interpreted context of the shifted context is covered by the shifted context with a new variable. -/
theorem ctx_shift {n : ℕ} (Γ : List (Fm T n)) {χ : Fm T' (n + 1)}
    (h0 : (χ :: (ctx P Γ).map Fm.shift) ⊢[Ax'] dom P.D (Syn.var 0)) :
    ∀ ψ ∈ ctx P (Γ.map Fm.shift), (χ :: (ctx P Γ).map Fm.shift) ⊢[Ax'] ψ := by
  intro ψ hψ
  unfold ctx at hψ
  rcases List.mem_append.1 hψ with h | h
  · obtain ⟨φ', hφ', rfl⟩ := List.mem_map.1 h
    obtain ⟨φ, hφ, rfl⟩ := List.mem_map.1 hφ'
    refine .hyp (List.mem_cons_of_mem _ (List.mem_map.2 ⟨tr P.f P.D P.E φ, ?_, ?_⟩))
    · exact List.mem_append_left _ (List.mem_map_of_mem hφ)
    · exact (tr_shift P φ).symm
  · obtain ⟨j, rfl⟩ := List.mem_ofFn.1 h
    refine Fin.cases ?_ (fun i => ?_) j
    · exact h0
    · refine .hyp (List.mem_cons_of_mem _ (List.mem_map.2 ⟨dom P.D (Syn.var i), ?_, ?_⟩))
      · exact List.mem_append_right _ (List.mem_ofFn.2 ⟨i, rfl⟩)
      · simp [dom_shift, Syn.shift]

/-- `prop:setoid-interpretation`: a source derivation `Γ ⊢ A` gives `Γ^I, D(x₀), …, D(x_{n−1}) ⊢ A^I`. -/
theorem sound {n : ℕ} {Γ : List (Fm T n)} {φ : Fm T n} (h : Γ ⊢[Ax] φ) :
    ctx P Γ ⊢[Ax'] tr P.f P.D P.E φ := by
  induction h with
  | hyp h => exact .hyp (List.mem_append_left _ (List.mem_map_of_mem h))
  | @ax n k Γ φ h σ =>
    rw [tr_subst]
    refine Prf.trans ((P.axioms h).subst (fun i => P.f n (σ i))) ?_
    intro ψ hψ
    simp only [domCtx, List.map_ofFn, List.mem_ofFn] at hψ
    obtain ⟨i, rfl⟩ := hψ
    simpa [dom_subst] using dom_term P Γ (σ i)
  | botE φ _ ih => exact .botE _ ih
  | andI _ _ ih₁ ih₂ => exact .andI ih₁ ih₂
  | andE₁ _ ih => exact .andE₁ ih
  | andE₂ _ ih => exact .andE₂ ih
  | orI₁ _ ih => exact .orI₁ ih
  | orI₂ _ ih => exact .orI₂ ih
  | orE _ _ _ ih ih₁ ih₂ => exact .orE ih ih₁ ih₂
  | impI _ ih => exact .impI ih
  | impE _ _ ih₁ ih₂ => exact .impE ih₁ ih₂
  | @allI n Γ φ _ ih =>
    refine .allI (.impI ?_)
    exact Prf.trans ih (ctx_shift P Γ Prf.hyp0)
  | @allE n Γ φ t _ ih =>
    have a := Prf.allE (P.f n t) ih
    simp only [Fm.subst_imp, dom_subst, Syn.subst_var, Syn.inst_zero] at a
    rw [tr_subst, f_inst]
    exact .impE a (dom_term P Γ t)
  | @exI n Γ φ t _ ih =>
    rw [tr_subst, f_inst] at ih
    refine .exI (P.f n t) ?_
    simp only [Fm.subst_and, dom_subst, Syn.subst_var, Syn.inst_zero]
    exact .andI (dom_term P Γ t) ih
  | @exE n Γ φ ψ _ _ ih₁ ih₂ =>
    refine .exE ih₁ ?_
    rw [tr_shift] at ih₂
    have e : ctx P (φ :: Γ.map Fm.shift) = tr P.f P.D P.E φ :: ctx P (Γ.map Fm.shift) := rfl
    rw [e] at ih₂
    refine Prf.trans ih₂ ?_
    intro χ hχ
    rcases List.mem_cons.1 hχ with rfl | hχ
    · exact .andE₂ Prf.hyp0
    · exact ctx_shift P Γ (.andE₁ Prf.hyp0) χ hχ
  | eqRefl t => exact P.refl (dom_term P _ t)
  | @eqSubst n k Γ φ σ σ' _ _ ih₁ ih₂ =>
    rw [tr_subst] at ih₂ ⊢
    exact .impE (cong P φ (fun i => dom_term P Γ (σ i)) (fun i => dom_term P Γ (σ' i)) ih₁) ih₂

end LeanProofs.IPRA.Foundations.SetoidInterpretation
