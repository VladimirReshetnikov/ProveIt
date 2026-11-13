import ConciseIPRA.NativeNonzeroSources

/-!
# Introduction with a reconstructed matrix

`wit:sec:recon`: the rule `DI_r` is given a witness `w`, the eigenvariable `z`, the
assumption `A` and a derivation of `Γ, A ⊢ C`; its matrix is computed from `C` by
abstracting `S z` to `y` and, in the mode of cases, `w` to `x`.  The side conditions
say that `z` is not free in the computed matrix and that `A` is its required instance.

In de Bruijn form the computed matrix is given as a formula `B` whose substitution
into the shape of the double abstraction equals it; this states at once that `z` is
not free and what the matrix is.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open Tm (zero succ iter)

variable {n m k : ℕ}

namespace Tm

/-- Whether the variable `i` occurs in a term. -/
def occ : {n : ℕ} → Fin n → Tm n → Bool
  | _, i, .var j => decide (i = j)
  | _, _, .zero => false
  | _, i, .succ a => occ i a
  | _, i, .iter c a h => occ i c || occ i a || occ i.succ h

@[simp] theorem occ_var (i j : Fin n) : occ i (Syn.var j) = decide (i = j) := rfl

theorem occ_ren (u : Tm n) : ∀ {m : ℕ} {ξ : Fin n → Fin m}, Function.Injective ξ → ∀ z : Fin n,
    occ (ξ z) (ren ξ u) = occ z u := by
  induction u with
  | var j => intro m ξ hξ z; simp [ren, hξ.eq_iff]
  | zero => intro m ξ _ z; rfl
  | succ a ih => intro m ξ hξ z; exact ih hξ z
  | iter c a h ihc iha ihh =>
    intro m ξ hξ z
    simp only [occ, ren, ihc hξ, iha hξ]
    rw [show (ξ z).succ = upRen ξ z.succ from rfl, ihh (upRen_inj hξ)]

theorem occ_shift_succ (u : Tm n) (z : Fin n) : occ z.succ (Syn.shift u) = occ z u := by
  rw [shift_eq_ren]; exact occ_ren u (Fin.succ_injective _) z

theorem occ_ren_not_mem (u : Tm n) : ∀ {m : ℕ} {ξ : Fin n → Fin m} {z : Fin m},
    (∀ i, ξ i ≠ z) → occ z (ren ξ u) = false := by
  induction u with
  | var j => intro m ξ z hz; simp [ren, Ne.symm (hz j)]
  | zero => intro m ξ z _; rfl
  | succ a ih => intro m ξ z hz; exact ih hz
  | iter c a h ihc iha ihh =>
    intro m ξ z hz
    simp only [occ, ren, ihc hz, iha hz, Bool.false_or]
    refine ihh fun i => ?_
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (Fin.succ_ne_zero z).symm
    · intro e; exact hz j (Fin.succ_injective _ e)

theorem occ_shift_zero (u : Tm n) : occ 0 (Syn.shift u) = false := by
  rw [shift_eq_ren]; exact occ_ren_not_mem u fun i => Fin.succ_ne_zero i

/-- Replacing `S(var z)` in a term in which `z` does not occur only renames. -/
theorem rpl_succ_not_occ (u : Tm n) : ∀ {m : ℕ} {z : Fin n} (v : Tm m) (ρ : Fin n → Tm m),
    occ z u = false → rpl (succ (Syn.var z)) v ρ u = Syn.subst ρ u := by
  induction u with
  | var j => intro m z v ρ _; simp only [rpl]; rw [if_neg (by intro e; cases e)]; rfl
  | zero => intro m z v ρ _; simp only [rpl]; rw [if_neg (by intro e; cases e)]; rfl
  | succ a ih =>
    intro m z v ρ hz
    simp only [rpl]
    rw [if_neg (by
      intro e
      have e' := Tm.succ.inj e
      subst e'
      change occ z (Tm.var z) = false at hz
      simp [occ] at hz), ih v ρ hz]
    rfl
  | iter c a h ihc iha ihh =>
    intro m z v ρ hz
    simp only [occ, Bool.or_eq_false_iff] at hz
    simp only [rpl]
    rw [if_neg (by intro e; cases e), ihc v ρ hz.1.1, iha v ρ hz.1.2]
    rw [Tm.subst_iter]
    congr 1
    exact ihh (Syn.shift v) (Syn.up ρ) hz.2

/-- `σs` is `σm` with each `S(var z)` replaced by `S` and the rest renamed by `ρ`, and `z`
occurs in `σm` only inside those markers. -/
def MarksZ (z : Fin n) (S : Tm m) (ρ : Fin n → Tm m) (σm : Fin k → Tm n)
    (σs : Fin k → Tm m) : Prop :=
  ∀ i, (σm i = succ (Syn.var z) ∧ σs i = S) ∨ (occ z (σm i) = false ∧ σs i = Syn.subst ρ (σm i))

theorem MarksZ.up {z : Fin n} {S : Tm m} {ρ : Fin n → Tm m} {σm : Fin k → Tm n}
    {σs : Fin k → Tm m} (h : MarksZ z S ρ σm σs) :
    MarksZ z.succ (Syn.shift S) (Syn.up ρ) (Syn.up σm) (Syn.up σs) := by
  refine Fin.cases (.inr ⟨by simp, rfl⟩) fun j => ?_
  rcases h j with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩
  · exact .inl ⟨by rw [Syn.up_succ, e₁]; rfl, by rw [Syn.up_succ, e₂]⟩
  · exact .inr ⟨by rw [Syn.up_succ, occ_shift_succ, e₁],
      by rw [Syn.up_succ, Syn.up_succ, e₂, Syn.subst_up_shift]⟩

/-- Replacing `S(var z)` in an instance whose substitution puts `S(var z)` or terms
without `z` at every index replaces exactly the marked positions. -/
theorem rpl_subst_succ (h : Tm k) : ∀ {n m : ℕ} {z : Fin n} {S : Tm m} {ρ : Fin n → Tm m}
    {σm : Fin k → Tm n} {σs : Fin k → Tm m},
    MarksZ z S ρ σm σs → rpl (succ (Syn.var z)) S ρ (Syn.subst σm h) = Syn.subst σs h := by
  induction h with
  | var i =>
    intro n m z S ρ σm σs hσ
    show rpl _ S ρ (σm i) = σs i
    rcases hσ i with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩
    · rw [e₁, e₂]; simp only [rpl, if_true]
    · rw [e₂]; exact rpl_succ_not_occ _ S ρ e₁
  | zero =>
    intro n m z S ρ σm σs _
    show rpl _ S ρ Tm.zero = Tm.zero
    simp only [rpl]; rw [if_neg (by intro e; cases e)]
  | succ a ih =>
    intro n m z S ρ σm σs hσ
    show rpl _ S ρ (Tm.succ (Syn.subst σm a)) = Tm.succ (Syn.subst σs a)
    have hne : Tm.succ (Syn.subst σm a) ≠ Tm.succ (Syn.var z) := by
      intro e
      have e' := Tm.succ.inj e
      cases a with
      | var i =>
        rcases hσ i with ⟨e₁, _⟩ | ⟨e₁, _⟩
        · have : σm i = Syn.var z := e'
          rw [e₁] at this; cases this
        · have : σm i = Syn.var z := e'
          rw [this] at e₁; simp at e₁
      | zero => cases e'
      | succ a => cases e'
      | iter c a b => cases e'
    simp only [rpl]; rw [if_neg hne, ih hσ]
  | iter c a b ihc iha ihb =>
    intro n m z S ρ σm σs hσ
    rw [Tm.subst_iter, Tm.subst_iter]; simp only [rpl]
    rw [if_neg (by intro e; cases e), ihc hσ, iha hσ]
    congr 1
    exact ihb hσ.up

end Tm

namespace NFm

/-- The formula form of `Tm.rpl_subst_succ`. -/
theorem rpl_subst_succ (B : NFm k) : ∀ {n m : ℕ} {z : Fin n} {S : Tm m} {ρ : Fin n → Tm m}
    {σm : Fin k → Tm n} {σs : Fin k → Tm m},
    Tm.MarksZ z S ρ σm σs → rpl (succ (Syn.var z)) S ρ (B.subst σm) = B.subst σs := by
  induction B with
  | eq a b =>
    intro n m z S ρ σm σs hσ
    simp only [subst_eq, rpl]
    rw [Tm.rpl_subst_succ a hσ, Tm.rpl_subst_succ b hσ]
  | Q B ih =>
    intro n m z S ρ σm σs hσ
    simp only [subst_Q, rpl]
    exact congrArg NFm.Q (ih hσ.up)
  | D B ih =>
    intro n m z S ρ σm σs hσ
    simp only [subst_D, rpl]
    exact congrArg NFm.D (ih hσ.up.up)

end NFm

/-! ### The calculus `W_r` -/

/-- The shape of the abstraction in the mode of progress: `y` stays, the index of `z`
is skipped. -/
def skz : Fin (n + 1) → Tm (n + 2) := Fin.cases (Syn.var 0) (fun i => Syn.var i.succ.succ)

/-- The shape of the double abstraction in the mode of cases: `y ↦ 1`, `x ↦ 0`, and the
other variables after `x`, `y`, `z`. -/
def tauC : Fin (n + 2) → Tm (n + 3) :=
  Fin.cases (Syn.var (Fin.succ 0)) (Fin.cases (Syn.var 0) fun i => Syn.var i.succ.succ.succ)

/-- `W_r`: the kernel with the introduction reconstructed from the conclusion of its
premise, in the mode of progress (`dIrP`, witness `0`, literal equations) and of cases
(`dIrC`). -/
inductive RPrf : {n : ℕ} → List (NFm n) → NFm n → Prop
  | hyp {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (h : A ∈ Γ) : RPrf Γ A
  | iterZero {n : ℕ} {Γ : List (NFm n)} (a : Tm n) (h : Tm (n + 1)) :
      RPrf Γ (.eq (iter zero a h) a)
  | iterSucc {n : ℕ} {Γ : List (NFm n)} (c a : Tm n) (h : Tm (n + 1)) :
      RPrf Γ (.eq (iter (succ c) a h) (Syn.subst (inst (iter c a h)) h))
  | trOne {n : ℕ} {Γ : List (NFm n)} (h : Tm (n + 1)) {s t u : Tm n}
      (h₁ : RPrf Γ (.eq s t)) (h₂ : RPrf Γ (.eq (Syn.subst (inst s) h) u)) :
      RPrf Γ (.eq u (Syn.subst (inst t) h))
  | qE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 1)} (t : Tm n)
      (h₁ : RPrf Γ (.Q B)) (h₂ : RPrf Γ (B.subst (inst zero))) : RPrf Γ (B.subst (inst t))
  | dE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 2)} {A : NFm n}
      (h₁ : RPrf Γ (.D B)) (h₂ : RPrf (.Q B :: Γ.map NFm.shift) A.shift) : RPrf Γ A
  | dIrP {n : ℕ} {Γ : List (NFm n)} {C : NFm (n + 1)} (a b : Tm (n + 1))
      (hC : NFm.abs (succ (Syn.var 0)) C = (NFm.eq a b).subst skz)
      (h : RPrf (NFm.eq a b :: Γ.map NFm.shift) C) : RPrf Γ (.D ((NFm.eq a b).subst skz))
  | dIrC {n : ℕ} {Γ : List (NFm n)} {C : NFm (n + 1)} (B : NFm (n + 2)) (w : Tm n)
      (hm : ¬ ((∃ a b, B = NFm.eq a b) ∧ w = zero))
      (hC : NFm.abs (Syn.shift (Syn.shift w)) (NFm.abs (succ (Syn.var 0)) C) = B.subst tauC)
      (h : RPrf ((B.subst (up (inst w))).subst (repl zero) :: Γ.map NFm.shift) C) :
      RPrf Γ (.D B)

variable {Γ : List (NFm n)} {A : NFm n}

/-- In the mode of progress the premise concludes the instance at `S z`. -/
theorem NFm.recon_progress {C : NFm (n + 1)} (a b : Tm (n + 1))
    (hC : NFm.abs (succ (Syn.var 0)) C = (NFm.eq a b).subst skz) :
    C = ((((NFm.eq a b).subst skz).subst (up (inst zero))).subst (repl (succ (Syn.var 0)))) := by
  have k := congrArg (fun F => NFm.subst F (inst (succ (Syn.var 0)))) hC
  simp only [NFm.abs_inst_self] at k
  rw [k, NFm.subst_subst, NFm.subst_subst, NFm.subst_subst]
  refine NFm.subst_ext _ fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [skz]

/-- In the mode of cases the premise concludes the instance at `w` and `S z`. -/
theorem NFm.recon_cases {C : NFm (n + 1)} (B : NFm (n + 2)) (w : Tm n)
    (hC : NFm.abs (Syn.shift (Syn.shift w)) (NFm.abs (succ (Syn.var 0)) C) = B.subst tauC) :
    C = (B.subst (up (inst w))).subst (repl (succ (Syn.var 0))) := by
  have k₁ := congrArg (fun F => NFm.subst F (inst (Syn.shift (Syn.shift w)))) hC
  simp only [NFm.abs_inst_self] at k₁
  have k₂ := congrArg (fun F => NFm.subst F (inst (succ (Syn.var 0)))) k₁
  simp only [NFm.abs_inst_self] at k₂
  rw [k₂, NFm.subst_subst, NFm.subst_subst, NFm.subst_subst]
  refine NFm.subst_ext _ fun i => ?_
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun l => ?_) j) i <;> simp [tauC]

/-- **Soundness**: every instance of the reconstructed introduction is an instance of
the single introduction. -/
theorem RPrf.toNPrf (h : RPrf Γ A) : NPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | trOne h _ _ ih₁ ih₂ => exact .trOne h ih₁ ih₂
  | qE t _ _ ih₁ ih₂ => exact .qE t ih₁ ih₂
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | @dIrP _ Γ C a b hC _ ih =>
    refine NPrf.ofDI _ zero ?_
    rw [← NFm.recon_progress a b hC]
    have e : ((((NFm.eq a b).subst skz).subst (up (inst zero))).subst
        (repl (NFm.start ((NFm.eq a b).subst skz) zero))) = NFm.eq a b := by
      rw [show NFm.start ((NFm.eq a b).subst skz) (zero : Tm _) = Syn.var 0 from rfl,
        NFm.subst_subst, NFm.subst_subst]
      refine NFm.subst_eq_self _ fun i => ?_
      refine Fin.cases ?_ (fun j => ?_) i <;> simp [skz]
    rw [e]; exact ih
  | @dIrC _ Γ C B w hm hC _ ih =>
    refine NPrf.ofDI B w ?_
    rw [← NFm.recon_cases B w hC, NFm.start_of_not hm]
    exact ih

/-- **Reconstruction at a marker**: with a large marker `M` as the witness, the double
abstraction of `B(M, S z)` is `B` itself. -/
theorem NFm.recon_mark (B : NFm (n + 2)) (M : Tm n) (hM : Tm.Big (NFm.sz B) M) :
    NFm.abs (Syn.shift (Syn.shift M)) (NFm.abs (succ (Syn.var 0))
      ((B.subst (up (inst M))).subst (repl (succ (Syn.var 0))))) = B.subst tauC := by
  have e₁ : (B.subst (up (inst M))).subst (repl (succ (Syn.var 0)))
      = B.subst (Fin.cases (succ (Syn.var 0)) (Fin.cases (Syn.shift M)
          fun i => Syn.var i.succ)) := by
    rw [NFm.subst_subst]
    refine NFm.subst_ext _ fun i => ?_
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun l => ?_) j) i
    all_goals simp [Syn.subst_shift]
    rfl
  have e₂ : NFm.abs (succ (Syn.var 0)) (B.subst (Fin.cases (succ (Syn.var 0)) (Fin.cases
      (Syn.shift M) fun i => Syn.var i.succ)))
      = B.subst (Fin.cases (Syn.var 0) (Fin.cases (Syn.shift (Syn.shift M))
          fun i => Syn.var i.succ.succ)) := by
    refine NFm.rpl_subst_succ B fun i => ?_
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun l => ?_) j) i
    · exact .inl ⟨rfl, rfl⟩
    · refine .inr ⟨Tm.occ_shift_zero M, ?_⟩
      simp only [Fin.cases_succ, Fin.cases_zero]
      rfl
    · refine .inr ⟨by simpa using (Fin.succ_ne_zero l).symm, ?_⟩
      simp
  have e₃ : NFm.abs (Syn.shift (Syn.shift M)) (B.subst (Fin.cases (Syn.var 0) (Fin.cases
      (Syn.shift (Syn.shift M)) fun i => Syn.var i.succ.succ))) = B.subst tauC := by
    refine NFm.rpl_subst B hM.shift.shift fun i => ?_
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun l => ?_) j) i
    · exact .inr ⟨0, rfl, by simp [tauC]⟩
    · exact .inl ⟨rfl, by simp [tauC]⟩
    · exact .inr ⟨l.succ.succ, by simp, by simp [tauC]⟩
  rw [e₁, e₂, e₃]

/-! ### Structural rules of `W_r` -/

theorem NFm.skz_rn (A : NFm (n + 1)) (ξ : Fin n → Fin m) :
    (A.subst skz).subst (up (up fun i => (Syn.var (ξ i) : Tm m)))
      = (A.subst (up fun i => (Syn.var (ξ i) : Tm m))).subst skz := by
  rw [NFm.subst_subst, NFm.subst_subst]
  refine NFm.subst_ext _ fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [skz]

theorem NFm.tauC_rn (B : NFm (n + 2)) (ξ : Fin n → Fin m) :
    (B.subst tauC).subst (up (up (up fun i => (Syn.var (ξ i) : Tm m))))
      = (B.subst (up (up fun i => (Syn.var (ξ i) : Tm m)))).subst tauC := by
  rw [NFm.subst_subst, NFm.subst_subst]
  refine NFm.subst_ext _ fun i => ?_
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun l => ?_) j) i <;> simp [tauC]

/-- Abstraction of `S z` commutes with an injective renaming of the other variables. -/
theorem NFm.abs_succ_rn (C : NFm (n + 1)) {ξ : Fin n → Fin m} (hξ : Function.Injective ξ) :
    NFm.abs (succ (Syn.var 0)) (C.subst (up fun i => (Syn.var (ξ i) : Tm m)))
      = (NFm.abs (succ (Syn.var 0)) C).subst (up (up fun i => (Syn.var (ξ i) : Tm m))) := by
  rw [Tm.up_rn ξ, NFm.abs_rn _ _ (Tm.upRen_inj hξ)]
  rfl

/-- The double abstraction commutes with an injective renaming of the other variables. -/
theorem NFm.abs2_rn (C : NFm (n + 1)) (w : Tm n) {ξ : Fin n → Fin m}
    (hξ : Function.Injective ξ) :
    NFm.abs (Syn.shift (Syn.shift (Syn.subst (fun i => (Syn.var (ξ i) : Tm m)) w)))
        (NFm.abs (succ (Syn.var 0)) (C.subst (up fun i => (Syn.var (ξ i) : Tm m))))
      = (NFm.abs (Syn.shift (Syn.shift w)) (NFm.abs (succ (Syn.var 0)) C)).subst
          (up (up (up fun i => (Syn.var (ξ i) : Tm m)))) := by
  rw [NFm.abs_succ_rn C hξ, Tm.up_rn ξ, Tm.up_rn (Tm.upRen ξ),
    NFm.abs_rn _ _ (Tm.upRen_inj (Tm.upRen_inj hξ))]
  congr 1
  rw [Tm.subst_var_ren, Tm.subst_var_ren, Tm.shift_eq_ren, Tm.shift_eq_ren, Tm.shift_eq_ren,
    Tm.shift_eq_ren, Tm.ren_ren, Tm.ren_ren, Tm.ren_ren, Tm.ren_ren]
  rfl

namespace RPrf

theorem hyp0 : RPrf (A :: Γ) A := .hyp List.mem_cons_self

theorem weaken (h : RPrf Γ A) : ∀ {Δ : List (NFm n)}, Γ ⊆ Δ → RPrf Δ A := by
  induction h with
  | hyp h => intro Δ s; exact .hyp (s h)
  | iterZero a h => intro Δ _; exact .iterZero a h
  | iterSucc c a h => intro Δ _; exact .iterSucc c a h
  | trOne h _ _ ih₁ ih₂ => intro Δ s; exact .trOne h (ih₁ s) (ih₂ s)
  | qE t _ _ ih₁ ih₂ => intro Δ s; exact .qE t (ih₁ s) (ih₂ s)
  | dE _ _ ih₁ ih₂ =>
    intro Δ s
    exact .dE (ih₁ s) (ih₂ (List.cons_subset_cons _ (List.map_subset _ s)))
  | dIrP a b hC _ ih =>
    intro Δ s; exact .dIrP a b hC (ih (List.cons_subset_cons _ (List.map_subset _ s)))
  | dIrC B w hm hC _ ih =>
    intro Δ s; exact .dIrC B w hm hC (ih (List.cons_subset_cons _ (List.map_subset _ s)))

theorem wk {B : NFm n} (h : RPrf Γ A) : RPrf (B :: Γ) A :=
  h.weaken (List.subset_cons_self _ _)

theorem ren (h : RPrf Γ A) : ∀ {m : ℕ} (ξ : Fin n → Fin m), Function.Injective ξ →
    RPrf (Γ.map fun B => B.subst fun i => (Syn.var (ξ i) : Tm m))
      (A.subst fun i => (Syn.var (ξ i) : Tm m)) := by
  induction h with
  | hyp h => intro m ξ _; exact .hyp (List.mem_map_of_mem h)
  | iterZero a h => intro m ξ _; exact .iterZero _ _
  | iterSucc c a h =>
    intro m ξ _
    simp only [NFm.subst_eq, Tm.subst_iter, Tm.subst_succ, Syn.subst_subst_inst]
    exact .iterSucc _ _ _
  | trOne h _ _ ih₁ ih₂ =>
    intro m ξ hξ
    have h₂ := ih₂ ξ hξ
    simp only [NFm.subst_eq, Syn.subst_subst_inst] at h₂ ⊢
    exact .trOne _ (ih₁ ξ hξ) h₂
  | qE t _ _ ih₁ ih₂ =>
    intro m ξ hξ
    have h₂ := ih₂ ξ hξ
    rw [NFm.subst_inst] at h₂ ⊢
    exact .qE _ (ih₁ ξ hξ) h₂
  | dE _ _ ih₁ ih₂ =>
    intro m ξ hξ
    have h := ih₂ (Tm.upRen ξ) (Tm.upRen_inj hξ)
    rw [← Tm.up_rn, List.map_cons, NFm.map_shift_subst, NFm.shift_subst_up] at h
    exact .dE (ih₁ ξ hξ) h
  | @dIrP _ Γ C a b hC _ ih =>
    intro m ξ hξ
    have h := ih (Tm.upRen ξ) (Tm.upRen_inj hξ)
    rw [← Tm.up_rn, List.map_cons, NFm.map_shift_subst] at h
    show RPrf _ (.D (((NFm.eq a b).subst skz).subst (up (up fun i => Syn.var (ξ i)))))
    rw [NFm.skz_rn]
    refine .dIrP _ _ ?_ h
    rw [NFm.abs_succ_rn C hξ, hC, NFm.skz_rn]
    rfl
  | @dIrC _ Γ C B w hm hC _ ih =>
    intro m ξ hξ
    have h := ih (Tm.upRen ξ) (Tm.upRen_inj hξ)
    rw [← Tm.up_rn, List.map_cons, NFm.map_shift_subst, NFm.subst_repl_up, NFm.subst_up_inst]
      at h
    show RPrf _ (.D (B.subst (up (up fun i => Syn.var (ξ i)))))
    refine RPrf.dIrC (C := C.subst (up fun i => Syn.var (ξ i))) _
      (Syn.subst (fun i => Syn.var (ξ i)) w) ?_ ?_ ?_
    · rintro ⟨⟨a', b', e⟩, hw⟩
      refine hm ⟨?_, ?_⟩
      · cases B with
        | eq a b => exact ⟨a, b, rfl⟩
        | Q B => cases e
        | D B => cases e
      · by_contra hw'
        exact Tm.subst_rn_ne_zero hw' ξ hw
    · rw [NFm.abs2_rn C w hξ, hC, NFm.tauC_rn]
    · simpa using h

theorem shift (h : RPrf Γ A) : RPrf (Γ.map NFm.shift) A.shift :=
  h.ren Fin.succ (Fin.succ_injective _)

theorem cutLift {Δ : List (NFm n)} (h : ∀ B ∈ Γ, RPrf Δ B) (C : NFm (n + 1)) :
    ∀ B ∈ C :: Γ.map NFm.shift, RPrf (C :: Δ.map NFm.shift) B := by
  intro B hB
  rcases List.mem_cons.1 hB with rfl | hB
  · exact hyp0
  · obtain ⟨B₀, hB₀, rfl⟩ := List.mem_map.1 hB
    exact (h B₀ hB₀).shift.wk

/-- Cut: hypotheses may be replaced by derivations of them. -/
theorem cut (h : RPrf Γ A) : ∀ {Δ : List (NFm n)}, (∀ B ∈ Γ, RPrf Δ B) → RPrf Δ A := by
  induction h with intro Δ hΔ
  | hyp h => exact hΔ _ h
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | trOne h _ _ ih₁ ih₂ => exact .trOne h (ih₁ hΔ) (ih₂ hΔ)
  | qE t _ _ ih₁ ih₂ => exact .qE t (ih₁ hΔ) (ih₂ hΔ)
  | dE _ _ ih₁ ih₂ => exact .dE (ih₁ hΔ) (ih₂ (cutLift hΔ _))
  | dIrP a b hC _ ih => exact .dIrP a b hC (ih (cutLift hΔ _))
  | dIrC B w hm hC _ ih => exact .dIrC B w hm hC (ih (cutLift hΔ _))

end RPrf

/-! ### Completeness, generically over the class `RKernel` -/

/-- The marker of a binary matrix with the seed `t`. -/
def NFm.markD (B : NFm (n + 2)) (t : Tm n) : Tm n := .iter .zero t (Tm.big (NFm.sz B))

theorem NFm.big_markD (B : NFm (n + 2)) (t : Tm n) : Tm.Big (NFm.sz B) (NFm.markD B t) :=
  ⟨_, _, _, rfl, by rw [Tm.sz_big]; omega⟩

/-- The rules used by completeness: computation, transport in equation templates,
elimination by abstraction, `DE`, the reconstructed introduction in both modes, and the
structural rules. -/
class RKernel (P : ∀ {n : ℕ}, List (NFm n) → NFm n → Prop) : Prop where
  hyp : ∀ {n : ℕ} {Γ : List (NFm n)} {A : NFm n}, A ∈ Γ → P Γ A
  iterZero : ∀ {n : ℕ} {Γ : List (NFm n)} (a : Tm n) (h : Tm (n + 1)),
    P Γ (.eq (iter zero a h) a)
  iterSucc : ∀ {n : ℕ} {Γ : List (NFm n)} (c a : Tm n) (h : Tm (n + 1)),
    P Γ (.eq (iter (succ c) a h) (Syn.subst (inst (iter c a h)) h))
  trEq : ∀ {n : ℕ} {Γ : List (NFm n)} (a b : Tm (n + 1)) {s t : Tm n}, P Γ (.eq s t) →
    P Γ (.eq (Syn.subst (inst s) a) (Syn.subst (inst s) b)) →
    P Γ (.eq (Syn.subst (inst t) a) (Syn.subst (inst t) b))
  aqE : ∀ {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (t : Tm n), P Γ (.Q (NFm.abs t A)) →
    P Γ (NFm.rep t zero A) → P Γ A
  dE : ∀ {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 2)} {A : NFm n}, P Γ (.D B) →
    P (.Q B :: Γ.map NFm.shift) A.shift → P Γ A
  dIrP : ∀ {n : ℕ} {Γ : List (NFm n)} {C : NFm (n + 1)} (a b : Tm (n + 1)),
    NFm.abs (succ (Syn.var 0)) C = (NFm.eq a b).subst skz →
    P (NFm.eq a b :: Γ.map NFm.shift) C → P Γ (.D ((NFm.eq a b).subst skz))
  dIrC : ∀ {n : ℕ} {Γ : List (NFm n)} {C : NFm (n + 1)} (B : NFm (n + 2)) (w : Tm n),
    ¬ ((∃ a b, B = NFm.eq a b) ∧ w = zero) →
    NFm.abs (Syn.shift (Syn.shift w)) (NFm.abs (succ (Syn.var 0)) C) = B.subst tauC →
    P ((B.subst (up (inst w))).subst (repl zero) :: Γ.map NFm.shift) C → P Γ (.D B)
  weaken : ∀ {n : ℕ} {Γ Δ : List (NFm n)} {A : NFm n}, P Γ A → Γ ⊆ Δ → P Δ A
  shift : ∀ {n : ℕ} {Γ : List (NFm n)} {A : NFm n}, P Γ A → P (Γ.map NFm.shift) A.shift
  cut : ∀ {n : ℕ} {Γ Δ : List (NFm n)} {A : NFm n}, P Γ A → (∀ B ∈ Γ, P Δ B) → P Δ A

namespace RKernel

variable {P : ∀ {n : ℕ}, List (NFm n) → NFm n → Prop} [RKernel @P] {Γ : List (NFm n)}
  {A : NFm n}

theorem hyp0 : P (A :: Γ) A := hyp List.mem_cons_self

theorem wk {B : NFm n} (h : P Γ A) : P (B :: Γ) A := weaken h (List.subset_cons_self _ _)

theorem eqRefl (t : Tm n) : P Γ (.eq t t) := by
  have h := trEq (Γ := Γ) (Syn.var 0) (Syn.shift t) (iterZero t (Syn.var 0))
    (by simpa using iterZero (P := @P) (Γ := Γ) t (Syn.var 0))
  simpa using h

theorem eqSymm {s t : Tm n} (h : P Γ (.eq s t)) : P Γ (.eq t s) := by
  have k := trEq (Syn.var 0) (Syn.shift s) h (by simpa using eqRefl (P := @P) (Γ := Γ) s)
  simpa using k

/-- The introduction at the marker of the matrix, in the mode of cases. -/
theorem dIM (B : NFm (n + 2)) (t : Tm n)
    (h : P ((B.subst (up (inst (NFm.markD B t)))).subst (repl zero) :: Γ.map NFm.shift)
      ((B.subst (up (inst (NFm.markD B t)))).subst (repl (succ (Syn.var 0))))) :
    P Γ (.D B) :=
  dIrC B (NFm.markD B t) (fun h' => by cases h'.2)
    (NFm.recon_mark B _ (NFm.big_markD B t)) h

/-- `Q` by cases, through the introduction at a marker of the matrix with a dummy first
variable. -/
theorem qCases (B : NFm (n + 1))
    (h : P ((B.subst (inst zero)).shift :: Γ.map NFm.shift)
      (B.subst (repl (succ (Syn.var 0))))) : P Γ (.Q B) := by
  have hD : P Γ (.D (B.subst (up (fun i => Syn.var i.succ)))) := by
    refine dIM _ zero ?_
    rw [NFm.subst_dummy_inst, ← NFm.shift_subst_inst_zero]
    exact h
  exact dE hD hyp0

/-- Introduction in the mode of cases at any witness, for matrices with at most `r`
binders. -/
def DI (P : ∀ {n : ℕ}, List (NFm n) → NFm n → Prop) (r : ℕ) : Prop :=
  ∀ (n : ℕ) (Γ : List (NFm n)) (B : NFm (n + 2)) (t : Tm n), B.rk ≤ r →
    P ((B.subst (up (inst t))).subst (repl zero) :: Γ.map NFm.shift)
      ((B.subst (up (inst t))).subst (repl (succ (Syn.var 0)))) → P Γ (.D B)

theorem i0 (G : NFm (m + 2)) (x : Tm m) :
    (G.subst (Fin.cases zero (Fin.cases (Syn.var 0)
      fun j => Syn.var j.succ.succ))).subst (inst (Syn.shift x))
      = ((G.subst (up (inst x))).subst (inst zero)).shift := by
  simp only [NFm.shift, NFm.subst_subst]
  refine G.subst_ext fun i => ?_
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun l => ?_) j) i <;>
    first | rfl | simp [Syn.shift, Syn.subst_subst]

theorem i1 (G : NFm (m + 2)) (x : Tm m) :
    (G.subst (Fin.cases (succ (Syn.var 1)) (Fin.cases (Syn.var 0)
      fun j => Syn.var j.succ.succ))).subst (inst (Syn.shift x))
      = (G.subst (up (inst x))).subst (repl (succ (Syn.var 0))) := by
  simp only [NFm.subst_subst]
  refine G.subst_ext fun i => ?_
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun l => ?_) j) i <;>
    first | rfl | simp [Syn.shift, Syn.subst_subst]

/-- **Introduction at any witness from transport**: move the assumption to the marker by
transport and cut, derive the conclusion there, and introduce at the marker. -/
theorem di_of_tr {r : ℕ} (hT : AKernel.Tr @P r) : DI @P r := by
  intro n Γ B t hr h
  have hA0 : ((B.subst (up (inst (NFm.markD B t)))).subst (repl zero))
      = ((B.subst (up (inst (NFm.markD B t)))).subst (inst zero)).shift :=
    (NFm.shift_subst_inst_zero _).symm
  have eM : P (((B.subst (up (inst (NFm.markD B t)))).subst (repl zero)) :: Γ.map NFm.shift)
      (.eq (Syn.shift (NFm.markD B t)) (Syn.shift t)) :=
    wk (shift (iterZero (P := @P) (Γ := Γ) t (Tm.big (NFm.sz B))))
  have hA : P (((B.subst (up (inst (NFm.markD B t)))).subst (repl zero)) :: Γ.map NFm.shift)
      ((B.subst (up (inst t))).subst (repl zero)) := by
    have k := hT _ _ (B.subst (Fin.cases zero (Fin.cases (Syn.var 0)
      fun j => Syn.var j.succ.succ))) (by rw [NFm.rk_subst]; exact hr) eM
      (by rw [i0, ← hA0]; exact hyp0)
    rw [i0, NFm.shift_subst_inst_zero] at k
    exact k
  have hC := cut (Δ := ((B.subst (up (inst (NFm.markD B t)))).subst (repl zero))
      :: Γ.map NFm.shift) h fun ψ hψ => by
    rcases List.mem_cons.1 hψ with rfl | hψ
    · exact hA
    · exact hyp (List.mem_cons_of_mem _ hψ)
  have hC' := hT _ _ (B.subst (Fin.cases (succ (Syn.var 1)) (Fin.cases (Syn.var 0)
      fun j => Syn.var j.succ.succ))) (by rw [NFm.rk_subst]; exact hr) (eqSymm eM)
      (by rw [i1]; exact hC)
  rw [i1] at hC'
  exact dIM B t hC'

/-- Elimination is `aqE` at the marker of the matrix followed by transport
along the computation `marker = t`. -/
theorem el_of_tr {r : ℕ} (hT : AKernel.Tr @P r) : AKernel.El @P r := by
  intro n Γ B t hr hQ h0
  have hK : P Γ (B.subst (inst (NFm.mark B t))) := by
    refine aqE (NFm.mark B t) ?_ ?_
    · rw [NFm.abs_mark]; exact hQ
    · rw [NFm.rep_mark]; exact h0
  exact hT _ _ B hr (iterZero t _) hK

/-- The step of a closure transported along `s = t`: from `B(t, 0)` to
`B(t, S z)`, through `B(s, 0)` and the closure `Q_y B(s, y)`. -/
theorem qStep {r : ℕ} (hT : AKernel.Tr @P r) (hE : AKernel.El @P r) {Θ : List (NFm m)} (G : NFm (m + 2))
    (hG : G.rk ≤ r) {s t : Tm m} (e : P Θ (.eq s t))
    (hQ : P Θ (.Q (G.subst (up (inst s))))) :
    P (((G.subst (up (inst t))).subst (inst zero)).shift :: Θ.map NFm.shift)
      ((G.subst (up (inst t))).subst (repl (succ (Syn.var 0)))) := by
  have e' : P (((G.subst (up (inst t))).subst (inst zero)).shift :: Θ.map NFm.shift)
      (.eq (Syn.shift s) (Syn.shift t)) := wk (shift e)
  have hQ' : P (((G.subst (up (inst t))).subst (inst zero)).shift :: Θ.map NFm.shift)
      (.Q ((G.subst (up (inst s))).subst (up fun i => Syn.var i.succ))) := wk (shift hQ)
  -- the template of the instances at zero
  have i0 : ∀ x : Tm m, (G.subst (Fin.cases zero (Fin.cases (Syn.var 0)
      fun j => Syn.var j.succ.succ))).subst (inst (Syn.shift x))
      = ((G.subst (up (inst x))).subst (inst zero)).shift := by
    intro x
    simp only [NFm.shift, NFm.subst_subst]
    refine G.subst_ext fun i => ?_
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun l => ?_) j) i <;>
      first | rfl | simp [Syn.shift, Syn.subst_subst]
  -- the template of the instances at `S z`
  have i1 : ∀ x : Tm m, (G.subst (Fin.cases (succ (Syn.var 1)) (Fin.cases (Syn.var 0)
      fun j => Syn.var j.succ.succ))).subst (inst (Syn.shift x))
      = (G.subst (up (inst x))).subst (repl (succ (Syn.var 0))) := by
    intro x
    simp only [NFm.subst_subst]
    refine G.subst_ext fun i => ?_
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun l => ?_) j) i <;>
      first | rfl | simp [Syn.shift, Syn.subst_subst]
  have h1 : P (((G.subst (up (inst t))).subst (inst zero)).shift :: Θ.map NFm.shift)
      (((G.subst (up (inst s))).subst (up fun i => Syn.var i.succ)).subst (inst zero)) := by
    rw [NFm.subst_dummy_up_inst, ← NFm.shift_subst_inst_zero, ← i0 s]
    exact hT _ _ (G.subst (Fin.cases zero (Fin.cases (Syn.var 0) fun j => Syn.var j.succ.succ)))
      (by rw [NFm.rk_subst]; exact hG) (eqSymm e') (by rw [i0]; exact hyp0)
  have h2 := hE _ _ ((G.subst (up (inst s))).subst (up fun i => Syn.var i.succ)) (succ (Syn.var 0))
    (by rw [NFm.rk_subst, NFm.rk_subst]; exact hG) hQ' h1
  rw [NFm.subst_dummy_up_inst, ← i1] at h2
  have h3 := hT _ _ (G.subst (Fin.cases (succ (Syn.var 1)) (Fin.cases (Syn.var 0)
      fun j => Syn.var j.succ.succ))) (by rw [NFm.rk_subst]; exact hG) e' h2
  rwa [i1] at h3

/-- **Transport and elimination**, by induction on the number of binders. -/
theorem trEl : ∀ r, AKernel.Tr @P r ∧ AKernel.El @P r ∧ DI @P r
  | 0 => by
    have hT : AKernel.Tr @P 0 := by
      intro n Γ F s t hr e h
      match F, hr with
      | .eq a b, _ => exact trEq a b e h
    exact ⟨hT, el_of_tr hT, di_of_tr hT⟩
  | r + 1 => by
    obtain ⟨hT, hE, hD⟩ := trEl r
    have hT' : AKernel.Tr @P (r + 1) := by
      intro n Γ F s t hr e h
      match F, hr with
      | .eq a b, _ => exact trEq a b e h
      | .Q B, hr =>
        exact qCases _ (qStep hT hE B (by simp only [NFm.rk] at hr; omega) e h)
      | .D B, hr =>
        refine dE h ?_
        show P _ (.D ((B.subst (up (up (inst t)))).subst (up (up fun i => Syn.var i.succ))))
        refine hD _ _ _ (Syn.var 0)
          (by rw [NFm.rk_subst, NFm.rk_subst]; simp only [NFm.rk] at hr; omega) ?_
        -- the instance at the eigenvariable of the reintroduced closure is the matrix itself
        have hτ : ((B.subst (up (up (inst t)))).subst (up (up fun i => Syn.var i.succ))).subst
            (up (inst (Syn.var 0))) = B.subst (up (up (inst t))) := by
          rw [NFm.subst_subst _ (up (up fun i => Syn.var i.succ))]
          refine NFm.subst_eq_self _ fun i => ?_
          refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun q => ?_) j) i <;> simp
        rw [hτ]
        -- the matrix with the eigenvariable in the place of the witness, and a hole for `v`
        have gx : ∀ x : Tm n, (B.subst (Fin.cases (Syn.var 0) (Fin.cases
            (Syn.var (Fin.succ (Fin.succ 0))) (Fin.cases (Syn.var (Fin.succ 0))
              fun j => Syn.var j.succ.succ.succ)))).subst (up (inst (Syn.shift x)))
            = B.subst (up (up (inst x))) := by
          intro x
          simp only [NFm.subst_subst]
          refine B.subst_ext fun i => ?_
          refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun l => Fin.cases ?_ (fun q => ?_) l) j)
            i <;> simp only [Fin.cases_succ, Fin.cases_zero, Syn.up_succ, Syn.up_zero,
              Syn.inst_zero, Syn.inst_succ, Syn.subst_var]
          all_goals simp
        have hq := qStep hT hE (Θ := .Q (B.subst (up (up (inst s)))) :: Γ.map NFm.shift)
          (B.subst (Fin.cases (Syn.var 0) (Fin.cases (Syn.var (Fin.succ (Fin.succ 0)))
            (Fin.cases (Syn.var (Fin.succ 0)) fun j => Syn.var j.succ.succ.succ))))
          (by rw [NFm.rk_subst]; simp only [NFm.rk] at hr; omega)
          (by exact wk (shift e) : P _ (.eq (Syn.shift s) (Syn.shift t)))
          (by rw [gx]; exact hyp0)
        rw [gx, NFm.shift_subst_inst_zero] at hq
        exact hq
    exact ⟨hT', el_of_tr hT', di_of_tr hT'⟩


theorem NFm.recon_eqP (E : NFm (n + 1)) :
    NFm.abs (succ (Syn.var 0)) (E.subst (repl (succ (Syn.var 0)))) = E.subst skz := by
  refine NFm.rpl_subst_succ E fun i => ?_
  refine Fin.cases (.inl ⟨rfl, rfl⟩) (fun j => .inr ⟨by simpa using (Fin.succ_ne_zero j).symm, ?_⟩) i
  simp [skz]

/-- Every rule of the kernel is a derived rule. -/
theorem ofNPrf (h : NPrf Γ A) : P Γ A := by
  induction h with
  | hyp h => exact hyp h
  | iterZero a h => exact iterZero a h
  | iterSucc c a h => exact iterSucc c a h
  | @trOne _ Γ h s t u _ _ ih₁ ih₂ =>
    have k := trEq (Syn.shift u) h ih₁ (by rw [Syn.subst_inst_shift]; exact eqSymm ih₂)
    rwa [Syn.subst_inst_shift] at k
  | qE t _ _ ih₁ ih₂ => exact (trEl _).2.1 _ _ _ t le_rfl ih₁ ih₂
  | dE _ _ ih₁ ih₂ => exact dE ih₁ ih₂
  | dICase B t _ ih =>
    rw [NFm.shift_subst_inst_zero] at ih
    exact (trEl B.rk).2.2 _ _ B t le_rfl ih
  | @qIInd _ Γ s₁ s₂ _ ih =>
    have hD := dIrP (P := @P) s₁ s₂ (NFm.recon_eqP _) ih
    refine dE hD ?_
    have e : (NFm.eq s₁ s₂).subst skz = (NFm.eq s₁ s₂).subst (up fun i => Syn.var i.succ) :=
      NFm.subst_ext _ fun i => by refine Fin.cases ?_ (fun j => ?_) i <;> simp [skz]
    rw [e]
    exact hyp0

end RKernel

theorem RPrf.trEq (a b : Tm (n + 1)) {s t : Tm n} (h₁ : RPrf Γ (.eq s t))
    (h₂ : RPrf Γ (.eq (Syn.subst (inst s) a) (Syn.subst (inst s) b))) :
    RPrf Γ (.eq (Syn.subst (inst t) a) (Syn.subst (inst t) b)) :=
  .trOne b h₁ (.trOne a h₁ h₂)

instance : RKernel @RPrf :=
  ⟨fun h => .hyp h, fun a h => .iterZero a h, fun c a h => .iterSucc c a h,
    fun a b => RPrf.trEq a b,
    NFm.aqE_of_qE (fun t h₁ h₂ => .qE t h₁ h₂), fun h₁ h₂ => .dE h₁ h₂,
    fun a b hC h => .dIrP a b hC h, fun B w hm hC h => .dIrC B w hm hC h,
    fun h s => h.weaken s, fun h => h.shift, fun h s => h.cut s⟩

/-- **The reconstructed introduction** (`wit:thm:recon`): `W_r` and the kernel derive the
same sequents. -/
theorem rprf_iff_nprf : RPrf Γ A ↔ NPrf Γ A := ⟨RPrf.toNPrf, RKernel.ofNPrf⟩



/-! ### Both matrices reconstructed: `W_rr` -/

/-- `W_rr`: `W_r` with elimination by abstraction in place of `QE`; both the introduction
and the elimination of a closure find their matrix by abstraction. -/
inductive RRPrf : {n : ℕ} → List (NFm n) → NFm n → Prop
  | hyp {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (h : A ∈ Γ) : RRPrf Γ A
  | iterZero {n : ℕ} {Γ : List (NFm n)} (a : Tm n) (h : Tm (n + 1)) :
      RRPrf Γ (.eq (iter zero a h) a)
  | iterSucc {n : ℕ} {Γ : List (NFm n)} (c a : Tm n) (h : Tm (n + 1)) :
      RRPrf Γ (.eq (iter (succ c) a h) (Syn.subst (inst (iter c a h)) h))
  | trOne {n : ℕ} {Γ : List (NFm n)} (h : Tm (n + 1)) {s t u : Tm n}
      (h₁ : RRPrf Γ (.eq s t)) (h₂ : RRPrf Γ (.eq (Syn.subst (inst s) h) u)) :
      RRPrf Γ (.eq u (Syn.subst (inst t) h))
  | aqE {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (t : Tm n) (h₁ : RRPrf Γ (.Q (NFm.abs t A)))
      (h₂ : RRPrf Γ (NFm.rep t zero A)) : RRPrf Γ A
  | dE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 2)} {A : NFm n}
      (h₁ : RRPrf Γ (.D B)) (h₂ : RRPrf (.Q B :: Γ.map NFm.shift) A.shift) : RRPrf Γ A
  | dIrP {n : ℕ} {Γ : List (NFm n)} {C : NFm (n + 1)} (a b : Tm (n + 1))
      (hC : NFm.abs (succ (Syn.var 0)) C = (NFm.eq a b).subst skz)
      (h : RRPrf (NFm.eq a b :: Γ.map NFm.shift) C) : RRPrf Γ (.D ((NFm.eq a b).subst skz))
  | dIrC {n : ℕ} {Γ : List (NFm n)} {C : NFm (n + 1)} (B : NFm (n + 2)) (w : Tm n)
      (hm : ¬ ((∃ a b, B = NFm.eq a b) ∧ w = zero))
      (hC : NFm.abs (Syn.shift (Syn.shift w)) (NFm.abs (succ (Syn.var 0)) C) = B.subst tauC)
      (h : RRPrf ((B.subst (up (inst w))).subst (repl zero) :: Γ.map NFm.shift) C) :
      RRPrf Γ (.D B)

variable {Γ : List (NFm n)} {A : NFm n}

/-- **Soundness**: of `W_rr`. -/
theorem RRPrf.toNPrf (h : RRPrf Γ A) : NPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | trOne h _ _ ih₁ ih₂ => exact .trOne h ih₁ ih₂
  | @aqE _ _ A t _ _ ih₁ ih₂ =>
    rw [← NFm.abs_inst] at ih₂
    have h := NPrf.qE t ih₁ ih₂
    rwa [NFm.abs_inst_self] at h
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | @dIrP _ Γ C a b hC _ ih =>
    refine NPrf.ofDI _ zero ?_
    rw [← NFm.recon_progress a b hC]
    have e : ((((NFm.eq a b).subst skz).subst (up (inst zero))).subst
        (repl (NFm.start ((NFm.eq a b).subst skz) zero))) = NFm.eq a b := by
      rw [show NFm.start ((NFm.eq a b).subst skz) (zero : Tm _) = Syn.var 0 from rfl,
        NFm.subst_subst, NFm.subst_subst]
      refine NFm.subst_eq_self _ fun i => ?_
      refine Fin.cases ?_ (fun j => ?_) i <;> simp [skz]
    rw [e]; exact ih
  | @dIrC _ Γ C B w hm hC _ ih =>
    refine NPrf.ofDI B w ?_
    rw [← NFm.recon_cases B w hC, NFm.start_of_not hm]
    exact ih

namespace RRPrf

theorem hyp0 : RRPrf (A :: Γ) A := .hyp List.mem_cons_self

theorem weaken (h : RRPrf Γ A) : ∀ {Δ : List (NFm n)}, Γ ⊆ Δ → RRPrf Δ A := by
  induction h with
  | hyp h => intro Δ s; exact .hyp (s h)
  | iterZero a h => intro Δ _; exact .iterZero a h
  | iterSucc c a h => intro Δ _; exact .iterSucc c a h
  | trOne h _ _ ih₁ ih₂ => intro Δ s; exact .trOne h (ih₁ s) (ih₂ s)
  | aqE t _ _ ih₁ ih₂ => intro Δ s; exact .aqE t (ih₁ s) (ih₂ s)
  | dE _ _ ih₁ ih₂ =>
    intro Δ s
    exact .dE (ih₁ s) (ih₂ (List.cons_subset_cons _ (List.map_subset _ s)))
  | dIrP a b hC _ ih =>
    intro Δ s; exact .dIrP a b hC (ih (List.cons_subset_cons _ (List.map_subset _ s)))
  | dIrC B w hm hC _ ih =>
    intro Δ s; exact .dIrC B w hm hC (ih (List.cons_subset_cons _ (List.map_subset _ s)))

theorem wk {B : NFm n} (h : RRPrf Γ A) : RRPrf (B :: Γ) A :=
  h.weaken (List.subset_cons_self _ _)

theorem ren (h : RRPrf Γ A) : ∀ {m : ℕ} (ξ : Fin n → Fin m), Function.Injective ξ →
    RRPrf (Γ.map fun B => B.subst fun i => (Syn.var (ξ i) : Tm m))
      (A.subst fun i => (Syn.var (ξ i) : Tm m)) := by
  induction h with
  | hyp h => intro m ξ _; exact .hyp (List.mem_map_of_mem h)
  | iterZero a h => intro m ξ _; exact .iterZero _ _
  | iterSucc c a h =>
    intro m ξ _
    simp only [NFm.subst_eq, Tm.subst_iter, Tm.subst_succ, Syn.subst_subst_inst]
    exact .iterSucc _ _ _
  | trOne h _ _ ih₁ ih₂ =>
    intro m ξ hξ
    have h₂ := ih₂ ξ hξ
    simp only [NFm.subst_eq, Syn.subst_subst_inst] at h₂ ⊢
    exact .trOne _ (ih₁ ξ hξ) h₂
  | aqE t _ _ ih₁ ih₂ =>
    intro m ξ hξ
    have h₁ := ih₁ ξ hξ
    have h₂ := ih₂ ξ hξ
    simp only [NFm.subst_Q, NFm.abs_rn _ _ hξ] at h₁
    rw [NFm.rep_rn _ _ _ hξ] at h₂
    exact .aqE _ h₁ h₂
  | dE _ _ ih₁ ih₂ =>
    intro m ξ hξ
    have h := ih₂ (Tm.upRen ξ) (Tm.upRen_inj hξ)
    rw [← Tm.up_rn, List.map_cons, NFm.map_shift_subst, NFm.shift_subst_up] at h
    exact .dE (ih₁ ξ hξ) h
  | @dIrP _ Γ C a b hC _ ih =>
    intro m ξ hξ
    have h := ih (Tm.upRen ξ) (Tm.upRen_inj hξ)
    rw [← Tm.up_rn, List.map_cons, NFm.map_shift_subst] at h
    show RRPrf _ (.D (((NFm.eq a b).subst skz).subst (up (up fun i => Syn.var (ξ i)))))
    rw [NFm.skz_rn]
    refine .dIrP _ _ ?_ h
    rw [NFm.abs_succ_rn C hξ, hC, NFm.skz_rn]
    rfl
  | @dIrC _ Γ C B w hm hC _ ih =>
    intro m ξ hξ
    have h := ih (Tm.upRen ξ) (Tm.upRen_inj hξ)
    rw [← Tm.up_rn, List.map_cons, NFm.map_shift_subst, NFm.subst_repl_up, NFm.subst_up_inst]
      at h
    show RRPrf _ (.D (B.subst (up (up fun i => Syn.var (ξ i)))))
    refine RRPrf.dIrC (C := C.subst (up fun i => Syn.var (ξ i))) _
      (Syn.subst (fun i => Syn.var (ξ i)) w) ?_ ?_ ?_
    · rintro ⟨⟨a', b', e⟩, hw⟩
      refine hm ⟨?_, ?_⟩
      · cases B with
        | eq a b => exact ⟨a, b, rfl⟩
        | Q B => cases e
        | D B => cases e
      · by_contra hw'
        exact Tm.subst_rn_ne_zero hw' ξ hw
    · rw [NFm.abs2_rn C w hξ, hC, NFm.tauC_rn]
    · simpa using h

theorem shift (h : RRPrf Γ A) : RRPrf (Γ.map NFm.shift) A.shift :=
  h.ren Fin.succ (Fin.succ_injective _)

theorem cutLift {Δ : List (NFm n)} (h : ∀ B ∈ Γ, RRPrf Δ B) (C : NFm (n + 1)) :
    ∀ B ∈ C :: Γ.map NFm.shift, RRPrf (C :: Δ.map NFm.shift) B := by
  intro B hB
  rcases List.mem_cons.1 hB with rfl | hB
  · exact hyp0
  · obtain ⟨B₀, hB₀, rfl⟩ := List.mem_map.1 hB
    exact (h B₀ hB₀).shift.wk

/-- Cut: hypotheses may be replaced by derivations of them. -/
theorem cut (h : RRPrf Γ A) : ∀ {Δ : List (NFm n)}, (∀ B ∈ Γ, RRPrf Δ B) → RRPrf Δ A := by
  induction h with intro Δ hΔ
  | hyp h => exact hΔ _ h
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | trOne h _ _ ih₁ ih₂ => exact .trOne h (ih₁ hΔ) (ih₂ hΔ)
  | aqE t _ _ ih₁ ih₂ => exact .aqE t (ih₁ hΔ) (ih₂ hΔ)
  | dE _ _ ih₁ ih₂ => exact .dE (ih₁ hΔ) (ih₂ (cutLift hΔ _))
  | dIrP a b hC _ ih => exact .dIrP a b hC (ih (cutLift hΔ _))
  | dIrC B w hm hC _ ih => exact .dIrC B w hm hC (ih (cutLift hΔ _))

end RRPrf

theorem RRPrf.trEq (a b : Tm (n + 1)) {s t : Tm n} (h₁ : RRPrf Γ (.eq s t))
    (h₂ : RRPrf Γ (.eq (Syn.subst (inst s) a) (Syn.subst (inst s) b))) :
    RRPrf Γ (.eq (Syn.subst (inst t) a) (Syn.subst (inst t) b)) :=
  .trOne b h₁ (.trOne a h₁ h₂)

instance : RKernel @RRPrf :=
  ⟨fun h => .hyp h, fun a h => .iterZero a h, fun c a h => .iterSucc c a h,
    fun a b => RRPrf.trEq a b, fun t h₁ h₂ => .aqE t h₁ h₂, fun h₁ h₂ => .dE h₁ h₂,
    fun a b hC h => .dIrP a b hC h, fun B w hm hC h => .dIrC B w hm hC h,
    fun h s => h.weaken s, fun h => h.shift, fun h s => h.cut s⟩

/-- **Both matrices reconstructed** (`wit:q:recon`): `W_r` with elimination by abstraction
in place of `QE` is still equivalent to the kernel. -/
theorem rrprf_iff_nprf : RRPrf Γ A ↔ NPrf Γ A := ⟨RRPrf.toNPrf, RKernel.ofNPrf⟩

end LeanProofs.ConciseIPRA
