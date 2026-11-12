import ConciseIPRA.NativeTemplateFree
import ConciseIPRA.NativeClausal

/-!
# Full normal forms of iterator terms

Both computations of the iterator can be contracted,

  `I(0, a; u.h) ⟶ a`,  `I(S c, a; u.h) ⟶ h[I(c, a; u.h)/u]`,

and every term has a normal form.  The normalizer is defined by evaluation,
with no termination argument: `Tm.nbe t ρ` evaluates `t` in an environment `ρ`
of terms by structural recursion on `t`, and the iterator is evaluated by
`Tm.recV`, a recursion on the *value* of its counter that unfolds a numeral
prefix and leaves a neutral counter in place.  `Tm.full t` is the value of `t`
in the identity environment.

The laws of a normalizer are four lemmas about evaluation:

* evaluation commutes with renaming of the target (`ren_nbe`) and of the source
  (`nbe_ren`);
* evaluating a substitution instance is evaluating in the evaluated
  environment (`nbe_sub`);
* evaluating a value is evaluating in the composed environment (`nbe_nbe`).

Idempotence, the coherence of normalization with substitution
(`full_subst_congr`) and with renaming follow, and the same for formulas
(`NFm.full`).  The kernel proves every term equal to its normal form
(`NPrf.eqFull`) and every formula interderivable with its normal form
(`equivFull`).
-/

namespace LeanProofs.ConciseIPRA

open Syn
open Tm (zero succ iter)

variable {n m k : ℕ}

namespace Tm

/-- The iterator on values: a numeral prefix of the counter is unfolded, a
neutral counter stays. -/
def recV : {m : ℕ} → Tm m → Tm m → (Tm m → Tm m) → Tm (m + 1) → Tm m
  | _, .zero, a, _, _ => a
  | _, .succ c, a, f, b => f (recV c a f b)
  | _, .var i, a, _, b => .iter (.var i) a b
  | _, .iter c a' h, a, _, b => .iter (.iter c a' h) a b

/-- Evaluation of a term in an environment of terms. -/
def nbe : {n : ℕ} → Tm n → {m : ℕ} → (Fin n → Tm m) → Tm m
  | _, .var i, _, ρ => ρ i
  | _, .zero, _, _ => .zero
  | _, .succ t, _, ρ => .succ (nbe t ρ)
  | _, .iter c a h, _, ρ =>
    recV (nbe c ρ) (nbe a ρ) (fun v => nbe h (Fin.cases v ρ))
      (nbe h (Fin.cases (.var 0) fun i => ren Fin.succ (ρ i)))

/-- The full normal form. -/
def full (t : Tm n) : Tm n := nbe t Tm.var

theorem ren_recV (x : Tm m) : ∀ {k : ℕ} (ξ : Fin m → Fin k) (a : Tm m) (f : Tm m → Tm m)
    (b : Tm (m + 1)) (f' : Tm k → Tm k), (∀ w, ren ξ (f w) = f' (ren ξ w)) →
      ren ξ (recV x a f b) = recV (ren ξ x) (ren ξ a) f' (ren (upRen ξ) b) := by
  induction x with
  | var i => intro k ξ a f b f' _; rfl
  | zero => intro k ξ a f b f' _; rfl
  | succ x ih =>
    intro k ξ a f b f' hf
    show ren ξ (f (recV x a f b)) = f' (recV (ren ξ x) (ren ξ a) f' (ren (upRen ξ) b))
    rw [hf, ih ξ a f b f' hf]
  | iter c a' h _ _ _ => intro k ξ a f b f' _; rfl

/-- Evaluation commutes with renaming of the target. -/
theorem ren_nbe (t : Tm n) : ∀ {m k : ℕ} (ξ : Fin m → Fin k) (ρ : Fin n → Tm m),
    ren ξ (nbe t ρ) = nbe t fun i => ren ξ (ρ i) := by
  induction t with
  | var i => intro m k ξ ρ; rfl
  | zero => intro m k ξ ρ; rfl
  | succ t ih => intro m k ξ ρ; exact congrArg succ (ih ξ ρ)
  | iter c a h ihc iha ihh =>
    intro m k ξ ρ
    have hf : ∀ w, ren ξ (nbe h (Fin.cases w ρ))
        = nbe h (Fin.cases (ren ξ w) fun i => ren ξ (ρ i)) := by
      intro w
      rw [ihh]
      refine congrArg (fun r => nbe h r) (funext fun i => ?_)
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
    have hb : ren (upRen ξ) (nbe h (Fin.cases (.var 0) fun i => ren Fin.succ (ρ i)))
        = nbe h (Fin.cases (.var 0) fun i => ren Fin.succ (ren ξ (ρ i))) := by
      rw [ihh]
      refine congrArg (fun r => nbe h r) (funext fun i => ?_)
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · simp only [Fin.cases_succ, ren_ren, upRen_succ]
    refine (ren_recV (nbe c ρ) ξ (nbe a ρ) (fun v => nbe h (Fin.cases v ρ)) _
      (fun v => nbe h (Fin.cases v fun i => ren ξ (ρ i))) hf).trans ?_
    rw [ihc, iha, hb]
    rfl

/-- Evaluation of a renamed term. -/
theorem nbe_ren (t : Tm n) : ∀ {m k : ℕ} (ξ : Fin n → Fin m) (ρ : Fin m → Tm k),
    nbe (ren ξ t) ρ = nbe t fun i => ρ (ξ i) := by
  induction t with
  | var i => intro m k ξ ρ; rfl
  | zero => intro m k ξ ρ; rfl
  | succ t ih => intro m k ξ ρ; exact congrArg succ (ih ξ ρ)
  | iter c a h ihc iha ihh =>
    intro m k ξ ρ
    have e₁ : ∀ v : Tm k, (fun i => (Fin.cases v ρ : Fin (m + 1) → Tm k) (upRen ξ i))
        = Fin.cases v fun i => ρ (ξ i) := by
      intro v
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
    have e₂ : (fun i => (Fin.cases (.var 0) (fun i => ren Fin.succ (ρ i))
          : Fin (m + 1) → Tm (k + 1)) (upRen ξ i))
        = Fin.cases (.var 0) fun i => ren Fin.succ (ρ (ξ i)) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
    show recV (nbe (ren ξ c) ρ) (nbe (ren ξ a) ρ)
        (fun v => nbe (ren (upRen ξ) h) (Fin.cases v ρ))
        (nbe (ren (upRen ξ) h) (Fin.cases (.var 0) fun i => ren Fin.succ (ρ i)))
      = recV (nbe c fun i => ρ (ξ i)) (nbe a fun i => ρ (ξ i))
        (fun v => nbe h (Fin.cases v fun i => ρ (ξ i)))
        (nbe h (Fin.cases (.var 0) fun i => ren Fin.succ (ρ (ξ i))))
    simp only [ihc, iha, ihh, e₁, e₂]

/-- Evaluation of a substitution instance. -/
theorem nbe_sub (t : Tm n) : ∀ {m k : ℕ} (σ : Fin n → Tm m) (ρ : Fin m → Tm k),
    nbe (sub σ t) ρ = nbe t fun i => nbe (σ i) ρ := by
  induction t with
  | var i => intro m k σ ρ; rfl
  | zero => intro m k σ ρ; rfl
  | succ t ih => intro m k σ ρ; exact congrArg succ (ih σ ρ)
  | iter c a h ihc iha ihh =>
    intro m k σ ρ
    have e₁ : ∀ v : Tm k, (fun i => nbe (upS σ i) (Fin.cases v ρ))
        = Fin.cases v fun i => nbe (σ i) ρ := by
      intro v
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · simp only [upS_succ, nbe_ren, Fin.cases_succ]
    have e₂ : (fun i => nbe (upS σ i) (Fin.cases (.var 0) fun i => ren Fin.succ (ρ i)))
        = Fin.cases (.var 0) fun i => ren Fin.succ (nbe (σ i) ρ) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · simp only [upS_succ, nbe_ren, Fin.cases_succ, ren_nbe]
    show recV (nbe (sub σ c) ρ) (nbe (sub σ a) ρ)
        (fun v => nbe (sub (upS σ) h) (Fin.cases v ρ))
        (nbe (sub (upS σ) h) (Fin.cases (.var 0) fun i => ren Fin.succ (ρ i)))
      = recV (nbe c fun i => nbe (σ i) ρ) (nbe a fun i => nbe (σ i) ρ)
        (fun v => nbe h (Fin.cases v fun i => nbe (σ i) ρ))
        (nbe h (Fin.cases (.var 0) fun i => ren Fin.succ (nbe (σ i) ρ)))
    simp only [ihc, iha, ihh, e₁, e₂]

theorem nbe_recV (x : Tm m) : ∀ {k : ℕ} (a : Tm m) (f : Tm m → Tm m) (b : Tm (m + 1))
    (τ : Fin m → Tm k) (g : Tm k → Tm k) (b' : Tm (k + 1)),
    (∀ w, nbe (f w) τ = g (nbe w τ)) → (∀ v, nbe b (Fin.cases v τ) = g v) →
    nbe b (Fin.cases (.var 0) fun i => ren Fin.succ (τ i)) = b' →
      nbe (recV x a f b) τ = recV (nbe x τ) (nbe a τ) g b' := by
  induction x with
  | var i =>
    intro k a f b τ g b' _ hg hb
    show recV (τ i) (nbe a τ) (fun v => nbe b (Fin.cases v τ)) (nbe b _) = _
    rw [funext hg, hb]
    rfl
  | zero => intro k a f b τ g b' _ _ _; rfl
  | succ x ih =>
    intro k a f b τ g b' hf hg hb
    show nbe (f (recV x a f b)) τ = g (recV (nbe x τ) (nbe a τ) g b')
    rw [hf, ih a f b τ g b' hf hg hb]
  | iter c a' h _ _ _ =>
    intro k a f b τ g b' _ hg hb
    show recV (nbe (iter c a' h) τ) (nbe a τ) (fun v => nbe b (Fin.cases v τ)) (nbe b _) = _
    rw [funext hg, hb]

/-- Evaluation of a value. -/
theorem nbe_nbe (t : Tm n) : ∀ {m k : ℕ} (ρ : Fin n → Tm m) (τ : Fin m → Tm k),
    nbe (nbe t ρ) τ = nbe t fun i => nbe (ρ i) τ := by
  induction t with
  | var i => intro m k ρ τ; rfl
  | zero => intro m k ρ τ; rfl
  | succ t ih => intro m k ρ τ; exact congrArg succ (ih ρ τ)
  | iter c a h ihc iha ihh =>
    intro m k ρ τ
    show nbe (recV (nbe c ρ) (nbe a ρ) (fun v => nbe h (Fin.cases v ρ))
        (nbe h (Fin.cases (.var 0) fun i => ren Fin.succ (ρ i)))) τ
      = recV (nbe c fun i => nbe (ρ i) τ) (nbe a fun i => nbe (ρ i) τ)
        (fun v => nbe h (Fin.cases v fun i => nbe (ρ i) τ))
        (nbe h (Fin.cases (.var 0) fun i => ren Fin.succ (nbe (ρ i) τ)))
    rw [← ihc ρ τ, ← iha ρ τ]
    refine nbe_recV _ _ _ _ τ _ _ (fun w => ?_) (fun v => ?_) ?_
    · rw [ihh]
      refine congrArg (fun r => nbe h r) (funext fun i => ?_)
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
    · rw [ihh]
      refine congrArg (fun r => nbe h r) (funext fun i => ?_)
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · simp only [Fin.cases_succ, nbe_ren]
    · rw [ihh]
      refine congrArg (fun r => nbe h r) (funext fun i => ?_)
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · simp only [Fin.cases_succ, nbe_ren, ren_nbe]

/-! ### The laws of the normalizer -/

theorem nbe_full (t : Tm n) (τ : Fin n → Tm m) : nbe (full t) τ = nbe t τ :=
  nbe_nbe t Tm.var τ

@[simp] theorem full_idem (t : Tm n) : full (full t) = full t := nbe_full t Tm.var

theorem full_subst (t : Tm n) (σ : Fin n → Tm m) :
    full (Syn.subst σ t) = nbe t fun i => full (σ i) := nbe_sub t σ Tm.var

/-- The normal form of a substitution instance depends only on normal forms. -/
theorem full_subst_congr {t t' : Tm n} {σ σ' : Fin n → Tm m} (ht : full t = full t')
    (hσ : ∀ i, full (σ i) = full (σ' i)) : full (Syn.subst σ t) = full (Syn.subst σ' t') := by
  rw [full_subst, full_subst, ← nbe_full t, ← nbe_full t', ht, funext hσ]

theorem full_ren (t : Tm n) (ξ : Fin n → Fin m) : full (ren ξ t) = ren ξ (full t) :=
  (nbe_ren t ξ Tm.var).trans (ren_nbe t ξ Tm.var).symm

@[simp] theorem full_shift (t : Tm n) : full (Syn.shift t) = Syn.shift (full t) := by
  rw [shift_eq_ren, shift_eq_ren, full_ren]

theorem full_rn (t : Tm n) (ξ : Fin n → Fin m) :
    full (Syn.subst (fun i => (Syn.var (ξ i) : Tm m)) t)
      = Syn.subst (fun i => (Syn.var (ξ i) : Tm m)) (full t) := by
  show full (sub (fun i => var (ξ i)) t) = sub (fun i => var (ξ i)) (full t)
  rw [← ren_eq_sub, ← ren_eq_sub, full_ren]

theorem full_inst (t : Tm n) (i : Fin (n + 1)) : full (inst (full t) i) = full (inst t i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact full_idem t
  · simp

theorem full_up (σ : Fin n → Tm m) : (fun i => full (up σ i)) = up fun i => full (σ i) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp

theorem full_up_congr {σ σ' : Fin n → Tm m} (h : ∀ i, full (σ i) = full (σ' i))
    (i : Fin (n + 1)) : full (up σ i) = full (up σ' i) :=
  (congrFun (full_up σ) i).trans (by rw [funext h]; exact (congrFun (full_up σ') i).symm)

end Tm

/-! ### Correctness in the kernel -/

namespace NPrf

/-- The iterator on values is the iterator, provably. -/
theorem recVEq (x : Tm m) : ∀ {Γ : List (NFm m)} (a₀ a : Tm m) (h₀ : Tm (m + 1))
    (f : Tm m → Tm m) (b : Tm (m + 1)), NPrf Γ (.eq a₀ a) →
    (∀ v w, NPrf Γ (.eq v w) → NPrf Γ (.eq (Syn.subst (inst v) h₀) (f w))) →
    NPrf (Γ.map NFm.shift) (.eq h₀ b) → NPrf Γ (.eq (iter x a₀ h₀) (Tm.recV x a f b)) := by
  induction x with
  | var i =>
    intro Γ a₀ a h₀ f b ha _ hb
    exact eqTrans (iterCongr h₀ (eqRefl _) ha) (iterBody _ a hb)
  | zero => intro Γ a₀ a h₀ f b ha _ _; exact eqTrans (.iterZero a₀ h₀) ha
  | succ x ih =>
    intro Γ a₀ a h₀ f b ha hf hb
    exact eqTrans (.iterSucc x a₀ h₀) (hf _ _ (ih a₀ a h₀ f b ha hf hb))
  | iter c a' h _ _ _ =>
    intro Γ a₀ a h₀ f b ha _ hb
    exact eqTrans (iterCongr h₀ (eqRefl _) ha) (iterBody _ a hb)

/-- A substitution instance is provably equal to the value in an environment
of provably equal terms. -/
theorem nbeEq (t : Tm n) : ∀ {m : ℕ} {Γ : List (NFm m)} (σ ρ : Fin n → Tm m),
    (∀ i, NPrf Γ (.eq (σ i) (ρ i))) → NPrf Γ (.eq (Syn.subst σ t) (Tm.nbe t ρ)) := by
  induction t with
  | var i => intro m Γ σ ρ he; exact he i
  | zero => intro m Γ σ ρ _; exact eqRefl _
  | succ t ih => intro m Γ σ ρ he; exact eqCongr (succ (Syn.var 0)) (ih σ ρ he)
  | iter c a h ihc iha ihh =>
    intro m Γ σ ρ he
    rw [Tm.subst_iter]
    refine eqTrans (iterCongr _ (ihc σ ρ he) (eqRefl _)) ?_
    refine recVEq _ _ _ _ _ _ (iha σ ρ he) (fun v w hvw => ?_) ?_
    · have e : Syn.subst (inst v) (Syn.subst (up σ) h)
          = Syn.subst (Fin.cases v σ : Fin (_ + 1) → Tm m) h := by
        rw [Syn.subst_subst]
        refine congrArg (fun r => Syn.subst r h) (funext fun i => ?_)
        refine Fin.cases ?_ (fun j => ?_) i <;> simp
      rw [e]
      refine ihh _ _ fun i => ?_
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hvw
      · simp only [Fin.cases_succ]; exact he j
    · refine ihh _ _ fun i => ?_
      refine Fin.cases ?_ (fun j => ?_) i
      · exact eqRefl _
      · simp only [Fin.cases_succ, Syn.up_succ, ← Tm.shift_eq_ren]
        exact (he j).shift

/-- A term is provably equal to its full normal form. -/
theorem eqFull {Γ : List (NFm n)} (t : Tm n) : NPrf Γ (.eq t t.full) := by
  have h := nbeEq (Γ := Γ) t Syn.var Tm.var fun i => eqRefl _
  rwa [Syn.subst_id] at h

end NPrf

/-! ### Formulas -/

/-- The full normal form of a formula. -/
def NFm.full : {n : ℕ} → NFm n → NFm n
  | _, .eq s t => .eq s.full t.full
  | _, .Q B => .Q (NFm.full B)
  | _, .D B => .D (NFm.full B)

namespace NFm

@[simp] theorem full_idem (A : NFm n) : A.full.full = A.full := by
  induction A with
  | eq s t => simp only [NFm.full, Tm.full_idem]
  | Q B ih => exact congrArg NFm.Q ih
  | D B ih => exact congrArg NFm.D ih

theorem full_subst (A : NFm n) : ∀ {m : ℕ} (σ : Fin n → Tm m),
    (A.full.subst fun i => (σ i).full).full = (A.subst σ).full := by
  induction A with
  | eq s t =>
    intro m σ
    simp only [NFm.full, NFm.subst_eq]
    rw [Tm.full_subst_congr (Tm.full_idem s) fun i => Tm.full_idem (σ i),
      Tm.full_subst_congr (Tm.full_idem t) fun i => Tm.full_idem (σ i)]
  | Q B ih =>
    intro m σ
    have h := ih (up σ)
    rw [Tm.full_up] at h
    exact congrArg NFm.Q h
  | D B ih =>
    intro m σ
    have h := ih (up (up σ))
    rw [Tm.full_up, Tm.full_up] at h
    exact congrArg NFm.D h

theorem full_subst_congr {A A' : NFm n} {σ σ' : Fin n → Tm m} (hA : A.full = A'.full)
    (hσ : ∀ i, (σ i).full = (σ' i).full) : (A.subst σ).full = (A'.subst σ').full := by
  rw [← full_subst A σ, ← full_subst A' σ', hA, funext hσ]

theorem full_rn (A : NFm n) : ∀ {m : ℕ} (ξ : Fin n → Fin m),
    (A.subst fun i => (Syn.var (ξ i) : Tm m)).full
      = A.full.subst fun i => (Syn.var (ξ i) : Tm m) := by
  induction A with
  | eq s t => intro m ξ; simp only [NFm.subst_eq, NFm.full, Tm.full_rn]
  | Q B ih => intro m ξ; simp only [NFm.subst_Q, NFm.full, Tm.up_rn, ih]
  | D B ih => intro m ξ; simp only [NFm.subst_D, NFm.full, Tm.up_rn, ih]

theorem full_shift (A : NFm n) : A.shift.full = A.full.shift := full_rn A Fin.succ

theorem map_full_shift (Γ : List (NFm n)) :
    (Γ.map NFm.shift).map NFm.full = (Γ.map NFm.full).map NFm.shift := by
  rw [List.map_map, List.map_map]
  exact List.map_congr_left fun A _ => full_shift A

end NFm

/-- A formula and its full normal form are interderivable in the kernel. -/
theorem equivFull (A : NFm n) : NEquiv A A.full := by
  induction A with
  | eq s t => exact NEquiv.eqs (NPrf.eqFull s) (NPrf.eqFull t)
  | Q B ih => exact NEquiv.Q ih
  | D B ih => exact NEquiv.D ih

end LeanProofs.ConciseIPRA
