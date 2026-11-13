import ConciseIPRA.TeqPred

/-!
# The equational calculus, and its terms modulo provable equality

`EqPrf Γ s t` is derivability of the equation `s = t` from a list `Γ` of
equations, by five rules and nothing else:

* `hyp`, a hypothesis;
* `iterZero`, `iterSucc`, the two computations of the iterator;
* `trOne`, transport along an equation in one term template;
* `ind`, induction for a literal equation with parameters: from `E(0)` and
  `E(z) ⊢ E(S z)` with `z` fresh infer `E(a)`.

There are no formulas other than equations, no coverage `x = 0 ∨ ∃y x = S y`,
no separation and no case rule.  The calculus is closed under substitution and
weakening (`EqPrf.substW`).

`EQ Γ` is the type of terms modulo `EqPrf Γ`, with the interface of
`Lindenbaum` for `T_eq`: operations that commute with substitution descend
(`EQ.op₁`, `EQ.op₂`, `EQ.op₃`), an extension of the context induces a map
(`EExt.map`), and `EQ.eqInd` is the induction rule with its hypothesis in the
extended context.  The commands `lift_eop₁` and `lift_eop₂` declare the
operation on classes for a term operation of the `T_eq` development.

The package `uniform_raw` and its companions observe that the predecessor of
`T_eq` needs no more than this calculus; `EqPred` carries that out.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open Tm (zero succ iter)

variable {n m : ℕ}

/-- A context of equations. -/
abbrev ECtx (n : ℕ) := List (Tm n × Tm n)

/-- Substitution in a context of equations. -/
def ECtx.subst (Γ : ECtx n) (σ : Fin n → Tm m) : ECtx m :=
  Γ.map fun p => (Syn.subst σ p.1, Syn.subst σ p.2)

/-- A context moved under a fresh variable. -/
def ECtx.shift (Γ : ECtx n) : ECtx (n + 1) := Γ.subst fun i => Syn.var i.succ

/-- Substitution commutes with instantiation of the first variable. -/
theorem Tm.subst_inst_comm (σ : Fin n → Tm m) (t : Tm n) (h : Tm (n + 1)) :
    Syn.subst σ (Syn.subst (inst t) h) = Syn.subst (inst (Syn.subst σ t)) (Syn.subst (up σ) h) := by
  rw [Syn.subst_subst, Syn.subst_subst, inst_comp_up]

theorem Tm.subst_repl_succ (s : Tm (n + 1)) (σ : Fin n → Tm m) :
    Syn.subst (up σ) (Syn.subst (repl (succ (Syn.var 0))) s)
      = Syn.subst (repl (succ (Syn.var 0))) (Syn.subst (up σ) s) := by
  rw [Syn.subst_subst, Syn.subst_subst]
  refine congrArg (fun ρ => Syn.subst ρ s) (funext (Fin.cases ?_ fun j => ?_))
  · simp
  · simp only [repl_succ, Syn.subst_var, up_succ, subst_repl_shift]

/-- Derivability of an equation from equations. -/
inductive EqPrf : {n : ℕ} → ECtx n → Tm n → Tm n → Prop
  | hyp {n : ℕ} {Γ : ECtx n} {s t : Tm n} (h : (s, t) ∈ Γ) : EqPrf Γ s t
  | iterZero {n : ℕ} {Γ : ECtx n} (a : Tm n) (h : Tm (n + 1)) : EqPrf Γ (iter zero a h) a
  | iterSucc {n : ℕ} {Γ : ECtx n} (c a : Tm n) (h : Tm (n + 1)) :
      EqPrf Γ (iter (succ c) a h) (Syn.subst (inst (iter c a h)) h)
  | trOne {n : ℕ} {Γ : ECtx n} (h : Tm (n + 1)) {s t u : Tm n} (h₁ : EqPrf Γ s t)
      (h₂ : EqPrf Γ (Syn.subst (inst s) h) u) : EqPrf Γ u (Syn.subst (inst t) h)
  | ind {n : ℕ} {Γ : ECtx n} (s t : Tm (n + 1)) (a : Tm n)
      (h0 : EqPrf Γ (Syn.subst (inst zero) s) (Syn.subst (inst zero) t))
      (hS : EqPrf ((s, t) :: Γ.shift) (Syn.subst (repl (succ (Syn.var 0))) s)
        (Syn.subst (repl (succ (Syn.var 0))) t)) :
      EqPrf Γ (Syn.subst (inst a) s) (Syn.subst (inst a) t)

namespace EqPrf

variable {Γ : ECtx n}

theorem hyp0 {s t : Tm n} : EqPrf ((s, t) :: Γ) s t := .hyp List.mem_cons_self

theorem eqRefl (t : Tm n) : EqPrf Γ t t :=
  .trOne (Syn.var 0) (.iterZero t (Syn.var 0)) (.iterZero t (Syn.var 0))

theorem eqSymm {s t : Tm n} (h : EqPrf Γ s t) : EqPrf Γ t s :=
  .trOne (Syn.var 0) (eqRefl s) h

theorem eqTrans {s t u : Tm n} (h₁ : EqPrf Γ s t) (h₂ : EqPrf Γ t u) : EqPrf Γ s u :=
  .trOne (Syn.var 0) h₂ (eqSymm h₁)

/-- Congruence for one variable. -/
theorem eqCongr1 (u : Tm (n + 1)) {s t : Tm n} (h : EqPrf Γ s t) :
    EqPrf Γ (Syn.subst (inst s) u) (Syn.subst (inst t) u) :=
  .trOne u h (eqRefl _)

/-- **Substitution and weakening**, in one induction. -/
theorem substW {s t : Tm n} (h : EqPrf Γ s t) : ∀ {m : ℕ} (σ : Fin n → Tm m) (Δ : ECtx m),
    (∀ p ∈ Γ.subst σ, p ∈ Δ) → EqPrf Δ (Syn.subst σ s) (Syn.subst σ t) := by
  induction h with intro m σ Δ R
  | hyp h => exact .hyp (R _ (List.mem_map_of_mem (f := fun p => (Syn.subst σ p.1, Syn.subst σ p.2)) h))
  | iterZero a h => rw [Tm.subst_iter]; exact .iterZero _ _
  | iterSucc c a h =>
    simp only [Tm.subst_iter, Tm.subst_succ, Tm.subst_inst_comm]
    exact .iterSucc _ _ _
  | trOne h _ _ ih₁ ih₂ =>
    have h₂ := ih₂ σ Δ R
    simp only [Tm.subst_inst_comm] at h₂ ⊢
    exact .trOne _ (ih₁ σ Δ R) h₂
  | @ind _ Γ s t a _ _ ih₀ ihS =>
    have h₀ := ih₀ σ Δ R
    have hS := ihS (up σ) ((Syn.subst (up σ) s, Syn.subst (up σ) t) :: Δ.shift) (by
      intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact List.mem_cons_self
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
        obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hq
        refine List.mem_cons_of_mem _ ?_
        show (Syn.subst (up σ) (Syn.shift r.1), Syn.subst (up σ) (Syn.shift r.2)) ∈ _
        rw [Syn.subst_up_shift, Syn.subst_up_shift]
        exact List.mem_map_of_mem (f := fun p : Tm m × Tm m => (Syn.shift p.1, Syn.shift p.2))
          (R _ (List.mem_map_of_mem (f := fun p => (Syn.subst σ p.1, Syn.subst σ p.2)) hr)))
    rw [Tm.subst_repl_succ, Tm.subst_repl_succ] at hS
    rw [Tm.subst_inst_comm, Tm.subst_inst_comm]
    rw [Tm.subst_inst_comm, Tm.subst_inst_comm] at h₀
    exact .ind _ _ _ h₀ hS

theorem congr₁ {f : ∀ k, Tm k → Tm k} (hf : Sub₁ f) {a a' : Tm n} (ha : EqPrf Γ a a') :
    EqPrf Γ (f n a) (f n a') := by
  have h := eqCongr1 (f (n + 1) (Syn.var 0)) ha
  simpa only [hf, Syn.subst_var, Syn.inst_zero] using h

theorem congr₂ {f : ∀ k, Tm k → Tm k → Tm k} (hf : Sub₂ f) {a a' b b' : Tm n}
    (ha : EqPrf Γ a a') (hb : EqPrf Γ b b') : EqPrf Γ (f n a b) (f n a' b') := by
  have h₁ := eqCongr1 (f (n + 1) (Syn.var 0) (Syn.shift b)) ha
  have h₂ := eqCongr1 (f (n + 1) (Syn.shift a') (Syn.var 0)) hb
  simp only [hf, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at h₁ h₂
  exact eqTrans h₁ h₂

theorem congr₃ {f : ∀ k, Tm k → Tm k → Tm k → Tm k} (hf : Sub₃ f) {a a' b b' c c' : Tm n}
    (ha : EqPrf Γ a a') (hb : EqPrf Γ b b') (hc : EqPrf Γ c c') :
    EqPrf Γ (f n a b c) (f n a' b' c') := by
  have h₁ := eqCongr1 (f (n + 1) (Syn.var 0) (Syn.shift b) (Syn.shift c)) ha
  have h₂ := eqCongr1 (f (n + 1) (Syn.shift a') (Syn.var 0) (Syn.shift c)) hb
  have h₃ := eqCongr1 (f (n + 1) (Syn.shift a') (Syn.shift b') (Syn.var 0)) hc
  simp only [hf, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at h₁ h₂ h₃
  exact eqTrans (eqTrans h₁ h₂) h₃

/-- Congruence of the iterator in its count and its seed. -/
theorem iterCongr (h : Tm (n + 1)) {c c' a a' : Tm n} (hc : EqPrf Γ c c') (ha : EqPrf Γ a a') :
    EqPrf Γ (iter c a h) (iter c' a' h) := by
  have h₁ := eqCongr1
    (iter (Syn.var 0) (Syn.shift a) (Syn.subst (up (fun i => Syn.var i.succ)) h)) hc
  have h₂ := eqCongr1
    (iter (Syn.shift c') (Syn.var 0) (Syn.subst (up (fun i => Syn.var i.succ)) h)) ha
  simp only [Tm.subst_iter, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    Syn.subst_up_inst_up_shift] at h₁ h₂
  exact eqTrans h₁ h₂

end EqPrf

/-- Provable equality of terms in a context of equations. -/
def eqSetoid (Γ : ECtx n) : Setoid (Tm n) where
  r a b := EqPrf Γ a b
  iseqv := ⟨fun a => EqPrf.eqRefl a, fun h => EqPrf.eqSymm h,
    fun h₁ h₂ => EqPrf.eqTrans h₁ h₂⟩

/-- Terms modulo provable equality in the context `Γ`. -/
def EQ (Γ : ECtx n) : Type := Quotient (eqSetoid Γ)

/-- A substitution sending the hypotheses of `Γ` into `Γ'`. -/
structure EExt (Γ : ECtx n) (Γ' : ECtx m) where
  /-- The underlying substitution. -/
  σ : Fin n → Tm m
  sub : ∀ p ∈ Γ.subst σ, p ∈ Γ'

namespace EQ

variable {Γ : ECtx n} {Γ' : ECtx m}

/-- The class of a term. -/
def mk (Γ : ECtx n) (a : Tm n) : EQ Γ := Quotient.mk (eqSetoid Γ) a

theorem sound {a b : Tm n} (h : EqPrf Γ a b) : mk Γ a = mk Γ b := Quotient.sound h

theorem exact {a b : Tm n} (h : mk Γ a = mk Γ b) : EqPrf Γ a b := Quotient.exact h

theorem ind {p : EQ Γ → Prop} (h : ∀ a, p (mk Γ a)) (x : EQ Γ) : p x := Quotient.ind h x

theorem ind₂ {p : EQ Γ → EQ Γ → Prop} (h : ∀ a b, p (mk Γ a) (mk Γ b)) (x y : EQ Γ) : p x y :=
  Quotient.inductionOn₂ x y h

theorem ind₃ {p : EQ Γ → EQ Γ → EQ Γ → Prop} (h : ∀ a b c, p (mk Γ a) (mk Γ b) (mk Γ c))
    (x y z : EQ Γ) : p x y z :=
  Quotient.inductionOn₃ x y z h

theorem hyp0 {a b : Tm n} : mk ((a, b) :: Γ) a = mk ((a, b) :: Γ) b := sound EqPrf.hyp0

/-- A unary operation on classes. -/
def op₁ (f : ∀ k, Tm k → Tm k) (hf : Sub₁ f) : EQ Γ → EQ Γ :=
  Quotient.lift (fun a => mk Γ (f n a)) (fun _ _ h => sound (EqPrf.congr₁ hf h))

/-- A binary operation on classes. -/
def op₂ (f : ∀ k, Tm k → Tm k → Tm k) (hf : Sub₂ f) : EQ Γ → EQ Γ → EQ Γ :=
  Quotient.lift₂ (fun a b => mk Γ (f n a b))
    (fun _ _ _ _ ha hb => sound (EqPrf.congr₂ hf ha hb))

/-- A ternary operation on classes. -/
def op₃ (f : ∀ k, Tm k → Tm k → Tm k → Tm k) (hf : Sub₃ f) (x y z : EQ Γ) : EQ Γ :=
  Quotient.lift
    (fun a => Quotient.lift₂ (fun b c => mk Γ (f n a b c))
      (fun _ _ _ _ hb hc => sound (EqPrf.congr₃ hf (EqPrf.eqRefl _) hb hc)) y z)
    (fun _ _ ha => Quotient.inductionOn₂ y z (fun b c =>
      sound (EqPrf.congr₃ hf ha (EqPrf.eqRefl b) (EqPrf.eqRefl c)))) x

instance : Zero (EQ Γ) := ⟨mk Γ Tm.zero⟩

instance : One (EQ Γ) := ⟨mk Γ Tm.one⟩

/-- Successor on classes. -/
def succ : EQ Γ → EQ Γ := op₁ (fun _ => Tm.succ) (fun _ _ => rfl)

@[simp] theorem mk_zero : mk Γ Tm.zero = 0 := rfl

@[simp] theorem mk_one : mk Γ Tm.one = 1 := rfl

@[simp] theorem mk_succ (a : Tm n) : mk Γ (Tm.succ a) = succ (mk Γ a) := rfl

theorem one_eq : (1 : EQ Γ) = succ 0 := rfl

/-- Induction for a literal equation, with the induction hypothesis available
in the extended context.  The base and the step are found by `simp` when they
are not given. -/
theorem eqInd (s t : Tm (n + 1)) (a : Tm n)
    (h0 : mk Γ (Syn.subst (inst Tm.zero) s) = mk Γ (Syn.subst (inst Tm.zero) t) := by simp)
    (hS : mk ((s, t) :: Γ.shift) s = mk ((s, t) :: Γ.shift) t →
      mk ((s, t) :: Γ.shift) (Syn.subst (repl (Tm.succ (Syn.var 0))) s)
        = mk ((s, t) :: Γ.shift) (Syn.subst (repl (Tm.succ (Syn.var 0))) t) := by
      intro ih; simp at ih; simp [ih]) :
    mk Γ (Syn.subst (inst a) s) = mk Γ (Syn.subst (inst a) t) :=
  sound (.ind s t a (exact h0) (exact (hS hyp0)))

end EQ

namespace EExt

variable {Γ : ECtx n} {Γ' : ECtx m}

/-- The map of classes induced by an extension. -/
def map (e : EExt Γ Γ') : EQ Γ → EQ Γ' :=
  Quotient.lift (fun a => EQ.mk Γ' (Syn.subst e.σ a))
    (fun _ _ h => EQ.sound (h.substW e.σ Γ' e.sub))

@[simp] theorem map_zero (e : EExt Γ Γ') : e.map 0 = 0 := rfl

@[simp] theorem map_one (e : EExt Γ Γ') : e.map 1 = 1 := rfl

theorem map_op₁ (e : EExt Γ Γ') (f : ∀ k, Tm k → Tm k) (hf : Sub₁ f) (x : EQ Γ) :
    e.map (EQ.op₁ f hf x) = EQ.op₁ f hf (e.map x) := by
  induction x using EQ.ind with | _ a => exact congrArg (EQ.mk Γ') (hf e.σ a)

theorem map_op₂ (e : EExt Γ Γ') (f : ∀ k, Tm k → Tm k → Tm k) (hf : Sub₂ f) (x y : EQ Γ) :
    e.map (EQ.op₂ f hf x y) = EQ.op₂ f hf (e.map x) (e.map y) := by
  induction x, y using EQ.ind₂ with | _ a b => exact congrArg (EQ.mk Γ') (hf e.σ a b)

theorem map_op₃ (e : EExt Γ Γ') (f : ∀ k, Tm k → Tm k → Tm k → Tm k) (hf : Sub₃ f)
    (x y z : EQ Γ) : e.map (EQ.op₃ f hf x y z) = EQ.op₃ f hf (e.map x) (e.map y) (e.map z) := by
  induction x, y, z using EQ.ind₃ with | _ a b c => exact congrArg (EQ.mk Γ') (hf e.σ a b c)

@[simp] theorem map_succ (e : EExt Γ Γ') (x : EQ Γ) : e.map (EQ.succ x) = EQ.succ (e.map x) :=
  map_op₁ e (fun _ => Tm.succ) (fun _ _ => rfl) x

end EExt

/-! ## Lifting the term operations of the `T_eq` development -/

open Lean in
/-- The three declarations made for one lifted operation; the term operation
`Tm.f` and the lemma `Tm.subst_f` are those of the `T_eq` development. -/
def liftEOp (op mapOp : Ident) (as xs : Array Ident) (f : Ident) : MacroM (Array Syntax) := do
  let s := f.getId.toString
  let tmF := mkIdent (.str `Tm s)
  let sub := mkIdent (.str `Tm ("subst_" ++ s))
  let qF := mkIdent (.str `EQ s)
  let mkF := mkIdent (.str `EQ ("mk_" ++ s))
  let mapF := mkIdent (.str `EExt ("map_" ++ s))
  let ma ← as.mapM fun a => `(EQ.mk Γ $a)
  let mx ← xs.mapM fun x => `(e.map $x)
  return #[
    ← `(def $qF {n : ℕ} {Γ : ECtx n} := $op (Γ := Γ) (fun _ => $tmF) $sub),
    ← `(@[simp] theorem $mkF {n : ℕ} {Γ : ECtx n} ($as* : Tm n) :
      EQ.mk Γ ($tmF $as*) = $qF $ma* := rfl),
    ← `(@[simp] theorem $mapF {n m : ℕ} {Γ : ECtx n} {Γ' : ECtx m}
      (e : EExt Γ Γ') ($xs* : EQ Γ) : e.map ($qF $xs*) = $qF $mx* :=
      $mapOp e (fun _ => $tmF) $sub $xs*)]

open Lean in
/-- `lift_eop₁ f g …`: declare the operation `EQ.f` on classes for each unary
term operation `Tm.f`, with the simp lemmas `EQ.mk_f` and `EExt.map_f`. -/
macro "lift_eop₁ " fs:ident+ : command => do
  let mut cmds : Array Syntax := #[]
  for f in fs do
    cmds := cmds ++ (← liftEOp (mkIdent ``EQ.op₁) (mkIdent ``EExt.map_op₁) #[mkIdent `a]
      #[mkIdent `x] f)
  return ⟨mkNullNode cmds⟩

open Lean in
/-- `lift_eop₂ f g …`: the binary form of `lift_eop₁`. -/
macro "lift_eop₂ " fs:ident+ : command => do
  let mut cmds : Array Syntax := #[]
  for f in fs do
    cmds := cmds ++ (← liftEOp (mkIdent ``EQ.op₂) (mkIdent ``EExt.map_op₂)
      #[mkIdent `a, mkIdent `b] #[mkIdent `x, mkIdent `y] f)
  return ⟨mkNullNode cmds⟩

end LeanProofs.ConciseIPRA
