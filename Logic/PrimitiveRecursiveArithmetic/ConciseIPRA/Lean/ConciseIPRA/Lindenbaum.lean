import ConciseIPRA.Scalar

/-!
# Terms of `T_eq` modulo provable equality

For a context `Γ`, the type `Q Γ` is the type of terms modulo the relation
`Γ ⊢ a ≐ b` of `T_eq`.  A derivation of an equation is then an equation of
Lean, so the equational reasoning inside `T_eq` can be carried out by
rewriting.

* Every operation on terms that commutes with substitution descends to `Q Γ`
  (`Q.op₁`, `Q.op₂`, `Q.op₃`); congruence follows from the Leibniz rule.
* An extension `Ext Γ Γ'` is a substitution that sends the hypotheses of `Γ`
  into `Γ'`.  It induces a map `Q Γ → Q Γ'` commuting with these operations.
* `Q.eqInd` is induction for literal equations, and `Q.cases` is proof of an
  equation by cases on a number, stated over all extensions of the context.
* The commands `lift_op₁` and `lift_op₂` declare the operation on classes
  induced by a term operation, with its two compatibility lemmas.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm

namespace Syn

variable {T : ℕ → Type} [Syn T] {n m : ℕ}

theorem subst_up_shift (σ : Fin n → T m) (t : T n) :
    subst (up σ) (shift t) = shift (subst σ t) := by
  rw [subst_shift, shift_subst]; simp

@[simp] theorem subst_repl_shift (s : T (n + 1)) (t : T n) :
    subst (repl s) (shift t) = shift t := by
  rw [subst_shift]; simp [shift]

/-- Weakening under a binder followed by instantiation of the new variable. -/
theorem subst_up_inst_up_shift (c : T n) (h : T (n + 1)) :
    subst (up (inst c)) (subst (up (fun i => var i.succ)) h) = h := by
  have e : (fun i : Fin n => subst (inst c) (var i.succ : T (n + 1))) = var := by
    funext i; simp
  rw [subst_subst, up_comp, e, up_var, subst_id]

end Syn

variable {n m : ℕ}

/-- Operations on terms that commute with substitution. -/
abbrev Sub₁ (f : ∀ k, Tm k → Tm k) : Prop :=
  ∀ {k k' : ℕ} (σ : Fin k → Tm k') (a : Tm k), Syn.subst σ (f k a) = f k' (Syn.subst σ a)

/-- Binary operations on terms that commute with substitution. -/
abbrev Sub₂ (f : ∀ k, Tm k → Tm k → Tm k) : Prop :=
  ∀ {k k' : ℕ} (σ : Fin k → Tm k') (a b : Tm k),
    Syn.subst σ (f k a b) = f k' (Syn.subst σ a) (Syn.subst σ b)

/-- Ternary operations on terms that commute with substitution. -/
abbrev Sub₃ (f : ∀ k, Tm k → Tm k → Tm k → Tm k) : Prop :=
  ∀ {k k' : ℕ} (σ : Fin k → Tm k') (a b c : Tm k),
    Syn.subst σ (f k a b c) = f k' (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ c)

namespace Teq

variable {Γ : List (Fm Tm n)}

theorem congr₁ {f : ∀ k, Tm k → Tm k} (hf : Sub₁ f) {a a' : Tm n}
    (ha : Γ ⊢[TeqAx] a ≐ a') : Γ ⊢[TeqAx] f n a ≐ f n a' := by
  simpa only [hf, Syn.subst_var, Syn.inst_zero] using Prf.eqCongr1 (f (n + 1) (var 0)) ha

theorem congr₂ {f : ∀ k, Tm k → Tm k → Tm k} (hf : Sub₂ f) {a a' b b' : Tm n}
    (ha : Γ ⊢[TeqAx] a ≐ a') (hb : Γ ⊢[TeqAx] b ≐ b') :
    Γ ⊢[TeqAx] f n a b ≐ f n a' b' := by
  have h₁ := Prf.eqCongr1 (f (n + 1) (var 0) (shift b)) ha
  have h₂ := Prf.eqCongr1 (f (n + 1) (shift a') (var 0)) hb
  simp only [hf, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at h₁ h₂
  exact Prf.eqTrans h₁ h₂

theorem congr₃ {f : ∀ k, Tm k → Tm k → Tm k → Tm k} (hf : Sub₃ f) {a a' b b' c c' : Tm n}
    (ha : Γ ⊢[TeqAx] a ≐ a') (hb : Γ ⊢[TeqAx] b ≐ b') (hc : Γ ⊢[TeqAx] c ≐ c') :
    Γ ⊢[TeqAx] f n a b c ≐ f n a' b' c' := by
  have h₁ := Prf.eqCongr1 (f (n + 1) (var 0) (shift b) (shift c)) ha
  have h₂ := Prf.eqCongr1 (f (n + 1) (shift a') (var 0) (shift c)) hb
  have h₃ := Prf.eqCongr1 (f (n + 1) (shift a') (shift b') (var 0)) hc
  simp only [hf, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at h₁ h₂ h₃
  exact Prf.eqTrans (Prf.eqTrans h₁ h₂) h₃

/-- Congruence of the iterator in its count and its seed. -/
theorem iterCongr (h : Tm (n + 1)) {c c' a a' : Tm n}
    (hc : Γ ⊢[TeqAx] c ≐ c') (ha : Γ ⊢[TeqAx] a ≐ a') :
    Γ ⊢[TeqAx] Tm.iter c a h ≐ Tm.iter c' a' h := by
  have h₁ := Prf.eqCongr1
    (Tm.iter (var 0) (shift a) (Syn.subst (up (fun i => var i.succ)) h)) hc
  have h₂ := Prf.eqCongr1
    (Tm.iter (shift c') (var 0) (Syn.subst (up (fun i => var i.succ)) h)) ha
  simp only [Tm.subst_iter, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    Syn.subst_up_inst_up_shift] at h₁ h₂
  exact Prf.eqTrans h₁ h₂

end Teq

/-- Provable equality of terms in a context. -/
def teqSetoid (Γ : List (Fm Tm n)) : Setoid (Tm n) where
  r a b := Γ ⊢[TeqAx] a ≐ b
  iseqv := ⟨fun a => Prf.eqRefl a, fun h => Prf.eqSymm h, fun h₁ h₂ => Prf.eqTrans h₁ h₂⟩

/-- Terms modulo provable equality in the context `Γ`. -/
def Q (Γ : List (Fm Tm n)) : Type := Quotient (teqSetoid Γ)

/-- A substitution sending the hypotheses of `Γ` into `Γ'`. -/
structure Ext (Γ : List (Fm Tm n)) (Γ' : List (Fm Tm m)) where
  /-- The underlying substitution. -/
  σ : Fin n → Tm m
  sub : ∀ φ ∈ Γ, φ.subst σ ∈ Γ'

namespace Q

variable {Γ : List (Fm Tm n)} {Γ' : List (Fm Tm m)}

/-- The class of a term. -/
def mk (Γ : List (Fm Tm n)) (a : Tm n) : Q Γ := Quotient.mk (teqSetoid Γ) a

theorem sound {a b : Tm n} (h : Γ ⊢[TeqAx] a ≐ b) : mk Γ a = mk Γ b := Quotient.sound h

theorem exact {a b : Tm n} (h : mk Γ a = mk Γ b) : Γ ⊢[TeqAx] a ≐ b := Quotient.exact h

theorem ind {p : Q Γ → Prop} (h : ∀ a, p (mk Γ a)) (x : Q Γ) : p x := Quotient.ind h x

theorem ind₂ {p : Q Γ → Q Γ → Prop} (h : ∀ a b, p (mk Γ a) (mk Γ b)) (x y : Q Γ) : p x y :=
  Quotient.inductionOn₂ x y h

theorem ind₃ {p : Q Γ → Q Γ → Q Γ → Prop} (h : ∀ a b c, p (mk Γ a) (mk Γ b) (mk Γ c))
    (x y z : Q Γ) : p x y z :=
  Quotient.inductionOn₃ x y z h

theorem hyp0 {a b : Tm n} : mk ((a ≐ b) :: Γ) a = mk ((a ≐ b) :: Γ) b := sound Prf.hyp0

/-- A unary operation on classes. -/
def op₁ (f : ∀ k, Tm k → Tm k) (hf : Sub₁ f) : Q Γ → Q Γ :=
  Quotient.lift (fun a => mk Γ (f n a)) (fun _ _ h => sound (Teq.congr₁ hf h))

/-- A binary operation on classes. -/
def op₂ (f : ∀ k, Tm k → Tm k → Tm k) (hf : Sub₂ f) : Q Γ → Q Γ → Q Γ :=
  Quotient.lift₂ (fun a b => mk Γ (f n a b))
    (fun _ _ _ _ ha hb => sound (Teq.congr₂ hf ha hb))

/-- A ternary operation on classes. -/
def op₃ (f : ∀ k, Tm k → Tm k → Tm k → Tm k) (hf : Sub₃ f) (x y z : Q Γ) : Q Γ :=
  Quotient.lift
    (fun a => Quotient.lift₂ (fun b c => mk Γ (f n a b c))
      (fun _ _ _ _ hb hc => sound (Teq.congr₃ hf (Prf.eqRefl _) hb hc)) y z)
    (fun _ _ ha => Quotient.inductionOn₂ y z (fun b c =>
      sound (Teq.congr₃ hf ha (Prf.eqRefl b) (Prf.eqRefl c)))) x

instance : Zero (Q Γ) := ⟨mk Γ Tm.zero⟩

instance : One (Q Γ) := ⟨mk Γ Tm.one⟩

/-- Successor on classes. -/
def succ : Q Γ → Q Γ := op₁ (fun _ => Tm.succ) (fun _ _ => rfl)

@[simp] theorem mk_zero : mk Γ Tm.zero = 0 := rfl

@[simp] theorem mk_one : mk Γ Tm.one = 1 := rfl

@[simp] theorem mk_succ (a : Tm n) : mk Γ (Tm.succ a) = succ (mk Γ a) := rfl

theorem one_eq : (1 : Q Γ) = succ 0 := rfl

/-- The iterator with a fixed step term. -/
def iterate (h : Tm (n + 1)) : Q Γ → Q Γ → Q Γ :=
  Quotient.lift₂ (fun c a => mk Γ (Tm.iter c a h))
    (fun _ _ _ _ hc ha => sound (Teq.iterCongr h hc ha))

/-- Instantiation of a step term. -/
def app (h : Tm (n + 1)) : Q Γ → Q Γ :=
  Quotient.lift (fun a => mk Γ (Syn.subst (inst a) h)) (fun _ _ e => sound (Prf.eqCongr1 h e))

theorem mk_iter (c a : Tm n) (h : Tm (n + 1)) :
    mk Γ (Tm.iter c a h) = iterate h (mk Γ c) (mk Γ a) := rfl

theorem app_mk (h : Tm (n + 1)) (a : Tm n) : app h (mk Γ a) = mk Γ (Syn.subst (inst a) h) := rfl

@[simp] theorem iterate_zero (h : Tm (n + 1)) (x : Q Γ) : iterate h 0 x = x := by
  induction x using Q.ind with | _ a => exact sound (Teq.iterZero a h)

@[simp] theorem iterate_succ (h : Tm (n + 1)) (c x : Q Γ) :
    iterate h (succ c) x = app h (iterate h c x) := by
  induction c, x using Q.ind₂ with | _ c a => exact sound (Teq.iterSucc c a h)

/-- If `0 = 1` then all classes coincide. -/
theorem absurd (h : (0 : Q Γ) = 1) (x y : Q Γ) : x = y := by
  induction x, y using Q.ind₂ with | _ a b => exact sound (.botE _ (.impE Teq.sep (exact h)))

/-- Induction for a literal equation, with the induction hypothesis available
in the extended context.  The base and the step are found by `simp` when they
are not given. -/
theorem eqInd (s t : Tm (n + 1)) (a : Tm n)
    (h0 : mk Γ (Syn.subst (inst Tm.zero) s) = mk Γ (Syn.subst (inst Tm.zero) t) := by simp)
    (hS : mk ((s ≐ t) :: Γ.map Fm.shift) s = mk ((s ≐ t) :: Γ.map Fm.shift) t →
      mk ((s ≐ t) :: Γ.map Fm.shift) (Syn.subst (repl (Tm.succ (var 0))) s)
        = mk ((s ≐ t) :: Γ.map Fm.shift) (Syn.subst (repl (Tm.succ (var 0))) t) := by
      intro ih; simp at ih; simp [ih]) :
    mk Γ (Syn.subst (inst a) s) = mk Γ (Syn.subst (inst a) t) :=
  sound (Prf.allE a (Teq.eqInd s t (exact h0) (exact (hS hyp0))))

end Q

namespace Ext

variable {Γ : List (Fm Tm n)} {Γ' : List (Fm Tm m)}

theorem prf (e : Ext Γ Γ') {φ : Fm Tm n} (h : Γ ⊢[TeqAx] φ) : Γ' ⊢[TeqAx] φ.subst e.σ :=
  h.substWeaken e.σ (List.forall_mem_map.2 e.sub)

/-- The map of classes induced by an extension. -/
def map (e : Ext Γ Γ') : Q Γ → Q Γ' :=
  Quotient.lift (fun a => Q.mk Γ' (Syn.subst e.σ a)) (fun _ _ h => Q.sound (e.prf h))

@[simp] theorem map_zero (e : Ext Γ Γ') : e.map 0 = 0 := rfl

@[simp] theorem map_one (e : Ext Γ Γ') : e.map 1 = 1 := rfl

theorem map_op₁ (e : Ext Γ Γ') (f : ∀ k, Tm k → Tm k) (hf : Sub₁ f) (x : Q Γ) :
    e.map (Q.op₁ f hf x) = Q.op₁ f hf (e.map x) := by
  induction x using Q.ind with | _ a => exact congrArg (Q.mk Γ') (hf e.σ a)

theorem map_op₂ (e : Ext Γ Γ') (f : ∀ k, Tm k → Tm k → Tm k) (hf : Sub₂ f) (x y : Q Γ) :
    e.map (Q.op₂ f hf x y) = Q.op₂ f hf (e.map x) (e.map y) := by
  induction x, y using Q.ind₂ with | _ a b => exact congrArg (Q.mk Γ') (hf e.σ a b)

theorem map_op₃ (e : Ext Γ Γ') (f : ∀ k, Tm k → Tm k → Tm k → Tm k) (hf : Sub₃ f)
    (x y z : Q Γ) : e.map (Q.op₃ f hf x y z) = Q.op₃ f hf (e.map x) (e.map y) (e.map z) := by
  induction x, y, z using Q.ind₃ with | _ a b c => exact congrArg (Q.mk Γ') (hf e.σ a b c)

@[simp] theorem map_succ (e : Ext Γ Γ') (x : Q Γ) : e.map (Q.succ x) = Q.succ (e.map x) :=
  map_op₁ e (fun _ => Tm.succ) (fun _ _ => rfl) x

/-- Adding a hypothesis. -/
def wk (ψ : Fm Tm n) : Ext Γ (ψ :: Γ) where
  σ := var
  sub φ h := by rw [Fm.subst_id]; exact List.mem_cons_of_mem _ h

/-- Adding a variable and then a hypothesis. -/
def shiftCons (ψ : Fm Tm (n + 1)) : Ext Γ (ψ :: Γ.map Fm.shift) where
  σ := fun i => var i.succ
  sub _ h := List.mem_cons_of_mem _ (List.mem_map_of_mem (f := Fm.shift) h)

theorem wk_map_mk (ψ : Fm Tm n) (a : Tm n) :
    (wk ψ : Ext Γ (ψ :: Γ)).map (Q.mk Γ a) = Q.mk (ψ :: Γ) a :=
  congrArg (Q.mk (ψ :: Γ)) (Syn.subst_id a)

end Ext

namespace Q

variable {Γ : List (Fm Tm n)}

/-- Proof of an equation by cases on a term, by coverage. -/
theorem casesTm (a : Tm n) {s t : Tm n}
    (h0 : mk ((a ≐ Tm.zero) :: Γ) s = mk ((a ≐ Tm.zero) :: Γ) t)
    (hS : mk ((shift a ≐ Tm.succ (var 0)) :: Γ.map Fm.shift) (shift s)
      = mk ((shift a ≐ Tm.succ (var 0)) :: Γ.map Fm.shift) (shift t)) :
    mk Γ s = mk Γ t :=
  sound (Teq.casesOn a (exact h0) (exact hS))

/-- Proof of an equation by cases on a number: it is `0` or a successor in an
extension of the context. -/
theorem cases (x : Q Γ) {p q : Q Γ}
    (h0 : ∀ {m : ℕ} {Γ' : List (Fm Tm m)} (e : Ext Γ Γ'), e.map x = 0 → e.map p = e.map q)
    (hS : ∀ {m : ℕ} {Γ' : List (Fm Tm m)} (e : Ext Γ Γ') (z : Q Γ'),
      e.map x = succ z → e.map p = e.map q) : p = q := by
  induction x, p, q using Q.ind₃ with | _ a s t
  refine casesTm a ?_ ?_
  · have h := h0 (Ext.wk (a ≐ Tm.zero)) (by rw [Ext.wk_map_mk]; exact hyp0)
    rwa [Ext.wk_map_mk, Ext.wk_map_mk] at h
  · exact hS (Ext.shiftCons _) (mk _ (var 0)) hyp0

end Q

/-! ## Lifting term operations to classes

Every term operation `Tm.f` defined from the iterator commutes with
substitution (`Tm.subst_f`) and so induces an operation `Q.f` on classes, with
a lemma `Q.mk_f` for the class of `Tm.f a` and a lemma `Ext.map_f` for
extensions of the context.  The commands `lift_op₁` and `lift_op₂` prove the
first and declare the other three, for unary and binary operations. -/

open Lean in
/-- The four declarations made for one lifted operation: `op` and `mapOp` are the lifting
and its compatibility with extensions, `as` the term variables and `xs` the class variables. -/
def liftOp (op mapOp : Ident) (as xs : Array Ident) (f : Ident) : MacroM (Array Syntax) := do
  let s := f.getId.toString
  let tmF := mkIdent (.str `Tm s)
  let sub := mkIdent (.str `Tm ("subst_" ++ s))
  let qF := mkIdent (.str `Q s)
  let mkF := mkIdent (.str `Q ("mk_" ++ s))
  let mapF := mkIdent (.str `Ext ("map_" ++ s))
  let sa ← as.mapM fun a => `(Syn.subst σ $a)
  let ma ← as.mapM fun a => `(Q.mk Γ $a)
  let mx ← xs.mapM fun x => `(e.map $x)
  return #[
    ← `(@[simp] theorem $sub {n m : ℕ} (σ : Fin n → Tm m) ($as* : Tm n) :
      Syn.subst σ ($tmF $as*) = $tmF $sa* := by
      first | (simp [$tmF:ident]; done) | simp [$tmF:ident, Syn.subst_up_shift]),
    ← `(def $qF {n : ℕ} {Γ : List (Fm Tm n)} := $op (Γ := Γ) (fun _ => $tmF) $sub),
    ← `(@[simp] theorem $mkF {n : ℕ} {Γ : List (Fm Tm n)} ($as* : Tm n) :
      Q.mk Γ ($tmF $as*) = $qF $ma* := rfl),
    ← `(@[simp] theorem $mapF {n m : ℕ} {Γ : List (Fm Tm n)} {Γ' : List (Fm Tm m)}
      (e : Ext Γ Γ') ($xs* : Q Γ) : e.map ($qF $xs*) = $qF $mx* :=
      $mapOp e (fun _ => $tmF) $sub $xs*)]

open Lean in
/-- `lift_op₁ f g …`: for each unary term operation `Tm.f`, prove that it commutes with
substitution (`Tm.subst_f`), and declare the operation `Q.f` on classes with the simp lemmas
`Q.mk_f` and `Ext.map_f`. -/
macro "lift_op₁ " fs:ident+ : command => do
  let mut cmds : Array Syntax := #[]
  for f in fs do
    cmds := cmds ++ (← liftOp (mkIdent ``Q.op₁) (mkIdent ``Ext.map_op₁) #[mkIdent `a]
      #[mkIdent `x] f)
  return ⟨mkNullNode cmds⟩

open Lean in
/-- `lift_op₂ f g …`: the binary form of `lift_op₁`. -/
macro "lift_op₂ " fs:ident+ : command => do
  let mut cmds : Array Syntax := #[]
  for f in fs do
    cmds := cmds ++ (← liftOp (mkIdent ``Q.op₂) (mkIdent ``Ext.map_op₂)
      #[mkIdent `a, mkIdent `b] #[mkIdent `x, mkIdent `y] f)
  return ⟨mkNullNode cmds⟩

end LeanProofs.ConciseIPRA
