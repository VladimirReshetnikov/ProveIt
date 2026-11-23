import Std

/-!
Finite Boolean semantics with de Bruijn indices. The language has constants,
unary and binary functions, relation atoms of arbitrary finite arity, equality,
and all first-order connectives. Every model uses an explicit finite carrier.
No classical decision procedure is used.
-/
namespace FirstOrderPacket.Substitution

inductive Term (k : Nat) where
  | var (i : Fin k)
  | const (symbol : Nat)
  | unary (symbol : Nat) (a : Term k)
  | binary (symbol : Nat) (a b : Term k)

inductive Formula : Nat → Type where
  | bot {k} : Formula k
  | eqv {k} (a b : Term k) : Formula k
  | rel {k} (symbol : Nat) (args : List (Term k)) : Formula k
  | conj {k} (a b : Formula k) : Formula k
  | disj {k} (a b : Formula k) : Formula k
  | impl {k} (a b : Formula k) : Formula k
  | all {k} (a : Formula (k + 1)) : Formula k
  | ex {k} (a : Formula (k + 1)) : Formula k

structure Model (n : Nat) where
  const : Nat → Fin n
  unary : Nat → Fin n → Fin n
  binary : Nat → Fin n → Fin n → Fin n
  rel : Nat → List (Fin n) → Bool

abbrev Env (n k : Nat) := Fin k → Fin n
abbrev Sub (k l : Nat) := Fin k → Term l

def extend {n k} (x : Fin n) (e : Env n k) : Env n (k + 1) :=
  Fin.cases x e

namespace Term

def rename {k l} (f : Fin k → Fin l) : Term k → Term l
  | .var i => .var (f i)
  | .const c => .const c
  | .unary s a => .unary s (rename f a)
  | .binary s a b => .binary s (rename f a) (rename f b)

def subst {k l} (σ : Sub k l) : Term k → Term l
  | .var i => σ i
  | .const c => .const c
  | .unary s a => .unary s (subst σ a)
  | .binary s a b => .binary s (subst σ a) (subst σ b)

def eval {n k} (m : Model n) (e : Env n k) : Term k → Fin n
  | .var i => e i
  | .const c => m.const c
  | .unary s a => m.unary s (eval m e a)
  | .binary s a b => m.binary s (eval m e a) (eval m e b)

theorem evalRename {n k l} (m : Model n) (e : Env n l) (d : Env n k)
    (f : Fin k → Fin l) (h : ∀ i, e (f i) = d i) (a : Term k) :
    eval m e (rename f a) = eval m d a := by
  induction a <;> simp_all [rename, eval]

theorem evalSubst {n k l} (m : Model n) (e : Env n l) (d : Env n k)
    (σ : Sub k l) (h : ∀ i, eval m e (σ i) = d i) (a : Term k) :
    eval m e (subst σ a) = eval m d a := by
  induction a <;> simp_all [subst, eval]

def free {k} : Term k → Fin k → Prop
  | .var j, i => i = j
  | .const _, _ => False
  | .unary _ a, i => free a i
  | .binary _ a b, i => free a i ∨ free b i

theorem coincidence {n k} (m : Model n) (e d : Env n k) (a : Term k)
    (h : ∀ i, free a i → e i = d i) : eval m e a = eval m d a := by
  induction a with
  | var i => exact h i rfl
  | const _ => rfl
  | unary _ _ ih => simp only [eval, ih h]
  | binary _ _ _ ia ib =>
    simp only [eval, ia (fun i hi => h i (Or.inl hi)), ib (fun i hi => h i (Or.inr hi))]

theorem substIdOf {k} (σ : Sub k k) (h : ∀ i, σ i = .var i) (a : Term k) :
    subst σ a = a := by
  induction a <;> simp_all [subst]

end Term

def lift {k l} (σ : Sub k l) : Sub (k + 1) (l + 1) :=
  Fin.cases (.var 0) (fun i => Term.rename Fin.succ (σ i))

theorem evalLift {n k l} (m : Model n) (e : Env n l) (d : Env n k)
    (σ : Sub k l) (h : ∀ i, Term.eval m e (σ i) = d i) (x : Fin n) :
    ∀ j, Term.eval m (extend x e) (lift σ j) = extend x d j := by
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · rfl
  · change Term.eval m (extend x e) (Term.rename Fin.succ (σ i)) = d i
    exact (Term.evalRename m (extend x e) e Fin.succ (fun _ => rfl) (σ i)).trans (h i)

private theorem mapAgree {α β : Type} (xs : List α) (p q : α → β)
    (h : ∀ z ∈ xs, p z = q z) : xs.map p = xs.map q := by
  induction xs with
  | nil => rfl
  | cons z zs ih =>
    simp only [List.map_cons]
    rw [h z (by simp), ih (fun t ht => h t (by simp [ht]))]

private theorem mapIdDirect {α : Type} (xs : List α) : xs.map id = xs := by
  induction xs with
  | nil => rfl
  | cons z zs ih => exact congrArg (List.cons z) ih

private theorem anyAgree {α : Type} (xs : List α) (p q : α → Bool)
    (h : ∀ z, p z = q z) : xs.any p = xs.any q := by
  induction xs with
  | nil => rfl
  | cons z zs ih => simp only [List.any_cons, h z, ih]

private theorem allAgree {α : Type} (xs : List α) (p q : α → Bool)
    (h : ∀ z, p z = q z) : xs.all p = xs.all q := by
  induction xs with
  | nil => rfl
  | cons z zs ih => simp only [List.all_cons, h z, ih]

namespace Formula

def subst {k l} (σ : Sub k l) : Formula k → Formula l
  | .bot => .bot
  | .eqv a b => .eqv (Term.subst σ a) (Term.subst σ b)
  | .rel s args => .rel s (args.map (Term.subst σ))
  | .conj a b => .conj (subst σ a) (subst σ b)
  | .disj a b => .disj (subst σ a) (subst σ b)
  | .impl a b => .impl (subst σ a) (subst σ b)
  | .all a => .all (subst (lift σ) a)
  | .ex a => .ex (subst (lift σ) a)

def truth {n k} (m : Model n) (e : Env n k) : Formula k → Bool
  | .bot => false
  | .eqv a b => decide (Term.eval m e a = Term.eval m e b)
  | .rel s args => m.rel s (args.map (Term.eval m e))
  | .conj a b => truth m e a && truth m e b
  | .disj a b => truth m e a || truth m e b
  | .impl a b => !truth m e a || truth m e b
  | .all a => (List.finRange n).all (fun x => truth m (extend x e) a)
  | .ex a => (List.finRange n).any (fun x => truth m (extend x e) a)

theorem truthSubstOf {n k l} (m : Model n) (A : Formula k)
    (σ : Sub k l) (e : Env n l) (d : Env n k)
    (h : ∀ i, Term.eval m e (σ i) = d i) :
    truth m e (subst σ A) = truth m d A := by
  induction A generalizing l with
  | bot => rfl
  | eqv a b => simp only [subst, truth, Term.evalSubst m e d σ h]
  | rel s args =>
    simp only [subst, truth, List.map_map]
    exact congrArg (m.rel s) (mapAgree args _ _ (fun t _ => Term.evalSubst m e d σ h t))
  | conj a b ia ib => simp only [subst, truth, ia σ e d h, ib σ e d h]
  | disj a b ia ib => simp only [subst, truth, ia σ e d h, ib σ e d h]
  | impl a b ia ib => simp only [subst, truth, ia σ e d h, ib σ e d h]
  | all a ia =>
    exact allAgree _ _ _ (fun x =>
      ia (lift σ) (extend x e) (extend x d) (evalLift m e d σ h x))
  | ex a ia =>
    exact anyAgree _ _ _ (fun x =>
      ia (lift σ) (extend x e) (extend x d) (evalLift m e d σ h x))

theorem truthSubst {n k l} (m : Model n) (A : Formula k)
    (σ : Sub k l) (e : Env n l) :
    truth m e (subst σ A) = truth m (fun i => Term.eval m e (σ i)) A :=
  truthSubstOf m A σ e _ (fun _ => rfl)

def rename {k l} (f : Fin k → Fin l) (A : Formula k) : Formula l :=
  subst (fun i => .var (f i)) A

theorem truthRename {n k l} (m : Model n) (A : Formula k)
    (f : Fin k → Fin l) (e : Env n l) :
    truth m e (rename f A) = truth m (fun i => e (f i)) A :=
  truthSubstOf m A _ e _ (fun _ => rfl)

def free {k} : Formula k → Fin k → Prop
  | .bot, _ => False
  | .eqv a b, i => Term.free a i ∨ Term.free b i
  | .rel _ args, i => ∃ t ∈ args, Term.free t i
  | .conj a b, i | .disj a b, i | .impl a b, i => free a i ∨ free b i
  | .all a, i | .ex a, i => free a i.succ

private theorem agreeBody {n k} (B : Formula (k + 1)) (e d : Env n k) (x : Fin n)
    (h : ∀ i, free B i.succ → e i = d i) :
    ∀ j, free B j → extend x e j = extend x d j := by
  intro j
  exact Fin.cases (fun _ => rfl) (fun i hi => h i hi) j

theorem coincidence {n k} (m : Model n) (A : Formula k) (e d : Env n k)
    (h : ∀ i, free A i → e i = d i) : truth m e A = truth m d A := by
  induction A with
  | bot => rfl
  | eqv a b =>
    simp only [truth, Term.coincidence m e d a (fun i hi => h i (Or.inl hi)),
      Term.coincidence m e d b (fun i hi => h i (Or.inr hi))]
  | rel s args =>
    exact congrArg (m.rel s) (mapAgree args _ _ (fun t ht =>
      Term.coincidence m e d t (fun i hi => h i ⟨t, ht, hi⟩)))
  | conj a b ia ib =>
    simp only [truth, ia e d (fun i hi => h i (Or.inl hi)),
      ib e d (fun i hi => h i (Or.inr hi))]
  | disj a b ia ib =>
    simp only [truth, ia e d (fun i hi => h i (Or.inl hi)),
      ib e d (fun i hi => h i (Or.inr hi))]
  | impl a b ia ib =>
    simp only [truth, ia e d (fun i hi => h i (Or.inl hi)),
      ib e d (fun i hi => h i (Or.inr hi))]
  | all a ia =>
    exact allAgree _ _ _ (fun x => ia _ _ (agreeBody a e d x h))
  | ex a ia =>
    exact anyAgree _ _ _ (fun x => ia _ _ (agreeBody a e d x h))

private theorem liftIdOf {k} (σ : Sub k k) (h : ∀ i, σ i = .var i) :
    ∀ j, lift σ j = .var j := by
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · rfl
  · change Term.rename Fin.succ (σ i) = .var i.succ
    rw [h i]
    rfl

theorem substIdOf {k} (A : Formula k) (σ : Sub k k) (h : ∀ i, σ i = .var i) :
    subst σ A = A := by
  induction A with
  | bot => rfl
  | eqv a b => simp only [subst, Term.substIdOf σ h]
  | rel s args =>
    simp only [subst]
    exact congrArg (Formula.rel s) ((mapAgree args _ id (fun t _ => Term.substIdOf σ h t)).trans (mapIdDirect args))
  | conj a b ia ib => simp only [subst, ia σ h, ib σ h]
  | disj a b ia ib => simp only [subst, ia σ h, ib σ h]
  | impl a b ia ib => simp only [subst, ia σ h, ib σ h]
  | all a ia => simp only [subst, ia (lift σ) (liftIdOf σ h)]
  | ex a ia => simp only [subst, ia (lift σ) (liftIdOf σ h)]

theorem substId {k} (A : Formula k) : subst Term.var A = A :=
  substIdOf A _ (fun _ => rfl)

end Formula
end FirstOrderPacket.Substitution
