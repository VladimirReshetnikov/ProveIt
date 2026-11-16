import TermCompiler
import BackwardDemand

/-!
# Explicit PR syntax for parameter-changing recursion

Input: fixed symbols `D : PR 2`, `b : PR 1`, `F : PR 3`.
Output: one symbol `compiled D b F : PR 2` satisfying, in the host semantics,

  C(0,k) = b(k)
  C(N+1,k) = F(N,k,C(N,D(N,k))).

This closes the *PR syntax* gap explicitly left in the prior BackwardDemand
module.  It does not assert that the full recursion-equation theorem has yet
been translated to a `Prf PRAAx` derivation.  `TermCompiler.symbol_correct`
is an object-theory result; the denotation results below are host theorems.

`denote` is a host interpreter over PR syntax.  It is NOT itself claimed to be
primitive recursive, and no object-language symbol evaluates arbitrary PR code.
-/

namespace LeanProofs.ConciseIPRA.DemandCompiler

def v2 {α : Type} (a b : α) : Fin 2 → α := Fin.cases a (fun _ => b)
def v3 {α : Type} (a b c : α) : Fin 3 → α := Fin.cases a (Fin.cases b (fun _ => c))

/-- External semantics of the syntax, not an internal PR universal evaluator. -/
def denote : {k : Nat} → PR k → (Fin k → Nat) → Nat
  | _, .zero, _ => 0
  | _, .succ, xs => xs 0 + 1
  | _, .proj i, xs => xs i
  | _, .comp f gs, xs => denote f (fun i => denote (gs i) xs)
  | _, .prec f g, xs =>
      Nat.rec (denote f (fun i => xs i.succ))
        (fun n z => denote g (Fin.cases n (Fin.cases z (fun i => xs i.succ)))) (xs 0)

def zeroAt (k : Nat) : PR k := .comp .zero Fin.elim0
def succOf {k : Nat} (p : PR k) : PR k := .comp .succ (fun _ => p)
def call1 {k : Nat} (f : PR 1) (a : PR k) : PR k := .comp f (fun _ => a)
def call2 {k : Nat} (f : PR 2) (a b : PR k) : PR k := .comp f (v2 a b)
def call3 {k : Nat} (f : PR 3) (a b c : PR k) : PR k := .comp f (v3 a b c)

@[simp] theorem denote_zeroAt (k : Nat) (xs : Fin k → Nat) : denote (zeroAt k) xs = 0 := rfl
@[simp] theorem denote_succOf {k : Nat} (p : PR k) (xs : Fin k → Nat) :
    denote (succOf p) xs = denote p xs + 1 := rfl
@[simp] theorem denote_call1 {k : Nat} (f : PR 1) (a : PR k) (xs : Fin k → Nat) :
    denote (call1 f a) xs = denote f (fun _ => denote a xs) := rfl
@[simp] theorem denote_call2 {k : Nat} (f : PR 2) (a b : PR k) (xs : Fin k → Nat) :
    denote (call2 f a b) xs = denote f (v2 (denote a xs) (denote b xs)) := by
  change denote f (fun i => denote (v2 a b i) xs) = _
  apply congrArg (denote f)
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  have hj : j = 0 := by omega
  subst j
  rfl
@[simp] theorem denote_call3 {k : Nat} (f : PR 3) (a b c : PR k) (xs : Fin k → Nat) :
    denote (call3 f a b c) xs = denote f (v3 (denote a xs) (denote b xs) (denote c xs)) := by
  change denote f (fun i => denote (v3 a b c i) xs) = _
  apply congrArg (denote f)
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  refine Fin.cases rfl (fun l => ?_) j
  have hl : l = 0 := by omega
  subst l
  rfl

def predSymbol : PR 1 := .prec .zero (.proj 0)
def monusRev : PR 2 := .prec (.proj 0) (call1 predSymbol (.proj 1))
def subOf {k : Nat} (a b : PR k) : PR k := call2 monusRev b a

@[simp] theorem denote_pred (xs : Fin 1 → Nat) : denote predSymbol xs = xs 0 - 1 := by
  simp only [predSymbol, denote]
  cases xs 0 <;> rfl

@[simp] theorem denote_monusRev (n a : Nat) : denote monusRev (v2 n a) = a - n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change denote predSymbol (fun _ => denote monusRev (v2 n a)) = a - (n + 1)
      rw [denote_pred, ih]
      omega

@[simp] theorem denote_subOf {k : Nat} (a b : PR k) (xs : Fin k → Nat) :
    denote (subOf a b) xs = denote a xs - denote b xs := by
  simp only [subOf, denote_call2, denote_monusRev]

/-- Backward state: arguments of the step are `(j, previous, N, k)`. -/
def backStep (D : PR 2) : PR 4 :=
  call2 D (subOf (.proj 2) (succOf (.proj 0))) (.proj 1)

/-- Arguments `(j,N,k)`; `j` counts reverse steps. -/
def backwardSymbol (D : PR 2) : PR 3 := .prec (.proj 1) (backStep D)

/-- Arguments `(N,k,t)`; demand at forward time `t`. -/
def horizonSymbol (D : PR 2) : PR 3 :=
  call3 (backwardSymbol D) (subOf (.proj 0) (.proj 2)) (.proj 0) (.proj 1)

/-- Forward initial value, with arguments `(N,k)`. -/
def forwardBase (D : PR 2) (b : PR 1) : PR 2 :=
  call1 b (call3 (horizonSymbol D) (.proj 0) (.proj 1) (zeroAt 2))

/-- Forward step arguments `(t, previous, N, k)`. -/
def forwardStep (D : PR 2) (F : PR 3) : PR 4 :=
  call3 F (.proj 0)
    (call3 (horizonSymbol D) (.proj 2) (.proj 3) (succOf (.proj 0))) (.proj 1)

/-- Arguments `(t,N,k)`. -/
def forwardSymbol (D : PR 2) (b : PR 1) (F : PR 3) : PR 3 :=
  .prec (forwardBase D b) (forwardStep D F)

/-- The final PR symbol has arguments `(N,k)`. -/
def compiled (D : PR 2) (b : PR 1) (F : PR 3) : PR 2 :=
  call3 (forwardSymbol D b F) (.proj 0) (.proj 0) (.proj 1)

abbrev evalD (D : PR 2) (n k : Nat) : Nat := denote D (v2 n k)
abbrev evalB (b : PR 1) (k : Nat) : Nat := denote b (fun _ => k)
abbrev evalF (F : PR 3) (n k s : Nat) : Nat := denote F (v3 n k s)

theorem denote_backward (D : PR 2) (j N k : Nat) :
    denote (backwardSymbol D) (v3 j N k) = FiniteDemand.backward (evalD D) N k j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      change denote (backStep D)
        (Fin.cases j (Fin.cases (denote (backwardSymbol D) (v3 j N k)) (v2 N k))) = _
      simp only [backStep, denote_call2, denote_subOf, denote_succOf, denote]
      change evalD D (N - (j + 1)) (denote (backwardSymbol D) (v3 j N k)) = _
      rw [ih]
      rfl

theorem denote_horizon (D : PR 2) (N k t : Nat) :
    denote (horizonSymbol D) (v3 N k t) = FiniteDemand.horizon (evalD D) N k t := by
  simp only [horizonSymbol, denote_call3, denote_subOf, denote]
  exact denote_backward D (N - t) N k

theorem denote_forward (D : PR 2) (b : PR 1) (F : PR 3) (t N k : Nat) :
    denote (forwardSymbol D b F) (v3 t N k) =
      FiniteDemand.advance (evalF F) (FiniteDemand.horizon (evalD D) N k)
        (evalB b (FiniteDemand.horizon (evalD D) N k 0)) t := by
  induction t with
  | zero =>
      change denote (forwardBase D b) (v2 N k) = _
      simp only [forwardBase, denote_call1, denote_call3, denote_zeroAt, denote]
      change evalB b (denote (horizonSymbol D) (v3 N k 0)) = _
      rw [denote_horizon]
      rfl
  | succ t ih =>
      change denote (forwardStep D F)
        (Fin.cases t (Fin.cases (denote (forwardSymbol D b F) (v3 t N k)) (v2 N k))) = _
      simp only [forwardStep, denote_call3, denote_succOf, denote]
      change evalF F t (denote (horizonSymbol D) (v3 N k (t + 1)))
        (denote (forwardSymbol D b F) (v3 t N k)) = _
      rw [denote_horizon, ih]
      rfl

/-- The generated symbol denotes the previously proved two-pass construction. -/
theorem denote_compiled (D : PR 2) (b : PR 1) (F : PR 3) (N k : Nat) :
    denote (compiled D b F) (v2 N k) =
      FiniteDemand.compiledRecursion (evalD D) (evalB b) (evalF F) N k := by
  simp only [compiled, denote_call3, denote]
  exact denote_forward D b F N N k

theorem compiled_zero (D : PR 2) (b : PR 1) (F : PR 3) (k : Nat) :
    denote (compiled D b F) (v2 0 k) = evalB b k := by
  rw [denote_compiled, FiniteDemand.compiledRecursion_zero]

theorem compiled_succ (D : PR 2) (b : PR 1) (F : PR 3) (N k : Nat) :
    denote (compiled D b F) (v2 (N + 1) k) =
      evalF F N k (denote (compiled D b F) (v2 N (evalD D N k))) := by
  rw [denote_compiled, FiniteDemand.compiledRecursion_succ, denote_compiled]

end LeanProofs.ConciseIPRA.DemandCompiler

#print axioms LeanProofs.ConciseIPRA.DemandCompiler.denote_compiled
#print axioms LeanProofs.ConciseIPRA.DemandCompiler.compiled_zero
#print axioms LeanProofs.ConciseIPRA.DemandCompiler.compiled_succ
