import DemandCompiler

/-!
# Fixed-dimensional lexicographic fuel: concrete definitions and PR syntax

`fuelSymbol d h` is a PR symbol for every fixed external natural number d.
`denote_fuelSymbol` proves this compiler correct.  This makes no assertion
that `(d,s) ↦ fuel d h s` has a single primitive-recursive implementation.
The controlled-chain and termination propositions at the end are defined
targets, not theorems; their human proofs are in the accompanying article.
-/

namespace LeanProofs.ConciseIPRA.LexFuel

open DemandCompiler

def iter (f : Nat → Nat) : Nat → Nat → Nat
  | 0, s => s
  | n + 1, s => f (iter f n s)

def fuel : Nat → (Nat → Nat) → Nat → Nat
  | 0, _, s => s + 1
  | d + 1, h, s => iter (fuel d h) (h s + 1) s

/-- Unary iteration has arguments `(number of steps, starting value)`. -/
def iterateSymbol (f : PR 1) : PR 2 :=
  .prec (.proj 0) (call1 f (.proj 1))

/-- Construction of syntax recurses on external dimension.  Evaluation of
the output symbol is not uniform PR evaluation of its code. -/
def fuelSymbol : Nat → PR 1 → PR 1
  | 0, _ => .succ
  | d + 1, h => call2 (iterateSymbol (fuelSymbol d h)) (succOf h) (.proj 0)

theorem denote_iterateSymbol (f : PR 1) (n s : Nat) :
    denote (iterateSymbol f) (v2 n s) = iter (evalB f) n s := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change evalB f (denote (iterateSymbol f) (v2 n s)) = _
      rw [ih]
      rfl

/-- A checked explicit PR realization of every fixed-dimensional fuel. -/
theorem denote_fuelSymbol (d : Nat) (h : PR 1) :
    ∀ s, evalB (fuelSymbol d h) s = fuel d (evalB h) s := by
  induction d with
  | zero => intro s; rfl
  | succ d ih =>
      intro s
      change denote (call2 (iterateSymbol (fuelSymbol d h)) (succOf h) (.proj 0))
        (fun _ => s) = _
      rw [denote_call2, denote_succOf, denote_iterateSymbol]
      change iter (evalB (fuelSymbol d h)) (evalB h s + 1) s = _
      have he : evalB (fuelSymbol d h) = fuel d (evalB h) := funext ih
      rw [he]
      rfl

/-- Parameter-preserving iteration, arguments `(steps, input, seed)`. -/
def iterateParamSymbol (f : PR 2) : PR 3 :=
  .prec (.proj 1) (call2 f (.proj 2) (.proj 1))

/-- The input parameter remains variable. `h` has arguments `(input,time)`,
and the result has arguments `(input,start)`. This is the version needed for
one uniform witness function of the machine input, at fixed dimension. -/
def fuelParamSymbol : Nat → PR 2 → PR 2
  | 0, _ => succOf (.proj 1)
  | d + 1, h =>
      call3 (iterateParamSymbol (fuelParamSymbol d h)) (succOf h) (.proj 0) (.proj 1)

def boundSymbol (d : Nat) (h : PR 2) : PR 1 :=
  call2 (fuelParamSymbol d h) (.proj 0) (zeroAt 1)

theorem denote_iterateParamSymbol (f : PR 2) (n x s : Nat) :
    denote (iterateParamSymbol f) (v3 n x s) =
      iter (fun t => evalD f x t) n s := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change denote (call2 f (.proj 2) (.proj 1))
        (Fin.cases n (Fin.cases (denote (iterateParamSymbol f) (v3 n x s)) (v2 x s))) = _
      rw [denote_call2]
      change evalD f x (denote (iterateParamSymbol f) (v3 n x s)) = _
      rw [ih]
      rfl

theorem denote_fuelParamSymbol (d : Nat) (h : PR 2) (x : Nat) :
    ∀ s, evalD (fuelParamSymbol d h) x s = fuel d (fun t => evalD h x t) s := by
  induction d with
  | zero => intro s; rfl
  | succ d ih =>
      intro s
      change denote (call3 (iterateParamSymbol (fuelParamSymbol d h))
        (succOf h) (.proj 0) (.proj 1)) (v2 x s) = _
      rw [denote_call3, denote_succOf, denote_iterateParamSymbol]
      change iter (fun t => evalD (fuelParamSymbol d h) x t) (evalD h x s + 1) s = _
      have he : (fun t => evalD (fuelParamSymbol d h) x t) =
          fuel d (fun t => evalD h x t) := funext ih
      rw [he]
      rfl

theorem denote_boundSymbol (d : Nat) (h : PR 2) (x : Nat) :
    evalB (boundSymbol d h) x = fuel d (fun t => evalD h x t) 0 := by
  change denote (call2 (fuelParamSymbol d h) (.proj 0) (zeroAt 1)) (fun _ => x) = _
  rw [denote_call2, denote_zeroAt]
  exact denote_fuelParamSymbol d h x 0

abbrev Rank (d : Nat) := Fin d → Nat

/-- Lexicographic decrease, most significant coordinate first. -/
def lexDropB : {d : Nat} → Rank d → Rank d → Bool
  | 0, _, _ => false
  | d + 1, u, v =>
      if v 0 < u 0 then true
      else if u 0 < v 0 then false
      else lexDropB (d := d) (fun i => u i.succ) (fun i => v i.succ)

/-- Explicit finite-coordinate maximum. -/
def coordMax : {d : Nat} → Rank d → Nat
  | 0, _ => 0
  | d + 1, v => max (v 0) (coordMax (d := d) (fun i => v i.succ))

def run (step : Nat → Nat) (initial : Nat) : Nat → Nat
  | 0 => initial
  | n + 1 => step (run step initial n)

def prefixMax (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => max (prefixMax f n) (f n)

def trajectoryEnvelope {d : Nat} (rank : Nat → Rank d)
    (step : Nat → Nat) (initial t : Nat) : Nat :=
  prefixMax (fun i => coordMax (rank (run step initial i))) (t + 1)

def monotone (h : Nat → Nat) : Prop := ∀ s t, s ≤ t → h s ≤ h t

/-- `v` is used only at the L positions beginning at s. -/
def ControlledChain {d : Nat} (h : Nat → Nat)
    (v : Nat → Rank d) (s L : Nat) : Prop :=
  (∀ i, i < L → ∀ j, v (s + i) j ≤ h (s + i)) ∧
  (∀ i, i + 1 < L → lexDropB (v (s + i)) (v (s + i + 1)) = true)

def FuelGrowthTarget : Prop :=
  ∀ d h, monotone h → (∀ s, s + 1 ≤ fuel d h s) ∧ monotone (fuel d h)

def ControlledChainBoundTarget : Prop :=
  ∀ d h (v : Nat → Rank d) s L,
    monotone h → ControlledChain h v s L → s + L ≤ fuel d h s

/-- Concrete first-order coded states, Boolean activity/invariant, and a
fixed tuple of rank functions.  These fields are data, not correctness axioms. -/
structure Machine (d : Nat) where
  initial : Nat
  step : Nat → Nat
  active : Nat → Bool
  invariant : Nat → Bool
  rank : Nat → Rank d
  output : Nat → Nat

def LocalConditions {d : Nat} (M : Machine d) : Prop :=
  M.invariant M.initial = true ∧
  (∀ u, M.invariant u = true → M.invariant (M.step u) = true) ∧
  (∀ u, M.active u = false → M.step u = u) ∧
  (∀ u, M.invariant u = true → M.active u = true → M.active (M.step u) = true →
    lexDropB (M.rank u) (M.rank (M.step u)) = true)

def machineFuel {d : Nat} (M : Machine d) : Nat :=
  fuel d (trajectoryEnvelope M.rank M.step M.initial) 0

def BoundedTerminationTarget : Prop :=
  ∀ d (M : Machine d), LocalConditions M →
    M.active (run M.step M.initial (machineFuel M)) = false

def WitnessTarget : Prop :=
  ∀ d (M : Machine d) (post : Nat → Prop),
    LocalConditions M →
    (∀ u, M.invariant u = true → M.active u = false → post (M.output u)) →
    post (M.output (run M.step M.initial (machineFuel M)))

end LeanProofs.ConciseIPRA.LexFuel

#print axioms LeanProofs.ConciseIPRA.LexFuel.denote_iterateSymbol
#print axioms LeanProofs.ConciseIPRA.LexFuel.denote_fuelSymbol
#print axioms LeanProofs.ConciseIPRA.LexFuel.denote_fuelParamSymbol
#print axioms LeanProofs.ConciseIPRA.LexFuel.denote_boundSymbol
