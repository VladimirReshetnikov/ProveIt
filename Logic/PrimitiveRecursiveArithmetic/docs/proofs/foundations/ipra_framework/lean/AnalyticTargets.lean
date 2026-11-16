import Std

/-!
# Represented analysis: concrete definitions and UNPROVED targets

This file names propositions; it does not assume or prove them.  It contains
no `axiom` or placeholder proof.  Successful compilation validates the syntax
and types of these specifications only.  The accompanying article supplies
the human arguments and the object-iPRA formalization plan.

Function arguments below are host-Lean interfaces. In an iPRA instance their
evaluators, moduli and controls must be fixed PR symbols, with the stated
arithmetic contracts. No universal PR evaluator for arbitrary program codes
is postulated. Universal name/continuity/monotonicity hypotheses below are
not called quantifier-free merely because their outer index set is finite.
-/

namespace IPRAFramework.AnalyticTargets

def qabs (q : Rat) : Rat := if q < 0 then -q else q

def dyadic (k : Nat) : Rat := mkRat 1 (2 ^ k)

def qsum (xs : List Rat) : Rat := xs.foldl (· + ·) 0

abbrev RealName := Nat → Rat
abbrev RealSequence := Nat → RealName
abbrev ParameterizedSequence := Nat → RealSequence

def Regular (q : RealName) : Prop :=
  ∀ p r, qabs (q p - q r) ≤ dyadic p + dyadic r

def NameEqual (q r : RealName) : Prop :=
  ∀ p, qabs (q p - r p) ≤ 2 * dyadic p

def NameLE (q r : RealName) : Prop :=
  ∀ p, q p ≤ r p + 2 * dyadic p

def NameLower (c : Rat) (q : RealName) : Prop :=
  ∀ p, c ≤ q p + dyadic p

def NameUpper (q : RealName) (c : Rat) : Prop :=
  ∀ p, q p ≤ c + dyadic p

/-- A concrete rational margin, not mere negated equality. -/
def NameSeparated (q r : RealName) (margin : Rat) : Prop :=
  0 < margin ∧ ∀ p, q p + margin ≤ r p + 2 * dyadic p

def SequenceRegular (q : RealSequence) : Prop := ∀ n, Regular (q n)

def SequenceMonotone (q : RealSequence) : Prop :=
  ∀ n m, n ≤ m → NameLE (q n) (q m)

def SequenceBounded (q : RealSequence) (B : Nat) : Prop :=
  ∀ n, NameLower 0 (q n) ∧ NameUpper (q n) (B : Rat)

/-! ## Finite rational observations and the algebra of names -/

def Observations (q : RealName) (horizon : Nat) : Prop :=
  ∀ p, p ≤ horizon → ∀ r, r ≤ horizon →
    qabs (q p - q r) ≤ dyadic p + dyadic r

/-- Named goal: rational slack can be removed without taking a real limit. -/
def RationalSlackRemovalTarget : Prop :=
  ∀ x y : Rat, (∀ k, x ≤ y + dyadic k) → x ≤ y

def NameEquivalenceTarget : Prop :=
  (∀ q, Regular q → NameEqual q q) ∧
  (∀ q r, Regular q → Regular r → NameEqual q r → NameEqual r q) ∧
  (∀ q r s, Regular q → Regular r → Regular s →
    NameEqual q r → NameEqual r s → NameEqual q s)

def NameOrderTransitiveTarget : Prop :=
  ∀ q r s, Regular q → Regular r → Regular s →
    NameLE q r → NameLE r s → NameLE q s

/-! ## Concrete finite arithmetic tables -/

inductive Gate where
  | add (left right : Nat)
  | sub (left right : Nat)
  | mul (left right : Nat)
  deriving Repr, DecidableEq

def entry (xs : List Rat) (i : Nat) : Rat := xs[i]?.getD 0

def gateValid (available : Nat) : Gate → Bool
  | .add i j | .sub i j | .mul i j => decide (i < available ∧ j < available)

def tableValid (inputCount : Nat) (gates : List Gate) : Bool :=
  gates.zipIdx.all (fun (g, j) => gateValid (inputCount + j) g)

def evalGate (env : List Rat) : Gate → Rat
  | .add i j => entry env i + entry env j
  | .sub i j => entry env i - entry env j
  | .mul i j => entry env i * entry env j

/-- Addition and subtraction both add the supplied operand magnitude bounds. -/
def boundGate (env : List Rat) : Gate → Rat
  | .add i j | .sub i j => entry env i + entry env j
  | .mul i j => entry env i * entry env j

def evalTable (env : List Rat) : List Gate → List Rat → List Rat
  | [], _ => env
  | g :: gs, errors =>
      evalTable (env ++ [evalGate env g + errors.headD 0]) gs errors.tail

def boundTable (env : List Rat) : List Gate → List Rat
  | [] => env
  | g :: gs => boundTable (env ++ [boundGate env g]) gs

def InputBounded (inputs bounds : List Rat) : Prop :=
  inputs.length = bounds.length ∧
    ∀ i, i < inputs.length → qabs (entry inputs i) ≤ entry bounds i

def InputErrors (inputs approximate : List Rat) (delta : Rat) : Prop :=
  inputs.length = approximate.length ∧
    ∀ i, i < inputs.length →
      qabs (entry inputs i - entry approximate i) ≤ delta

def LocalErrors (gates : List Gate) (errors : List Rat) (delta : Rat) : Prop :=
  ∀ i, i < gates.length → qabs (entry errors i) ≤ delta

def Dominates (B : Nat) (bounds : List Rat) : Prop :=
  ∀ i, i < bounds.length → entry bounds i ≤ (B : Rat)

/-- Named goal for the paper's `L=2B+3` schedule. -/
def ArithmeticTableErrorTarget : Prop :=
  ∀ (inputs approximate bounds errors : List Rat) (gates : List Gate)
      (B s : Nat) (delta : Rat),
    tableValid inputs.length gates = true → 1 ≤ B → 0 ≤ delta →
    InputBounded inputs bounds → InputErrors inputs approximate delta →
    LocalErrors gates errors delta → Dominates B (boundTable bounds gates) →
    delta ≤ dyadic s / (2 * (B : Rat) + 3) ^ (gates.length + 1) →
    ∀ i, i < inputs.length + gates.length →
      qabs (entry (evalTable inputs gates []) i -
        entry (evalTable approximate gates errors) i) ≤ dyadic s

/-! ## Deterministic soft endpoint selection -/

def start (g : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => start g n + g (start g n) + 1

/-- Least index minimizing `f` among `0,...,last`, keeping the earlier tie. -/
def firstMin (f : Nat → Rat) : Nat → Nat
  | 0 => 0
  | n + 1 =>
      let j := firstMin f n
      if f (n + 1) < f j then n + 1 else j

def FirstMinTarget : Prop :=
  ∀ (f : Nat → Rat) last,
    let j := firstMin f last
    j ≤ last ∧
      (∀ i, i ≤ last → f j ≤ f i) ∧
      (∀ i, i < j → f j < f i)

def windowCount (k B : Nat) : Nat := 2 ^ (k + 1) * B + 1

def endpoint (q : RealSequence) (g : Nat → Nat) (k i : Nat) : Rat :=
  q (start g i) (k + 3)

def endpointDifference (q : RealSequence) (g : Nat → Nat) (k i : Nat) : Rat :=
  endpoint q g k (i + 1) - endpoint q g k i

def selectedIndex (q : RealSequence) (g : Nat → Nat) (k B : Nat) : Nat :=
  firstMin (endpointDifference q g k) (windowCount k B - 1)

def selectedStart (q : RealSequence) (g : Nat → Nat) (k B : Nat) : Nat :=
  start g (selectedIndex q g k B)

def stabilityMargin (k B : Nat) : Rat :=
  dyadic k / (2 * (windowCount k B : Rat))

/--
The principal represented finite-window target.

Every quantifier here is an ordinary host specification. In the object
schema `q` and `g` are fixed PR families; `B,k,u,v,p` are numerical inputs.
Its conclusion is a finite rational comparison at the arbitrary precision
`p`. Generalizing over `p` expresses the represented bound, with explicit
positive margin `stabilityMargin k B`.
-/
def RepresentedWindowTarget : Prop :=
  ∀ (q : RealSequence) (g : Nat → Nat) (B k : Nat),
    SequenceRegular q → SequenceMonotone q → SequenceBounded q B →
    let N := selectedStart q g k B
    selectedIndex q g k B < windowCount k B ∧
      0 < stabilityMargin k B ∧
      ∀ u v p, N ≤ u → u ≤ N + g N → N ≤ v → v ≤ N + g N →
        qabs (q u p - q v p) ≤
          dyadic k - stabilityMargin k B + 2 * dyadic p

/-! ## Rational-domain evaluation, extension, and dyadic integration -/

abbrev QPoint := List Rat
abbrev Evaluator := QPoint → Nat → Rat
abbrev CoordinateNames := Nat → RealName

def InCube (dimension : Nat) (x : QPoint) : Prop :=
  x.length = dimension ∧
    ∀ i, i < dimension → 0 ≤ entry x i ∧ entry x i ≤ 1

def qmax (x y : Rat) : Rat := if x ≤ y then y else x

def supDistance (dimension : Nat) (x y : QPoint) : Rat :=
  (List.range dimension).foldl
    (fun acc i => qmax acc (qabs (entry x i - entry y i))) 0

def MonotoneModulus (mu : Nat → Nat) : Prop :=
  ∀ j k, j ≤ k → mu j ≤ mu k

/-- Uniform continuity expressed solely by rational name comparisons. -/
def UniformEvaluator (dimension : Nat) (f : Evaluator) (mu : Nat → Nat) : Prop :=
  (∀ x, InCube dimension x → Regular (f x)) ∧
    ∀ j x y, InCube dimension x → InCube dimension y →
      supDistance dimension x y ≤ dyadic (mu j) →
      ∀ p, qabs (f x p - f y p) ≤ dyadic j + 2 * dyadic p

def PointNames (dimension : Nat) (X : CoordinateNames) : Prop :=
  ∀ i, i < dimension →
    Regular (X i) ∧ NameLower 0 (X i) ∧ NameUpper (X i) 1

def clipUnit (x : Rat) : Rat := if x < 0 then 0 else if 1 < x then 1 else x

def pointApproximation (dimension : Nat) (X : CoordinateNames) (p : Nat) : QPoint :=
  (List.range dimension).map (fun i => clipUnit (X i p))

def extensionName (dimension : Nat) (f : Evaluator) (mu : Nat → Nat)
    (X : CoordinateNames) (k : Nat) : Rat :=
  f (pointApproximation dimension X (mu (k + 3) + 2)) (k + 3)

def ExtensionRegularTarget : Prop :=
  ∀ dimension f mu X, MonotoneModulus mu →
    UniformEvaluator dimension f mu → PointNames dimension X →
    Regular (extensionName dimension f mu X)

def indexGrid : Nat → Nat → List (List Nat)
  | 0, _ => [[]]
  | d + 1, side =>
      (List.range side).flatMap (fun i => (indexGrid d side).map (fun xs => i :: xs))

def dyadicGrid (dimension meshPower : Nat) : List QPoint :=
  (indexGrid dimension (2 ^ meshPower)).map
    (fun xs => xs.map (fun (i : Nat) => (i : Rat) * dyadic meshPower))

def integralName (dimension : Nat) (f : Evaluator) (mu : Nat → Nat)
    (k : Nat) : Rat :=
  let m := mu (k + 3)
  dyadic (dimension * m) *
    qsum ((dyadicGrid dimension m).map (fun x => f x (k + 3)))

def FiniteGridIntegralTarget : Prop :=
  ∀ dimension f mu, 1 ≤ dimension → MonotoneModulus mu →
    UniformEvaluator dimension f mu →
    ∀ k l, k ≤ l →
      qabs (integralName dimension f mu k - integralName dimension f mu l) ≤
        3 * dyadic (k + 3)

def IntegralRegularTarget : Prop :=
  ∀ dimension f mu, 1 ≤ dimension → MonotoneModulus mu →
    UniformEvaluator dimension f mu → Regular (integralName dimension f mu)

end IPRAFramework.AnalyticTargets
