import Std

/-!
# Executable split-branch definitions and unproved mathematical goals

This file defines the exact finite algorithms used in Section 5.  Every
`...Goal : Prop` below is a specification, NOT an asserted theorem.  No
axiom, `sorry`, or assumed proof of these specifications is introduced.
Compiling this file checks the definitions and proposition types.  It does
not prove the split-branch height theorem or an embedded iPRA theorem.

Polynomial coefficients are integers listed in ascending degree order.
All algorithms are total, including on certificates rejected by
`checkSplit`.  The complete-solution claims are conditional on acceptance.
-/

namespace IPRALocalGlobal.Split

abbrev PolyCode := List Int

/-- Canonical form: delete trailing zero coefficients; zero becomes `[]`. -/
def trim (p : PolyCode) : PolyCode :=
  (p.reverse.dropWhile (fun a => a == 0)).reverse

/-- Horner evaluation of ascending coefficient arrays. -/
def eval (p : PolyCode) (x : Int) : Int :=
  p.foldr (fun a value => a + x * value) 0

/-- Coefficient lookup with explicit zero padding. -/
def coeff (p : PolyCode) (k : Nat) : Int :=
  (p[k]?).getD 0

/-- Subtraction computes and normalizes the actual difference array. -/
def sub (p q : PolyCode) : PolyCode :=
  trim ((List.range (max p.length q.length)).map
    (fun k => coeff p k - coeff q k))

/-- Natural degree, with default zero for the zero polynomial.
All uses requiring a genuine degree also require `trim p ≠ []`. -/
def degree (p : PolyCode) : Nat :=
  (trim p).length - 1

def absSum (p : PolyCode) : Nat :=
  p.foldl (fun total a => total + a.natAbs) 0

/-- Sum of absolute coefficients strictly below the leading degree. -/
def lowerAbsSum (p : PolyCode) : Nat :=
  let q := trim p
  absSum (q.take (q.length - 1))

/-- `weightedBound p H = ∑ |p_k| H^k`, computed by Horner recursion. -/
def weightedBound (p : PolyCode) (H : Nat) : Nat :=
  p.foldr (fun a value => a.natAbs + H * value) 0

structure SplitCertificate where
  branches : List PolyCode
  remainder : PolyCode
  first : Nat
  second : Nat
  deriving Repr, DecidableEq

/-- A missing branch has the harmless total default `[]`.
`checkSplit` separately rejects missing selected indices. -/
def branchAt (c : SplitCertificate) (i : Nat) : PolyCode :=
  (c.branches[i]?).getD []

def difference (c : SplitCertificate) : PolyCode :=
  sub (branchAt c c.first) (branchAt c c.second)

/-- Check precisely the finite hypotheses of the height theorem.
The difference polynomial is recomputed rather than supplied on trust. -/
def checkSplit (c : SplitCertificate) : Bool :=
  let r := trim c.remainder
  let p := difference c
  decide (2 ≤ c.branches.length ∧
    c.first < c.branches.length ∧
    c.second < c.branches.length ∧
    r ≠ [] ∧ r.length < p.length)

/-- The explicit coordinate bound `max 1 (L + 2 C)`. -/
def heightX (c : SplitCertificate) : Nat :=
  max 1 (lowerAbsSum (difference c) + 2 * absSum c.remainder)

/-- The explicit bound `max_t E_(A_t)(H) + E_R(H)`. -/
def heightY (c : SplitCertificate) : Nat :=
  let H := heightX c
  c.branches.foldl (fun bound p => max bound (weightedBound p H)) 0
    + weightedBound c.remainder H

def branchProduct (c : SplitCertificate) (x y : Int) : Int :=
  c.branches.foldl (fun value p => value * (y - eval p x)) 1

/-- The exact equation `∏_t (y - A_t(x)) = R(x)`. -/
def Equation (c : SplitCertificate) (x y : Int) : Prop :=
  branchProduct c x y = eval c.remainder x

/-- The signed interval `[-H, H]`, with `2H+1` explicit entries. -/
def signedInterval (H : Nat) : List Int :=
  (List.range (2 * H + 1)).map (fun (k : Nat) => Int.ofNat k - Int.ofNat H)

/-- Total bounded enumeration; rejected certificates return the empty list. -/
def enumerateSolutions (c : SplitCertificate) : List (Int × Int) :=
  if checkSplit c = true then
    (signedInterval (heightX c)).flatMap fun x =>
      (signedInterval (heightY c)).filterMap fun y =>
        if branchProduct c x y = eval c.remainder x then some (x, y)
        else none
  else []

/-- Certificate for `∏_(j=1)^m (y-x^j)=1`.
The selected exponents are 1 and 3; acceptance is intended for `m ≥ 3`. -/
def powerFamily (m : Nat) : SplitCertificate where
  branches := (List.range m).map (fun j => List.replicate (j + 1) 0 ++ [1])
  remainder := [1]
  first := 0
  second := 2

/-- Exact candidate list from the uniform classification in the paper. -/
def classificationList (m : Nat) : List (Int × Int) :=
  [(0, 1), (1, 2)] ++
    (if m % 2 = 0 then [(0, -1), (1, 0)] else []) ++
    (if m % 4 = 0 ∨ m % 4 = 1 then [(-1, 0)] else [])

/-- Expanded mathematical statement of the same classification. -/
def ClassificationCondition (m : Nat) (x y : Int) : Prop :=
  (x = 0 ∧ y = 1) ∨
  (x = 1 ∧ y = 2) ∨
  (m % 2 = 0 ∧ ((x = 0 ∧ y = -1) ∨ (x = 1 ∧ y = 0))) ∨
  ((m % 4 = 0 ∨ m % 4 = 1) ∧ x = -1 ∧ y = 0)

/-! ## Pending semantic goals

These declarations only name propositions.  A later implementation must
provide proof terms for them and separately compile the finite arithmetic
arguments into the object calculus `Prf PRAAx`.
-/

def intFactorAbsLeGoal : Prop :=
  ∀ (u v w : Int), u * v = w → w ≠ 0 → u.natAbs ≤ w.natAbs

def polyEvalAbsLeGoal : Prop :=
  ∀ (p : PolyCode) (x : Int) (H : Nat),
    x.natAbs ≤ H → (eval p x).natAbs ≤ weightedBound p H

def polyDominanceGoal : Prop :=
  ∀ (p : PolyCode) (x : Int),
    trim p ≠ [] → 1 ≤ degree p → 1 ≤ x.natAbs →
    x.natAbs ^ degree p ≤
      (eval p x).natAbs + lowerAbsSum p * x.natAbs ^ (degree p - 1)

def nonzeroPolyNoLargeRootGoal : Prop :=
  ∀ (p : PolyCode) (x : Int),
    trim p ≠ [] → absSum p < x.natAbs → eval p x ≠ 0

/-- Pending: every solution of an accepted certificate obeys the x-bound. -/
def splitXBoundGoal : Prop :=
  ∀ (c : SplitCertificate) (x y : Int),
    checkSplit c = true → Equation c x y → x.natAbs ≤ heightX c

/-- Pending: every solution of an accepted certificate obeys the y-bound,
including the exceptional case `eval c.remainder x = 0`. -/
def splitYBoundGoal : Prop :=
  ∀ (c : SplitCertificate) (x y : Int),
    checkSplit c = true → Equation c x y → y.natAbs ≤ heightY c

/-- Pending: exact soundness and completeness of the returned finite list. -/
def enumerateSolutionsIffGoal : Prop :=
  ∀ (c : SplitCertificate), checkSplit c = true →
    ∀ (x y : Int), (x, y) ∈ enumerateSolutions c ↔ Equation c x y

/-- Pending: full uniform classification for every `m ≥ 3`. -/
def classificationGoal : Prop :=
  ∀ (m : Nat), 3 ≤ m →
    ∀ (x y : Int), Equation (powerFamily m) x y ↔ ClassificationCondition m x y

/-- Pending: the explicit finite list is the same complete classification. -/
def classificationListGoal : Prop :=
  ∀ (m : Nat), 3 ≤ m →
    ∀ (x y : Int), (x, y) ∈ classificationList m ↔ Equation (powerFamily m) x y

end IPRALocalGlobal.Split
