import Std
import Lean.Elab.Tactic.Omega

/-!
# A constructive four-square program and a conditional correctness assembly

STATUS: formalization scaffold, not compiled in the producing environment.

All programs below are total. Their loops use structural recursion on an explicit
natural fuel. The unfinished arithmetic is collected in `ArithmeticContracts`.
The final theorem is conditional on those contracts; this file does NOT claim to
have completed a Lean proof of Lagrange's theorem or an arithmetized iPRA proof.

No `sorry`, `admit`, `axiom`, `unsafe`, or `partial` declaration is used.
See OBLIGATIONS.md for the proofs still required and README.md for the distinction
between host Lean correctness and object-theory iPRA derivability.
-/

namespace ConstructiveFourSquares

/-! ## Finite searches -/

/-- `allLt n test` is the conjunction of `test 0`, ..., `test (n-1)`. -/
def allLt (test : Nat → Bool) : Nat → Bool
  | 0 => true
  | k + 1 => allLt test k && test k

/-- Least successful index below `bound`, or the sentinel `bound`. -/
def firstLt (test : Nat → Bool) : Nat → Nat
  | 0 => 0
  | k + 1 =>
    let earlier := firstLt test k
    if earlier < k then earlier
    else if test k then k
    else k + 1

/-- A definition using only bounded divisibility tests, not `Nat.Prime`. -/
def primeB (n : Nat) : Bool :=
  decide (2 ≤ n) &&
    allLt (fun d => if d < 2 then true else decide (n % d ≠ 0)) n

def IsPrime (n : Nat) : Prop := primeB n = true

/-- The least divisor at least two; the total default for n < 2 is one. -/
def leastDivisor (n : Nat) : Nat :=
  if n < 2 then 1
  else firstLt (fun d => decide (2 ≤ d) && decide (n % d = 0)) (n + 1)

/-! ## Four signed coordinates and Hamilton multiplication -/

structure Z4 where
  a : Int
  b : Int
  c : Int
  d : Int
  deriving Repr, DecidableEq

namespace Z4

def zero : Z4 := ⟨0, 0, 0, 0⟩
def one : Z4 := ⟨1, 0, 0, 0⟩

def ofNats (a b c d : Nat) : Z4 :=
  ⟨Int.ofNat a, Int.ofNat b, Int.ofNat c, Int.ofNat d⟩

def normSq (x : Z4) : Int :=
  x.a * x.a + x.b * x.b + x.c * x.c + x.d * x.d

def conj (x : Z4) : Z4 := ⟨x.a, -x.b, -x.c, -x.d⟩

def mul (x y : Z4) : Z4 :=
  ⟨x.a*y.a - x.b*y.b - x.c*y.c - x.d*y.d,
   x.a*y.b + x.b*y.a + x.c*y.d - x.d*y.c,
   x.a*y.c - x.b*y.d + x.c*y.a + x.d*y.b,
   x.a*y.d + x.b*y.c - x.c*y.b + x.d*y.a⟩

/-- Total integer quotients. In the descent proof every division is exact. -/
def divide (x : Z4) (m : Nat) : Z4 :=
  let M := Int.ofNat m
  ⟨x.a / M, x.b / M, x.c / M, x.d / M⟩

end Z4

/-- Euclidean centered residue; the proof only uses this with positive odd m. -/
def centered (m : Nat) (z : Int) : Int :=
  let M := Int.ofNat m
  let r := z % M
  if 2*r ≤ M then r else r-M

def centered4 (m : Nat) (x : Z4) : Z4 :=
  ⟨centered m x.a, centered m x.b, centered m x.c, centered m x.d⟩

def halfPairs (a b c d : Int) : Z4 :=
  ⟨(a+b)/2, (a-b)/2, (c+d)/2, (c-d)/2⟩

/-- One of three fixed pairings. For even norm both selected pairs have equal parity. -/
def evenHalf (x : Z4) : Z4 :=
  if x.a % 2 = x.b % 2 then halfPairs x.a x.b x.c x.d
  else if x.a % 2 = x.c % 2 then halfPairs x.a x.c x.b x.d
  else halfPairs x.a x.d x.b x.c

/-! ## Seed and bounded descent for primes -/

structure DescentState where
  multiplier : Nat
  vector : Z4
  deriving Repr, DecidableEq

/-- The seed search is lexicographic in (a,b), with 0 ≤ a,b ≤ (p-1)/2. -/
def seedState (p : Nat) : DescentState :=
  if p = 2 then ⟨1, Z4.ofNats 1 1 0 0⟩
  else if p < 3 then ⟨1, Z4.zero⟩
  else
    let width := (p - 1) / 2 + 1
    let bound := width * width
    let index := firstLt (fun k =>
      let a := k / width
      let b := k % width
      decide ((a*a+b*b+1) % p = 0)) bound
    if index < bound then
      let a := index / width
      let b := index % width
      ⟨(a*a+b*b+1)/p, Z4.ofNats a b 1 0⟩
    else ⟨1, Z4.zero⟩

/-- `multiplier ≤ 1` is absorbing, including the irrelevant malformed zero case. -/
def descentStep (s : DescentState) : DescentState :=
  if s.multiplier ≤ 1 then s
  else if s.multiplier % 2 = 0 then
    ⟨s.multiplier/2, evenHalf s.vector⟩
  else
    let r := centered4 s.multiplier s.vector
    let k := (r.normSq / Int.ofNat s.multiplier).toNat
    ⟨k, Z4.divide (Z4.mul s.vector (Z4.conj r)) s.multiplier⟩

def PrimeState (p : Nat) (s : DescentState) : Prop :=
  0 < s.multiplier ∧ s.multiplier < p ∧
    s.vector.normSq = Int.ofNat (s.multiplier * p)

def descentRank (s : DescentState) : Nat := s.multiplier - 1

/-! ## Primitive recursion with an explicit iteration count -/

universe u

def iterate {α : Type u} (step : α → α) : Nat → α → α
  | 0, s => s
  | k + 1, s => step (iterate step k s)

theorem iterate_preserves {α : Type u} (step : α → α) (I : α → Prop)
    (hstep : ∀ s, I s → I (step s)) (fuel : Nat) (s : α) (hs : I s) :
    I (iterate step fuel s) := by
  induction fuel with
  | zero => exact hs
  | succ fuel ih => exact hstep _ ih

/-- A saturated rank decreases to zero after its original value many steps. -/
theorem iterate_rank_bound {α : Type u} (step : α → α) (I : α → Prop)
    (rank : α → Nat)
    (hstep : ∀ s, I s → I (step s))
    (hdrop : ∀ s, I s → rank (step s) ≤ rank s - 1)
    (fuel : Nat) (s : α) (hs : I s) :
    rank (iterate step fuel s) ≤ rank s - fuel := by
  induction fuel with
  | zero => simp [iterate]
  | succ fuel ih =>
    have hvalid := iterate_preserves step I hstep fuel s hs
    have hnext := hdrop (iterate step fuel s) hvalid
    change rank (step (iterate step fuel s)) ≤ rank s - (fuel + 1)
    omega

def primeRep (p : Nat) : Z4 :=
  (iterate descentStep p (seedState p)).vector

def PrimeRepresentationsCorrect : Prop :=
  ∀ p, IsPrime p → (primeRep p).normSq = Int.ofNat p

/-! ## Fixed-length trial-factor loop -/

structure FactorState where
  remaining : Nat
  accumulated : Z4
  deriving Repr, DecidableEq

def factorInit (n : Nat) : FactorState := ⟨n, Z4.one⟩

def factorStep (s : FactorState) : FactorState :=
  if s.remaining ≤ 1 then s
  else
    let p := leastDivisor s.remaining
    ⟨s.remaining / p, Z4.mul s.accumulated (primeRep p)⟩

def FactorInvariant (n : Nat) (s : FactorState) : Prop :=
  0 < s.remaining ∧
    Int.ofNat s.remaining * s.accumulated.normSq = Int.ofNat n

def factorRank (s : FactorState) : Nat := s.remaining - 1

def signedFourSquares (n : Nat) : Z4 :=
  if n = 0 then Z4.zero
  else (iterate factorStep n (factorInit n)).accumulated

structure N4 where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  deriving Repr, DecidableEq

namespace N4

def normSq (x : N4) : Nat :=
  x.a*x.a + x.b*x.b + x.c*x.c + x.d*x.d

end N4

def naturalize (x : Z4) : N4 :=
  ⟨x.a.natAbs, x.b.natAbs, x.c.natAbs, x.d.natAbs⟩

/-- The four desired primitive recursive coordinate functions are projections of this. -/
def fourSquares (n : Nat) : N4 := naturalize (signedFourSquares n)

/-! ## Unfinished arithmetic, exposed as assumptions rather than hidden axioms

Each field is a local lemma (seed correctness, one-step descent, one-step trial
division, or absolute-value compatibility). None asserts the final four-square
theorem. The accompanying ledger decomposes these into elementary obligations.

Constructing a value of this structure remains to be done.
-/

structure ArithmeticContracts where
  seed_sound : ∀ p, IsPrime p → PrimeState p (seedState p)
  descent_preserves : ∀ p s, IsPrime p → PrimeState p s →
    PrimeState p (descentStep s)
  descent_decreases : ∀ p s, IsPrime p → PrimeState p s →
    descentRank (descentStep s) ≤ descentRank s - 1
  factor_preserves : PrimeRepresentationsCorrect → ∀ n s,
    FactorInvariant n s → FactorInvariant n (factorStep s)
  factor_decreases : ∀ n s, FactorInvariant n s →
    factorRank (factorStep s) ≤ factorRank s - 1
  naturalize_norm : ∀ x,
    Int.ofNat (naturalize x).normSq = x.normSq

theorem primeRep_correct (C : ArithmeticContracts) :
    PrimeRepresentationsCorrect := by
  intro p hp
  have h0 := C.seed_sound p hp
  have hpstep := fun s hs => C.descent_preserves p s hp hs
  have hpdrop := fun s hs => C.descent_decreases p s hp hs
  have hinv := iterate_preserves descentStep (PrimeState p) hpstep p (seedState p) h0
  have hbound := iterate_rank_bound descentStep (PrimeState p) descentRank
    hpstep hpdrop p (seedState p) h0
  have hseedlt := h0.2.1
  have hpos := hinv.1
  have hm : (iterate descentStep p (seedState p)).multiplier = 1 := by
    simp only [descentRank] at hbound
    omega
  simpa [primeRep, hm] using hinv.2.2

theorem factorInit_valid (n : Nat) (hn : 0 < n) :
    FactorInvariant n (factorInit n) := by
  constructor
  · exact hn
  · simp [factorInit, Z4.one, Z4.normSq]

theorem signedFourSquares_correct (C : ArithmeticContracts) (n : Nat) :
    (signedFourSquares n).normSq = Int.ofNat n := by
  by_cases hn : n = 0
  · simp [signedFourSquares, hn, Z4.zero, Z4.normSq]
  · have hnpos : 0 < n := by omega
    have h0 := factorInit_valid n hnpos
    have hstep := fun s hs => C.factor_preserves (primeRep_correct C) n s hs
    have hdrop := fun s hs => C.factor_decreases n s hs
    have hinv := iterate_preserves factorStep (FactorInvariant n) hstep n (factorInit n) h0
    have hbound := iterate_rank_bound factorStep (FactorInvariant n) factorRank
      hstep hdrop n (factorInit n) h0
    have hpos := hinv.1
    have hremaining : (iterate factorStep n (factorInit n)).remaining = 1 := by
      simp only [factorRank, factorInit] at hbound
      omega
    simpa [signedFourSquares, hn, hremaining] using hinv.2

/-- CONDITIONAL assembly: the arithmetic contracts still have to be constructed. -/
theorem fourSquares_correct (C : ArithmeticContracts) (n : Nat) :
    (fourSquares n).normSq = n := by
  have h : Int.ofNat (fourSquares n).normSq = Int.ofNat n := by
    calc
      Int.ofNat (fourSquares n).normSq = (signedFourSquares n).normSq :=
        C.naturalize_norm (signedFourSquares n)
      _ = Int.ofNat n := signedFourSquares_correct C n
  exact Int.ofNat.inj h

/-- The familiar existential conclusion, still explicitly conditional on C. -/
theorem lagrange_from_contracts (C : ArithmeticContracts) (n : Nat) :
    ∃ a b c d : Nat, n = a*a+b*b+c*c+d*d := by
  let w := fourSquares n
  refine ⟨w.a, w.b, w.c, w.d, ?_⟩
  exact (fourSquares_correct C n).symm

end ConstructiveFourSquares
