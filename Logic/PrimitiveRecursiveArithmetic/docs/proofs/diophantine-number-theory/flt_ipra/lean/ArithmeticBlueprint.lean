import Mathlib

/-!
# Arithmetic blueprint for the explicit FLT specializations

STATUS: uncompiled Lean 4 blueprint. No Lean executable was available in
the preparation environment. This file supplies definitions, small ambient
Lean proofs, and explicit obligation structures. It does not supply completed
proofs of the exponent 3, 4, 5, or 7 descent obligations.

In particular, `FourBaseProofs` is a hypothesis package; it is not constructed
here. The theorem about covered exponents is conditional on that package.
None of the definitions below certifies primitive recursiveness by itself.
The separate ProveIt object-language translation must register the bounded
algorithms as PR constructions and prove their qf-induction invariants.
-/

namespace FLTIPRA

structure NTriple where
  x : Nat
  y : Nat
  z : Nat
  deriving DecidableEq, Repr

structure ZTriple where
  x : Int
  y : Int
  z : Int
  deriving DecidableEq, Repr

def FermatN (n : Nat) : Prop :=
  ∀ x y z : Nat, 0 < x → 0 < y → 0 < z → x ^ n + y ^ n ≠ z ^ n

def FermatCounterexample (n : Nat) (t : NTriple) : Prop :=
  0 < t.x ∧ 0 < t.y ∧ 0 < t.z ∧ t.x ^ n + t.y ^ n = t.z ^ n

def Covered (n : Nat) : Prop :=
  3 ≤ n ∧ (3 ∣ n ∨ 4 ∣ n ∨ 5 ∣ n ∨ 7 ∣ n)

def pairwiseCoprimeNat (x y z : Nat) : Prop :=
  Nat.gcd x y = 1 ∧ Nat.gcd y z = 1 ∧ Nat.gcd z x = 1

def pairwiseCoprimeInt (x y z : Int) : Prop :=
  pairwiseCoprimeNat x.natAbs y.natAbs z.natAbs

def PrimitiveCube (t : ZTriple) : Prop :=
  t.x ≠ 0 ∧ t.y ≠ 0 ∧ t.z ≠ 0 ∧
  pairwiseCoprimeInt t.x t.y t.z ∧
  t.x ^ 3 + t.y ^ 3 + t.z ^ 3 = 0 ∧
  (3 : Int) ∣ t.z ∧ ¬ (3 : Int) ∣ t.x ∧ ¬ (3 : Int) ∣ t.y

def PrimitiveFour (t : NTriple) : Prop :=
  0 < t.x ∧ 0 < t.y ∧ 0 < t.z ∧
  Nat.gcd t.x t.y = 1 ∧ t.x ^ 4 + t.y ^ 4 = t.z ^ 2

instance (t : ZTriple) : Decidable (PrimitiveCube t) := by
  unfold PrimitiveCube pairwiseCoprimeInt pairwiseCoprimeNat
  infer_instance

instance (t : NTriple) : Decidable (PrimitiveFour t) := by
  unfold PrimitiveFour
  infer_instance

def cubeCheck (t : ZTriple) : Bool := decide (PrimitiveCube t)
def fourCheck (t : NTriple) : Bool := decide (PrimitiveFour t)
def cubeRank (t : ZTriple) : Nat := t.z.natAbs
def fourRank (t : NTriple) : Nat := t.z

/-! Fixed integer-pair arithmetic; no complex or real number is used. -/

structure ZPair where
  a : Int
  b : Int
  deriving DecidableEq, Repr

namespace Eisenstein

def add (u v : ZPair) : ZPair := ⟨u.a + v.a, u.b + v.b⟩
def neg (u : ZPair) : ZPair := ⟨-u.a, -u.b⟩
def mul (u v : ZPair) : ZPair :=
  ⟨u.a * v.a - u.b * v.b,
   u.a * v.b + u.b * v.a - u.b * v.b⟩
def conj (u : ZPair) : ZPair := ⟨u.a - u.b, -u.b⟩
def norm (u : ZPair) : Int := u.a ^ 2 - u.a * u.b + u.b ^ 2
def cube (u : ZPair) : ZPair := mul (mul u u) u
def omega : ZPair := ⟨0, 1⟩
def lambda : ZPair := ⟨1, -1⟩

theorem norm_mul (u v : ZPair) : norm (mul u v) = norm u * norm v := by
  rcases u with ⟨a, b⟩
  rcases v with ⟨c, d⟩
  dsimp [norm, mul]
  ring

theorem twice_norm (u : ZPair) :
    2 * norm u = u.a ^ 2 + u.b ^ 2 + (u.a - u.b) ^ 2 := by
  dsimp [norm]
  ring

end Eisenstein

namespace Golden

def add (u v : ZPair) : ZPair := ⟨u.a + v.a, u.b + v.b⟩
def neg (u : ZPair) : ZPair := ⟨-u.a, -u.b⟩
def mul (u v : ZPair) : ZPair :=
  ⟨u.a * v.a + u.b * v.b,
   u.a * v.b + u.b * v.a + u.b * v.b⟩
def conj (u : ZPair) : ZPair := ⟨u.a + u.b, -u.b⟩
def norm (u : ZPair) : Int := u.a ^ 2 + u.a * u.b - u.b ^ 2
def normMagnitude (u : ZPair) : Nat := (norm u).natAbs
def phi : ZPair := ⟨0, 1⟩
def sqrtFive : ZPair := ⟨-1, 2⟩

def pow (u : ZPair) : Nat → ZPair
  | 0 => ⟨1, 0⟩
  | k + 1 => mul (pow u k) u

theorem norm_mul (u v : ZPair) : norm (mul u v) = norm u * norm v := by
  rcases u with ⟨a, b⟩
  rcases v with ⟨c, d⟩
  dsimp [norm, mul]
  ring

end Golden

/-! Exact states of the quintic descent. -/

def quinticF (t s : Nat) : Nat := t ^ 4 + 10 * t ^ 2 * s ^ 2 + 5 * s ^ 4
def quinticG (t s : Nat) : Nat := t ^ 4 + 50 * t ^ 2 * s ^ 2 + 125 * s ^ 4

structure QuinticState where
  h : Nat
  t : Nat
  s : Nat
  w : Nat
  deriving DecidableEq, Repr

def QuinticOdd (v : QuinticState) : Prop :=
  0 < v.t ∧ 0 < v.s ∧ 0 < v.w ∧ Nat.gcd v.t v.s = 1 ∧
  v.t % 2 = 1 ∧ v.s % 2 = 1 ∧ 5 ∣ v.s ∧ ¬ 5 ∣ v.t ∧
  5 ^ v.h * v.s * quinticF v.t v.s = 16 * v.w ^ 5

def QuinticEven (v : QuinticState) : Prop :=
  0 < v.t ∧ 0 < v.s ∧ 0 < v.w ∧ Nat.gcd v.t v.s = 1 ∧
  v.t % 2 = 1 ∧ v.s % 2 = 0 ∧ 5 ∣ v.s ∧ ¬ 5 ∣ v.t ∧
  2 * 5 ^ v.h * v.s * quinticF v.t v.s = v.w ^ 5

instance (v : QuinticState) : Decidable (QuinticOdd v) := by
  unfold QuinticOdd
  infer_instance

instance (v : QuinticState) : Decidable (QuinticEven v) := by
  unfold QuinticEven
  infer_instance

def quinticOddCheck (v : QuinticState) : Bool := decide (QuinticOdd v)
def quinticEvenCheck (v : QuinticState) : Bool := decide (QuinticEven v)
def quinticRank (v : QuinticState) : Nat := v.s

structure DirectFifthCoordinates (P Q : Nat) where
  t : Nat
  s : Nat
  t_pos : 0 < t
  s_pos : 0 < s
  coprime : Nat.gcd t s = 1
  t_odd : t % 2 = 1
  s_even : s % 2 = 0
  t_not_five : ¬ 5 ∣ t
  first : P = t * quinticG t s
  second : Q = 5 * s * quinticF t s
  t_bound : t ≤ 16 * (P + Q + 1)
  s_bound : s ≤ 16 * (P + Q + 1)

structure HalfFifthCoordinates (P Q : Nat) where
  t : Nat
  s : Nat
  t_pos : 0 < t
  s_pos : 0 < s
  coprime : Nat.gcd t s = 1
  t_odd : t % 2 = 1
  s_odd : s % 2 = 1
  t_not_five : ¬ 5 ∣ t
  first : 16 * P = t * quinticG t s
  second : 16 * Q = 5 * s * quinticF t s
  t_bound : t ≤ 16 * (P + Q + 1)
  s_bound : s ≤ 16 * (P + Q + 1)

/-! The septimal quartic uses an equivalent subtraction-free Nat equation. -/

structure SeptimalState where
  a : Nat
  P : Nat
  Q : Nat
  R : Nat
  deriving DecidableEq, Repr

def SeptimalQuartic (v : SeptimalState) : Prop :=
  1 ≤ v.a ∧ 0 < v.P ∧ 0 < v.Q ∧ 0 < v.R ∧
  v.P % 2 = 1 ∧ v.Q % 2 = 1 ∧ v.R % 2 = 1 ∧
  pairwiseCoprimeNat v.P v.Q v.R ∧
  v.P ^ 2 + 3 * 7 ^ 4 * 2 ^ (2 * v.a) * v.Q ^ 2 * v.R ^ 2 =
    v.Q ^ 4 + 7 ^ 7 * 2 ^ (4 * v.a + 4) * v.R ^ 4

instance (v : SeptimalState) : Decidable (SeptimalQuartic v) := by
  unfold SeptimalQuartic pairwiseCoprimeNat
  infer_instance

def septimalCheck (v : SeptimalState) : Bool := decide (SeptimalQuartic v)
def septimalRank (v : SeptimalState) : Nat := v.a

/-! Finite iteration and the ambient mathematical descent lemma. -/

def iterate {S : Type} (step : S → S) : Nat → S → S
  | 0, s => s
  | k + 1, s => step (iterate step k s)

theorem noNatRankDescent {S : Type} (Valid : S → Prop)
    (step : S → S) (rank : S → Nat)
    (hstep : ∀ s, Valid s → Valid (step s) ∧ rank (step s) < rank s)
    (initial : S) : ¬ Valid initial := by
  intro hinit
  have trace : ∀ k : Nat,
      Valid (iterate step k initial) ∧
        rank (iterate step k initial) + k ≤ rank initial := by
    intro k
    induction k with
    | zero =>
        constructor
        · exact hinit
        · simp [iterate]
    | succ k ih =>
        have hnext := hstep (iterate step k initial) ih.1
        refine ⟨hnext.1, ?_⟩
        change rank (step (iterate step k initial)) + (k + 1) ≤ rank initial
        have hbound := ih.2
        have hless := hnext.2
        omega
  have impossible := (trace (rank initial + 1)).2
  omega

/-!
These records name missing proof obligations. No record is instantiated.
For an iPRA proof, additionally supply PR codes for each selector and the
object-language derivations of `correct`; ambient Lean fields are insufficient.
-/

structure DescentObligations (S : Type) (Valid : S → Prop) (rank : S → Nat) where
  step : S → S
  correct : ∀ s, Valid s → Valid (step s) ∧ rank (step s) < rank s

structure InitialStateObligations (n : Nat) (S : Type) (Valid : S → Prop) where
  toState : NTriple → S
  correct : ∀ t, FermatCounterexample n t → Valid (toState t)

abbrev CubicDescentObligations :=
  DescentObligations ZTriple PrimitiveCube cubeRank

abbrev QuarticDescentObligations :=
  DescentObligations NTriple PrimitiveFour fourRank

abbrev QuinticOddDescentObligations :=
  DescentObligations QuinticState QuinticOdd quinticRank

abbrev QuinticEvenDescentObligations :=
  DescentObligations QuinticState QuinticEven quinticRank

abbrev SeptimalDescentObligations :=
  DescentObligations SeptimalState SeptimalQuartic septimalRank

theorem fermatOfDescent {n : Nat} {S : Type} {Valid : S → Prop} {rank : S → Nat}
    (D : DescentObligations S Valid rank)
    (I : InitialStateObligations n S Valid) : FermatN n := by
  intro x y z hx hy hz heq
  let t : NTriple := ⟨x, y, z⟩
  have ht : FermatCounterexample n t := ⟨hx, hy, hz, heq⟩
  have hv : Valid (I.toState t) := I.correct t ht
  exact noNatRankDescent Valid D.step rank D.correct (I.toState t) hv

/-! Exponent lifting. This uses completed base proofs only as hypotheses. -/

theorem fermat_multiple {d n : Nat} (hd : FermatN d) (hdiv : d ∣ n) :
    FermatN n := by
  rcases hdiv with ⟨k, rfl⟩
  intro x y z hx hy hz heq
  have lifted : (x ^ k) ^ d + (y ^ k) ^ d = (z ^ k) ^ d := by
    simpa only [← pow_mul, Nat.mul_comm] using heq
  exact hd (x ^ k) (y ^ k) (z ^ k)
    (pow_pos hx k) (pow_pos hy k) (pow_pos hz k) lifted

structure FourBaseProofs where
  three : FermatN 3
  four : FermatN 4
  five : FermatN 5
  seven : FermatN 7

theorem covered_of_four_base_proofs (base : FourBaseProofs) {n : Nat}
    (hn : Covered n) : FermatN n := by
  rcases hn.2 with h3 | h4 | h5 | h7
  · exact fermat_multiple base.three h3
  · exact fermat_multiple base.four h4
  · exact fermat_multiple base.five h5
  · exact fermat_multiple base.seven h7

end FLTIPRA
