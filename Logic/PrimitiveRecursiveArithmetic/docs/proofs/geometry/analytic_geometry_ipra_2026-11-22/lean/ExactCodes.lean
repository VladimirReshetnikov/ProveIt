import Mathlib

/-!
# Executable data model for the report

STATUS: uncompiled Lean 4 outline. These are data definitions, not an iPRA
soundness theorem. In particular, the higher-order functions in the final
section are metatheoretic notation for a *fixed* primitive-recursive family.
They are never quantified over inside first-order iPRA.
-/

namespace AnalyticGeometryIPRA

/-- Signed integers as differences; no normalization is needed. -/
structure ZCode where
  pos : ℕ
  neg : ℕ
  deriving Repr, DecidableEq

namespace ZCode

def zero : ZCode := ⟨0, 0⟩
def one : ZCode := ⟨1, 0⟩
def value (a : ZCode) : ℤ := (a.pos : ℤ) - a.neg
def add (a b : ZCode) : ZCode := ⟨a.pos+b.pos, a.neg+b.neg⟩
def negated (a : ZCode) : ZCode := ⟨a.neg, a.pos⟩
def sub (a b : ZCode) : ZCode := add a (negated b)
def mul (a b : ZCode) : ZCode :=
  ⟨a.pos*b.pos+a.neg*b.neg, a.pos*b.neg+a.neg*b.pos⟩
def scale (k : ℕ) (a : ZCode) : ZCode := ⟨k*a.pos, k*a.neg⟩
def eqb (a b : ZCode) : Bool := (a.pos+b.neg == b.pos+a.neg)
def leb (a b : ZCode) : Bool := decide (a.pos+b.neg ≤ b.pos+a.neg)

end ZCode

/-- A rational code (p,n,d) denotes (p-n)/(d+1). -/
structure RatCode where
  num : ZCode
  denPred : ℕ
  deriving Repr, DecidableEq

namespace RatCode

def den (q : RatCode) : ℕ := q.denPred+1
def value (q : RatCode) : ℚ :=
  ((q.num.pos : ℚ)-q.num.neg)/(q.den : ℚ)
def zero : RatCode := ⟨ZCode.zero, 0⟩
def one : RatCode := ⟨ZCode.one, 0⟩
def ofNat (a : ℕ) : RatCode := ⟨⟨a, 0⟩, 0⟩

/-- d1*d2+d1+d2 is the predecessor of (d1+1)(d2+1). -/
def productDenPred (a b : RatCode) : ℕ :=
  a.denPred*b.denPred+a.denPred+b.denPred

def add (a b : RatCode) : RatCode :=
  ⟨ZCode.add (ZCode.scale b.den a.num) (ZCode.scale a.den b.num),
   productDenPred a b⟩
def negated (a : RatCode) : RatCode := ⟨ZCode.negated a.num, a.denPred⟩
def sub (a b : RatCode) : RatCode := add a (negated b)
def mul (a b : RatCode) : RatCode :=
  ⟨ZCode.mul a.num b.num, productDenPred a b⟩

/-- Totalized inverse: inv(0)=0. Every geometric use carries a nonzero guard. -/
def inv (a : RatCode) : RatCode :=
  if a.num.pos = a.num.neg then zero
  else if a.num.neg < a.num.pos then
    ⟨⟨a.den, 0⟩, a.num.pos-a.num.neg-1⟩
  else
    ⟨⟨0, a.den⟩, a.num.neg-a.num.pos-1⟩

def div (a b : RatCode) : RatCode := mul a (inv b)
def eqb (a b : RatCode) : Bool :=
  ZCode.eqb (ZCode.scale b.den a.num) (ZCode.scale a.den b.num)
def leb (a b : RatCode) : Bool :=
  ZCode.leb (ZCode.scale b.den a.num) (ZCode.scale a.den b.num)
def nonzero (a : RatCode) : Prop := a.num.pos ≠ a.num.neg

end RatCode

structure Point2 (α : Type) where
  x : α
  y : α
  deriving Repr, DecidableEq

structure Point3 (α : Type) where
  x : α
  y : α
  z : α
  deriving Repr, DecidableEq

structure Line2 (α : Type) where
  a : α
  b : α
  c : α
  deriving Repr, DecidableEq

structure Plane3 (α : Type) where
  a : α
  b : α
  c : α
  d : α
  deriving Repr, DecidableEq

structure Conic (α : Type) where
  a : α
  b : α
  c : α
  d : α
  e : α
  f : α
  deriving Repr, DecidableEq

def dot2 (u v : Point2 ℚ) : ℚ := u.x*v.x+u.y*v.y
def det2 (u v : Point2 ℚ) : ℚ := u.x*v.y-u.y*v.x
def normSq2 (u : Point2 ℚ) : ℚ := dot2 u u
def lineValue (l : Line2 ℚ) (p : Point2 ℚ) : ℚ := l.a*p.x+l.b*p.y+l.c
def properLine (l : Line2 ℚ) : Prop := l.a ≠ 0 ∨ l.b ≠ 0
def lineDet (l m : Line2 ℚ) : ℚ := l.a*m.b-m.a*l.b

/-- Candidate intersection; its theorem has the guard lineDet l m ≠ 0. -/
def lineMeet (l m : Line2 ℚ) : Point2 ℚ :=
  ⟨(l.b*m.c-m.b*l.c)/lineDet l m,
   (l.c*m.a-m.c*l.a)/lineDet l m⟩

def conicValue (q : Conic ℚ) (p : Point2 ℚ) : ℚ :=
  q.a*p.x^2+q.b*p.x*p.y+q.c*p.y^2+q.d*p.x+q.e*p.y+q.f

/-- A bounded natural loop implements this exact square-root index. B>0 is required. -/
def sqrtIndex (A B k : ℕ) : ℕ := Nat.sqrt ((A*4^k)/B)

def sqrtLower (A B k : ℕ) : ℚ := (sqrtIndex A B k : ℚ)/(2:ℚ)^k
def sqrtUpper (A B k : ℕ) : ℚ := ((sqrtIndex A B k+1 : ℕ):ℚ)/(2:ℚ)^k

def dyadic (k : ℕ) : ℚ := 1/(2:ℚ)^k

/-- Metatheoretic abbreviation for a finite-observation name condition.
The function q must be a fixed PR family before arithmetical translation. -/
def NameCondition (q : ℕ → RatCode) : Prop :=
  ∀ m n, |RatCode.value (q m)-RatCode.value (q n)| ≤ dyadic m+dyadic n

def NameBound (q : ℕ → RatCode) (B : ℕ) : Prop :=
  ∀ n, |RatCode.value (q n)| ≤ (B : ℚ)+dyadic n

def NameNonnegative (q : ℕ → RatCode) : Prop :=
  ∀ n, -dyadic n ≤ RatCode.value (q n)

def GapContract (q : ℕ → RatCode) (k : ℕ) : Prop :=
  ∀ n, dyadic k-dyadic n ≤ |RatCode.value (q n)|

/-- A finite observation certifies a positive gap from zero. -/
def PositiveWitness (q : ℕ → RatCode) (k : ℕ) : Prop :=
  dyadic k+dyadic (k+2) ≤ RatCode.value (q (k+2))

def ApartWitness (q : ℕ → RatCode) (k : ℕ) : Prop :=
  dyadic k+dyadic (k+2) ≤ |RatCode.value (q (k+2))|

/- Under NameCondition q, ApartWitness q k implies GapContract q k:
subtract the bound |q(n)-q(k+2)| <= 2^-n+2^-(k+2) from the finite
absolute-value lower bound. This is a rational triangle-inequality argument;
no zero test on real names is involved. Its Lean proof is a remaining gate. -/

end AnalyticGeometryIPRA
