import Std.Internal.Rat

/-!
A host-level specification of the named-field theorem in the report.
Coordinates are exact rationals. The main unmechanized statements are
propositions; this file introduces neither assumptions about them nor
proof placeholders. The three search-interface lemmas are proved below.
-/
namespace HairyBall.NamedField

abbrev Q := Std.Internal.Rat
abbrev Vec (d : Nat) := Fin d → Q

def fromNat (n : Nat) : Q := ((n : Int) : Q)

def dyadic (h : Nat) : Q := 1 / fromNat (2 ^ h)

/-- Read external coordinates through the normalized integer fraction.
This keeps the public specification independent of the raw storage
in Std.Internal.Rat.  Its constructor mkRat is total at denominator zero. -/
def canon (x : Q) : Q := Std.Internal.mkRat x.num x.den

def absQ (x : Q) : Q :=
  let a := canon x
  if a < 0 then -a else a

def l1 {d : Nat} (v : Vec d) : Q :=
  Fin.foldl d (fun acc i => acc + absQ (v i)) 0

def dist {d : Nat} (v w : Vec d) : Q := l1 (fun i => canon (v i) - canon (w i))

def dot {d : Nat} (v w : Vec d) : Q :=
  Fin.foldl d (fun acc i => acc + canon (v i) * canon (w i)) 0

def OnBoundary {d : Nat} (p : Vec d) : Prop := l1 p = 1

instance {d : Nat} (p : Vec d) : Decidable (OnBoundary p) :=
  inferInstanceAs (Decidable (l1 p = 1))

/-- Orthogonal projection of v into p's tangent hyperplane. -/
def project {d : Nat} (p v : Vec d) : Vec d :=
  fun i => canon (v i) - (dot p v / dot p p) * canon (p i)

structure Name (d : Nat) where
  A : Vec d → Nat → Vec d
  μ : Nat → Nat

def CauchyLaw {d : Nat} (F : Name d) : Prop :=
  ∀ p, OnBoundary p → ∀ h j, h ≤ j →
    dist (F.A p j) (F.A p h) ≤ 2 * dyadic h

def UniformLaw {d : Nat} (F : Name d) : Prop :=
  ∀ p q, OnBoundary p → OnBoundary q → ∀ h,
    dist p q ≤ dyadic (F.μ h) →
    dist (F.A p h) (F.A q h) ≤ 3 * dyadic h

def TangencyLaw {d : Nat} (F : Name d) : Prop :=
  ∀ p, OnBoundary p → ∀ h, absQ (dot p (F.A p h)) ≤ dyadic h

def Valid {d : Nat} (F : Name d) : Prop :=
  CauchyLaw F ∧ UniformLaw F ∧ TangencyLaw F

def gridDen {d : Nat} (F : Name d) (k : Nat) : Nat :=
  2 * d * 2 ^ (F.μ (k + 6))

/-- All integer rows with each coordinate in [-D,D], in lexicographic order. -/
def integerRows (D : Nat) : Nat → List (List Int)
  | 0 => [[]]
  | d + 1 =>
    let tailRows := integerRows D d
    (List.range (2 * D + 1)).flatMap fun (b : Nat) =>
      tailRows.map (fun tail => ((b : Int) - (D : Int)) :: tail)

def rowPoint (d D : Nat) (row : List Int) : Vec d :=
  fun i => ((row.getD i.val 0 : Int) : Q) / fromNat D

/-- The exhaustive cube implementation is intentionally simple.
The report's signed compositions enumerate this same finite grid. -/
def grid (d D : Nat) : List (Vec d) :=
  if D = 0 then [] else
    ((integerRows D d).map (rowPoint d D)).filter (fun p => decide (OnBoundary p))

def accepted {d : Nat} (F : Name d) (k : Nat) (p : Vec d) : Bool :=
  decide (l1 (F.A p (k + 6)) ≤ 3 * dyadic k / 4)

def firstWitness {d : Nat} (F : Name d) (k : Nat) : Option (Vec d) :=
  (grid d (gridDen F k)).find? (accepted F k)

def TailSmall {d : Nat} (F : Name d) (k : Nat) (p : Vec d) : Prop :=
  ∀ j, k + 6 ≤ j → l1 (F.A p j) ≤ 25 * dyadic k / 32

/-- The continuous-field theorem as a proposition with a specified witness. -/
def ApproximateHairyBall : Prop :=
  ∀ (m : Nat) (F : Name (2 * m + 1)), Valid F → ∀ k,
    ∃ p, firstWitness F k = some p ∧ OnBoundary p ∧ TailSmall F k p

/-- Exact intermediate target: there is an accepted grid point. -/
def GridHit : Prop :=
  ∀ (m : Nat) (F : Name (2 * m + 1)), Valid F → ∀ k,
    ∃ p, p ∈ grid (2 * m + 1) (gridDen F k) ∧ accepted F k p = true

/-- Triangle-inequality bridge for rational Cauchy names. -/
def TailBound : Prop :=
  ∀ {d : Nat} (F : Name d) (k : Nat) (p : Vec d), CauchyLaw F →
    OnBoundary p → accepted F k p = true → TailSmall F k p

theorem grid_member_onBoundary {d D : Nat} {p : Vec d}
    (hp : p ∈ grid d D) : OnBoundary p := by
  unfold grid at hp
  split at hp
  · simp at hp
  · exact of_decide_eq_true (List.mem_filter.mp hp).2

theorem witness_onBoundary {d : Nat} {F : Name d} {k : Nat} {p : Vec d}
    (hp : firstWitness F k = some p) : OnBoundary p :=
  grid_member_onBoundary (List.mem_of_find?_eq_some hp)

theorem witness_accepted {d : Nat} {F : Name d} {k : Nat} {p : Vec d}
    (hp : firstWitness F k = some p) :
    l1 (F.A p (k + 6)) ≤ 3 * dyadic k / 4 :=
  of_decide_eq_true (List.find?_some hp : accepted F k p = true)

/-- With the two stated mathematical lemmas, the actual bounded search
supplies the conclusion. No choice operator picks a Cauchy name. -/
theorem assemble (hit : GridHit) (tail : TailBound) : ApproximateHairyBall := by
  intro m F valid k
  obtain ⟨q, hq, small⟩ := hit m F valid k
  cases outcome : firstWitness F k with
  | none =>
    have impossible := List.find?_eq_none.mp outcome q hq small
    exact False.elim impossible
  | some p =>
    have dom := witness_onBoundary outcome
    exact ⟨p, rfl, dom, tail F k p valid.1 dom (List.find?_some outcome)⟩

end HairyBall.NamedField
