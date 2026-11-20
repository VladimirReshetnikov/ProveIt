import Std

/-! Finite boundary and clearance lemmas used to move the centre of a square.
    The coefficient functional E can count the signed occurrence of any fixed
    elementary edge. Integral values play no role in the incidence proof. -/
namespace NamedResidue

variable {V : Type} (E : V → V → Int)

/-- Oriented simplex boundary, stored in its vertex order. -/
def tri (u v w : V) : Int := E u v + E v w - E u w

/-- Signed pair of triangles between the lower and upper copy of one edge. -/
def panel (p q : V × V) : Int :=
  tri E p.1 q.1 q.2 - tri E p.1 p.2 q.2

theorem panel_boundary (p q : V × V) :
    panel E p q = E p.1 q.1 - E p.2 q.2 + E q.1 q.2 - E p.1 p.2 := by
  unfold panel tri
  omega

/-- Sum of edge coefficients along a possibly open path. -/
def edges (f : V × V → V) (p : V × V) : List (V × V) → Int
  | [] => 0
  | q :: qs => E (f p) (f q) + edges f q qs

def panels (p : V × V) : List (V × V) → Int
  | [] => 0
  | q :: qs => panel E p q + panels q qs

def endpoint (p : V × V) : List (V × V) → V × V
  | [] => p
  | q :: qs => endpoint q qs

/-- Interior connector edges cancel and the exposed endpoint edges remain. -/
theorem strip_boundary (p : V × V) (rest : List (V × V)) :
    panels E p rest =
      edges E Prod.fst p rest - edges E Prod.snd p rest
        + E (endpoint p rest).1 (endpoint p rest).2 - E p.1 p.2 := by
  induction rest generalizing p with
  | nil => simp [panels, edges, endpoint]
  | cons q qs ih =>
    simp only [panels, edges, endpoint, panel_boundary, ih q]
    omega

theorem closed_strip (p : V × V) (rest : List (V × V))
    (h : endpoint p rest = p) :
    panels E p rest = edges E Prod.fst p rest - edges E Prod.snd p rest := by
  rw [strip_boundary, h]
  omega

/-- Clearance in units of 1/32 of a radius, scaled to a common
    denominator. x is the sup norm before translation, y after it. -/
theorem annulus_clearance (R x y e : Nat)
    (hx₀ : 4*R ≤ x) (hx₁ : x ≤ 256*R) (he : e ≤ R)
    (h₀ : x ≤ y+e) (h₁ : y ≤ x+e) :
    2*R ≤ y ∧ y ≤ 288*R := by omega


/-- Taxicab norm on the integer numerators of Gaussian rationals. -/
def l1 (x y : Int) : Nat := x.natAbs + y.natAbs

theorem mul_upper (u v x y : Int) :
    l1 (u*x - v*y) (u*y + v*x) ≤ l1 u v * l1 x y := by
  unfold l1
  have a := Int.natAbs_sub_le (u*x) (v*y)
  have b := Int.natAbs_add_le (u*y) (v*x)
  simp only [Int.natAbs_mul] at a b
  calc
    _ ≤ (u.natAbs*x.natAbs + v.natAbs*y.natAbs)
          + (u.natAbs*y.natAbs + v.natAbs*x.natAbs) := Nat.add_le_add a b
    _ = _ := by grind

private theorem sum_sq (a b : Nat) :
    (a+b)*(a+b) ≤ 2*(a*a + b*b) := by
  apply Int.ofNat_le.mp
  simp only [Int.natCast_mul, Int.natCast_add]
  have h := Int.sq_nonneg ((a : Int) - (b : Int))
  grind

/-- Conditioning of complex multiplication, with denominators cleared. -/
theorem mul_lower (u v x y : Int) :
    l1 u v * l1 x y ≤ 2 * l1 (u*x - v*y) (u*y + v*x) := by
  let Q := x.natAbs*x.natAbs + y.natAbs*y.natAbs
  have qcast : (Q : Int) = x*x+y*y := by
    simp only [Q, Int.natCast_add, Int.natAbs_mul_self]
  have re : (u*x-v*y)*x - (u*y+v*x)*(-y) = u*(Q:Int) := by
    rw [qcast]
    grind
  have im : (u*x-v*y)*(-y) + (u*y+v*x)*x = v*(Q:Int) := by
    rw [qcast]
    grind
  have hinv := mul_upper (u*x-v*y) (u*y+v*x) x (-y)
  rw [re, im] at hinv
  have hnorm : l1 (u*(Q:Int)) (v*(Q:Int)) = l1 u v * Q := by
    simp [l1, Int.natAbs_mul, Nat.add_mul]
  have hneg : l1 x (-y) = l1 x y := by simp [l1]
  rw [hnorm, hneg] at hinv
  have hs : l1 x y * l1 x y ≤ 2 * Q := sum_sq _ _
  by_cases h : l1 x y = 0
  · simp [h]
  · apply Nat.le_of_mul_le_mul_right _ (Nat.pos_of_ne_zero h)
    calc
      _ = l1 u v * (l1 x y * l1 x y) := Nat.mul_assoc _ _ _
      _ ≤ l1 u v * (2 * Q) := Nat.mul_le_mul_left _ hs
      _ = 2 * (l1 u v * Q) := by grind
      _ ≤ 2 * (l1 (u*x-v*y) (u*y+v*x) * l1 x y) := Nat.mul_le_mul_left _ hinv
      _ = _ := by grind

/-- Given the norm bound from the two Taylor residuals, recover the
    derivative variation. Positive common denominators can be cleared first. -/
theorem derivative_variation (u v x y : Int) (E : Nat) (hd : 0 < l1 x y)
    (h : l1 (u*x-v*y) (u*y+v*x) ≤ 2*E*l1 x y) :
    l1 u v ≤ 4*E := by
  apply Nat.le_of_mul_le_mul_right _ hd
  calc
    _ ≤ 2*l1 (u*x-v*y) (u*y+v*x) := mul_lower _ _ _ _
    _ ≤ 2*(2*E*l1 x y) := Nat.mul_le_mul_left _ h
    _ = _ := by grind

end NamedResidue
