import Std

/-! Oriented contour transport across a triangulated rational strip.
The arithmetic proof applies to every antisymmetric integer edge observation,
so in particular to each coefficient of a coded rational edge. -/

namespace ContourRibbon

variable {V : Type} (edge : V → V → Int)

def triangle (a b c : V) : Int :=
  edge a b + edge b c + edge c a

/-- Two triangles between consecutive bottom and top vertices. -/
def panel (p q : V × V) : Int :=
  triangle edge p.1 q.1 q.2 + triangle edge p.1 q.2 p.2

theorem panel_cancel (rev : ∀ a b, edge a b = -edge b a) (p q : V × V) :
    panel edge p q =
      edge p.1 q.1 - edge p.2 q.2 + edge q.1 q.2 - edge p.1 p.2 := by
  unfold panel triangle
  have h₁ := rev q.2 p.1
  have h₂ := rev q.2 p.2
  have h₃ := rev p.2 p.1
  omega

/-- Fold an edge observation along an open vertex path. -/
def walk {A : Type} (step : A → A → Int) (start : A) : List A → Int
  | [] => 0
  | q :: tail => step start q + walk step q tail

def endpoint {A : Type} (start : A) : List A → A
  | [] => start
  | q :: tail => endpoint q tail

theorem strip_cancel (rev : ∀ a b, edge a b = -edge b a)
    (p : V × V) (rest : List (V × V)) :
    walk (panel edge) p rest =
      walk (fun x y : V × V => edge x.1 y.1) p rest -
      walk (fun x y : V × V => edge x.2 y.2) p rest +
      edge (endpoint p rest).1 (endpoint p rest).2 - edge p.1 p.2 := by
  induction rest generalizing p with
  | nil => simp [walk, endpoint]
  | cons q tail ih =>
    simp only [walk, endpoint]
    rw [panel_cancel edge rev, ih q]
    omega

theorem closed_strip (rev : ∀ a b, edge a b = -edge b a)
    (p : V × V) (rest : List (V × V)) (closes : endpoint p rest = p) :
    walk (panel edge) p rest =
      walk (fun x y : V × V => edge x.1 y.1) p rest -
      walk (fun x y : V × V => edge x.2 y.2) p rest := by
  rw [strip_cancel edge rev, closes]
  omega

end ContourRibbon
