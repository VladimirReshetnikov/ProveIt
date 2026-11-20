import Std

/-! Finite arithmetic used by transport of contour integrals to named centres.
    No analyticity axiom or representation of an infinite complex path is used. -/
namespace MovingCentre

@[ext] structure GQ where
  re : Rat
  im : Rat
deriving DecidableEq, Repr

def plus (u v : GQ) : GQ := ⟨u.re + v.re, u.im + v.im⟩
def minus (u v : GQ) : GQ := ⟨u.re - v.re, u.im - v.im⟩
def times (u v : GQ) : GQ :=
  ⟨u.re*v.re - u.im*v.im, u.re*v.im + u.im*v.re⟩
def size (u : GQ) : Rat := u.re.abs + u.im.abs

theorem abs_add (x y : Rat) : (x+y).abs ≤ x.abs+y.abs := by
  simp only [Rat.abs]
  split <;> split <;> split <;> grind

theorem abs_product (x y : Rat) : (x*y).abs = x.abs*y.abs := by
  by_cases hx : 0 ≤ x <;> by_cases hy : 0 ≤ y
  · rw [Rat.abs_of_nonneg (Rat.mul_nonneg hx hy), Rat.abs_of_nonneg hx, Rat.abs_of_nonneg hy]
  · have hy' : y ≤ 0 := by grind
    have h : x*y ≤ 0 := by
      have := Rat.mul_le_mul_of_nonneg_left hy' hx
      simpa using this
    rw [Rat.abs_of_nonpos h, Rat.abs_of_nonneg hx, Rat.abs_of_nonpos hy']
    grind
  · have hx' : x ≤ 0 := by grind
    have h : x*y ≤ 0 := by
      have := Rat.mul_le_mul_of_nonneg_right hx' hy
      simpa using this
    rw [Rat.abs_of_nonpos h, Rat.abs_of_nonpos hx', Rat.abs_of_nonneg hy]
    grind
  · have hx' : x ≤ 0 := by grind
    have hy' : y ≤ 0 := by grind
    have h : 0 ≤ x*y := by
      have : 0 ≤ (-x)*(-y) := Rat.mul_nonneg (by grind) (by grind)
      grind
    rw [Rat.abs_of_nonneg h, Rat.abs_of_nonpos hx', Rat.abs_of_nonpos hy']
    grind

theorem size_plus (u v : GQ) : size (plus u v) ≤ size u + size v := by
  have hr := abs_add u.re v.re
  have hi := abs_add u.im v.im
  unfold size plus
  grind

theorem size_times (u v : GQ) : size (times u v) ≤ size u * size v := by
  have hr := abs_add (u.re*v.re) (-(u.im*v.im))
  have hi := abs_add (u.re*v.im) (u.im*v.re)
  simp only [Rat.abs_neg, abs_product] at hr hi
  unfold times size
  dsimp
  rw [Rat.sub_eq_add_neg]
  grind

def qsum (a : Nat → Rat) : Nat → Rat
  | 0 => 0
  | n+1 => qsum a n + a n

def integralSum (f dz : Nat → GQ) : Nat → GQ
  | 0 => ⟨0, 0⟩
  | n+1 => plus (integralSum f dz n) (times (f n) (dz n))

/-- A translated contour has the same increments. The sample mismatch is
    multiplied by total polygonal length, irrespective of the mesh size. -/
theorem same_increments (f g dz : Nat → GQ) (d : Rat) (n : Nat)
    (samples : ∀ i, i < n → size (minus (f i) (g i)) ≤ d) :
    size (minus (integralSum f dz n) (integralSum g dz n)) ≤
      d * qsum (fun i => size (dz i)) n := by
  induction n with
  | zero => simp [integralSum, minus, size, qsum, Rat.sub_eq_add_neg] <;> grind [Rat.abs]
  | succ n ih =>
    have hp := ih (fun i hi => samples i (Nat.lt_trans hi (Nat.lt_succ_self n)))
    have hlast := samples n (Nat.lt_succ_self n)
    let s := minus (integralSum f dz n) (integralSum g dz n)
    let t := times (minus (f n) (g n)) (dz n)
    have heq : minus (integralSum f dz (n+1)) (integralSum g dz (n+1)) = plus s t := by
      apply GQ.ext <;> dsimp [integralSum, s, t, plus, minus, times] <;> grind
    have hn : 0 ≤ size (dz n) := by
      dsimp [size]
      have := Rat.abs_nonneg (x := (dz n).re)
      have := Rat.abs_nonneg (x := (dz n).im)
      grind
    have hmul := Rat.mul_le_mul_of_nonneg_right hlast hn
    have ht : size t ≤ d * size (dz n) :=
      Rat.le_trans (size_times _ _) hmul
    rw [heq, qsum]
    have hpre : size s ≤ d * qsum (fun i => size (dz i)) n := hp
    have htriangle := size_plus s t
    grind

/-- Two triangles transgress between opposite quadrilateral edges. The
    identity is valid for one coordinate, with all rational weights. -/
def triangle {α : Type} (e : α → α → Rat) (a b c : α) : Rat :=
  e a b + e b c + e c a

def strip {α : Type} (e : α → α → Rat) (a b A B : α) : Rat :=
  triangle e a b B + triangle e a B A

theorem strip_boundary {α : Type} (e : α → α → Rat)
    (rev : ∀ a b, e a b = -e b a) (a b A B : α) :
    strip e a b A B = e a b - e A B + e b B - e a A := by
  unfold strip triangle
  have hd := rev B a
  have he := rev B A
  have hf := rev A a
  grind

def square {α : Type} (e : α → α → Rat) (a b c d : α) : Rat :=
  e a b + e b c + e c d + e d a

/-- Eight oriented triangles have precisely the difference of the two
    square boundaries, including in degenerate parallel strips. -/
theorem four_strips {α : Type} (e : α → α → Rat)
    (rev : ∀ a b, e a b = -e b a) (a b c d A B C D : α) :
    strip e a b A B + strip e b c B C + strip e c d C D + strip e d a D A =
      square e a b c d - square e A B C D := by
  simp only [strip_boundary e rev, square]
  grind

/-- Precision unit, shared by the stage modulus and the inner quadrature. -/
def dyad : Nat → Rat
  | 0 => 1
  | n+1 => dyad n / 2

theorem dyad_nonneg (n : Nat) : 0 ≤ dyad n := by
  induction n with
  | zero => simp [dyad] <;> grind
  | succ n ih => rw [dyad]; grind

/-- Each rational centre gives one coefficient name. This rate counts
    the precision of the centre, not stages of a universal evaluator. -/
def diagonal (cut : Nat → Nat) (value : Nat → Nat → GQ) (p : Nat) : GQ :=
  value (cut (p+2)) (p+2)

theorem diagonal_regular (cut : Nat → Nat) (value : Nat → Nat → GQ)
    (mono : ∀ i j, i ≤ j → cut i ≤ cut j)
    (stage : ∀ k n m p q, cut k ≤ n → cut k ≤ m →
      size (minus (value n p) (value m q)) ≤ dyad k + dyad p + dyad q)
    (p q : Nat) :
    size (minus (diagonal cut value p) (diagonal cut value q)) ≤ dyad p + dyad q := by
  unfold diagonal
  have hp := dyad_nonneg p
  have hq := dyad_nonneg q
  by_cases h : p ≤ q
  · have bound := stage (p+2) (cut (p+2)) (cut (q+2)) (p+2) (q+2)
      (Nat.le_refl _) (mono _ _ (by omega))
    simp only [dyad] at bound
    grind
  · have bound := stage (q+2) (cut (p+2)) (cut (q+2)) (p+2) (q+2)
      (mono _ _ (by omega)) (Nat.le_refl _)
    simp only [dyad] at bound
    grind

end MovingCentre
