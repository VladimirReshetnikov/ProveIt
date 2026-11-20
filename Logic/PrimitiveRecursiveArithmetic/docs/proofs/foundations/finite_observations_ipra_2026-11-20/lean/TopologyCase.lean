import Std

/-! Finite kernel for a positive-clearance crossing. All numbers held in the
state are rational or natural. The callbacks stand for fixed first-order
programs in each arithmetic instantiation. -/
namespace Crossing

structure Mark where
  time : Rat
  exponent : Nat
  deriving Inhabited, Repr

structure Cell where
  left : Mark
  right : Mark
  deriving Inhabited, Repr

def width (I : Cell) : Rat := I.right.time - I.left.time

def middle (I : Cell) (p : Mark) : Prop :=
  3*I.left.time + I.right.time ≤ 4*p.time ∧
  4*p.time ≤ I.left.time + 3*I.right.time

def nested (J I : Cell) : Prop :=
  I.left.time ≤ J.left.time ∧ J.right.time ≤ I.right.time

def good (clear color : Mark → Bool) (I : Cell) : Prop :=
  I.left.time < I.right.time ∧ clear I.left = true ∧
  clear I.right = true ∧ color I.left ≠ color I.right

def cut (color : Mark → Bool) (I : Cell) (p : Mark) : Cell :=
  if color I.left = color p then ⟨p, I.right⟩ else ⟨I.left, p⟩

theorem cut_spec (clear color : Mark → Bool) (I : Cell) (p : Mark)
    (hI : good clear color I) (hp : clear p = true) (hc : middle I p) :
    good clear color (cut color I p) ∧ nested (cut color I p) I ∧
    4*width (cut color I p) ≤ 3*width I ∧ width I ≤ 4*width (cut color I p) := by
  rcases hI with ⟨hab, ha, hb, hd⟩
  rcases hc with ⟨hl, hr⟩
  unfold cut
  split <;> simp only [good, nested, width]
  all_goals grind

def iterate (color : Mark → Bool) (probe : Cell → Mark) (I : Cell) : Nat → Cell
  | 0 => I
  | n+1 => let J := iterate color probe I n; cut color J (probe J)

theorem good_iterate (clear color : Mark → Bool) (probe : Cell → Mark)
    (H : ∀ J, good clear color J → clear (probe J) = true ∧ middle J (probe J))
    (I : Cell) (hI : good clear color I) (n : Nat) :
    good clear color (iterate color probe I n) := by
  induction n with
  | zero => exact hI
  | succ n ih =>
    exact (cut_spec _ _ _ _ ih (H _ ih).1 (H _ ih).2).1

theorem one_step (clear color : Mark → Bool) (probe : Cell → Mark)
    (H : ∀ J, good clear color J → clear (probe J) = true ∧ middle J (probe J))
    (I : Cell) (hI : good clear color I) (n : Nat) :
    let cell := iterate color probe I
    nested (cell (n+1)) (cell n) ∧
      4*width (cell (n+1)) ≤ 3*width (cell n) ∧
      width (cell n) ≤ 4*width (cell (n+1)) := by
  have hj := good_iterate clear color probe H I hI n
  exact (cut_spec _ _ _ _ hj (H _ hj).1 (H _ hj).2).2

theorem three_steps (w : Nat → Rat)
    (h : ∀ i, 4*w (i+1) ≤ 3*w i) (h0 : ∀ i, 0 ≤ w i) (i : Nat) :
    2*w (i+3) ≤ w i := by
  have h1 := h i
  have h2 := h (i+1)
  have h3 := h (i+2)
  have hw := h0 i
  grind

def twoPow : Nat → Rat
  | 0 => 1
  | n+1 => 2*twoPow n

theorem twoPow_nonneg (n : Nat) : 0 ≤ twoPow n := by
  induction n with
  | zero => decide
  | succ n ih => simp only [twoPow]; grind

theorem rate (w : Nat → Rat)
    (h : ∀ i, 4*w (i+1) ≤ 3*w i) (h0 : ∀ i, 0 ≤ w i) (n : Nat) :
    twoPow n * w (3*n) ≤ w 0 := by
  induction n with
  | zero => simp [twoPow]
  | succ n ih =>
    have ha := three_steps w h h0 (3*n)
    have hb := Rat.mul_le_mul_of_nonneg_left ha (twoPow_nonneg n)
    have he : 3 * (n+1) = 3*n + 3 := by omega
    rw [he, twoPow]
    grind

/-- Signed forward differences of the sampled rational values. -/
def diff (v : Nat → Rat) : Nat → Nat → Rat
  | 0, k => v k
  | d+1, k => diff v d (k+1) - diff v d k

theorem diff_enclosure (v : Nat → Rat) (M : Rat) (N : Nat)
    (hv : ∀ j, j ≤ N → -M ≤ v j ∧ v j ≤ M) (d k : Nat) (hk : k+d ≤ N) :
    -(twoPow d*M) ≤ diff v d k ∧ diff v d k ≤ twoPow d*M := by
  induction d generalizing k with
  | zero =>
    have h := hv k (by omega)
    simpa [twoPow, diff] using h
  | succ d ih =>
    have hu := ih (k+1) (by omega)
    have hl := ih k (by omega)
    simp only [twoPow, diff]
    grind

theorem diff_linear_prod (f l : Nat → Rat) (h : Rat)
    (hl : ∀ k, l (k+1) = l k + h) (n k : Nat) :
    diff (fun i => l i * f i) (n+1) k =
      l (k+(n+1)) * diff f (n+1) k + ((n+1 : Nat) : Rat)*h*diff f n k := by
  induction n generalizing k with
  | zero =>
    simp only [diff]
    rw [hl k]
    grind
  | succ n ih =>
    change diff _ (n+1) (k+1) - diff _ (n+1) k =
      l (k+(n+1+1)) * (diff f (n+1) (k+1) - diff f (n+1) k) +
      ((n+1+1 : Nat) : Rat)*h*diff f (n+1) k
    rw [ih (k+1), ih k]
    have hk : k+1+(n+1) = k+(n+1+1) := by omega
    rw [hk]
    have hx := hl (k+(n+1))
    have hc : ((n+1+1 : Nat) : Rat) = ((n+1 : Nat) : Rat) + 1 := by grind
    have hd : diff f (n+1) k = diff f n (k+1) - diff f n k := rfl
    grind

theorem diff_add_const (f : Nat → Rat) (c : Rat) (d k : Nat) :
    diff (fun i => c+f i) (d+1) k = diff f (d+1) k := by
  induction d generalizing k with
  | zero => simp only [diff]; grind
  | succ d ih =>
    change diff _ (d+1) (k+1) - diff _ (d+1) k = _
    rw [ih, ih]
    rfl

/-- Coefficients in ascending order, with the leading coefficient stored
    separately. A zero leading coefficient is also allowed. -/
def horner (leading : Rat) : List Rat → Rat → Rat
  | [], _ => leading
  | c::tail, x => c + x*horner leading tail x

/-- By its recurrence this is the signed factor d! h^d. -/
def diffFactor (h : Rat) : Nat → Rat
  | 0 => 1
  | d+1 => ((d+1 : Nat) : Rat) * h * diffFactor h d

theorem horner_top_difference (l : Nat → Rat) (h : Rat)
    (hl : ∀ i, l (i+1) = l i+h) (leading : Rat) (coeff : List Rat) (k : Nat) :
    diff (fun i => horner leading coeff (l i)) coeff.length k =
      diffFactor h coeff.length * leading := by
  induction coeff generalizing k with
  | nil => simp [diff, horner, diffFactor]
  | cons c tail ih =>
    let f := fun i => horner leading tail (l i)
    change diff (fun i => c+l i*f i) (tail.length+1) k =
      diffFactor h (tail.length+1) * leading
    rw [diff_add_const, diff_linear_prod f l h hl]
    have hk : diff f tail.length k = diffFactor h tail.length * leading := ih k
    have hn : diff f tail.length (k+1) = diffFactor h tail.length * leading := ih (k+1)
    have hz : diff f (tail.length+1) k = 0 := by
      change diff f tail.length (k+1) - diff f tail.length k = 0
      rw [hk, hn]
      grind
    rw [hz, hk, diffFactor]
    grind

/-- The two-sided bound underlying (*) in the paper. If M is a bound on
    the samples then 2^d M bounds the absolute top difference. -/
theorem polynomial_probe_bound (l : Nat → Rat) (h : Rat)
    (hl : ∀ i, l (i+1) = l i+h) (a M : Rat) (coeff : List Rat)
    (hm : ∀ j, j ≤ coeff.length →
      -M ≤ horner a coeff (l j) ∧ horner a coeff (l j) ≤ M) :
    -(twoPow coeff.length*M) ≤ diffFactor h coeff.length*a ∧
    diffFactor h coeff.length*a ≤ twoPow coeff.length*M := by
  have bound := diff_enclosure (fun j => horner a coeff (l j)) M
    coeff.length hm coeff.length 0 (by omega)
  rw [horner_top_difference l h hl a coeff 0] at bound
  exact bound

end Crossing
