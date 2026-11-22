import Std

/-!
One-query halving for a separated increasing map. All order tests in
`choose` are comparisons of finite rationals. A probe at precision p
stands for the closed interval [at p - rad p, at p + rad p].
-/
namespace ConditionedZero

structure Scalar (rad : Nat → Rat) where
  atPrec : Nat → Rat
  consistent : ∀ i j, atPrec i - rad i ≤ atPrec j + rad j

def Gap {rad : Nat → Rat} (δ : Rat) (x y : Scalar rad) : Prop :=
  ∀ i j, x.atPrec i - rad i + δ ≤ y.atPrec j + rad j

structure Box where
  lo : Rat
  hi : Rat
  deriving Repr

def Box.width (I : Box) := I.hi - I.lo
def Box.mid (I : Box) := (I.lo + I.hi) / 2
def Box.q₁ (I : Box) := (3 * I.lo + I.hi) / 4
def Box.q₃ (I : Box) := (I.lo + 3 * I.hi) / 4

inductive Branch where
  | left | middle | right
  deriving DecidableEq, Repr

def choose (v e : Rat) : Branch :=
  if e ≤ v then .left else if v ≤ -e then .right else .middle

def update (I : Box) : Branch → Box
  | .left => ⟨I.lo, I.mid⟩
  | .middle => ⟨I.q₁, I.q₃⟩
  | .right => ⟨I.mid, I.hi⟩

theorem width_update (I : Box) (s : Branch) :
    (update I s).width = I.width / 2 := by
  cases s <;> simp [update, Box.width, Box.mid, Box.q₁, Box.q₃] <;> grind

theorem nested_update (I : Box) (h : I.lo ≤ I.hi) (s : Branch) :
    I.lo ≤ (update I s).lo ∧ (update I s).lo ≤ (update I s).hi ∧
      (update I s).hi ≤ I.hi := by
  cases s <;> simp [update, Box.mid, Box.q₁, Box.q₃] <;> grind

def GoodAt {rad : Nat → Rat} (f : Rat → Scalar rad) (I : Box) (t : Nat) : Prop :=
  (f I.lo).atPrec t - rad t ≤ 0 ∧ 0 ≤ (f I.hi).atPrec t + rad t

/-- The inherited endpoints are needed only at the fixed test precision t. -/
theorem goodAt_update {rad : Nat → Rat} (f : Rat → Scalar rad)
    (I : Box) (p t : Nat) (old : GoodAt f I t)
    (g₁ : Gap (2 * rad p) (f I.q₁) (f I.mid))
    (g₃ : Gap (2 * rad p) (f I.mid) (f I.q₃)) :
    GoodAt f (update I (choose ((f I.mid).atPrec p) (rad p))) t := by
  obtain ⟨hl, hr⟩ := old
  unfold choose
  split
  · exact ⟨hl, by
      have := (f I.mid).consistent p t
      change 0 ≤ (f I.mid).atPrec t + rad t
      grind⟩
  · split
    · exact ⟨by
        have := (f I.mid).consistent t p
        change (f I.mid).atPrec t - rad t ≤ 0
        grind, hr⟩
    · have lo := g₁ t p
      have hi := g₃ p t
      change (f I.q₁).atPrec t - rad t ≤ 0 ∧ 0 ≤ (f I.q₃).atPrec t + rad t
      grind

def run {rad : Nat → Rat} (f : Rat → Scalar rad) (precision : Nat → Nat)
    (initial : Box) : Nat → Box
  | 0 => initial
  | n + 1 =>
      let I := run f precision initial n
      let p := precision n
      update I (choose ((f I.mid).atPrec p) (rad p))

/-- A rational, quantifier-free invariant for every fixed t. -/
theorem goodAt_run {rad : Nat → Rat} (f : Rat → Scalar rad)
    (precision : Nat → Nat) (initial : Box) (t : Nat) (h0 : GoodAt f initial t)
    (gaps : ∀ n, let I := run f precision initial n
                 let d := 2 * rad (precision n)
                 Gap d (f I.q₁) (f I.mid) ∧ Gap d (f I.mid) (f I.q₃)) :
    ∀ n, GoodAt f (run f precision initial n) t := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih => exact goodAt_update _ _ _ _ ih (gaps n).1 (gaps n).2

theorem width_run {rad : Nat → Rat} (f : Rat → Scalar rad)
    (precision : Nat → Nat) (initial : Box) (n : Nat) :
    (run f precision initial n).width = initial.width * ((1/2 : Rat)^n) := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
    simp only [run, width_update, ih]
    grind

/-- Compatible forward modulus gives a finite residual bound at the midpoint. -/
theorem residual_at {rad : Nat → Rat} (f : Rat → Scalar rad)
    (I : Box) (t : Nat) (e : Rat) (bracket : GoodAt f I t)
    (fromLeft : (f I.mid).atPrec t ≤ (f I.lo).atPrec t + e + 2 * rad t)
    (fromRight : (f I.hi).atPrec t ≤ (f I.mid).atPrec t + e + 2 * rad t) :
    -(e + 3 * rad t) ≤ (f I.mid).atPrec t ∧
      (f I.mid).atPrec t ≤ e + 3 * rad t := by
  obtain ⟨hl, hr⟩ := bracket
  grind

/-- A single sufficiently accurate pair of tests rules out disjoint sign brackets. -/
theorem no_cross {rad : Nat → Rat} (x y : Scalar rad) (p : Nat) (δ : Rat)
    (xPos : 0 ≤ x.atPrec p + rad p) (yNeg : y.atPrec p - rad p ≤ 0)
    (hgap : Gap δ x y) (small : 4 * rad p < δ) : False := by
  have := hgap p p
  grind

def eps (k : Nat) : Rat := (1/2 : Rat)^k

def unitBox : Box := ⟨0, 1⟩

def InverseBound (f : Rat → Scalar eps) (g : Nat → Nat) : Prop :=
  ∀ k x y, 0 ≤ x → y ≤ 1 → eps k ≤ y - x → Gap (eps (g k)) (f x) (f y)

def schedule (g : Nat → Nat) (n : Nat) : Nat := g (n+2) + 1

theorem eps_succ (n : Nat) : eps (n+1) = eps n / 2 := by
  unfold eps
  grind

theorem inside_run {rad : Nat → Rat} (f : Rat → Scalar rad)
    (p : Nat → Nat) (n : Nat) :
    let I := run f p unitBox n
    0 ≤ I.lo ∧ I.lo ≤ I.hi ∧ I.hi ≤ 1 := by
  induction n with
  | zero => change (0 : Rat) ≤ 0 ∧ (0 : Rat) ≤ 1 ∧ (1 : Rat) ≤ 1; decide
  | succ n ih =>
    simp only [run]
    have h := nested_update _ ih.2.1 (choose
      ((f (run f p unitBox n).mid).atPrec (p n)) (rad (p n)))
    exact ⟨Rat.le_trans ih.1 h.1, h.2.1, Rat.le_trans h.2.2 ih.2.2⟩

theorem goodAt_unit (f : Rat → Scalar eps) (g : Nat → Nat)
    (inverse : InverseBound f g) (t : Nat) (start : GoodAt f unitBox t) (n : Nat) :
    GoodAt f (run f (schedule g) unitBox n) t := by
  apply goodAt_run f _ _ t start _ n
  intro j
  let I := run f (schedule g) unitBox j
  have bounds : 0 ≤ I.lo ∧ I.lo ≤ I.hi ∧ I.hi ≤ 1 := inside_run f _ _
  have width : I.width = eps j := by
    have w := width_run f (schedule g) unitBox j
    change I.width = (1 - 0) * eps j at w
    grind
  have scale : eps (j+2) = eps j / 4 := by
    rw [eps_succ (j+1), eps_succ j]
    grind
  have h₁ := inverse (j+2) I.q₁ I.mid
  have h₃ := inverse (j+2) I.mid I.q₃
  have l : 0 ≤ I.q₁ := by unfold Box.q₁; grind
  have m₀ : 0 ≤ I.mid := by unfold Box.mid; grind
  have m₁ : I.mid ≤ 1 := by unfold Box.mid; grind
  have r : I.q₃ ≤ 1 := by unfold Box.q₃; grind
  have d₁ : eps (j+2) ≤ I.mid - I.q₁ := by
    unfold Box.width at width
    unfold Box.mid Box.q₁
    grind
  have d₃ : eps (j+2) ≤ I.q₃ - I.mid := by
    unfold Box.width at width
    unfold Box.mid Box.q₃
    grind
  have radius : 2 * eps (schedule g j) = eps (g (j+2)) := by
    unfold schedule
    rw [eps_succ]
    grind
  simpa only [radius] using And.intro (h₁ l m₁ d₁) (h₃ m₀ r d₃)

/-- Midpoints of overlapping boxes compare with the sum of their half-widths. -/
theorem mid_overlap (I J : Box) (h₁ : I.lo ≤ J.hi) (h₂ : J.lo ≤ I.hi) :
    -(I.width+J.width)/2 ≤ I.mid-J.mid ∧ I.mid-J.mid ≤ (I.width+J.width)/2 := by
  unfold Box.width Box.mid
  grind

theorem later_inside {rad : Nat → Rat} (f : Rat → Scalar rad) (p : Nat → Nat)
    (i d : Nat) :
    let I := run f p unitBox i
    let J := run f p unitBox (i+d)
    I.lo ≤ J.lo ∧ J.hi ≤ I.hi := by
  induction d with
  | zero => simp
  | succ d ih =>
    have h := nested_update _ (inside_run f p (i+d)).2.1
      (choose ((f (run f p unitBox (i+d)).mid).atPrec (p (i+d))) (rad (p (i+d))))
    exact ⟨Rat.le_trans ih.1 h.1, Rat.le_trans h.2.2 ih.2⟩

theorem later_midpoints {rad : Nat → Rat} (f : Rat → Scalar rad) (p : Nat → Nat)
    (i d : Nat) :
    let I := run f p unitBox i
    let J := run f p unitBox (i+d)
    (-(I.width)/2 ≤ I.mid-J.mid ∧ I.mid-J.mid ≤ I.width/2) := by
  have nest := later_inside f p i d
  have valid := (inside_run f p (i+d)).2.1
  dsimp only at nest ⊢
  unfold Box.width Box.mid
  grind


/-- A symmetric rational continuity contract, given here in one orientation. -/
def ForwardBound (f : Rat → Scalar eps) (μ : Nat → Nat) : Prop :=
  ∀ k x y i j, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 →
    x - y ≤ eps (μ k) → y - x ≤ eps (μ k) →
    (f x).atPrec i ≤ (f y).atPrec j + eps k + eps i + eps j

theorem eps_nonneg (n : Nat) : 0 ≤ eps n := by
  induction n with
  | zero => simp [eps]; decide
  | succ n ih => rw [eps_succ]; grind

theorem eps_later (n d : Nat) : eps (n + d) ≤ eps n := by
  induction d with
  | zero => exact Rat.le_refl
  | succ d ih =>
    rw [Nat.add_succ, eps_succ]
    have := eps_nonneg (n+d)
    grind

/-- The full scheduled residual bound on every sufficiently late output. -/
theorem residual_unit (f : Rat → Scalar eps) (g μ : Nat → Nat)
    (inverse : InverseBound f g) (forward : ForwardBound f μ)
    (start : ∀ t, GoodAt f unitBox t) (k d : Nat) :
    let I := run f (schedule g) unitBox (μ (k+1) + d)
    let z := (f I.mid).atPrec (k+3)
    (-(7 * eps k / 8) ≤ z ∧ z ≤ 7 * eps k / 8) := by
  let j := μ (k+1) + d
  let I := run f (schedule g) unitBox j
  let t := k+3
  have hI : 0 ≤ I.lo ∧ I.lo ≤ I.hi ∧ I.hi ≤ 1 := inside_run f _ _
  have w := width_run f (schedule g) unitBox j
  change I.hi-I.lo = (1-0) * eps j at w
  have bound : eps j ≤ eps (μ (k+1)) := eps_later _ _
  have h : I.hi-I.lo ≤ eps (μ (k+1)) := by grind
  have box : I.lo ≤ I.mid ∧ I.mid ≤ I.hi := by unfold Box.mid; grind
  have h₁ := forward (k+1) I.mid I.lo t t (by grind) (by grind)
    (by grind) (by grind) (by grind) (by grind)
  have h₂ := forward (k+1) I.hi I.mid t t (by grind) (by grind)
    (by grind) (by grind) (by grind) (by grind)
  have b := goodAt_unit f g inverse t (start t) j
  have result := residual_at f I t (eps (k+1)) b (by grind) (by grind)
  have e₁ := eps_succ k
  have e₂ := eps_succ (k+1)
  have e₃ : eps t = eps (k+2)/2 := eps_succ (k+2)
  change -(7 * eps k / 8) ≤ (f I.mid).atPrec t ∧ (f I.mid).atPrec t ≤ 7 * eps k / 8
  grind

end ConditionedZero

#print axioms ConditionedZero.goodAt_unit
#print axioms ConditionedZero.width_run
#print axioms ConditionedZero.later_midpoints
#print axioms ConditionedZero.residual_unit
#print axioms ConditionedZero.no_cross
