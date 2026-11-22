import Std

/-! A finite rational Kantorovich dual certificate on an ordered grid.
All sums are prefix recursions. A potential drops by its increment along
each edge. No separation, optimization oracle, or measure theory is used. -/
namespace LineDual

abbrev Row := Nat → Rat

/-- Sum the first `n` entries (the sum over the empty prefix is zero). -/
def pref (row : Row) : Nat → Rat
  | 0 => 0
  | n + 1 => pref row n + row n

/-- Zero discrepancy takes the positive-width tie branch. -/
def signStep (d w : Rat) : Rat := if 0 ≤ d then w else -w

theorem signStep_feasible {d w : Rat} (hw : 0 ≤ w) :
    (signStep d w).abs = w := by
  unfold signStep
  split <;> simp [Rat.abs_neg, Rat.abs_of_nonneg hw]

theorem edge_exact (d w : Rat) :
    d * signStep d w = w * d.abs := by
  unfold signStep
  split
  next h => rw [Rat.abs_of_nonneg h, Rat.mul_comm]
  next h =>
    have hd : d ≤ 0 := Rat.le_total.resolve_left h
    rw [Rat.abs_of_nonpos hd, Rat.mul_neg, Rat.mul_neg, Rat.mul_comm]

theorem edge_bound {d w v : Rat} (hv : v.abs ≤ w) :
    d * v ≤ w * d.abs := by
  have hplus : v ≤ v.abs := by
    unfold Rat.abs
    split <;> grind
  have hminus : -v ≤ v.abs := by
    unfold Rat.abs
    split <;> grind
  by_cases hd : 0 ≤ d
  · rw [Rat.abs_of_nonneg hd, Rat.mul_comm w]
    exact Rat.mul_le_mul_of_nonneg_left (Rat.le_trans hplus hv) hd
  · have hd' : d ≤ 0 := Rat.le_total.resolve_left hd
    have hn : 0 ≤ -d := by grind
    have hh := Rat.mul_le_mul_of_nonneg_left (Rat.le_trans hminus hv) hn
    rw [Rat.abs_of_nonpos hd', Rat.mul_comm w]
    simpa [Rat.neg_mul, Rat.mul_neg] using hh

/-- The signed objective and the absolute transport cost have one term per edge. -/
def score (d v : Row) (n : Nat) : Rat := pref (fun i => d i * v i) n
def cost (d w : Row) (n : Nat) : Rat := pref (fun i => w i * (d i).abs) n

theorem optimal (d w : Row) (n : Nat) :
    score d (fun i => signStep (d i) (w i)) n = cost d w n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change score d (fun i => signStep (d i) (w i)) n +
      d n * signStep (d n) (w n) = cost d w n + w n * (d n).abs
    rw [ih, edge_exact]

theorem upper (d v w : Row) (n : Nat) (hv : ∀ i, i < n → (v i).abs ≤ w i) :
    score d v n ≤ cost d w n := by
  induction n with
  | zero => exact Rat.le_refl
  | succ n ih =>
    have hs := ih (fun i hi => hv i (Nat.lt_trans hi (Nat.lt_succ_self n)))
    have he := edge_bound (d := d n) (hv n (Nat.lt_succ_self n))
    change score d v n + d n * v n ≤ cost d w n + w n * (d n).abs
    exact Rat.le_trans (Rat.add_le_add_right.mpr hs) (Rat.add_le_add_left.mpr he)

/-- `n` edges join `n+1` vertices. The last mass need not balance. -/
theorem abel (mass phi : Row) (n : Nat) :
    pref (fun i => mass i * phi i) (n+1) =
      pref mass (n+1) * phi n +
      score (fun i => pref mass (i+1)) (fun i => phi i - phi (i+1)) n := by
  induction n with
  | zero => simp [pref, score, Rat.zero_add, Rat.add_zero]
  | succ n ih =>
    let d := pref mass (n+1)
    let e := score (fun i => pref mass (i+1)) (fun i => phi i - phi (i+1)) n
    change pref (fun i => mass i * phi i) (n+1) + mass (n+1) * phi (n+1) =
      (d + mass (n+1)) * phi (n+1) + (e + d * (phi n - phi (n+1)))
    rw [ih]
    change d * phi n + e + mass (n+1) * phi (n+1) =
      (d + mass (n+1)) * phi (n+1) + (e + d * (phi n - phi (n+1)))
    grind

/-- Integrate the signed drops, fixing the leftmost potential to zero. -/
def potential (inc : Row) (i : Nat) : Rat := -pref inc i

theorem potential_drop (inc : Row) (i : Nat) :
    potential inc i - potential inc (i+1) = inc i := by
  change -pref inc i - -(pref inc i + inc i) = inc i
  grind

/-- Signed vertex masses of total zero admit a maximizing potential. -/
theorem dual_attained (mass w : Row) (n : Nat)
    (balance : pref mass (n+1) = 0) (hw : ∀ i, i < n → 0 ≤ w i) :
    ∃ phi : Row,
      (∀ i, i < n → (phi i - phi (i+1)).abs ≤ w i) ∧
      pref (fun i => mass i * phi i) (n+1) =
        cost (fun i => pref mass (i+1)) w n := by
  let d : Row := fun i => pref mass (i+1)
  let inc : Row := fun i => signStep (d i) (w i)
  refine ⟨potential inc, ?_, ?_⟩
  · intro i hi
    rw [potential_drop, show (inc i).abs = w i from signStep_feasible (hw i hi)]
    exact Rat.le_refl
  · rw [abel, balance, Rat.zero_mul, Rat.zero_add]
    simp only [potential_drop]
    exact optimal d w n

theorem dual_upper (mass w phi : Row) (n : Nat) (balance : pref mass (n+1) = 0)
    (hphi : ∀ i, i < n → (phi i - phi (i+1)).abs ≤ w i) :
    pref (fun i => mass i * phi i) (n+1) ≤ cost (fun i => pref mass (i+1)) w n := by
  rw [abel, balance, Rat.zero_mul, Rat.zero_add]
  exact upper _ _ _ n hphi

end LineDual

namespace LineDual.Scaled

/-- Clearing one positive denominator for discrepancies and one for lengths
reduces the arithmetic at each edge to this integer certificate. -/
def signedWidth (d w : Int) : Int := if 0 ≤ d then w else -w

def magnitude (d : Int) : Int := if 0 ≤ d then d else -d

theorem edge_certificate (d w : Int) (hw : 0 ≤ w) :
    -w ≤ signedWidth d w ∧ signedWidth d w ≤ w ∧
    d * signedWidth d w = w * magnitude d ∧
    ∀ v, -w ≤ v → v ≤ w → d * v ≤ d * signedWidth d w := by
  have hww := Int.le_trans (Int.neg_nonpos_of_nonneg hw) hw
  cases (inferInstance : Decidable (0 ≤ d)) with
  | isTrue hd =>
    simp only [signedWidth, magnitude, if_pos hd]
    exact ⟨hww, Int.le_refl _, Int.mul_comm _ _,
      fun _ _ hv => Int.mul_le_mul_of_nonneg_left hv hd⟩
  | isFalse hd =>
    simp only [signedWidth, magnitude, if_neg hd]
    refine ⟨Int.le_refl _, hww, ?_, fun _ hv _ =>
      Int.mul_le_mul_of_nonpos_left (Int.le_of_not_le hd) hv⟩
    rw [Int.mul_neg, Int.mul_neg, Int.mul_comm]

/-- The polynomial identity for one induction step of summation by parts;
`d` is the old prefix mass and `e` the preceding edge sum. -/
theorem abel_step (d e m u v : Int) :
    d * u + e + m * v = (d + m) * v + (e + d * (u - v)) := by
  rw [Int.add_mul, Int.mul_sub]
  omega

end LineDual.Scaled
