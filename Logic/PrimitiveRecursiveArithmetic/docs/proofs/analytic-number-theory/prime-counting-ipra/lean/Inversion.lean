import Std

/-! Finite divisor-incidence inversion for prime-power counting.
The sums range from 1 through the bound, inclusively. -/
namespace PrimeCounting.Inversion

def sumI : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | n + 1, f => sumI n f + f (n + 1)

theorem sumI_congr (n : Nat) (f g : Nat → Int)
    (h : ∀ i, 1 ≤ i → i ≤ n → f i = g i) :
    sumI n f = sumI n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumI]
    rw [ih (fun i hi hn => h i hi (by omega)), h (n+1) (by omega) (by omega)]

theorem sumI_zero (n : Nat) : sumI n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [sumI, ih]

theorem sumI_add (n : Nat) (f g : Nat → Int) :
    sumI n (fun i => f i + g i) = sumI n f + sumI n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sumI, ih]; omega

theorem sumI_mul_right (n : Nat) (f : Nat → Int) (v : Int) :
    sumI n (fun i => f i * v) = sumI n f * v := by
  induction n with
  | zero => simp [sumI]
  | succ n ih => simp only [sumI, ih, Int.add_mul]

theorem sumI_mul_left (n : Nat) (v : Int) (f : Nat → Int) :
    sumI n (fun i => v * f i) = v * sumI n f := by
  simpa only [Int.mul_comm v] using sumI_mul_right n f v

theorem sumI_swap (m n : Nat) (f : Nat → Nat → Int) :
    sumI m (fun i => sumI n (f i)) = sumI n (fun j => sumI m (fun i => f i j)) := by
  induction m with
  | zero => simp [sumI, sumI_zero]
  | succ m ih =>
    simp only [sumI, ih]
    exact (sumI_add n _ _).symm

/-- The Möbius function from the proper-divisor recurrence. -/
def mobius : Nat → Int
  | 0 => 0
  | 1 => 1
  | n + 2 => -sumI (n+1) (fun d =>
      if h : d < n+2 then (if d ∣ n+2 then mobius d else 0) else 0)
termination_by n => n

theorem divisor_sum (n : Nat) (hn : 0 < n) :
    sumI n (fun d => if d ∣ n then mobius d else 0) =
      (if n = 1 then 1 else 0) := by
  match n with
  | 0 => omega
  | 1 => simp [sumI, mobius]
  | n+2 =>
    have rec_eq : mobius (n+2) =
        -sumI (n+1) (fun d => if d ∣ n+2 then mobius d else 0) := by
      rw [mobius]
      congr 1
      apply sumI_congr
      intro d _ hd
      simp [show d < n+2 by omega]
    change sumI (n+1) _ + (if n+2 ∣ n+2 then mobius (n+2) else 0) = _
    simp [rec_eq] <;> omega

theorem divisor_sum_extend (n l : Nat) (hn : 0 < n) (hl : n ≤ l) :
    sumI l (fun d => if d ∣ n then mobius d else 0) =
      (if n = 1 then 1 else 0) := by
  induction l with
  | zero => omega
  | succ l ih =>
    by_cases h : n ≤ l
    · have nd : ¬ l+1 ∣ n := fun hd => by
        have := Nat.le_of_dvd hn hd
        omega
      simp [sumI, nd, ih h]
    · have eq : l+1 = n := by omega
      simpa [eq] using divisor_sum n hn

theorem sumI_first (l : Nat) (hl : 0 < l) (w : Nat → Int) :
    sumI l (fun j => if j = 1 then w j else 0) = w 1 := by
  cases l with
  | zero => exact False.elim (Nat.not_lt_zero _ hl)
  | succ l =>
    clear hl
    induction l with
    | zero => exact Int.zero_add (w 1)
    | succ l ih =>
      change sumI (l+1) _ + (if l+1+1 = 1 then _ else 0) = _
      rw [if_neg (by omega), Int.add_zero, ih]

/-- The integral-linear form of finite inversion. For an endpoint and a
prime, take w(j) to be an integer multiple of its cut weight divided by j. -/
theorem power_inversion (l : Nat) (hl : 0 < l) (w : Nat → Int) :
    sumI l (fun k => mobius k * sumI l (fun j => if k ∣ j then w j else 0)) = w 1 := by
  calc
    _ = sumI l (fun k => sumI l (fun j => mobius k * (if k ∣ j then w j else 0))) := by
      apply sumI_congr; intro k _ _; exact (sumI_mul_left _ _ _).symm
    _ = sumI l (fun j => sumI l (fun k => mobius k * (if k ∣ j then w j else 0))) :=
      sumI_swap _ _ _
    _ = sumI l (fun j => if j = 1 then w j else 0) := by
      apply sumI_congr; intro j hj hjl
      calc
        _ = sumI l (fun k => (if k ∣ j then mobius k else 0) * w j) := by
          apply sumI_congr; intro k _ _; split <;> simp_all
        _ = _ := by
          rw [sumI_mul_right, divisor_sum_extend j l (by omega) hjl]
          split <;> simp_all
    _ = _ := sumI_first _ hl _

/-- Numerator of the half-weight cut at x=A/B. Below x has weight two. -/
def twiceCut (a b m : Nat) : Int :=
  if b*m < a then 2 else if b*m = a then 1 else 0

def fac : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * fac n

/-- mark may be instantiated with any Boolean primality test. -/
def twiceCount (mark : Nat → Bool) (a b e : Nat) : Int :=
  sumI (a/b) (fun p => if mark p then twiceCut a b (p^e) else 0)

/-- For b,d,k>0 and a sufficiently large l, this is 2 l! J(dk;x)/k.
Its divisor indexing avoids irrational roots at midpoint endpoints. -/
def scaledJRow (mark : Nat → Bool) (a b d l k : Nat) : Int :=
  sumI l (fun j => if k ∣ j then
    Int.ofNat (fac l / j) * twiceCount mark a b (d*j) else 0)

theorem midpoint_inversion (mark : Nat → Bool) (a b d l : Nat) (hl : 0 < l) :
    sumI l (fun k => mobius k * scaledJRow mark a b d l k) =
      Int.ofNat (fac l) * twiceCount mark a b d := by
  simpa only [scaledJRow, Nat.div_one, Nat.mul_one] using
    power_inversion l hl (fun j => Int.ofNat (fac l / j) * twiceCount mark a b (d*j))

#eval (List.range 11).map mobius
#print axioms midpoint_inversion

end PrimeCounting.Inversion
