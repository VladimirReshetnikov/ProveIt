import Std

/-!
# Finite identities for the Mertens function

The only dependency is the Lean 4 standard library. Every sum below
has lower endpoint 1. The Möbius table is built by primitive recursion
from its divisor characterization. The module `PrimeStep` proves that
this agrees with the prime-factor definition.
-/
namespace Mertens

private theorem cast_succ (n : Nat) : ((n+1 : Nat) : Int) = (n : Int)+1 := rfl

def sum (f : Nat → Int) : Nat → Int
  | 0 => 0
  | n + 1 => sum f n + f (n + 1)

theorem sum_congr {f g : Nat → Int} {n : Nat}
    (h : ∀ i, 0 < i → i ≤ n → f i = g i) : sum f n = sum g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sum, sum, ih (fun i hi hn => h i hi (by omega)), h (n+1) (by omega) (by omega)]

theorem sum_zero (n : Nat) : sum (fun _ => 0) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [sum, ih]

theorem sum_add (f g : Nat → Int) (n : Nat) :
    sum (fun i => f i + g i) n = sum f n + sum g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sum, ih]; omega

theorem sum_swap (f : Nat → Nat → Int) (m n : Nat) :
    sum (fun i => sum (f i) n) m = sum (fun j => sum (fun i => f i j) m) n := by
  induction m with
  | zero => simp [sum, sum_zero]
  | succ m ih =>
    simp only [sum, ih, sum_add]

theorem sum_prefix (f : Nat → Int) {r n : Nat} (h : r ≤ n) :
    sum (fun i => if i ≤ r then f i else 0) n = sum f r := by
  induction n with
  | zero => have : r = 0 := by omega
            subst r; rfl
  | succ n ih =>
    by_cases hr : r = n + 1
    · subst r
      exact sum_congr (fun i _ hi => if_pos hi)
    · have hr' : r ≤ n := by omega
      simp [sum, ih hr', show ¬ n + 1 ≤ r by omega]

theorem sum_const (z : Int) (n : Nat) : sum (fun _ => z) n = (n : Int) * z := by
  induction n with
  | zero => simp [sum]
  | succ n ih => simp [sum, ih, cast_succ, Int.add_mul]

theorem sum_initial (f : Nat → Int) (n : Nat) :
    sum f (n + 1) = f 1 + sum (fun k => f (k+1)) n := by
  induction n with
  | zero => simp [sum]
  | succ n ih => change sum f (n+1) + _ = f 1 + (sum _ n + _)
                 rw [ih, Int.add_assoc]

def delta (n : Nat) : Int := if n = 1 then 1 else 0

def divsum (f : Nat → Int) (x bound : Nat) : Int :=
  sum (fun d => if d ∣ x then f d else 0) bound

def next (a : Array Int) (n : Nat) : Int :=
  delta (n + 1) - divsum (fun d => (a[d]?).getD 0) (n+1) n

def table : Nat → Array Int
  | 0 => #[0]
  | n + 1 => (table n).push (next (table n) n)

theorem table_size (n : Nat) : (table n).size = n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [table, ih]

def mu (n : Nat) : Int := ((table n)[n]?).getD 0

def M (n : Nat) : Int := sum mu n

theorem table_stable {d n : Nat} (h : d ≤ n) :
    ((table n)[d]?).getD 0 = mu d := by
  induction n with
  | zero => have : d = 0 := by omega
            subst d; rfl
  | succ n ih =>
    by_cases hd : d = n + 1
    · subst d; rfl
    · have hle : d ≤ n := by omega
      have hi : d < (table n).size := by rw [table_size]; omega
      change (((table n).push (next (table n) n))[d]?).getD 0 = _
      rw [Array.getElem?_push_lt hi]
      have old := ih hle
      rw [getElem?_pos (table n) d hi] at old
      exact old

theorem mu_step (n : Nat) : mu (n+1) = delta (n+1) - divsum mu (n+1) n := by
  change (((table n).push (next (table n) n))[n+1]?).getD 0 = _
  have atEnd : (((table n).push (next (table n) n))[(table n).size]?) =
      some (next (table n) n) := by
    rw [getElem?_pos _ _ (by simp only [Array.size_push]; omega), Array.getElem_push_eq]
  rw [table_size] at atEnd
  rw [atEnd]
  change delta (n+1) - divsum (fun d => ((table n)[d]?).getD 0) (n+1) n = _
  congr 1
  apply sum_congr
  intro d _ hd
  simp [table_stable hd]

theorem mu_divsum (x : Nat) : divsum mu x x = delta x := by
  cases x with
  | zero => rfl
  | succ n =>
    change divsum mu (n+1) n + (if n+1 ∣ n+1 then mu (n+1) else 0) = _
    simp only [Nat.dvd_refl, if_pos, mu_step]
    omega

/-- A prime-factor implementation only needs a divisor-cancellation lemma
and a convention at zero in order to use all subsequent results. -/
theorem mu_unique (f : Nat → Int) (h0 : f 0 = 0)
    (hf : ∀ n, divsum f n n = delta n) (x : Nat) : f x = mu x := by
  induction x using Nat.strongRecOn with
  | ind x ih =>
    cases x with
    | zero => exact h0
    | succ n =>
      have hprev : divsum f (n+1) n = divsum mu (n+1) n := by
        apply sum_congr
        intro d _ hd
        simp [ih d (by omega)]
      have h := hf (n+1)
      change divsum f (n+1) n + (if n+1 ∣ n+1 then f (n+1) else 0) = _ at h
      simp only [Nat.dvd_refl, if_pos, hprev] at h
      rw [mu_step]
      omega

theorem M_zero : M 0 = 0 := rfl
theorem M_one : M 1 = 1 := rfl
theorem M_step (n : Nat) : M (n+1) = M n + mu (n+1) := rfl

/-- Derive the two quotient update rules from the bounds for Euclidean
division. Using those bounds directly keeps the axiom audit small. -/
theorem div_next_multiple {a d : Nat} (hd : d ∣ a+1) :
    (a+1)/d = a/d + 1 := by
  obtain ⟨k, hk⟩ := hd
  cases k with
  | zero => simp only [Nat.mul_zero] at hk; omega
  | succ k =>
    rw [Nat.mul_comm d, Nat.add_one_mul] at hk
    have hdpos : 0 < d := by
      cases d with
      | zero => simp at hk
      | succ d => omega
    have first : a/d = k := Nat.div_eq_of_lt_le (by omega) (by rw [Nat.add_one_mul]; omega)
    rw [first]
    exact Nat.div_eq_of_lt_le (by rw [Nat.add_one_mul]; omega)
      (by rw [Nat.add_one_mul, Nat.add_one_mul]; omega)

theorem div_next_other {a d : Nat} (hd : ¬ d ∣ a+1) :
    (a+1)/d = a/d := by
  cases d with
  | zero => simp only [Nat.div_zero]
  | succ d =>
    have hlt := (Nat.div_lt_iff_lt_mul (Nat.succ_pos d)).1 (Nat.lt_succ_self (a/(d+1)))
    have hne : a+1 ≠ (a/(d+1)+1)*(d+1) :=
      fun h => hd ⟨a/(d+1)+1, h.trans (Nat.mul_comm _ _)⟩
    change a < (a/(d+1)+1)*(d+1) at hlt
    have hhigh : a+1 < (a/(d+1)+1)*(d+1) := by omega
    exact Nat.div_eq_of_lt_le (Nat.le_trans (Nat.div_mul_le_self _ _) (Nat.le_succ a)) hhigh

theorem multiple_weight (d n : Nat) (z : Int) :
    sum (fun x => if d ∣ x then z else 0) n = ((n / d : Nat) : Int) * z := by
  induction n with
  | zero => simp [sum]
  | succ n ih =>
    by_cases h : d ∣ n+1
    · simp [sum, ih, h, div_next_multiple h, cast_succ, Int.add_mul]
    · simp [sum, ih, h, div_next_other h]

theorem divsum_pad (f : Nat → Int) {x n : Nat} (hx : 0 < x) (hn : x ≤ n) :
    divsum f x n = divsum f x x := by
  unfold divsum
  rw [← sum_prefix (fun d => if d ∣ x then f d else 0) hn]
  apply sum_congr
  intro d _ _
  by_cases hd : d ∣ x
  · simp [hd, Nat.le_of_dvd hx hd]
  · simp [hd]

theorem sum_delta (n : Nat) :
    sum delta (n+1) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => change sum delta (n+1) + delta (n+1+1) = _
                 rw [ih, delta, if_neg (by omega), Int.add_zero]

theorem weighted_floor_sum {n : Nat} (hn : 0 < n) :
    sum (fun d => ((n / d : Nat) : Int) * mu d) n = 1 := by
  calc
    _ = sum (fun d => sum (fun x => if d ∣ x then mu d else 0) n) n :=
      sum_congr (fun d _ _ => (multiple_weight d n (mu d)).symm)
    _ = sum (fun x => divsum mu x n) n :=
      sum_swap (fun d x => if d ∣ x then mu d else 0) n n
    _ = sum delta n := sum_congr (fun x hx hxn => (divsum_pad mu hx hxn).trans (mu_divsum x))
    _ = 1 := by cases n with
                | zero => omega
                | succ n => exact sum_delta n

/-- Summatory Dirichlet hyperbola swap with an arbitrary row weight. -/
theorem summatory_swap (f : Nat → Int) (n : Nat) :
    sum (fun k => sum f (n / k)) n = sum (fun d => ((n / d : Nat) : Int) * f d) n := by
  calc
    _ = sum (fun k => sum (fun d => if d ≤ n/k then f d else 0) n) n :=
      sum_congr (fun k _ _ => (sum_prefix f (Nat.div_le_self n k)).symm)
    _ = sum (fun d => sum (fun k => if d ≤ n/k then f d else 0) n) n :=
      sum_swap (fun k d => if d ≤ n/k then f d else 0) n n
    _ = _ := by
      apply sum_congr
      intro d hd _
      calc
        _ = sum (fun k => if k ≤ n/d then f d else 0) n := by
          apply sum_congr
          intro k hk _
          simp only [Nat.le_div_iff_mul_le hk, Nat.le_div_iff_mul_le hd, Nat.mul_comm d k]
        _ = sum (fun _ => f d) (n/d) := sum_prefix _ (Nat.div_le_self n d)
        _ = _ := sum_const _ _

theorem quotient_sum {n : Nat} (hn : 0 < n) :
    sum (fun k => M (n / k)) n = 1 :=
  (summatory_swap mu n).trans (weighted_floor_sum hn)

/-- Isolate the k=1 term. Each remaining quotient is smaller than n+1. -/
theorem quotient_recurrence (n : Nat) :
    M (n+1) = 1 - sum (fun k => M ((n+1) / (k+1))) n := by
  have h := quotient_sum (n := n+1) (by omega)
  rw [sum_initial] at h
  simp only [Nat.div_one] at h
  omega

/-- Remove the multiplier 1; the loop variable k runs through 1,...,n-1. -/
def properQuotients (f : Nat → Int) (n : Nat) : Int :=
  sum (fun k => f (n / (k+1))) (n-1)

def emptyTuple (n : Nat) : Int := if n = 0 then 0 else 1

/-- The first coordinate has values 2,...,n. The bound left for the
product of the remaining coordinates is the ordinary integer quotient. -/
def tupleCount : Nat → Nat → Int
  | 0 => emptyTuple
  | r+1 => properQuotients (tupleCount r)

def altSign : Nat → Int
  | 0 => 1
  | r+1 => - altSign r

def alternatingCount : Nat → Nat → Int
  | 0, n => emptyTuple n
  | r+1, n => alternatingCount r n + altSign (r+1) * tupleCount (r+1) n

theorem sum_scale (c : Int) (f : Nat → Int) (n : Nat) :
    sum (fun k => c * f k) n = c * sum f n := by
  induction n with
  | zero => simp [sum]
  | succ n ih => simp [sum, ih, Int.mul_add]

theorem alternating_unfold (r n : Nat) :
    alternatingCount (r+1) n = emptyTuple n - properQuotients (alternatingCount r) n := by
  induction r with
  | zero =>
    simp [alternatingCount, altSign, tupleCount, Int.sub_eq_add_neg]
  | succ r ih =>
    have hlin : properQuotients (alternatingCount (r+1)) n =
        properQuotients (alternatingCount r) n
        + altSign (r+1) * properQuotients (tupleCount (r+1)) n := by
      simp only [properQuotients, alternatingCount, sum_add, sum_scale]
    rw [hlin]
    change alternatingCount (r+1) n + -(altSign (r+1)) * properQuotients (tupleCount (r+1)) n = _
    rw [ih, Int.neg_mul]
    omega

theorem M_proper (n : Nat) : M n = emptyTuple n - properQuotients M n := by
  cases n with
  | zero => rfl
  | succ n => simpa [emptyTuple, properQuotients] using quotient_recurrence n

/-- A product of r positive factors of size at least 2 cannot be below 2^r. -/
theorem no_tuples {r n : Nat} (h : n < 2^r) : tupleCount r n = 0 := by
  induction r generalizing n with
  | zero =>
    have hn : n = 0 := by simpa using h
    subst n; rfl
  | succ r ih =>
    unfold tupleCount properQuotients
    rw [← sum_zero (n-1)]
    apply sum_congr
    intro k hk _
    apply ih
    apply (Nat.div_lt_iff_lt_mul (by omega : 0 < k+1)).2
    have hmul := Nat.mul_le_mul_left (2^r) (show 2 ≤ k+1 by omega)
    rw [Nat.pow_succ] at h
    omega

/-- The article's finite alternating series, with any sufficiently large
cutoff r. For n≥1 its smallest logarithmic cutoff is floor(log2 n). -/
theorem hyperboloid {r n : Nat} (h : n < 2^(r+1)) :
    M n = alternatingCount r n := by
  induction r generalizing n with
  | zero =>
    have hn : n = 0 ∨ n = 1 := by omega
    rcases hn with hn | hn <;> subst n <;> rfl
  | succ r ih =>
    rw [alternating_unfold, M_proper]
    congr 1
    apply sum_congr
    intro k hk _
    apply ih
    apply (Nat.div_lt_iff_lt_mul (by omega : 0 < k+1)).2
    have hmul := Nat.mul_le_mul_left (2^(r+1)) (show 2 ≤ k+1 by omega)
    rw [Nat.pow_succ] at h
    omega

/-- Reuse one array of coefficients, avoiding rebuilding the table for
every summand when evaluating examples. -/
def fastM (n : Nat) : Int :=
  let a := table n
  sum (fun k => (a[k]?).getD 0) n

theorem fastM_correct (n : Nat) : fastM n = M n :=
  sum_congr (fun _ _ hk => table_stable hk)

theorem at_ten : M 10 = -1 := by
  rw [← fastM_correct]
  decide

def convolution (f g : Nat → Int) (x : Nat) : Int :=
  sum (fun d => if d ∣ x then f d * g (x/d) else 0) x

theorem multiple_subsum (g : Nat → Int) (d n : Nat) :
    sum (fun x => if d ∣ x then g (x/d) else 0) n = sum g (n/d) := by
  induction n with
  | zero => simp [sum]
  | succ n ih =>
    by_cases h : d ∣ n+1
    · simp only [sum, ih, if_pos h, div_next_multiple h]
    · simp only [sum, ih, if_neg h, div_next_other h, Int.add_zero]

theorem product_region (f g : Nat → Int) {d n : Nat} (hd : 0 < d) :
    sum (fun k => if k*d ≤ n then f d * g k else 0) n = f d * sum g (n/d) := by
  calc
    _ = sum (fun k => if k ≤ n/d then f d * g k else 0) n := by
      apply sum_congr
      intro k _ _
      simp only [Nat.le_div_iff_mul_le hd]
    _ = sum (fun k => f d * g k) (n/d) := sum_prefix _ (Nat.div_le_self n d)
    _ = _ := sum_scale _ _ _

theorem weighted_hyperbola (f g : Nat → Int) (n : Nat) :
    sum (fun d => f d * sum g (n/d)) n = sum (fun k => g k * sum f (n/k)) n := by
  calc
    _ = sum (fun d => sum (fun k => if k*d ≤ n then f d * g k else 0) n) n :=
      sum_congr (fun _ hd _ => (product_region f g hd).symm)
    _ = sum (fun k => sum (fun d => if k*d ≤ n then f d * g k else 0) n) n :=
      sum_swap _ n n
    _ = _ := by
      apply sum_congr
      intro k hk _
      rw [← product_region g f hk]
      apply sum_congr
      intro d _ _
      simp only [Nat.mul_comm k d, Int.mul_comm (f d) (g k)]

theorem summatory_convolution (f g : Nat → Int) (n : Nat) :
    sum (convolution f g) n = sum (fun k => g k * sum f (n/k)) n := by
  calc
    _ = sum (fun x => sum (fun d => if d ∣ x then f d * g (x/d) else 0) n) n := by
      apply sum_congr
      intro x hx hxn
      exact (divsum_pad (fun d => f d * g (x/d)) hx hxn).symm
    _ = sum (fun d => sum (fun x => if d ∣ x then f d * g (x/d) else 0) n) n :=
      sum_swap _ n n
    _ = sum (fun d => f d * sum g (n/d)) n := by
      apply sum_congr
      intro d _ _
      calc
        _ = sum (fun x => f d * (if d ∣ x then g (x/d) else 0)) n := by
          apply sum_congr
          intro x _ _
          by_cases h : d ∣ x <;> simp [h]
        _ = _ := by rw [sum_scale, multiple_subsum]
    _ = _ := weighted_hyperbola f g n

/-- Euler's totient: count positive k ≤ x for which gcd(k,x)=1. -/
def phi (x : Nat) : Int := sum (fun k => delta (Nat.gcd k x)) x

theorem phi_convolution (x : Nat) : phi x = convolution mu (fun k => (k : Int)) x := by
  cases x with
  | zero => rfl
  | succ m =>
    let x := m+1
    have hx : 0 < x := Nat.succ_pos _
    change phi x = convolution mu (fun k => (k : Int)) x
    calc
      _ = sum (fun k => divsum mu (Nat.gcd k x) x) x := by
        apply sum_congr
        intro k _ _
        rw [divsum_pad mu (Nat.gcd_pos_of_pos_right k hx) (Nat.le_of_dvd hx (Nat.gcd_dvd_right k x)), mu_divsum]
      _ = sum (fun d => sum (fun k => if d ∣ Nat.gcd k x then mu d else 0) x) x :=
        sum_swap _ x x
      _ = _ := by
        apply sum_congr
        intro d _ _
        by_cases hd : d ∣ x
        · simpa [Nat.dvd_gcd_iff, hd, Int.mul_comm (mu d)] using
            multiple_weight d x (mu d)
        · simp [Nat.dvd_gcd_iff, hd, sum_zero]

theorem summatory_totient (n : Nat) :
    sum phi n = sum (fun k => (k : Int) * M (n/k)) n := by
  calc
    _ = sum (convolution mu (fun k => (k : Int))) n :=
      sum_congr (fun x _ _ => phi_convolution x)
    _ = _ := summatory_convolution _ _ n

end Mertens
