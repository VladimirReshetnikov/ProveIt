import Std

/-!
# Finite triangular inversion and the Möbius function

Rows and columns are numbered from zero. Row i in the divisor specialization
is the positive integer i+1. The proofs use only the bundled Lean libraries.
-/
namespace FiniteInversion

/-- Sum f(0) through f(N-1). -/
def total (f : Nat → Int) : Nat → Int
  | 0 => 0
  | n + 1 => total f n + f n

theorem total_congr {f g : Nat → Int} {n : Nat}
    (h : ∀ i, i < n → f i = g i) : total f n = total g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [total]
    rw [ih (fun i hi => h i (by omega)), h n (by omega)]

abbrev Weight := Nat → Nat → Int
abbrev Sequence := Nat → Int

/-- The strictly lower part of an integer weight matrix. -/
def lower (w : Weight) (f : Sequence) (i : Nat) :=
  total (fun j => w i j * f j) i

theorem lower_congr (w : Weight) {f g : Sequence} {i : Nat}
    (h : ∀ j, j < i → f j = g j) : lower w f i = lower w g i := by
  exact total_congr (fun j hj => by rw [h j hj])

/-- Discrete integration on a lower triangular matrix whose diagonal is one. -/
def integrate (w : Weight) (f : Sequence) (i : Nat) := f i + lower w f i

/-- Finite-depth substitution; the theorem below removes the arbitrary depth. -/
def approx (w : Weight) (g : Sequence) : Nat → Sequence
  | 0 => fun _ => 0
  | t + 1 => fun i => g i - lower w (approx w g t) i

theorem stable_step (w : Weight) (g : Sequence) (t i : Nat) (hi : i < t) :
    approx w g t i = approx w g (t + 1) i := by
  induction t generalizing i with
  | zero => omega
  | succ t ih =>
    simp only [approx]
    congr 1
    exact lower_congr w (fun j hj => ih j (by omega))

theorem stable (w : Weight) (g : Sequence) {t u i : Nat}
    (hi : i < t) (htu : t ≤ u) : approx w g t i = approx w g u i := by
  induction u with
  | zero => omega
  | succ u ih =>
    by_cases he : t = u + 1
    · rw [he]
    · exact (ih (by omega)).trans (stable_step w g u i (by omega))

def invert (w : Weight) (g : Sequence) (i : Nat) := approx w g (i + 1) i

theorem invert_row (w : Weight) (g : Sequence) (i : Nat) :
    invert w g i = g i - lower w (invert w g) i := by
  change g i - lower w (approx w g i) i = _
  congr 1
  apply lower_congr
  intro j hj
  exact (stable w g (i := j) (t := j+1) (u := i) (by omega) (by omega)).symm

theorem integrate_invert (w : Weight) (g : Sequence) (i : Nat) :
    integrate w (invert w g) i = g i := by
  unfold integrate
  rw [invert_row w g i]
  omega

theorem invert_integrate (w : Weight) (f : Sequence) (i : Nat) :
    invert w (integrate w f) i = f i := by
  induction i using Nat.strongRecOn with
  | ind i ih =>
    rw [invert_row]
    rw [lower_congr w (fun j hj => ih j hj)]
    unfold integrate
    omega

/-- A solution of the triangular system is unique on every initial segment. -/
theorem unique_prefix (w : Weight) (f g : Sequence) (N : Nat)
    (h : ∀ i, i < N → integrate w f i = g i) :
    ∀ i, i < N → f i = invert w g i := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
    intro hi
    have hrow := h i hi
    have hlow : lower w f i = lower w (invert w g) i :=
      lower_congr w (fun j hj => ih j hj (by omega))
    unfold integrate at hrow
    rw [invert_row]
    omega

/-- Shift positive integer d to column d-1. -/
def dividesWeight (i j : Nat) : Int :=
  if (i + 1) % (j + 1) = 0 then 1 else 0

def delta (i : Nat) : Int := if i = 0 then 1 else 0

/-- This convention gives mu(0)=0 and the divisor-recurrence sequence for n≥1. -/
def mu : Nat → Int
  | 0 => 0
  | i + 1 => invert dividesWeight delta i

def divisorSum (f : Nat → Int) (i : Nat) : Int :=
  integrate dividesWeight (fun j => f (j + 1)) i

theorem divisor_cancellation (i : Nat) :
    divisorSum mu i = (if i = 0 then 1 else 0) :=
  integrate_invert dividesWeight delta i

theorem divisor_characterization (f : Nat → Int) (N : Nat)
    (h : ∀ i, i < N → divisorSum f i = delta i) (i : Nat) (hi : i < N) :
    f (i + 1) = mu (i + 1) :=
  unique_prefix dividesWeight (fun j => f (j+1)) delta N h i hi

example : (List.range 13).map mu = [0,1,-1,-1,0,-1,1,-1,0,0,1,-1,0] := by decide

/-- Signed length-r chains, ending in the value of g at the starting column.
The edge j→i has weight w i j. -/
def chainTerm (w : Weight) (g : Sequence) : Nat → Sequence
  | 0 => g
  | r + 1 => fun i => -lower w (chainTerm w g r) i

theorem total_sub (f g : Sequence) (n : Nat) :
    total (fun i => f i - g i) n = total f n - total g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [total, ih]
    omega

theorem lower_sub (w : Weight) (f g : Sequence) (i : Nat) :
    lower w (fun j => f j - g j) i = lower w f i - lower w g i := by
  unfold lower
  simp only [Int.mul_sub]
  exact total_sub _ _ _

theorem lower_zero_of (w : Weight) (f : Sequence) (i : Nat)
    (h : ∀ j, j < i → f j = 0) : lower w f i = 0 := by
  unfold lower
  apply Eq.trans (b := total (fun _ => 0) i)
  · exact total_congr (fun j hj => by simp [h j hj])
  · clear h
    induction i with
    | zero => rfl
    | succ i ih => simp [total, ih]

/-- Every strict chain ending at row i has length at most i. -/
theorem chainTerm_zero (w : Weight) (g : Sequence) (r i : Nat) (h : i < r) :
    chainTerm w g r i = 0 := by
  induction r generalizing i with
  | zero => omega
  | succ r ih =>
    simp only [chainTerm]
    rw [lower_zero_of w _ i (fun j hj => ih j (by omega))]
    decide

theorem chain_difference (w : Weight) (g : Sequence) (t i : Nat) :
    approx w g (t+1) i - approx w g t i = chainTerm w g t i := by
  induction t generalizing i with
  | zero =>
    simp only [approx, chainTerm]
    rw [lower_zero_of w _ i (fun _ _ => rfl)]
    omega
  | succ t ih =>
    change (g i - lower w (approx w g (t+1)) i) -
      (g i - lower w (approx w g t) i) = -lower w (chainTerm w g t) i
    have eq := lower_congr w (i := i) (fun j _ => ih j)
    rw [lower_sub] at eq
    omega

/-- The finite chain expansion is the same number as triangular substitution. -/
theorem chain_sum (w : Weight) (g : Sequence) (t i : Nat) :
    total (fun r => chainTerm w g r i) t = approx w g t i := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [total, ih]
    have := chain_difference w g t i
    omega

theorem invert_chain_sum (w : Weight) (g : Sequence) (i : Nat) :
    invert w g i = total (fun r => chainTerm w g r i) (i+1) :=
  (chain_sum w g (i+1) i).symm

theorem mobius_chain_sum (i : Nat) :
    mu (i+1) = total (fun r => chainTerm dividesWeight delta r i) (i+1) :=
  invert_chain_sum dividesWeight delta i

end FiniteInversion

/-! Independent factorization calculation on an exponent vector.
A coordinate j in a sub-vector is an exponent of a divisor.
On each prime the local Möbius values are 1,-1,0,0,... . -/
namespace ExponentBox

open FiniteInversion

def localMu : Nat → Int
  | 0 => 1
  | 1 => -1
  | _ + 2 => 0

def vectorMu : List Nat → Int
  | [] => 1
  | e :: es => localMu e * vectorMu es

/-- Enumerate all divisor exponent vectors, coordinatewise, with no duplicates. -/
def boxSum (f : List Nat → Int) : List Nat → Int
  | [] => f []
  | e :: es => total (fun j => boxSum (fun js => f (j :: js)) es) (e+1)

theorem total_scale (c : Int) (g : Sequence) (N : Nat) :
    total (fun i => c * g i) N = c * total g N := by
  induction N with
  | zero => simp [total]
  | succ N ih => simp only [total, ih, Int.mul_add]

theorem local_cancel (e : Nat) :
    total localMu (e+1) = (if e = 0 then 1 else 0) := by
  induction e with
  | zero => rfl
  | succ e ih =>
    cases e with
    | zero => rfl
    | succ e =>
      change total localMu (e+2) + 0 = 0
      have h : total localMu (e+2) = 0 := by
        simpa only [Nat.succ_ne_zero, if_false] using ih
      rw [h]
      rfl

theorem box_scale (c : Int) (f : List Nat → Int) (es : List Nat) :
    boxSum (fun v => c * f v) es = c * boxSum f es := by
  induction es generalizing f with
  | nil => rfl
  | cons e es ih =>
    simp only [boxSum]
    rw [← total_scale]
    exact total_congr (fun i _ => ih (fun v => f (i :: v)))

/-- Empty exponents represent 1. Zero coordinates may also be retained. -/
def unitIndicator : List Nat → Int
  | [] => 1
  | e :: es => (if e = 0 then 1 else 0) * unitIndicator es

theorem box_cancellation (es : List Nat) :
    boxSum vectorMu es = unitIndicator es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [boxSum, unitIndicator]
    have hc : total (fun j => boxSum (fun js => vectorMu (j::js)) es) (e+1) =
        total (fun j => unitIndicator es * localMu j) (e+1) := by
      apply total_congr
      intro i _
      change boxSum (fun js => localMu i * vectorMu js) es = _
      rw [box_scale, ih, Int.mul_comm]
    rw [hc, total_scale, local_cancel, Int.mul_comm]

end ExponentBox
