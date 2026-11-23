import Std

/-!
Pointwise cancellation and the complete outer inclusion-exclusion sum.
A mark is any executable Boolean test on an element of the interval.
Subsets are subsequences indexed by positions, so the theorem even allows
repeated marks. No primality or coprimality assumption enters this identity.
-/
namespace PrimeCounting.Sieve

variable {α : Type}

/-- Enumerate all binary choices, preserving the order of chosen positions. -/
def subsets : List α → List (List α)
  | [] => [[]]
  | a :: as => subsets as ++ (subsets as).map (a :: ·)

theorem subsets_length (as : List α) : (subsets as).length = 2 ^ as.length := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp [subsets, ih, Nat.pow_succ, Nat.mul_two]

def sign : List α → Int
  | [] => 1
  | _ :: as => -sign as

theorem sign_length (s : List α) : sign s = (-1 : Int) ^ s.length := by
  induction s with
  | nil => rfl
  | cons a as ih => simp [sign, ih, Int.pow_succ]

def alternating (as : List α) (f : List α → Int) : Int :=
  ((subsets as).map (fun s => sign s * f s)).sum

private theorem sumNeg {β : Type} (xs : List β) (f : β → Int) :
    (xs.map (fun x => -f x)).sum = -(xs.map f).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; omega

private theorem sumAppend (xs ys : List Int) :
    (xs ++ ys).sum = xs.sum + ys.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.cons_append, List.sum_cons, ih]; omega

theorem alternating_cons (a : α) (as : List α) (f : List α → Int) :
    alternating (a :: as) f = alternating as f - alternating as (fun s => f (a :: s)) := by
  simp only [alternating, subsets, List.map_append, sumAppend, List.map_map,
    Function.comp_def, sign, Int.neg_mul]
  change _ + ((subsets as).map (fun s => -(sign s * f (a :: s)))).sum = _
  rw [sumNeg]
  omega

private theorem sumAdd {β : Type} (xs : List β) (f g : β → Int) :
    (xs.map (fun x => f x + g x)).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; omega

theorem alternating_add (as : List α) (f g : List α → Int) :
    alternating as (fun s => f s + g s) = alternating as f + alternating as g := by
  simp only [alternating, Int.mul_add]
  exact sumAdd _ _ _

private theorem alternating_zero (as : List α) :
    alternating as (fun _ => 0) = 0 := by
  induction as with
  | nil => rfl
  | cons a as ih => rw [alternating_cons]; simp

def tick (b : Bool) : Int := if b then 1 else 0

def allHit (hit : α → Nat → Bool) (s : List α) (n : Nat) : Int :=
  tick (s.all (fun a => hit a n))

def survives (hit : α → Nat → Bool) (s : List α) (n : Nat) : Int :=
  tick (s.all (fun a => !(hit a n)))

theorem pointwise (hit : α → Nat → Bool) (as : List α) (n : Nat) :
    alternating as (fun s => allHit hit s n) = survives hit as n := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    rw [alternating_cons]
    cases h : hit a n with
    | false =>
      have hz : (fun s : List α => allHit hit (a :: s) n) = (fun _ => 0) := by
        funext s
        simp [allHit, h, tick]
      rw [hz, alternating_zero, Int.sub_zero, ih]
      simp [survives, h]
    | true =>
      have he : (fun s : List α => allHit hit (a :: s) n) =
          (fun s => allHit hit s n) := by
        funext s
        simp [allHit, h]
      rw [he, Int.sub_self]
      simp [survives, tick, h]

/-- Sum the indicated integer weights over 1,...,N inclusive. -/
def prefixSum (w : Nat → Int) : Nat → Int
  | 0 => 0
  | n + 1 => prefixSum w n + w (n + 1)

/-- Full Legendre inclusion-exclusion for any finite list of Boolean marks. -/
theorem inclusion_exclusion (hit : α → Nat → Bool) (as : List α) (N : Nat) :
    alternating as (fun s => prefixSum (allHit hit s) N) =
      prefixSum (survives hit as) N := by
  induction N with
  | zero => exact alternating_zero _
  | succ n ih => simp only [prefixSum, alternating_add, ih, pointwise]

/-- In particular, sieve the positive integers by any list of moduli. -/
theorem divisibility_sieve (ds : List Nat) (N : Nat) :
    alternating ds (fun s => prefixSum (fun n => tick (s.all (fun d => n % d == 0))) N) =
      prefixSum (fun n => tick (ds.all (fun d => !(n % d == 0)))) N :=
  inclusion_exclusion (fun d n => n % d == 0) ds N

/-- The empty intersection uses modulus one. -/
def commonModulus : List Nat → Nat
  | [] => 1
  | d :: ds => Nat.lcm d (commonModulus ds)

theorem commonModulus_dvd (s : List Nat) (n : Nat) :
    commonModulus s ∣ n ↔ ∀ d ∈ s, d ∣ n := by
  induction s with
  | nil => simp [commonModulus]
  | cons d ds ih =>
    simp only [commonModulus, List.forall_mem_cons]
    constructor
    · intro h
      exact ⟨Nat.dvd_trans (Nat.dvd_lcm_left _ _) h,
        ih.mp (Nat.dvd_trans (Nat.dvd_lcm_right _ _) h)⟩
    · rintro ⟨hd, ht⟩
      exact Nat.lcm_dvd hd (ih.mpr ht)

theorem multiple_count (d N : Nat) :
    prefixSum (fun n => tick (n % d == 0)) N = (N / d : Nat) := by
  induction N with
  | zero => simp [prefixSum]
  | succ n ih =>
    rw [prefixSum, ih]
    cases d with
    | zero => simp [tick]
    | succ d =>
      let b := d + 1
      change (↑(n / b) + tick ((n + 1) % b == 0)) = ↑((n + 1) / b)
      have hb : 0 < b := Nat.zero_lt_succ d
      have hr := Nat.mod_lt n hb
      have dec : n + 1 = b * (n / b) + (n % b + 1) := by
        have := Nat.div_add_mod n b
        omega
      rw [dec, Nat.mul_add_div hb, Nat.mul_add_mod]
      by_cases small : n % b + 1 < b
      · simp [Nat.div_eq_of_lt small, Nat.mod_eq_of_lt small, tick]
      · have carry : n % b + 1 = b := by omega
        simp [carry, Nat.div_self hb, tick]

theorem common_count (s : List Nat) (N : Nat) :
    prefixSum (fun n => tick (s.all (fun d => n % d == 0))) N =
      (N / commonModulus s : Nat) := by
  have he : (fun n => tick (s.all (fun d => n % d == 0))) =
      (fun n => tick (n % commonModulus s == 0)) := by
    funext n
    simp [tick, List.all_eq_true, ← Nat.dvd_iff_mod_eq_zero, commonModulus_dvd]
  rw [he, multiple_count]

/-- Full floor form, valid for arbitrary moduli via their subset lcm. -/
theorem floor_sieve (ds : List Nat) (N : Nat) :
    alternating ds (fun s => (N / commonModulus s : Nat)) =
      prefixSum (fun n => tick (ds.all (fun d => !(n % d == 0)))) N := by
  have h := divisibility_sieve ds N
  simpa only [common_count] using h

#print axioms inclusion_exclusion
#print axioms divisibility_sieve
#print axioms floor_sieve
end PrimeCounting.Sieve
