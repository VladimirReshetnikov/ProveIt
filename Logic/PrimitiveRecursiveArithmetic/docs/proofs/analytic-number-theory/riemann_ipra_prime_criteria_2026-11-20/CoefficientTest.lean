import SymmetricPrefixes

/-! Constructive coefficient and signed-value tests for the characteristic
polynomial of a finite list of signed excesses. Lists omit the leading one. -/
namespace RiemannIPRA.CoefficientTest
open RiemannIPRA.Discrete RiemannIPRA.SymmetricPrefixes

/-- Lower coefficients in ascending order; the leading coefficient is one. -/
def evaluate : List Int → Int → Int
  | [], _ => 1
  | a::rest, x => a + x*evaluate rest x

/-- Coefficients of carry + (X+s)P, with the leading one implicit. -/
def adjoin (s carry : Int) : List Int → List Int
  | [] => [carry+s]
  | a::rest => (carry+s*a)::adjoin s a rest

theorem evaluate_adjoin (s carry x : Int) (p : List Int) :
    evaluate (adjoin s carry p) x = carry + (x+s)*evaluate p x := by
  induction p generalizing carry with
  | nil => simp [adjoin,evaluate]; ring
  | cons a rest ih => simp only [adjoin,evaluate,ih]; ring

def coefficients (a b : Nat → Nat) : Nat → List Int
  | 0 => []
  | i+1 => adjoin ((b i : Int) - a i) 0 (coefficients a b i)

def nonnegative (p : List Int) := ∀ x ∈ p, 0 ≤ x

private theorem nonneg_adjoin {s carry : Int} {p : List Int} (hs : 0 ≤ s)
    (hc : 0 ≤ carry) (hp : nonnegative p) : nonnegative (adjoin s carry p) := by
  induction p generalizing carry with
  | nil => simp [adjoin,nonnegative]; omega
  | cons a p ih =>
    have ha := hp a (by simp)
    have ht : nonnegative p := fun t h => hp t (by simp [h])
    intro t h
    rcases List.mem_cons.mp h with rfl | h
    · exact Int.add_nonneg hc (Int.mul_nonneg hs ha)
    · exact ih ha ht _ h

private theorem nonneg_of_good (a b : Nat → Nat) (n : Nat) (h : ∀ i < n, a i ≤ b i) :
    nonnegative (coefficients a b n) := by
  induction n with
  | zero => simp [coefficients,nonnegative]
  | succ n ih =>
    have hn := h n (by omega)
    exact nonneg_adjoin (by omega) (by decide) (ih (fun i hi => h i (by omega)))

private theorem eval_pos (p : List Int) (h : nonnegative p) {x : Int} (hx : 0 < x) :
    0 < evaluate p x := by
  induction p with
  | nil => simp [evaluate]
  | cons a p ih =>
    have ha := h a (by simp)
    have hp : nonnegative p := fun t h' => h t (by simp [h'])
    have := Int.mul_pos hx (ih hp)
    change 0 < a+x*evaluate p x
    omega

private theorem eval_root (a b : Nat → Nat) {n i : Nat} (hi : i < n) :
    evaluate (coefficients a b n) ((a i : Int) - b i) = 0 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [coefficients,evaluate_adjoin]
    by_cases he : i=n
    · subst i; ring
    · rw [ih (by omega)]; simp

private theorem le_total (a : Nat → Nat) {n i : Nat} (hi : i < n) : a i ≤ total a n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [total]
    by_cases he : i=n
    · subst i; omega
    · have := ih (by omega); omega

/-- Signed evaluations on the finite integer grid give a sufficient and
necessary condition. -/
theorem grid_iff (a b : Nat → Nat) (n : Nat) :
    (∀ t : Nat, 0 < t → t ≤ total a n → 0 < evaluate (coefficients a b n) t)
      ↔ ∀ i < n, a i ≤ b i := by
  constructor
  · intro h i hi
    by_cases hg : a i ≤ b i
    · exact hg
    · have hu := le_total a hi
      have hp := h (a i - b i) (by omega) (by omega)
      have he : ((a i-b i : Nat) : Int) = (a i : Int)-b i := by omega
      rw [he, eval_root a b hi] at hp
      omega
  · intro h t ht _
    exact eval_pos _ (nonneg_of_good a b n h) (by omega)

/-- Every lower coefficient of the finite characteristic polynomial is
nonnegative iff all local inequalities hold. -/
theorem coefficients_iff (a b : Nat → Nat) (n : Nat) :
    nonnegative (coefficients a b n) ↔ ∀ i < n, a i ≤ b i := by
  refine ⟨fun h => (grid_iff a b n).mp (fun t ht _ => ?_), nonneg_of_good a b n⟩
  exact eval_pos _ h (by omega)

end RiemannIPRA.CoefficientTest
