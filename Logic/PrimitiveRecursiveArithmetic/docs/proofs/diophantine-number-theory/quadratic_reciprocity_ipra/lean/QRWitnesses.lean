import QREuler

namespace QR

/-- First square root at indices below `n`, with sentinel `n`. -/
def rootPrefix (p a : Nat) : Nat → Nat
  | 0 => 0
  | n+1 =>
    let w := rootPrefix p a n
    if w < n then w else if n*n % p = a % p then n else n+1

def leastRoot (p a : Nat) := rootPrefix p a p

private theorem prefix_bound (p a n : Nat) : rootPrefix p a n ≤ n := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih => simp only [rootPrefix]; split <;> first | omega | (split <;> omega)

private theorem prefix_sound (p a n : Nat) : rootPrefix p a n < n →
    rootPrefix p a n * rootPrefix p a n % p = a % p := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [rootPrefix]
    split
    · rename_i h; exact fun _ => ih h
    · split <;> simp_all

private theorem prefix_min (p a x n : Nat) (hx : x*x % p = a % p) :
    x < n → rootPrefix p a n ≤ x := by
  induction n with
  | zero => omega
  | succ n ih =>
    intro hx'
    by_cases h : x < n
    · have hmin := ih h
      simp only [rootPrefix, show rootPrefix p a n < n by omega, if_true]
      exact hmin
    · have he : x = n := by omega
      subst x
      simp only [rootPrefix, hx, if_true]
      split <;> omega

/-- Bounded square-root extraction, including the least-witness property. -/
theorem leastRoot_spec (p a : Nat) :
    leastRoot p a ≤ p ∧
    (leastRoot p a < p ↔ squareB p a = true) ∧
    (leastRoot p a < p → leastRoot p a * leastRoot p a % p = a % p) ∧
    (∀ x, x < p → x*x % p = a % p → leastRoot p a ≤ x) := by
  unfold leastRoot
  refine ⟨prefix_bound p a p, ⟨?_,?_⟩, prefix_sound p a p, ?_⟩
  · intro h
    exact squareB_spec.mpr ⟨_,h,prefix_sound _ _ _ h⟩
  · intro h
    obtain ⟨x,hx,hs⟩ := squareB_spec.mp h
    exact Nat.lt_of_le_of_lt (prefix_min _ _ _ _ hs hx) hx
  · intro x hx hs
    exact prefix_min _ _ _ _ hs hx

/-- If the Legendre bit is zero, this term is a certified square root. -/
theorem root_of_bit_zero {p a : Nat} (h : nonresBit p a = 0) :
    leastRoot p a < p ∧ leastRoot p a * leastRoot p a % p = a % p := by
  have hb : squareB p a = true := by
    cases he : squareB p a <;> simp_all [nonresBit]
  have hs := leastRoot_spec p a
  have hlt := hs.2.1.mpr hb
  exact ⟨hlt,hs.2.2.1 hlt⟩

theorem no_root_of_bit_one {p a : Nat} (h : nonresBit p a = 1) :
    ∀ x, x < p → x*x % p ≠ a % p := by
  intro x hx hr
  have hs := squareB_spec.mpr ⟨x,hx,hr⟩
  simp [nonresBit,hs] at h

/-- The explicit square root for primes congruent to three modulo four. -/
theorem fast_root {p a : Nat} (hp : primeB p = true) (hp4 : p%4 = 3)
    (ha : a%p ≠ 0) (hs : squareB p a = true) :
    let x := a^((p+1)/4) % p
    x*x % p = a % p := by
  have he := euler_criterion hp (show p%2=1 by omega) ha
  simp [hs] at he
  have hexp : (p+1)/4 + (p+1)/4 = half p + 1 := by unfold half; omega
  change (a^((p+1)/4)%p) * (a^((p+1)/4)%p) % p = a % p
  rw [← Nat.mul_mod, ← Nat.pow_add, hexp, Nat.pow_succ, Nat.mul_mod, he]
  simp

example : leastRoot 7 11 = 2 := by decide
example : leastRoot 11 7 = 11 := by decide

end QR
