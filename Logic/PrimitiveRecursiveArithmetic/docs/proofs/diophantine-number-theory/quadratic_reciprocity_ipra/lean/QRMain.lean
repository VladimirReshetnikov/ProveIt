import QREuler
import QRGauss
import Supplements

namespace QR

/-- Gauss's lemma with no remaining arithmetic premises besides prime, odd and unit. -/
theorem gauss {p a : Nat} (hp : primeB p=true) (hop : p%2=1) (ha : a%p≠0) :
    GaussLaw p a := gauss_of_euler hp hop ha (euler_criterion hp hop ha)

/-- Quadratic reciprocity as a numerical equality of parity bits. -/
theorem reciprocity {p q : Nat} (hp : primeB p=true) (hq : primeB q=true)
    (hop : p%2=1) (hoq : q%2=1) (hne : p≠q) :
    (nonresBit p q + nonresBit q p)%2 = (half p * half q)%2 :=
  reciprocity_of_euler hp hq hop hoq hne
    (euler_criterion hp hop (unit_at_distinct_primes hp hq hne))
    (euler_criterion hq hoq (unit_at_distinct_primes hq hp (Ne.symm hne)))

/-- Traditional signed Legendre symbol, with denominator as first argument. -/
def legendre (p a : Nat) : Int :=
  if a%p=0 then 0 else if squareB p a then 1 else -1

private theorem neg_one_pow (n : Nat) :
    (-1 : Int)^n = (if n%2=0 then 1 else -1) := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Int.pow_succ, ih]
    split <;> split <;> omega

theorem legendre_sign {p a : Nat} (ha : a%p≠0) :
    legendre p a = (-1 : Int)^(nonresBit p a) := by
  simp [legendre, nonresBit, ha]; split <;> decide

private theorem neg_one_pow_add (s t : Nat) :
    (-1 : Int)^(s+t) = (-1 : Int)^s * (-1 : Int)^t := by
  rw [neg_one_pow, neg_one_pow, neg_one_pow]
  split <;> split <;> split <;> omega

/-- The usual signed product formula. -/
theorem legendre_reciprocity {p q : Nat} (hp : primeB p=true) (hq : primeB q=true)
    (hop : p%2=1) (hoq : q%2=1) (hne : p≠q) :
    legendre p q * legendre q p = (-1 : Int)^(half p * half q) := by
  rw [legendre_sign (unit_at_distinct_primes hp hq hne),
    legendre_sign (unit_at_distinct_primes hq hp (Ne.symm hne)), ← neg_one_pow_add,
    neg_one_pow, neg_one_pow, reciprocity hp hq hop hoq hne]

theorem legendre_neg_one {p : Nat} (hp : primeB p=true) (hop : p%2=1) :
    legendre p (p-1) = (-1 : Int)^(half p) := by
  have hp1 := (primeB_spec.mp hp).1
  have hu : (p-1)%p ≠ 0 := by rw [Nat.mod_eq_of_lt (by omega)]; omega
  have hg := gauss hp hop hu
  unfold GaussLaw at hg
  rw [legendre_sign hu, neg_one_pow, neg_one_pow, hg, highCount_neg_one p (by omega), Nat.mod_mod]

theorem legendre_two {p : Nat} (hp : primeB p=true) (hop : p%2=1) :
    legendre p 2 = (-1 : Int)^((p*p-1)/8) := by
  have hp1 := (primeB_spec.mp hp).1
  have hu : 2%p ≠ 0 := by rw [Nat.mod_eq_of_lt (by omega)]; omega
  have hg := gauss hp hop hu
  unfold GaussLaw at hg
  rw [legendre_sign hu, neg_one_pow, neg_one_pow, hg, Nat.mod_mod, highCount_two_exponent p hop]

/-- Extension to any integer numerator by taking its Euclidean remainder. -/
def legendreZ (p : Nat) (a : Int) : Int := legendre p ((a % (p : Int)).toNat)

theorem legendreZ_ofNat (p a : Nat) : legendreZ p (a : Int) = legendre p a := by
  simp only [legendreZ, ← Int.ofNat_emod, Int.toNat_ofNat, legendre, squareB, Nat.mod_mod]

theorem legendreZ_neg_one {p : Nat} (hp : primeB p=true) (hop : p%2=1) :
    legendreZ p (-1) = (-1 : Int)^(half p) := by
  have hp1 := (primeB_spec.mp hp).1
  have h : (-1 : Int) % (p : Int) = (p : Int)-1 := by
    calc
      _ = ((p : Int) + (-1)) % (p : Int) := Int.add_emod_self_left.symm
      _ = _ := Int.emod_eq_of_lt (by omega) (by omega)
  have ht : ((p : Int)-1).toNat = p-1 := by omega
  simp only [legendreZ, h, ht, legendre_neg_one hp hop]

end QR

