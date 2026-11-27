import GRHArticle.ProgressionFree.Density
import GRHArticle.ProgressionFree.IntegerPrefixTransfer

/-!
# Smooth and rough parts of positive integers
-/

namespace GRHArticle.ProgressionFree

/-- The positive integers all of whose prime factors are greater than `Y`. -/
def integerRoughNumbers (Y : ℕ) : Set ℕ :=
  {n | n ≠ 0 ∧ ∀ p ∈ n.primeFactorsList, Y < p}

/-- The product, with multiplicities, of the prime factors up to `Y`. -/
def integerSmoothPart (Y n : ℕ) : ℕ :=
  (n.primeFactorsList.filter fun p ↦ decide (p < Y+1)).prod

/-- The product, with multiplicities, of the prime factors above `Y`. -/
def integerRoughPart (Y n : ℕ) : ℕ :=
  (n.primeFactorsList.filter fun p ↦ !(decide (p < Y+1))).prod

theorem integerSmoothPart_mem (Y n : ℕ) :
    integerSmoothPart Y n ∈ Nat.smoothNumbers (Y+1) :=
  Nat.prod_mem_smoothNumbers n (Y+1)

theorem integerRoughPart_mem (Y n : ℕ) : integerRoughPart Y n ∈ integerRoughNumbers Y := by
  let L := n.primeFactorsList.filter fun p ↦ !(decide (p < Y+1))
  have hprime : ∀ p ∈ L, p.Prime := fun p hp ↦
    Nat.prime_of_mem_primeFactorsList (List.mem_filter.mp hp).1
  refine ⟨?_, ?_⟩
  · intro hz
    have h0 : 0 ∈ L := List.prod_eq_zero_iff.mp hz
    exact (hprime 0 h0).ne_zero rfl
  · intro p hp
    have hperm : L.Perm (Nat.primeFactorsList L.prod) := Nat.primeFactorsList_unique rfl hprime
    have hm := (List.mem_filter.mp ((hperm.mem_iff).mpr hp)).2
    by_contra! hY
    have hlt : p < Y+1 := by omega
    simp [hlt] at hm

theorem integerSmoothPart_mul_roughPart (Y : ℕ) {n : ℕ} (hn : n ≠ 0) :
    integerSmoothPart Y n * integerRoughPart Y n = n := by
  unfold integerSmoothPart integerRoughPart
  rw [← List.prod_append, (List.filter_append_perm _ _).prod_eq, Nat.prod_primeFactorsList hn]

theorem integerSmoothPart_mul_of_parts {Y g s : ℕ}
    (hg : g ∈ integerRoughNumbers Y) (hs : s ∈ Nat.smoothNumbers (Y+1)) :
    integerSmoothPart Y (g*s) = s := by
  have hp := (Nat.perm_primeFactorsList_mul hg.1 hs.1).filter (fun p ↦ decide (p < Y+1))
  unfold integerSmoothPart
  rw [hp.prod_eq, List.filter_append]
  have hnil : g.primeFactorsList.filter (fun p ↦ decide (p < Y+1)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro p hp hbad
    have hlt : p < Y+1 := of_decide_eq_true hbad
    have hgt := hg.2 p hp
    omega
  have hself : s.primeFactorsList.filter (fun p ↦ decide (p < Y+1)) =
      s.primeFactorsList := List.filter_eq_self.mpr (fun p hp ↦ decide_eq_true (hs.2 p hp))
  rw [hnil, hself, List.nil_append, Nat.prod_primeFactorsList hs.1]

theorem integerRoughPart_mul_of_parts {Y g s : ℕ}
    (hg : g ∈ integerRoughNumbers Y) (hs : s ∈ Nat.smoothNumbers (Y+1)) :
    integerRoughPart Y (g*s) = g := by
  have h := integerSmoothPart_mul_roughPart Y (mul_ne_zero hg.1 hs.1)
  rw [integerSmoothPart_mul_of_parts hg hs] at h
  exact Nat.mul_left_cancel (Nat.pos_of_ne_zero hs.1) (h.trans (mul_comm g s))

theorem integerRoughNumbers_eq_valuationCylinder (Y : ℕ) :
    integerRoughNumbers Y = valuationCylinder (Nat.primesLE Y) (fun _ ↦ 0) := by
  ext n
  constructor
  · rintro ⟨hn, hrough⟩
    refine ⟨hn, fun p hp ↦ Nat.factorization_eq_zero_of_not_dvd ?_⟩
    intro hd
    obtain ⟨hpY, hp⟩ := Nat.mem_primesLE.mp hp
    exact (not_lt_of_ge hpY) (hrough p ((Nat.mem_primeFactorsList_iff_dvd hn hp).mpr hd))
  · rintro ⟨hn, hzero⟩
    refine ⟨hn, fun p hp ↦ lt_of_not_ge ?_⟩
    intro hpY
    have hprime := Nat.prime_of_mem_primeFactorsList hp
    have hpos := hprime.factorization_pos_of_dvd hn (Nat.dvd_of_mem_primeFactorsList hp)
    exact hpos.ne' (hzero p (Nat.mem_primesLE.mpr ⟨hpY, hprime⟩))

/-- The rough integers have the finite Euler-product density used by the smooth
optimizations. -/
theorem hasNaturalDensity_integerRoughNumbers (Y : ℕ) :
    HasNaturalDensity (integerRoughNumbers Y) (integerSmoothDensityFactor Y) := by
  rw [integerRoughNumbers_eq_valuationCylinder]
  simpa only [pow_zero, mul_one, one_div, integerSmoothDensityFactor] using
    hasNaturalDensity_valuationCylinder (Nat.primesLE Y) (fun _ ↦ 0)
      (fun p hp ↦ (Nat.mem_primesLE.mp hp).2)

end GRHArticle.ProgressionFree
