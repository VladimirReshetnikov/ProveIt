import GRHArticle.ProgressionFree.IntegerPrimeBlockFreeness
import GRHArticle.ProgressionFree.FinitePrimeBlockDensity
import GRHArticle.ProgressionFree.IntegerRoughTemplateDensity

/-!
# Smooth integer templates as rules on a prime block

Reconstructing an integer from the block exponents transfers local
progression-freeness. On an initial segment of primes the reconstructed
integer is exactly the smooth factor.
-/

namespace GRHArticle.ProgressionFree

open Finset

/-- The vectors of block exponents whose associated integer lies in the
given template. -/
def integerPrimeBlockPatterns (P : Finset ℕ) (F : Set ℕ) : Set (↥P → ℕ) :=
  {v | integerPrimeBlockProduct P v ∈ F}

/-- Progression-freeness of the integers in a template implies
progression-freeness of its block exponent patterns. -/
theorem kTermVectorAPFree_integerPrimeBlockPatterns {k : ℕ} (hk : 2 ≤ k)
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {F : Set ℕ} (hF : KTermGPFree k F) :
    KTermVectorAPFree k (integerPrimeBlockPatterns P F) := by
  intro x u d hx ha
  let a (i : Fin k) := integerPrimeBlockProduct P (x i)
  let v (p : ℕ) : ℤ := if h : p ∈ P then u ⟨p,h⟩ else 0
  let e (p : ℕ) : ℤ := if h : p ∈ P then d ⟨p,h⟩ else 0
  have hAff (i : Fin k) (p : ℕ) (_ : p.Prime) :
      ((a i).factorization p : ℤ) = v p + (i.val : ℤ)*e p := by
    rw [show (a i).factorization p = _ from factorization_integerPrimeBlockProduct hP (x i) p]
    by_cases hp : p ∈ P
    · simpa only [v,e,dif_pos hp] using ha i ⟨p,hp⟩
    · simp [v,e,hp]
  obtain ⟨b,r,hb,hr,hR,hstep⟩ := rationalGP_of_primeExponentAffine hk
    (fun i ↦ integerPrimeBlockProduct_ne_zero hP (x i)) hAff
  have hz := hstep (hF a b r hb hr (fun i ↦ hx i) hR)
  intro p
  simpa only [e,dif_pos p.property] using hz p.val (hP p.val p.property)

/-- Reconstructing the valuations of a positive integer on the primes at
most the cutoff yields its smooth part. -/
theorem integerPrimeBlockProduct_primesLE_eq_smoothPart (Y : ℕ) {n : ℕ} (hn : n ≠ 0) :
    integerPrimeBlockProduct (Nat.primesLE Y) (fun p ↦ n.factorization p.val) = integerSmoothPart Y n := by
  have hP : ∀ p ∈ Nat.primesLE Y, p.Prime := fun _ h ↦ Nat.prime_of_mem_primesLE h
  have hS := integerSmoothPart_mem Y n
  have hR := integerRoughPart_mem Y n
  apply Nat.factorization_inj (integerPrimeBlockProduct_ne_zero hP _) hS.1
  ext p
  rw [factorization_integerPrimeBlockProduct hP]
  by_cases hp : p.Prime
  · by_cases hpY : p ≤ Y
    · rw [dif_pos (Nat.mem_primesLE.mpr ⟨hpY,hp⟩)]
      have hzero : (integerRoughPart Y n).factorization p = 0 :=
        Nat.factorization_eq_zero_of_not_dvd fun hd ↦ (not_lt_of_ge hpY)
          (hR.2 p ((Nat.mem_primeFactorsList_iff_dvd hR.1 hp).mpr hd))
      have h := congrArg (fun j : ℕ ↦ j.factorization p) (integerSmoothPart_mul_roughPart Y hn)
      simpa only [Nat.factorization_mul hS.1 hR.1,Finsupp.add_apply,hzero,add_zero] using h.symm
    · rw [dif_neg (fun h ↦ hpY (Nat.mem_primesLE.mp h).1)]
      symm
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hd
      exact hpY (Nat.le_of_lt_succ (Nat.mem_smoothNumbers'.mp hS p hp hd))
  · rw [dif_neg (fun h ↦ hp (hP p h)),Nat.factorization_eq_zero_of_not_prime _ hp]

/-- Testing a smooth factor against a template agrees with the single
block consisting of all primes at most the cutoff. -/
theorem finitePrimeBlockRule_primesLE_eq_roughTemplate (Y : ℕ) {F : Set ℕ}
    (hF : F ⊆ Nat.smoothNumbers (Y+1)) (rules : (P : Finset ℕ) → Set (↥P → ℕ))
    (hRule : rules (Nat.primesLE Y) = integerPrimeBlockPatterns (Nat.primesLE Y) F) :
    finitePrimeBlockRule {Nat.primesLE Y} rules =
      integerRoughTemplateProducts (integerRoughNumbers Y) F := by
  ext n
  constructor
  · rintro ⟨hn,h⟩
    have he := h (Nat.primesLE Y) (mem_singleton_self _)
    rw [hRule] at he
    change integerPrimeBlockProduct (Nat.primesLE Y) (fun p ↦ n.factorization p.val) ∈ F at he
    rw [integerPrimeBlockProduct_primesLE_eq_smoothPart Y hn] at he
    refine ⟨integerRoughPart Y n,integerSmoothPart Y n,integerRoughPart_mem Y n,he,?_⟩
    rw [mul_comm,integerSmoothPart_mul_roughPart Y hn]
  · rintro ⟨r,s,hr,hs,rfl⟩
    have hn := mul_ne_zero hr.1 (hF hs).1
    refine ⟨hn,fun Q hQ ↦ ?_⟩
    obtain rfl := mem_singleton.mp hQ
    rw [hRule]
    change integerPrimeBlockProduct (Nat.primesLE Y) (fun p ↦ (r*s).factorization p.val) ∈ F
    rw [integerPrimeBlockProduct_primesLE_eq_smoothPart Y hn,integerSmoothPart_mul_of_parts hr (hF hs)]
    exact hs

end GRHArticle.ProgressionFree
