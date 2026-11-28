import GRHArticle.ProgressionFree.PolynomialExceptionalPrimeBounds
import Mathlib.Algebra.Ring.GeomSum

/-!
# Exceptional primes in the full polynomial degree ball

Every nonzero polynomial belongs to one degree and one nonzero
leading-coefficient class. Summing the uniform exceptional bound over
these classes gives the degree-ball estimate.
-/

namespace GRHArticle.ProgressionFree

open Polynomial Finset
open scoped BigOperators Classical

/-- The monic irreducibles of exactly the indicated degree. -/
noncomputable def polynomialDegreePrimes (F : Type*) [Field F] [Fintype F] (d : ℕ) : Finset F[X] :=
  (polynomialSmoothPrimes F d).filter (fun p ↦ p.natDegree = d)

/-- The nonzero polynomials through degree `N` above the degree-`d` threshold. -/
noncomputable def polynomialExceptionalBall (F : Type*) [Field F] [Fintype F] (N d : ℕ) : Finset F[X] :=
  (polynomialDegreeLTFinset F (N+1)).filter (fun g ↦ g ≠ 0 ∧
    polynomialExceptionalThreshold F d ≤ ((polynomialDegreePrimes F d).filter (· ∣ g)).card)

variable {F : Type*} [Field F] [Fintype F]

theorem mem_polynomialDegreePrimes {p : F[X]} {d : ℕ} :
    p ∈ polynomialDegreePrimes F d ↔ p.Monic ∧ Irreducible p ∧ p.natDegree = d := by
  simp only [polynomialDegreePrimes, mem_filter, mem_polynomialSmoothPrimes]
  exact ⟨fun ⟨⟨hm,hi,_⟩,he⟩ ↦ ⟨hm,hi,he⟩, fun ⟨hm,hi,he⟩ ↦ ⟨⟨hm,hi,he.le⟩,he⟩⟩

theorem card_polynomialDegreePrimes (F : Type*) [Field F] [Fintype F] (d : ℕ) :
    (polynomialDegreePrimes F d).card = polynomialIrreducibleCount F d := rfl

theorem mem_polynomialExceptionalBall {N d : ℕ} {g : F[X]} :
    g ∈ polynomialExceptionalBall F N d ↔ g ≠ 0 ∧ g.natDegree ≤ N ∧
      polynomialExceptionalThreshold F d ≤ ((polynomialDegreePrimes F d).filter (· ∣ g)).card := by
  simp only [polynomialExceptionalBall, mem_filter, mem_polynomialDegreeLTFinset]
  constructor
  · rintro ⟨hdeg,hg,h⟩
    rw [degree_eq_natDegree hg, Nat.cast_lt] at hdeg
    exact ⟨hg,Nat.le_of_lt_succ hdeg,h⟩
  · rintro ⟨hg,hn,h⟩
    refine ⟨?_,hg,h⟩
    rw [degree_eq_natDegree hg, Nat.cast_lt]
    exact Nat.lt_succ_of_le hn

/-- The bound with the exact number of nonzero polynomials in the ball. -/
theorem card_polynomialExceptionalBall_le_nonzero (F : Type*) [Field F] [Fintype F]
    (hq : 16 ≤ Fintype.card F) (N d : ℕ) (hd : 0 < d) :
    ((polynomialExceptionalBall F N d).card : ℝ) ≤ ((Fintype.card F : ℝ)^(N+1)-1) *
      polynomialExceptionalBound (Fintype.card F) d := by
  classical
  let q := Fintype.card F
  let Q := (q : ℝ)
  let B := polynomialExceptionalBound q d
  let A (n : ℕ) (u : Fˣ) := (polynomialDegreeLayer F n).filter (fun g ↦ g.leadingCoeff = (u : F) ∧
    polynomialExceptionalThreshold F d ≤ ((polynomialDegreePrimes F d).filter (· ∣ g)).card)
  let U (n : ℕ) := (univ : Finset Fˣ).biUnion (A n)
  have hsub : polynomialExceptionalBall F N d ⊆ (range (N+1)).biUnion U := by
    intro g hg
    obtain ⟨hg0,hn,ht⟩ := mem_polynomialExceptionalBall.mp hg
    let u := Units.mk0 g.leadingCoeff (leadingCoeff_ne_zero.mpr hg0)
    refine mem_biUnion.mpr ⟨g.natDegree,mem_range.mpr (Nat.lt_succ_of_le hn),?_⟩
    exact mem_biUnion.mpr ⟨u,mem_univ _,mem_filter.mpr ⟨mem_polynomialDegreeLayer.mpr ⟨hg0,rfl⟩,rfl,ht⟩⟩
  have hcount : (polynomialExceptionalBall F N d).card ≤
      ∑ n ∈ range (N+1), ∑ u : Fˣ, (A n u).card := by
    calc
      _ ≤ ((range (N+1)).biUnion U).card := Finset.card_le_card hsub
      _ ≤ ∑ n ∈ range (N+1), (U n).card := card_biUnion_le
      _ ≤ _ := sum_le_sum (fun n _ ↦ card_biUnion_le)
  have hq0 : 0 < Q := Nat.cast_pos.mpr Fintype.card_pos
  have hA (n : ℕ) (u : Fˣ) : ((A n u).card : ℝ) ≤ Q^n * B := by
    have he : ((A n u).card : ℝ)/Q^n ≤ B :=
      leadingCoeffLayer_exceptional_prime_bound u hq d n hd
    exact ((div_le_iff₀ (pow_pos hq0 n)).mp he).trans_eq (mul_comm _ _)
  have hcast : ((Fintype.card F-1 : ℕ) : ℝ) = Q-1 := by
    rw [Nat.cast_sub (by exact Fintype.card_pos), Nat.cast_one]
  change ((polynomialExceptionalBall F N d).card : ℝ) ≤ (Q^(N+1)-1)*B
  calc
    _ ≤ ∑ n ∈ range (N+1), ∑ u : Fˣ, ((A n u).card : ℝ) := by exact_mod_cast hcount
    _ ≤ ∑ n ∈ range (N+1), ∑ _u : Fˣ, Q^n*B := sum_le_sum fun n _ ↦ sum_le_sum fun u _ ↦ hA n u
    _ = (∑ n ∈ range (N+1), Q^n) * (Q-1)*B := by
      simp only [sum_const, card_univ, nsmul_eq_mul, Fintype.card_units, hcast]
      rw [sum_mul, sum_mul]
      apply sum_congr rfl
      intro n _
      ring
    _ = _ := by rw [geom_sum_mul]

/-- Exceptional count in the whole degree ball, uniform in all its layers. -/
theorem card_polynomialExceptionalBall_le (F : Type*) [Field F] [Fintype F]
    (hq : 16 ≤ Fintype.card F) (N d : ℕ) (hd : 0 < d) :
    ((polynomialExceptionalBall F N d).card : ℝ) ≤ (Fintype.card F : ℝ)^(N+1) *
      polynomialExceptionalBound (Fintype.card F) d :=
  (card_polynomialExceptionalBall_le_nonzero F hq N d hd).trans
    (mul_le_mul_of_nonneg_right (sub_le_self _ zero_le_one) (by unfold polynomialExceptionalBound; positivity))

/-- Summing over degrees `1` through `D` costs at most `D` times the
uniform linear-rate bound. -/
theorem sum_card_polynomialExceptionalBall_le (F : Type*) [Field F] [Fintype F]
    (hq : 16 ≤ Fintype.card F) (N D : ℕ) :
    (∑ d ∈ Icc 1 D, ((polynomialExceptionalBall F N d).card : ℝ)) ≤
      (D : ℝ) * (Fintype.card F : ℝ)^(N+1) * (Fintype.card F : ℝ)⁻¹^(Fintype.card F-14) := by
  let q := Fintype.card F
  let Q := (q : ℝ)
  change _ ≤ (D : ℝ)*Q^(N+1)*Q⁻¹^(q-14)
  calc
    _ ≤ ∑ d ∈ Icc 1 D, Q^(N+1)*Q⁻¹^(q-14) := by
      apply sum_le_sum
      intro d hd
      exact (card_polynomialExceptionalBall_le F hq N d (mem_Icc.mp hd).1).trans
        (mul_le_mul_of_nonneg_left (polynomialExceptionalBound_le_linear hq d) (by positivity))
    _ = _ := by simp [Nat.card_Icc, mul_assoc]

end GRHArticle.ProgressionFree
