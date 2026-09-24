import Diophantine.Paper1976.RefinedTwelveVariablePolynomial
import Diophantine.Paper1976.FiveSquarePrimePolynomial
import Diophantine.Common.RefinedRelationCombiningDegree

/-!
# Concrete degree certificates for the refined prime polynomials

The bounds follow the construction of each polynomial. They use only the
degree inequalities for sums, products, and powers, preserving the capital
abbreviations instead of expanding the resulting polynomials.
-/

namespace JSWW1976.RefinedPolynomialDegrees

open MvPolynomial
open TwelveVariable (Poly capitals radicands uPolynomial marginPolynomial)

noncomputable section

private theorem deg_X (i : Fin 12) : (X i : Poly).totalDegree ≤ 1 := by simp

private theorem deg_nat (n : ℕ) : (n : Poly).totalDegree ≤ 0 := by
  rw [← map_natCast (MvPolynomial.C : ℤ →+* Poly) n]
  exact le_of_eq (totalDegree_C (n : ℤ))

private theorem deg_add {p q : Poly} {a b : ℕ}
    (hp : p.totalDegree ≤ a) (hq : q.totalDegree ≤ b) :
    (p + q).totalDegree ≤ max a b :=
  (totalDegree_add _ _).trans (max_le_max hp hq)

private theorem deg_sub {p q : Poly} {a b : ℕ}
    (hp : p.totalDegree ≤ a) (hq : q.totalDegree ≤ b) :
    (p - q).totalDegree ≤ max a b :=
  (totalDegree_sub _ _).trans (max_le_max hp hq)

private theorem deg_mul {p q : Poly} {a b : ℕ}
    (hp : p.totalDegree ≤ a) (hq : q.totalDegree ≤ b) :
    (p * q).totalDegree ≤ a + b :=
  (totalDegree_mul _ _).trans (Nat.add_le_add hp hq)

private theorem deg_pow {p : Poly} {a : ℕ}
    (hp : p.totalDegree ≤ a) (n : ℕ) : (p ^ n).totalDegree ≤ n * a :=
  (totalDegree_pow _ _).trans (Nat.mul_le_mul_left n hp)

private theorem deg_add_nat {p : Poly} {a : ℕ} (hp : p.totalDegree ≤ a) (n : ℕ) :
    (p + n).totalDegree ≤ a := by
  simpa only [Nat.max_eq_left (Nat.zero_le a)] using deg_add hp (deg_nat n)

private theorem deg_sub_nat {p : Poly} {a : ℕ} (hp : p.totalDegree ≤ a) (n : ℕ) :
    (p - n).totalDegree ≤ a := by
  simpa only [Nat.max_eq_left (Nat.zero_le a)] using deg_sub hp (deg_nat n)

private theorem deg_nat_mul {p : Poly} {a : ℕ} (n : ℕ) (hp : p.totalDegree ≤ a) :
    ((n : Poly) * p).totalDegree ≤ a := by
  simpa only [zero_add] using deg_mul (deg_nat n) hp

/-- Select a bound before substituting the large polynomial expressions.
The case split therefore treats all five entries as opaque variables. -/
private theorem deg_vector_five {p₀ p₁ p₂ p₃ p₄ : Poly} {a₀ a₁ a₂ a₃ a₄ : ℕ}
    (h₀ : p₀.totalDegree ≤ a₀) (h₁ : p₁.totalDegree ≤ a₁)
    (h₂ : p₂.totalDegree ≤ a₂) (h₃ : p₃.totalDegree ≤ a₃)
    (h₄ : p₄.totalDegree ≤ a₄) (idx : Fin 5) :
    (![p₀, p₁, p₂, p₃, p₄] idx).totalDegree ≤ ![a₀, a₁, a₂, a₃, a₄] idx := by
  fin_cases idx
  · exact h₀
  · exact h₁
  · exact h₂
  · exact h₃
  · exact h₄

/-- Bounds in the order `M,A,B,C,D,E,F,G,H,I,K,L,R,S`. -/
theorem totalDegree_capitals (idx : Fin 14) :
    (capitals idx).totalDegree ≤
      ![3, 4, 1, 1, 10, 13, 34, 68, 2, 140, 4, 5, 6, 2] idx := by
  have hM : (capitals 0).totalDegree ≤ 3 := by
    change (16 * X 1 * X 2 * (X 3 + 2) + 1 : Poly).totalDegree ≤ 3
    exact deg_add_nat
      (deg_mul (deg_mul (deg_nat_mul 16 (deg_X 1)) (deg_X 2))
        (deg_add_nat (deg_X 3) 2)) 1
  have hA : (capitals 1).totalDegree ≤ 4 := by
    change (capitals 0 * (X 2 + 1)).totalDegree ≤ 4
    exact deg_mul hM (deg_add_nat (deg_X 2) 1)
  have hB : (capitals 2).totalDegree ≤ 1 := by
    change (X 1 + 1 : Poly).totalDegree ≤ 1
    exact deg_add_nat (deg_X 1) 1
  have hC : (capitals 3).totalDegree ≤ 1 := by
    change (X 4 + capitals 2).totalDegree ≤ 1
    exact deg_add (deg_X 4) hB
  have hD : (capitals 4).totalDegree ≤ 10 := by
    change ((capitals 1 ^ 2 - 1) * capitals 3 ^ 2 + 1).totalDegree ≤ 10
    exact deg_add_nat (deg_mul (deg_sub_nat (deg_pow hA 2) 1) (deg_pow hC 2)) 1
  have hE : (capitals 5).totalDegree ≤ 13 := by
    change (2 * (X 5 + 1) * capitals 4 * capitals 3 ^ 2).totalDegree ≤ 13
    exact deg_mul (deg_mul (deg_nat_mul 2 (deg_add_nat (deg_X 5) 1)) hD) (deg_pow hC 2)
  have hF : (capitals 6).totalDegree ≤ 34 := by
    change ((capitals 1 ^ 2 - 1) * capitals 5 ^ 2 + 1).totalDegree ≤ 34
    exact deg_add_nat (deg_mul (deg_sub_nat (deg_pow hA 2) 1) (deg_pow hE 2)) 1
  have hG : (capitals 7).totalDegree ≤ 68 := by
    change (capitals 1 + capitals 6 * (capitals 6 - capitals 1)).totalDegree ≤ 68
    exact deg_add hA (deg_mul hF (deg_sub hF hA))
  have hH : (capitals 8).totalDegree ≤ 2 := by
    change (capitals 2 + 2 * (X 6 + 1) * capitals 3).totalDegree ≤ 2
    exact deg_add hB (deg_mul (deg_nat_mul 2 (deg_add_nat (deg_X 6) 1)) hC)
  have hI : (capitals 9).totalDegree ≤ 140 := by
    change ((capitals 7 ^ 2 - 1) * capitals 8 ^ 2 + 1).totalDegree ≤ 140
    exact deg_add_nat (deg_mul (deg_sub_nat (deg_pow hG 2) 1) (deg_pow hH 2)) 1
  have hK : (capitals 10).totalDegree ≤ 4 := by
    change (X 1 + 1 + X 7 * (capitals 0 - 1) - (X 0 + 1)).totalDegree ≤ 4
    exact deg_sub
      (deg_add (deg_add_nat (deg_X 1) 1) (deg_mul (deg_X 7) (deg_sub_nat hM 1)))
      (deg_add_nat (deg_X 0) 1)
  have hL : (capitals 11).totalDegree ≤ 5 := by
    change (X 0 + 1 + 1 + X 8 * (capitals 0 * X 2 - 1)).totalDegree ≤ 5
    exact deg_add (deg_add_nat (deg_add_nat (deg_X 0) 1) 1)
      (deg_mul (deg_X 8) (deg_sub_nat (deg_mul hM (deg_X 2)) 1))
  have hR : (capitals 12).totalDegree ≤ 6 := by
    change (X 0 + 1 + 1 + X 9 * (capitals 0 * X 1 * X 2 - 1)).totalDegree ≤ 6
    exact deg_add (deg_add_nat (deg_add_nat (deg_X 0) 1) 1)
      (deg_mul (deg_X 9) (deg_sub_nat (deg_mul (deg_mul hM (deg_X 1)) (deg_X 2)) 1))
  have hS : (capitals 13).totalDegree ≤ 2 := by
    change ((X 10 + 1) * (X 0 + 1 + 1) - 2 : Poly).totalDegree ≤ 2
    exact deg_sub_nat
      (deg_mul (deg_add_nat (deg_X 10) 1) (deg_add_nat (deg_add_nat (deg_X 0) 1) 1)) 2
  fin_cases idx
  · exact hM
  · exact hA
  · exact hB
  · exact hC
  · exact hD
  · exact hE
  · exact hF
  · exact hG
  · exact hH
  · exact hI
  · exact hK
  · exact hL
  · exact hR
  · exact hS

/-- Degree arithmetic for the polynomial version of Definition 3.7. -/
theorem totalDegree_uPolynomial {p q : Poly} {a b : ℕ}
    (hp : p.totalDegree ≤ a) (hq : q.totalDegree ≤ b) :
    (uPolynomial p q).totalDegree ≤ 4 * a + 2 * b := by
  have h := deg_add_nat
    (deg_mul (deg_mul (deg_pow (deg_add_nat hp 2) 3) (deg_add_nat hp 4))
      (deg_pow (deg_add_nat hq 1) 2)) 1
  change (uPolynomial p q).totalDegree ≤ 3 * a + a + 2 * b at h
  omega

/-- The six radicands have degrees at most `6,6,184,14,18,22`. -/
theorem totalDegree_radicands (idx : Fin 6) :
    (radicands idx).totalDegree ≤ ![6, 6, 184, 14, 18, 22] idx := by
  fin_cases idx
  · exact totalDegree_uPolynomial (deg_nat_mul 2 (deg_add_nat (deg_X 0) 1)) (deg_X 1)
  · exact totalDegree_uPolynomial (deg_nat_mul 2 (deg_X 1)) (deg_X 2)
  · exact deg_mul (deg_mul (totalDegree_capitals 4) (totalDegree_capitals 6))
      (totalDegree_capitals 9)
  · exact deg_add_nat
      (deg_mul (deg_sub_nat (deg_pow (totalDegree_capitals 0) 2) 1)
        (deg_pow (totalDegree_capitals 10) 2)) 1
  · exact deg_add_nat
      (deg_mul (deg_sub_nat (deg_pow (deg_mul (totalDegree_capitals 0) (deg_X 2)) 2) 1)
        (deg_pow (totalDegree_capitals 11) 2)) 1
  · exact deg_add_nat
      (deg_mul (deg_sub_nat
        (deg_pow (deg_mul (deg_mul (totalDegree_capitals 0) (deg_X 1)) (deg_X 2)) 2) 1)
        (deg_pow (totalDegree_capitals 12) 2)) 1

/-- Clearing the rational inequality gives a polynomial of degree at most fifty. -/
theorem totalDegree_marginPolynomial : marginPolynomial.totalDegree ≤ 50 := by
  let d : Poly := (capitals 3 - (X 3 + 1) * X 2 * capitals 10 * capitals 11) *
    (capitals 3 - capitals 12) ^ 2
  have hd : d.totalDegree ≤ 23 := by
    exact deg_mul
      (deg_sub (totalDegree_capitals 3)
        (deg_mul (deg_mul (deg_mul (deg_add_nat (deg_X 3) 1) (deg_X 2))
          (totalDegree_capitals 10)) (totalDegree_capitals 11)))
      (deg_pow (deg_sub (totalDegree_capitals 3) (totalDegree_capitals 12)) 2)
  change (d ^ 2 - 4 * (capitals 12 * capitals 10 * capitals 3 ^ 2 -
    (capitals 13 + 1) * d) ^ 2).totalDegree ≤ 50
  exact deg_sub (deg_pow hd 2)
    (deg_nat_mul 4 (deg_pow
      (deg_sub (deg_mul (deg_mul (totalDegree_capitals 12) (totalDegree_capitals 10))
        (deg_pow (totalDegree_capitals 3) 2))
        (deg_mul (deg_add_nat (totalDegree_capitals 13) 1) hd)) 2))

/-- The separate polynomial weights have half the respective radicand budgets. -/
theorem totalDegree_weights (idx : Fin 6) :
    (RefinedTwelveVariable.weights idx).totalDegree ≤ ![3, 3, 92, 7, 9, 11] idx := by
  let k : Poly := X 0 + 1
  let K : Poly := X 1 + k + 1 + X 7 * (capitals 0 + 1)
  let L : Poly := k + 1 + X 8 * (capitals 0 * X 2 + 1)
  let R : Poly := k + 1 + X 9 * (capitals 0 * X 1 * X 2 + 1)
  let G : Poly := capitals 1 + capitals 6 * (capitals 6 + capitals 1)
  have hk : k.totalDegree ≤ 1 := deg_add_nat (deg_X 0) 1
  have hK : K.totalDegree ≤ 4 :=
    deg_add (deg_add_nat (deg_add (deg_X 1) hk) 1)
      (deg_mul (deg_X 7) (deg_add_nat (totalDegree_capitals 0) 1))
  have hL : L.totalDegree ≤ 5 :=
    deg_add (deg_add_nat hk 1)
      (deg_mul (deg_X 8) (deg_add_nat (deg_mul (totalDegree_capitals 0) (deg_X 2)) 1))
  have hR : R.totalDegree ≤ 6 :=
    deg_add (deg_add_nat hk 1)
      (deg_mul (deg_X 9)
        (deg_add_nat (deg_mul (deg_mul (totalDegree_capitals 0) (deg_X 1)) (deg_X 2)) 1))
  have hG : G.totalDegree ≤ 68 :=
    deg_add (totalDegree_capitals 1)
      (deg_mul (totalDegree_capitals 6) (deg_add (totalDegree_capitals 6) (totalDegree_capitals 1)))
  fin_cases idx
  · exact deg_add_nat
      (deg_mul (deg_mul (deg_add_nat (deg_nat_mul 2 hk) 4) (deg_add_nat (deg_nat_mul 2 hk) 2))
        (deg_add_nat (deg_X 1) 1)) 2
  · exact deg_add_nat
      (deg_mul (deg_mul (deg_add_nat (deg_nat_mul 2 (deg_X 1)) 4)
        (deg_add_nat (deg_nat_mul 2 (deg_X 1)) 2)) (deg_add_nat (deg_X 2) 1)) 2
  · exact deg_mul
      (deg_mul
        (deg_add_nat (deg_mul (deg_add_nat (totalDegree_capitals 1) 1) (totalDegree_capitals 3)) 2)
        (deg_add_nat (deg_mul (deg_add_nat (totalDegree_capitals 1) 1) (totalDegree_capitals 5)) 2))
      (deg_add_nat (deg_mul (deg_add_nat hG 1) (totalDegree_capitals 8)) 2)
  · exact deg_add_nat (deg_mul (deg_add_nat (totalDegree_capitals 0) 1) hK) 2
  · exact deg_add_nat
      (deg_mul (deg_add_nat (deg_mul (totalDegree_capitals 0) (deg_X 2)) 1) hL) 2
  · exact deg_add_nat
      (deg_mul (deg_add_nat (deg_mul (deg_mul (totalDegree_capitals 0) (deg_X 1)) (deg_X 2)) 1) hR) 2

theorem totalDegree_divisor : (capitals 6).totalDegree ≤ 34 := totalDegree_capitals 6

theorem totalDegree_dividend : (capitals 8 - capitals 3).totalDegree ≤ 2 :=
  deg_sub (totalDegree_capitals 8) (totalDegree_capitals 3)

/-- The refined six-square combined polynomial satisfies the article's degree bound. -/
theorem totalDegree_six_combined : RefinedTwelveVariable.combined.totalDegree ≤ 13376 := by
  apply Diophantine.RefinedRelationCombiningPolynomial.totalDegree_compose_six_le
  · exact totalDegree_radicands
  · exact totalDegree_weights
  · exact deg_X 11
  · exact totalDegree_divisor
  · exact totalDegree_dividend
  · exact totalDegree_marginPolynomial

/-- The final square and linear prime factor give degree at most `26753`. -/
theorem totalDegree_six_primePolynomial :
    RefinedTwelveVariable.primePolynomial.totalDegree ≤ 26753 := by
  exact deg_mul (deg_add_nat (deg_X 0) 2)
    (deg_sub (deg_nat 1) (deg_pow totalDegree_six_combined 2))

/-- The merged equation (24) has degree at most twenty-two. -/
theorem totalDegree_mergedRadicand :
    FiveSquarePrimePolynomial.mergedRadicand.totalDegree ≤ 22 := by
  have hT : FiveSquarePrimePolynomial.firstSquare.totalDegree ≤ 6 :=
    totalDegree_radicands 0
  exact deg_mul hT
    (deg_add_nat
      (deg_mul (deg_mul (deg_mul (deg_nat_mul 16 hT) (deg_sub_nat hT 1))
        (deg_pow (deg_add_nat (deg_X 1) 1) 2))
        (deg_pow (deg_add_nat (deg_X 2) 1) 2)) 1)

/-- The corresponding merged weight has degree at most eleven. -/
theorem totalDegree_mergedWeight :
    FiveSquarePrimePolynomial.mergedWeight.totalDegree ≤ 11 := by
  have hT : FiveSquarePrimePolynomial.firstSquare.totalDegree ≤ 6 :=
    totalDegree_radicands 0
  exact deg_mul (totalDegree_weights 0)
    (deg_add_nat
      (deg_mul (deg_mul (deg_nat_mul 4 hT) (deg_add_nat (deg_X 1) 1))
        (deg_add_nat (deg_X 2) 1)) 2)

/-- Degree budgets for the five radicands after merging the first two tests. -/
theorem totalDegree_five_radicands (idx : Fin 5) :
    (FiveSquarePrimePolynomial.radicands idx).totalDegree ≤ ![22, 184, 14, 18, 22] idx := by
  have h := deg_vector_five totalDegree_mergedRadicand
    (totalDegree_radicands 2) (totalDegree_radicands 3)
    (totalDegree_radicands 4) (totalDegree_radicands 5)
  exact h idx

/-- The five separate weight budgets sum to one hundred thirty. -/
theorem totalDegree_five_weights (idx : Fin 5) :
    (FiveSquarePrimePolynomial.weights idx).totalDegree ≤ ![11, 92, 7, 9, 11] idx := by
  have h := deg_vector_five totalDegree_mergedWeight
    (totalDegree_weights 2) (totalDegree_weights 3)
    (totalDegree_weights 4) (totalDegree_weights 5)
  exact h idx

/-- The five-square combined polynomial has total degree at most `6848`. -/
theorem totalDegree_five_combined : FiveSquarePrimePolynomial.combined.totalDegree ≤ 6848 := by
  apply Diophantine.RefinedRelationCombiningPolynomial.totalDegree_compose_five_le
  · exact totalDegree_five_radicands
  · exact totalDegree_five_weights
  · exact deg_X 11
  · exact totalDegree_divisor
  · exact totalDegree_dividend
  · exact totalDegree_marginPolynomial

/-- The constructed twelve-variable prime polynomial has degree at most `13697`. -/
theorem totalDegree_five_primePolynomial :
    FiveSquarePrimePolynomial.primePolynomial.totalDegree ≤ 13697 := by
  exact deg_mul (deg_add_nat (deg_X 0) 2)
    (deg_sub (deg_nat 1) (deg_pow totalDegree_five_combined 2))

end

end JSWW1976.RefinedPolynomialDegrees
