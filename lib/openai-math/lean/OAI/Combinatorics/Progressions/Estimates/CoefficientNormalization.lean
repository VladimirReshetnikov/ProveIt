import OAI.Combinatorics.Progressions.Lattices.BooleanAffineInput
import OAI.Combinatorics.Progressions.Polynomial.PolynomialParameterContinuity

namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def booleanCoefficientTail {T K I α : Type*} [Fintype α] [DecidableEq α]
    (terms : Finset T) (coefficient : T → MvPolynomial I ℝ)
    (exponent : T → K →₀ ℕ) (input : K → Option α → MvPolynomial I ℝ)
    (s : Finset α) : MvPolynomial I ℝ :=
  booleanCoefficient (fun t => ∑ n ∈ terms,
    coefficient n * polynomialMonomial (fun k => booleanAffineInput (input k) t) (exponent n)) s

theorem booleanCoefficientTail_eval {T K I α : Type*} [Fintype α] [DecidableEq α]
    (terms : Finset T) (coefficient : T → MvPolynomial I ℝ)
    (exponent : T → K →₀ ℕ) (input : K → Option α → MvPolynomial I ℝ)
    (s : Finset α) (x : I → ℝ) :
    MvPolynomial.eval x (booleanCoefficientTail terms coefficient exponent input s) =
      booleanCoefficient (fun t => ∑ n ∈ terms, MvPolynomial.eval x (coefficient n) *
        ∏ k ∈ (exponent n).support,
          (∑ r, (booleanFeature r t : ℝ) * MvPolynomial.eval x (input k r)) ^ exponent n k) s := by
  simp only [booleanCoefficientTail, booleanCoefficient_map, map_sum, map_mul,
    polynomialMonomial_eval, booleanAffineInput_eval]

theorem booleanCoefficientTail_mass_le {T K I α : Type*} [Fintype α] [DecidableEq α]
    (terms : Finset T) (coefficient : T → MvPolynomial I ℝ)
    (exponent : T → K →₀ ℕ) (input : K → Option α → MvPolynomial I ℝ)
    (s : Finset α) {h : ℕ} (hdegree : ∀ n ∈ terms, (exponent n).sum (fun _ d => d) ≤ h)
    {A : ℝ} (hbase : 1 ≤ ((Fintype.card α : ℝ) + 1) * A)
    (hinput : ∀ k r, realPolynomialMass (input k r) ≤ A) :
    realPolynomialMass (booleanCoefficientTail terms coefficient exponent input s) ≤
      (2 : ℝ) ^ s.card * ((∑ n ∈ terms, realPolynomialMass (coefficient n)) *
        (((Fintype.card α : ℝ) + 1) * A) ^ h) := by
  classical
  apply booleanCoefficient_mass_le
  intro t _
  apply (realPolynomialMass_sum_le _ _).trans
  calc
    _ ≤ ∑ n ∈ terms, realPolynomialMass (coefficient n) *
        (((Fintype.card α : ℝ) + 1) * A) ^ h := by
      apply Finset.sum_le_sum
      intro n hn
      apply (realPolynomialMass_mul_le _ _).trans
      apply mul_le_mul_of_nonneg_left _ (realPolynomialMass_nonneg _)
      exact (polynomialMonomial_mass_le _ _
        (fun k _ => booleanAffineInput_mass_le _ _ (hinput k))).trans
          (pow_le_pow_right₀ hbase (hdegree n hn))
    _ = _ := (Finset.sum_mul _ _ _).symm

theorem booleanCoefficientTail_totalDegree_le {T K I α : Type*} [Fintype α] [DecidableEq α]
    (terms : Finset T) (coefficient : T → MvPolynomial I ℝ)
    (exponent : T → K →₀ ℕ) (input : K → Option α → MvPolynomial I ℝ)
    (s : Finset α) {h e δ : ℕ}
    (hdegree : ∀ n ∈ terms, (exponent n).sum (fun _ d => d) ≤ h)
    (hcoefficient : ∀ n ∈ terms, (coefficient n).totalDegree ≤ δ)
    (hinput : ∀ k r, (input k r).totalDegree ≤ e) :
    (booleanCoefficientTail terms coefficient exponent input s).totalDegree ≤ δ + h * e := by
  classical
  apply booleanCoefficient_totalDegree_le
  intro t _
  apply MvPolynomial.totalDegree_finsetSum_le
  intro n hn
  apply (MvPolynomial.totalDegree_mul _ _).trans
  apply Nat.add_le_add (hcoefficient n hn)
  exact (polynomialMonomial_totalDegree_le _ _
    (fun k _ => booleanAffineInput_totalDegree_le _ _ (hinput k))).trans
      (Nat.mul_le_mul_right _ (hdegree n hn))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def booleanJetColumnPolynomial {K P α : Type*} [Fintype α] [DecidableEq α]
    (e : K →₀ ℕ) (input : K → Option α → MvPolynomial P ℝ) (s : Finset α) : MvPolynomial P ℝ :=
  booleanCoefficient (fun t => polynomialMonomial (fun k => booleanAffineInput (input k) t) e) s

theorem booleanJetColumnPolynomial_eval {K P α : Type*} [Fintype α] [DecidableEq α]
    (e : K →₀ ℕ) (input : K → Option α → MvPolynomial P ℝ) (s : Finset α) (x : P → ℝ) :
    MvPolynomial.eval x (booleanJetColumnPolynomial e input s) =
      booleanCoefficient (fun t => ∏ k ∈ e.support,
        (∑ r, (booleanFeature r t : ℝ) * MvPolynomial.eval x (input k r)) ^ e k) s := by
  simp only [booleanJetColumnPolynomial, booleanCoefficient_map, polynomialMonomial_eval, booleanAffineInput_eval]

theorem booleanJetColumnPolynomial_mass_le {K P α : Type*} [Fintype α] [DecidableEq α]
    (e : K →₀ ℕ) (input : K → Option α → MvPolynomial P ℝ) (s : Finset α)
    {d : ℕ} (hd : e.sum (fun _ n => n) ≤ d) {A : ℝ}
    (hA : 1 ≤ ((Fintype.card α : ℝ)+1)*A) (hi : ∀ k r, realPolynomialMass (input k r) ≤ A) :
    realPolynomialMass (booleanJetColumnPolynomial e input s) ≤
      2^s.card * (((Fintype.card α : ℝ)+1)*A)^d := by
  apply booleanCoefficient_mass_le
  intro t _
  exact (polynomialMonomial_mass_le _ _ (fun k _ => booleanAffineInput_mass_le _ _ (hi k))).trans
    (pow_le_pow_right₀ hA hd)

theorem booleanJetColumnPolynomial_degree_le {K P α : Type*} [Fintype α] [DecidableEq α]
    (e : K →₀ ℕ) (input : K → Option α → MvPolynomial P ℝ) (s : Finset α)
    {d a : ℕ} (hd : e.sum (fun _ n => n) ≤ d) (hi : ∀ k r, (input k r).totalDegree ≤ a) :
    (booleanJetColumnPolynomial e input s).totalDegree ≤ d*a := by
  apply booleanCoefficient_totalDegree_le
  intro t _
  exact (polynomialMonomial_totalDegree_le _ _ (fun k _ => booleanAffineInput_totalDegree_le _ _ (hi k))).trans
    (Nat.mul_le_mul_right a hd)

theorem booleanJetColumns_apply_coefficients {K P α O J : Type*} [Fintype α] [DecidableEq α]
    [Fintype O] [Fintype J] (e : J → K →₀ ℕ) (input : K → Option α → MvPolynomial P ℝ)
    (rows : O → Finset α) (x : P → ℝ) (c : J → ℝ) (o : O) :
    polynomialColumns (fun o j => booleanJetColumnPolynomial (e j) input (rows o)) x c o =
      booleanCoefficient (fun t => ∑ j, c j * ∏ k ∈ (e j).support,
        (∑ r, (booleanFeature r t : ℝ) * MvPolynomial.eval x (input k r)) ^ e j k) (rows o) := by
  simp only [booleanCoefficient_sum, booleanCoefficient_const_mul]
  change (∑ j, MvPolynomial.eval x (booleanJetColumnPolynomial (e j) input (rows o)) * c j) = _
  apply Finset.sum_congr rfl
  intro j _
  rw [booleanJetColumnPolynomial_eval, mul_comm]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem polynomialParameterPoint_some {Z I : Type*} (t : ℝ) (z : Z → ℝ) (x : I → ℝ)
    (j : Z ⊕ I) : polynomialParameterPoint t z x (some j) = Sum.elim z x j := by
  cases j <;> rfl

noncomputable def normalizedCoefficientTail {T K Z I α : Type*} [Fintype α] [DecidableEq α]
    (terms : Finset T) (weight : T → ℝ) (exponent : T → K →₀ ℕ)
    (coefficientIndex : T → Z) (inputIndex : K → Option α → Z ⊕ I) (s : Finset α) :
    MvPolynomial (PolynomialParameter Z I) ℝ :=
  booleanCoefficientTail terms
    (fun n => MvPolynomial.C (weight n) * MvPolynomial.X (some (.inl (coefficientIndex n))))
    exponent (fun k r => MvPolynomial.X (some (inputIndex k r))) s

noncomputable def normalizedCoefficientTailValue {T K Z I α : Type*} [Fintype α] [DecidableEq α]
    (terms : Finset T) (weight : T → ℝ) (exponent : T → K →₀ ℕ)
    (coefficientIndex : T → Z) (inputIndex : K → Option α → Z ⊕ I)
    (z : Z → ℝ) (x : I → ℝ) (s : Finset α) : ℝ :=
  booleanCoefficient (fun t => ∑ n ∈ terms, (weight n * z (coefficientIndex n)) *
    ∏ k ∈ (exponent n).support,
      (∑ r, (booleanFeature r t : ℝ) * Sum.elim z x (inputIndex k r)) ^ exponent n k) s

theorem normalizedCoefficientTail_eval {T K Z I α : Type*} [Fintype α] [DecidableEq α]
    (terms : Finset T) (weight : T → ℝ) (exponent : T → K →₀ ℕ)
    (coefficientIndex : T → Z) (inputIndex : K → Option α → Z ⊕ I)
    (t : ℝ) (z : Z → ℝ) (x : I → ℝ) (s : Finset α) :
    MvPolynomial.eval (polynomialParameterPoint t z x)
        (normalizedCoefficientTail terms weight exponent coefficientIndex inputIndex s) =
      normalizedCoefficientTailValue terms weight exponent coefficientIndex inputIndex z x s := by
  simp only [normalizedCoefficientTail, normalizedCoefficientTailValue, booleanCoefficientTail_eval,
    map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, polynomialParameterPoint_some, Sum.elim_inl]

theorem normalizedCoefficientTail_mass_le {T K Z I α : Type*} [Fintype α] [DecidableEq α]
    (terms : Finset T) (weight : T → ℝ) (exponent : T → K →₀ ℕ)
    (coefficientIndex : T → Z) (inputIndex : K → Option α → Z ⊕ I) (s : Finset α)
    {h : ℕ} (hdegree : ∀ n ∈ terms, (exponent n).sum (fun _ d => d) ≤ h) :
    realPolynomialMass (normalizedCoefficientTail terms weight exponent coefficientIndex inputIndex s) ≤
      (2 : ℝ) ^ s.card * ((∑ n ∈ terms, |weight n|) * ((Fintype.card α : ℝ) + 1) ^ h) := by
  classical
  have he := booleanCoefficientTail_mass_le terms
    (fun n => MvPolynomial.C (weight n) * MvPolynomial.X (some (.inl (coefficientIndex n))))
    exponent (fun k r => MvPolynomial.X (some (inputIndex k r))) s hdegree
    (A := 1) (by simp) (fun k r => (realPolynomialMass_X _).le)
  simp only [mul_one] at he
  apply he.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum
  intro n _
  simpa only [realPolynomialMass_X, mul_one] using realPolynomialMass_C_mul_le (weight n)
    (MvPolynomial.X (some (.inl (coefficientIndex n))) : MvPolynomial (PolynomialParameter Z I) ℝ)

theorem normalizedCoefficientTail_totalDegree_le {T K Z I α : Type*} [Fintype α] [DecidableEq α]
    (terms : Finset T) (weight : T → ℝ) (exponent : T → K →₀ ℕ)
    (coefficientIndex : T → Z) (inputIndex : K → Option α → Z ⊕ I) (s : Finset α)
    {h : ℕ} (hdegree : ∀ n ∈ terms, (exponent n).sum (fun _ d => d) ≤ h) :
    (normalizedCoefficientTail terms weight exponent coefficientIndex inputIndex s).totalDegree ≤ h + 1 := by
  have he := booleanCoefficientTail_totalDegree_le terms
    (fun n => MvPolynomial.C (weight n) * MvPolynomial.X (some (.inl (coefficientIndex n))))
    exponent (fun k r => MvPolynomial.X (some (inputIndex k r))) s hdegree
    (δ := 1) (e := 1)
    (fun n _ => (MvPolynomial.totalDegree_mul _ _).trans (by simp)) (fun k r => by simp)
  simpa only [normalizedCoefficientTail, Nat.mul_one, Nat.add_comm] using he

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem normalizedMonomialTerm {K : Type*} (m : K →₀ ℕ) (scale value : K → ℝ)
    (Q b : ℝ) (hQ : Q ≠ 0) (hscale : ∀ k, scale k ≠ 0) :
    ((Q * b / (∏ k ∈ m.support, scale k ^ m k)) *
      (∏ k ∈ m.support, (scale k * value k) ^ m k)) / Q =
        b * ∏ k ∈ m.support, value k ^ m k := by
  classical
  have hs : (∏ k ∈ m.support, scale k ^ m k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun k _ => pow_ne_zero _ (hscale k))
  simp_rw [mul_pow, Finset.prod_mul_distrib]
  field_simp

theorem normalizedProductTerm {F : Type*} [Fintype F] (scale value : F → ℝ)
    (Q b : ℝ) (hQ : Q ≠ 0) (hscale : ∀ k, scale k ≠ 0) :
    ((Q * b / (∏ k, scale k)) * (∏ k, scale k * value k)) / Q = b * ∏ k, value k := by
  classical
  have hs : (∏ k, scale k) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun k _ => hscale k)
  rw [Finset.prod_mul_distrib]
  field_simp

theorem booleanMonomialArray_rescaling {T K α : Type*} [DecidableEq α]
    (terms : Finset T) (coefficient : T → ℝ) (exponent : T → K →₀ ℕ)
    (scale : K → ℝ) (value : Finset α → K → ℝ) (Q : ℝ) (hQ : Q ≠ 0)
    (hscale : ∀ k, scale k ≠ 0) (s : Finset α) :
    booleanCoefficient (fun t => (∑ n ∈ terms,
      (Q * coefficient n / (∏ k ∈ (exponent n).support, scale k ^ exponent n k)) *
        ∏ k ∈ (exponent n).support, (scale k * value t k) ^ exponent n k) / Q) s =
      booleanCoefficient (fun t => ∑ n ∈ terms,
        coefficient n * ∏ k ∈ (exponent n).support, value t k ^ exponent n k) s := by
  classical
  congr 1
  funext t
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl (fun n _ => normalizedMonomialTerm (exponent n) scale (value t) Q _ hQ hscale)

theorem normalizedSmallCoefficientArray {T K Z I α : Type*} [Fintype α] [DecidableEq α]
    (terms : Finset T) (weight : T → ℝ) (exponent : T → K →₀ ℕ)
    (coefficientIndex : T → Z) (inputIndex : K → Option α → Z ⊕ I)
    (scale : K → ℝ) (Q t : ℝ) (hQ : Q ≠ 0) (hscale : ∀ k, scale k ≠ 0)
    (z : Z → ℝ) (x : I → ℝ) (s : Finset α) :
    booleanCoefficient (fun vertex => (∑ n ∈ terms,
      (Q * (t * (weight n * z (coefficientIndex n))) /
        (∏ k ∈ (exponent n).support, scale k ^ exponent n k)) *
        ∏ k ∈ (exponent n).support,
          (scale k * (∑ r, (booleanFeature r vertex : ℝ) * Sum.elim z x (inputIndex k r))) ^
            exponent n k) / Q) s =
      t * normalizedCoefficientTailValue terms weight exponent coefficientIndex inputIndex z x s := by
  rw [booleanMonomialArray_rescaling terms _ exponent scale _ Q hQ hscale]
  unfold normalizedCoefficientTailValue
  rw [← booleanCoefficient_const_mul]
  congr 1
  funext vertex
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  ring

end Erdos3

end

end OAI
