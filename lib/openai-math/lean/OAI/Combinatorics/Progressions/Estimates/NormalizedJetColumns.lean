import OAI.Combinatorics.Progressions.Sampling.CanonicalSamplerTuple

namespace OAI

section

namespace Erdos3

open scoped NNReal BigOperators

noncomputable def frozenTupleCoordinate {Z P : Type*} (z : Z → ℝ) : Z ⊕ P → MvPolynomial P ℝ
  | .inl j => MvPolynomial.C (z j)
  | .inr i => MvPolynomial.X i

theorem frozenTupleCoordinate_eval {Z P : Type*} (z : Z → ℝ) (x : P → ℝ) (i : Z ⊕ P) :
    MvPolynomial.eval x (frozenTupleCoordinate z i) = Sum.elim z x i := by
  cases i <;> simp [frozenTupleCoordinate]

theorem frozenTupleCoordinate_mass_le {Z P : Type*} (z : Z → ℝ) (hz : ∀ j, |z j| ≤ 1) (i : Z ⊕ P) :
    realPolynomialMass (frozenTupleCoordinate z i) ≤ 1 := by
  cases i with
  | inl j => exact (realPolynomialMass_C (z j)).le.trans (hz j)
  | inr i => exact (realPolynomialMass_X i).le

theorem frozenTupleCoordinate_degree_le {Z P : Type*} (z : Z → ℝ) (i : Z ⊕ P) :
    (frozenTupleCoordinate z i).totalDegree ≤ 1 := by
  cases i <;> simp [frozenTupleCoordinate]

noncomputable def normalizedJetColumn {Z P K α : Type*} [Fintype α] [DecidableEq α]
    (e : K →₀ ℕ) (input : K → Option α → Z ⊕ P) (z : Z → ℝ) (s : Finset α) : MvPolynomial P ℝ :=
  booleanJetColumnPolynomial e (fun k r => frozenTupleCoordinate z (input k r)) s

theorem normalizedJetColumn_degree_le {Z P K α : Type*} [Fintype α] [DecidableEq α]
    (e : K →₀ ℕ) (input : K → Option α → Z ⊕ P) (z : Z → ℝ) (s : Finset α)
    {d : ℕ} (hd : e.sum (fun _ n => n) ≤ d) : (normalizedJetColumn e input z s).totalDegree ≤ d := by
  simpa only [normalizedJetColumn, Nat.mul_one] using booleanJetColumnPolynomial_degree_le e _ s hd
    (fun k r => frozenTupleCoordinate_degree_le z (input k r))

theorem normalizedJetColumn_mass_le {Z P K α : Type*} [Fintype α] [DecidableEq α]
    (e : K →₀ ℕ) (input : K → Option α → Z ⊕ P) (z : Z → ℝ) (hz : ∀ j, |z j| ≤ 1)
    (s : Finset α) {d : ℕ} (hd : e.sum (fun _ n => n) ≤ d) :
    realPolynomialMass (normalizedJetColumn e input z s) ≤
      (2 : ℝ)^Fintype.card α * ((Fintype.card α : ℝ)+1)^d := by
  have he := booleanJetColumnPolynomial_mass_le e _ s hd (A := 1) (by simp)
    (fun k r => frozenTupleCoordinate_mass_le z hz (input k r))
  simp only [mul_one] at he
  exact he.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Finset.card_le_univ s)) (by positivity))

theorem normalizedJetColumns_apply_coefficients {Z P K α O J : Type*}
    [Fintype α] [DecidableEq α] [Fintype O] [Fintype J]
    (e : J → K →₀ ℕ) (input : K → Option α → Z ⊕ P) (z : Z → ℝ) (rows : O → Finset α)
    (x : P → ℝ) (c : J → ℝ) (o : O) :
    polynomialColumns (fun o j => normalizedJetColumn (e j) input z (rows o)) x c o =
      booleanCoefficient (fun t => ∑ j, c j * ∏ k ∈ (e j).support,
        (normalizedCubeTuple input z x t k)^e j k) (rows o) := by
  simpa only [normalizedJetColumn, frozenTupleCoordinate_eval, normalizedCubeTuple] using
    booleanJetColumns_apply_coefficients e (fun k r => frozenTupleCoordinate z (input k r)) rows x c o

noncomputable def normalizedJetMass (α : Type*) [Fintype α] (d : ℕ) : ℝ≥0 :=
  2^Fintype.card α * (Fintype.card α+1)^d

theorem normalizedJetColumns_lipschitzOn_box {Z P K α O J : Type*}
    [Fintype P] [DecidableEq P] [Fintype α] [DecidableEq α] [Fintype O] [Fintype J]
    (e : J → K →₀ ℕ) (input : K → Option α → Z ⊕ P) (z : Z → ℝ) (hz : ∀ j, |z j| ≤ 1)
    (rows : O → Finset α) {d : ℕ} (hd : ∀ j, (e j).sum (fun _ n => n) ≤ d) :
    LipschitzOnWith (Fintype.card J * polynomialBoxLip (Fintype.card P) d (normalizedJetMass α d))
      (polynomialColumns (fun o j => normalizedJetColumn (e j) input z (rows o))) (Metric.closedBall 0 1) := by
  apply polynomialColumns_lipschitzOn_box _ (fun o j => normalizedJetColumn_degree_le (e j) input z (rows o) (hd j))
  intro o j
  change realPolynomialMass (normalizedJetColumn (e j) input z (rows o)) ≤
    (2 : ℝ)^Fintype.card α * (Fintype.card α+1)^d
  exact normalizedJetColumn_mass_le (e j) input z hz (rows o) (hd j)

end Erdos3

end

end OAI
