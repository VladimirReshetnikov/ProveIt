import OAI.Combinatorics.Progressions.Dynamics.PartitionedRegularizationBudget

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {D : Type*} [Fintype D] (G Z α : Type*) [Fintype G] [Fintype Z] [Fintype α]
  {B : D → Type*} [∀ d, Fintype (B d)]

noncomputable def samplerParameterLog (h : D → ℕ) : ℝ :=
  Fintype.card Z + Fintype.card (JointBlockParameter B h α) + Fintype.card D +
    (∑ d, (h d : ℝ) * ((Fintype.card (SamplerTupleIndex G B h) : ℝ) + 1)) + 2

theorem samplerParameterLog_nonneg (h : D → ℕ) :
    0 ≤ samplerParameterLog G Z α (B := B) h := by
  unfold samplerParameterLog
  positivity

theorem samplerParameter_card_le_exp (h : D → ℕ) :
    (Fintype.card (PolynomialParameter (Z ⊕ (Σ d, SamplerCoefficientSlot G B h d))
      (JointBlockParameter B h α)) : ℝ) ≤ Real.exp (samplerParameterLog G Z α (B := B) h) := by
  have hc (d : D) : (Fintype.card (SamplerCoefficientSlot G B h d) : ℝ) ≤
      Real.exp ((h d : ℝ) * ((Fintype.card (SamplerTupleIndex G B h) : ℝ) + 1)) := by
    have hn : (Fintype.card (SamplerCoefficientSlot G B h d) : ℝ) ≤
        ((h d : ℝ) + 1) * ((Fintype.card (SamplerTupleIndex G B h) : ℝ) + 1) ^ (h d) := by
      exact_mod_cast VectorPolynomial.boundedCoefficientExponent_card_le
        (K := SamplerTupleIndex G B h) (h d)
    apply hn.trans
    calc
      _ ≤ Real.exp (h d) * (Real.exp (Fintype.card (SamplerTupleIndex G B h))) ^ (h d) := by
        gcongr
        · exact Real.add_one_le_exp _
        · exact Real.add_one_le_exp _
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
  have hsum := sum_le_exp_card_add_sum
    (fun d : D => (Fintype.card (SamplerCoefficientSlot G B h d) : ℝ))
    (fun d : D => (h d : ℝ) * ((Fintype.card (SamplerTupleIndex G B h) : ℝ) + 1))
    (fun _ => by positivity) hc
  have hbase : (Fintype.card Z : ℝ) + Fintype.card (JointBlockParameter B h α) + 1 ≤
      Real.exp ((Fintype.card Z : ℝ) + Fintype.card (JointBlockParameter B h α)) :=
    Real.add_one_le_exp _
  have he := add_le_exp_add_one
    (show 0 ≤ (Fintype.card Z : ℝ) + Fintype.card (JointBlockParameter B h α) by positivity)
    (show 0 ≤ (Fintype.card D : ℝ) +
      ∑ d, (h d : ℝ) * ((Fintype.card (SamplerTupleIndex G B h) : ℝ) + 1) by positivity)
    hbase hsum
  have hN : (Fintype.card (PolynomialParameter (Z ⊕ (Σ d, SamplerCoefficientSlot G B h d))
      (JointBlockParameter B h α)) : ℝ) =
      ((Fintype.card Z : ℝ) + Fintype.card (JointBlockParameter B h α) + 1) +
        ∑ d, (Fintype.card (SamplerCoefficientSlot G B h d) : ℝ) := by
    simp only [PolynomialParameter, Fintype.card_option, Fintype.card_sum,
      Fintype.card_sigma, Nat.cast_add, Nat.cast_one, Nat.cast_sum]
    ring
  rw [hN]
  apply he.trans
  apply Real.exp_le_exp.mpr
  unfold samplerParameterLog
  linarith

end Erdos3

end

end OAI
