import OAI.Combinatorics.Progressions.Estimates.ComparisonAmbient

namespace OAI

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

variable {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℚ V]

noncomputable def squarefreePolynomialLift (f : SquarefreeIndex ι → V) : VectorPolynomial ι ℚ V :=
  ∑ a, monomial a.val (f a)

theorem squarefreePolynomialLift_coefficient (f : SquarefreeIndex ι → V) (a : SquarefreeIndex ι) :
    coefficients (squarefreePolynomialLift f) a.val = f a := by
  classical
  simp only [squarefreePolynomialLift, map_sum, Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single a]
  · simp only [coefficients_monomial, Finsupp.single_eq_same]
  · intro b _ hb
    rw [coefficients_monomial]
    exact Finsupp.single_eq_of_ne (fun h => hb (Subtype.ext h.symm))
  · simp

theorem squarefreePolynomialLift_coefficient_nonsquarefree (f : SquarefreeIndex ι → V)
    (a : ι →₀ ℕ) (ha : ¬SquarefreeExponent a) : coefficients (squarefreePolynomialLift f) a = 0 := by
  classical
  simp only [squarefreePolynomialLift, map_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro b _
  rw [coefficients_monomial]
  apply Finsupp.single_eq_of_ne
  intro h
  apply ha
  rw [h]
  exact b.property

theorem squarefreePolynomialLift_eval (f : SquarefreeIndex ι → V) (x : ι → ℚ) :
    eval x (squarefreePolynomialLift f) = ∑ a, (a.val.prod fun i n => x i ^ n) • f a := by
  simp only [squarefreePolynomialLift, map_sum, eval_monomial]

end Erdos3

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def polarizedLog (p : F.adaptedLieSubalgebra) :
    VectorPolynomial ι ℚ (F.SquarefreeAlgebra π) :=
  squarefreePolynomialLift (F.polarizedCoefficient π p)

theorem polarizedLog_coefficient (p : F.adaptedLieSubalgebra) (a : SquarefreeIndex ι) :
    coefficients (F.polarizedLog π p) a.val = F.polarizedCoefficient π p a :=
  squarefreePolynomialLift_coefficient _ a

theorem polarizedLog_coefficient_nonsquarefree (p : F.adaptedLieSubalgebra)
    (a : ι →₀ ℕ) (ha : ¬SquarefreeExponent a) :
    coefficients (F.polarizedLog π p) a = 0 :=
  squarefreePolynomialLift_coefficient_nonsquarefree _ a ha

theorem polarizedLog_adapted (p : F.adaptedLieSubalgebra) :
    (F.squarefreeMultidegreeFiltration π).Adapted (F.polarizedLog π p) := by
  intro a
  by_cases ha : SquarefreeExponent a
  · rw [F.polarizedLog_coefficient π p ⟨a, ha⟩]
    exact F.polarizedCoefficient_mem π p ⟨a, ha⟩
  · rw [F.polarizedLog_coefficient_nonsquarefree π p a ha]
    exact Submodule.zero_mem _

theorem polarizedLog_eval (p : F.adaptedLieSubalgebra) (x : ι → ℚ) :
    eval x (F.polarizedLog π p) =
      ∑ a, (a.val.prod fun i n => x i ^ n) • F.polarizedCoefficient π p a :=
  squarefreePolynomialLift_eval _ x

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem polarizedLog_constant (p : F.adaptedLieSubalgebra) :
    coefficients (F.polarizedLog π p) 0 = 0 := by
  let a : SquarefreeIndex ι := ⟨0, fun _ => Nat.zero_le 1⟩
  exact (F.polarizedLog_coefficient π p a).trans (F.polarizedCoefficient_zero π p a rfl)

theorem polarizedLog_eval_zero (p : F.adaptedLieSubalgebra) :
    eval (fun _ => 0) (F.polarizedLog π p) = 0 := by
  rw [eval_zero_eq_coefficient, F.polarizedLog_constant]

noncomputable def polarizedOrbit (p : F.adaptedLieSubalgebra) :
    (F.squarefreeMultidegreeFiltration π).PolynomialOrbit :=
  (F.squarefreeMultidegreeFiltration π).polynomialOrbitOfLog
    (F.polarizedLog π p) (F.polarizedLog_adapted π p)

theorem polarizedOrbit_eval_coord (p : F.adaptedLieSubalgebra) (x : ι → ℤ) :
    ((F.squarefreeMultidegreeFiltration π).polynomialOrbitEval x
      (F.polarizedOrbit π p)).coord = eval (fun i => (x i : ℚ)) (F.polarizedLog π p) := rfl

theorem polarizedOrbit_eval_zero (p : F.adaptedLieSubalgebra) :
    (F.squarefreeMultidegreeFiltration π).polynomialOrbitEval 0
      (F.polarizedOrbit π p) = 1 := by
  apply NilpotentLieBCHGroup.ext
  exact F.polarizedLog_eval_zero π p

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped TensorProduct BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def realPolarizedLog (p : F.realification.adaptedLieSubalgebra) :
    VectorPolynomial ι ℚ (ℝ ⊗[ℚ] F.SquarefreeAlgebra π) :=
  squarefreePolynomialLift (F.realPolarizedCoefficient π p)

theorem realPolarizedLog_coefficient (p : F.realification.adaptedLieSubalgebra)
    (a : SquarefreeIndex ι) :
    coefficients (F.realPolarizedLog π p) a.val = F.realPolarizedCoefficient π p a :=
  squarefreePolynomialLift_coefficient _ a

theorem realPolarizedLog_coefficient_nonsquarefree (p : F.realification.adaptedLieSubalgebra)
    (a : ι →₀ ℕ) (ha : ¬SquarefreeExponent a) :
    coefficients (F.realPolarizedLog π p) a = 0 :=
  squarefreePolynomialLift_coefficient_nonsquarefree _ a ha

theorem realPolarizedLog_adapted (p : F.realification.adaptedLieSubalgebra) :
    (F.squarefreeMultidegreeFiltration π).realification.Adapted (F.realPolarizedLog π p) := by
  intro a
  by_cases ha : SquarefreeExponent a
  · rw [F.realPolarizedLog_coefficient π p ⟨a, ha⟩]
    exact F.realPolarizedCoefficient_mem π p ⟨a, ha⟩
  · rw [F.realPolarizedLog_coefficient_nonsquarefree π p a ha]
    exact Submodule.zero_mem _

theorem realPolarizedLog_eval (p : F.realification.adaptedLieSubalgebra) (x : ι → ℚ) :
    eval x (F.realPolarizedLog π p) =
      ∑ a, (a.val.prod fun i n => x i ^ n) • F.realPolarizedCoefficient π p a :=
  squarefreePolynomialLift_eval _ x

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem realPolarizedLog_constant (p : F.realification.adaptedLieSubalgebra) :
    coefficients (F.realPolarizedLog π p) 0 = 0 := by
  let a : SquarefreeIndex ι := ⟨0, fun _ => Nat.zero_le 1⟩
  exact (F.realPolarizedLog_coefficient π p a).trans (F.realPolarizedCoefficient_zero π p a rfl)

theorem realPolarizedLog_eval_zero (p : F.realification.adaptedLieSubalgebra) :
    eval (fun _ => 0) (F.realPolarizedLog π p) = 0 := by
  rw [eval_zero_eq_coefficient, F.realPolarizedLog_constant]

noncomputable def realPolarizedOrbit (p : F.realification.adaptedLieSubalgebra) :
    (F.squarefreeMultidegreeFiltration π).realification.PolynomialOrbit :=
  (F.squarefreeMultidegreeFiltration π).realification.polynomialOrbitOfLog
    (F.realPolarizedLog π p) (F.realPolarizedLog_adapted π p)

theorem realPolarizedOrbit_eval_coord (p : F.realification.adaptedLieSubalgebra) (x : ι → ℤ) :
    ((F.squarefreeMultidegreeFiltration π).realification.polynomialOrbitEval x
      (F.realPolarizedOrbit π p)).coord = eval (fun i => (x i : ℚ)) (F.realPolarizedLog π p) := rfl

theorem realPolarizedOrbit_eval_zero (p : F.realification.adaptedLieSubalgebra) :
    (F.squarefreeMultidegreeFiltration π).realification.polynomialOrbitEval 0
      (F.realPolarizedOrbit π p) = 1 := by
  apply NilpotentLieBCHGroup.ext
  exact F.realPolarizedLog_eval_zero π p

end Erdos3.MultidegreeLieFiltration

end

end OAI
