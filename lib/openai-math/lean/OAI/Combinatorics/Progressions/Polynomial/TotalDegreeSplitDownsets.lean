/- Modified for ProveIt: Import the finite-weight compatibility lemma for Lean 4.32.
Mathematical statements and proof bodies are unchanged. -/
import OAI.Compat.FinsuppWeight
import Mathlib.Data.Fin.VecNotation
import Mathlib.Order.UpperLower.Basic
import OAI.Combinatorics.Progressions.Estimates.PolarizedCoefficientPermutation

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open scoped BigOperators

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem totalDegree_zero_layer : F.layer 0 = ⊤ := by
  apply top_unique
  rw [← F.one_eq_top]
  exact F.antitone (Nat.zero_le 1)

noncomputable def totalDegreeMultifiltration (σ : Type*) [Fintype σ] [Nonempty σ] :
    MultidegreeLieFiltration σ L s (fun _ => s) := by
  classical
  exact {
    ordinary := F
    layer := fun a => F.layer (∑ i, a i)
    antitone := fun _ _ h => F.antitone (Finset.sum_le_sum fun i _ => h i)
    zero_eq_top := by simpa only [Pi.zero_apply, Finset.sum_const_zero] using F.totalDegree_zero_layer
    lie_mem := by
      intro a b x y hx hy
      simpa only [Pi.add_apply, Finset.sum_add_distrib] using F.lie_mem hx hy
    terminal := by
      intro a ha
      change ¬∀ i, a i ≤ s at ha
      push Not at ha
      obtain ⟨i, hi⟩ := ha
      have hsum : a i ≤ ∑ j, a j :=
        Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) (Finset.mem_univ i)
      exact F.layer_eq_bot_above_step (hi.trans_le hsum)
    degree_eq := by
      intro n
      apply le_antisymm
      · let i : σ := Classical.choice (inferInstance : Nonempty σ)
        let a : σ → ℕ := Pi.single i n
        have hsum : ∑ j, a j = n := by simp [a]
        apply le_iSup_of_le a
        apply le_iSup_of_le (show n ≤ ∑ j, a j by omega)
        rw [hsum]
      · apply iSup_le
        intro a
        apply iSup_le
        intro ha
        exact F.antitone ha }

theorem totalDegreeMultifiltration_layer (σ : Type*) [Fintype σ] [Nonempty σ]
    (a : σ → ℕ) : (F.totalDegreeMultifiltration σ).layer a = F.layer (∑ i, a i) := rfl

theorem totalDegreeMultifiltration_real_layer (σ : Type*) [Fintype σ] [Nonempty σ]
    (a : σ → ℕ) :
    (F.totalDegreeMultifiltration σ).realification.layer a =
      F.realification.layer (∑ i, a i) := rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped BigOperators TensorProduct

variable {σ L : Type*} [Fintype σ] [Nonempty σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} (F : NilpotentLieFiltration L s)

theorem totalDegree_adapted (g : F.PolynomialOrbit (fun _ : σ => 1)) :
    (F.totalDegreeMultifiltration σ).Adapted g.log := by
  intro a
  change coefficients g.log a ∈ F.layer (∑ i, a i)
  simpa only [Finsupp.weight_eq_sum, smul_eq_mul, mul_one] using
    (F.adapted_iff_coefficients (fun _ : σ => 1) g.log).mp g.adapted a

noncomputable def totalDegreeOrbit (g : F.PolynomialOrbit (fun _ : σ => 1)) :
    (F.totalDegreeMultifiltration σ).PolynomialOrbit :=
  (F.totalDegreeMultifiltration σ).polynomialOrbitOfLog g.log (F.totalDegree_adapted g)

theorem totalDegreeOrbit_eval (g : F.PolynomialOrbit (fun _ : σ => 1)) (x : σ → ℤ) :
    (F.totalDegreeMultifiltration σ).polynomialOrbitEval x (F.totalDegreeOrbit g) =
      F.polynomialOrbitEval (fun _ : σ => 1) x g := rfl

theorem real_totalDegree_adapted (g : F.realification.PolynomialOrbit (fun _ : σ => 1)) :
    (F.totalDegreeMultifiltration σ).realification.Adapted g.log := by
  intro a
  change coefficients g.log a ∈ F.realification.layer (∑ i, a i)
  simpa only [Finsupp.weight_eq_sum, smul_eq_mul, mul_one] using
    (F.realification.adapted_iff_coefficients (fun _ : σ => 1) g.log).mp g.adapted a

noncomputable def realTotalDegreeOrbit (g : F.realification.PolynomialOrbit (fun _ : σ => 1)) :
    (F.totalDegreeMultifiltration σ).realification.PolynomialOrbit :=
  (F.totalDegreeMultifiltration σ).realification.polynomialOrbitOfLog g.log
    (F.real_totalDegree_adapted g)

theorem realTotalDegreeOrbit_eval (g : F.realification.PolynomialOrbit (fun _ : σ => 1))
    (x : σ → ℤ) :
    (F.totalDegreeMultifiltration σ).realification.polynomialOrbitEval x (F.realTotalDegreeOrbit g) =
      F.realification.polynomialOrbitEval (fun _ : σ => 1) x g := rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open scoped BigOperators

def totalDegreeSplitBound (s : ℕ) (b : Bool) : Fin 2 → ℕ :=
  ![if b then s else 0, if b then s - 1 else s]

def totalDegreeSplitDownset (s : ℕ) (b : Bool) : Set (Fin 2 →₀ ℕ) :=
  {a | ∀ i, a i ≤ totalDegreeSplitBound s b i}

theorem totalDegreeSplitBound_le (s : ℕ) (b : Bool) :
    totalDegreeSplitBound s b ≤ fun _ => s := by
  intro i
  fin_cases i <;> cases b <;> simp [totalDegreeSplitBound]

theorem totalDegreeSplitDownset_lower (s : ℕ) (b : Bool) :
    IsLowerSet (totalDegreeSplitDownset s b) :=
  fun _ _ hab hb i => (hab i).trans (hb i)

theorem mem_totalDegreeSplitDownset_false (s : ℕ) (a : Fin 2 →₀ ℕ) :
    a ∈ totalDegreeSplitDownset s false ↔ a 0 = 0 ∧ a 1 ≤ s := by
  simp [totalDegreeSplitDownset, totalDegreeSplitBound, Fin.forall_fin_two]

theorem mem_totalDegreeSplitDownset_true (s : ℕ) (a : Fin 2 →₀ ℕ) :
    a ∈ totalDegreeSplitDownset s true ↔ a 0 ≤ s ∧ a 1 ≤ s - 1 := by
  simp [totalDegreeSplitDownset, totalDegreeSplitBound, Fin.forall_fin_two]

theorem totalDegreeSplitDownset_covers (s : ℕ) (a : Fin 2 →₀ ℕ)
    (ha : (∑ i, a i) ≤ s) :
    a ∈ totalDegreeSplitDownset s false ∪ totalDegreeSplitDownset s true := by
  rw [Fin.sum_univ_two] at ha
  by_cases hzero : a 0 = 0
  · exact Or.inl ((mem_totalDegreeSplitDownset_false s a).mpr ⟨hzero, by omega⟩)
  · exact Or.inr ((mem_totalDegreeSplitDownset_true s a).mpr ⟨by omega, by omega⟩)

theorem totalDegreeSplitDownset_terminal {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} (F : NilpotentLieFiltration L s) (a : Fin 2 →₀ ℕ)
    (ha : a ∉ totalDegreeSplitDownset s false ∪ totalDegreeSplitDownset s true) :
    (F.totalDegreeMultifiltration (Fin 2)).layer (fun i => a i) = ⊥ := by
  apply F.layer_eq_bot_above_step
  exact Nat.lt_of_not_ge (fun h => ha (totalDegreeSplitDownset_covers s a h))

end Erdos3

end

end OAI
