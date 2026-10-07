/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.SymmetricIntervalDilation
import OAI.Combinatorics.Progressions.Probability.DenseProductDensity

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

abbrev SymmetricIntegerInterval (N : ℕ) :=
  ↥(Finset.Icc (-(N : ℤ)) (N : ℤ))

instance symmetricIntegerInterval_inhabited (N : ℕ) : Inhabited (SymmetricIntegerInterval N) :=
  ⟨⟨0, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩⟩

theorem symmetricIntegerInterval_card (N : ℕ) :
    Fintype.card (SymmetricIntegerInterval N) = 2*N+1 := by
  simpa only [Fintype.card_coe] using symmetricInterval_card N

theorem symmetricIntegerInterval_abs_le (N : ℕ) (x : SymmetricIntegerInterval N) :
    |(x : ℤ)| ≤ (N : ℤ) :=
  abs_le.mpr (Finset.mem_Icc.mp x.property)

theorem dense_product_signed_box (e : ℕ) (N : Fin e → ℕ)
    {η θ ε : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hN : ∀ i, denseProductDensityBudget e η ≤ N i)
    (hε : 0 ≤ ε) (hsmall : ε ≤ 1/denseProductDensityBudget e η)
    (hdensity : η ≤ nearIntegerDensity
      (fun x : ∀ i, SymmetricIntegerInterval (N i) => θ * ∏ i, ((x i : ℤ) : ℝ)) ε) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ denseProductDensityBudget e η ∧
      NearInteger (denseProductDensityBudget e η*ε / ∏ i, (N i : ℝ)) ((q : ℝ)*θ) := by
  apply dense_product_approximation_density e (X := fun i => SymmetricIntegerInterval (N i))
    (fun _ x => (x : ℤ))
    (fun _ => Subtype.val_injective) N hη hη1 hN
  · intro i
    rw [symmetricIntegerInterval_card]
    omega
  · exact fun i => symmetricIntegerInterval_abs_le (N i)
  · exact hε
  · exact hsmall
  · exact hdensity

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

def intervalDifference (N : ℕ) (y x : Fin N) : SymmetricIntegerInterval N :=
  ⟨(x.val : ℤ)-y.val, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩

theorem intervalDifference_injective (N : ℕ) (y : Fin N) :
    Function.Injective (intervalDifference N y) := by
  intro x x' h
  have he := congrArg Subtype.val h
  dsimp [intervalDifference] at he
  apply Fin.ext
  omega

def intervalBoxDifference {ι : Type*} (N : ι → ℕ)
    (y x : ∀ i, Fin (N i)) : ∀ i, SymmetricIntegerInterval (N i) :=
  fun i => intervalDifference (N i) (y i) (x i)

theorem intervalBoxDifference_injective {ι : Type*} (N : ι → ℕ)
    (y : ∀ i, Fin (N i)) : Function.Injective (intervalBoxDifference N y) := by
  intro x x' h
  funext i
  exact intervalDifference_injective (N i) (y i) (congrFun h i)

theorem intervalBox_card_ratio {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ι → ℕ) (hN : ∀ i, 0 < N i) :
    (1 : ℝ)/3^Fintype.card ι ≤
      (Fintype.card (∀ i, Fin (N i)) : ℝ) /
        Fintype.card (∀ i, SymmetricIntegerInterval (N i)) := by
  have hden : (0 : ℝ) < Fintype.card (∀ i, SymmetricIntegerInterval (N i)) := by
    exact_mod_cast Fintype.card_pos
  apply (div_le_div_iff₀ (by positivity) hden).mpr
  simp only [Fintype.card_pi, Fintype.card_fin, symmetricIntegerInterval_card,
    Nat.cast_prod, one_mul]
  calc
    (∏ i, ((2*N i+1 : ℕ) : ℝ)) ≤ ∏ i, (N i : ℝ)*3 := by
      apply Finset.prod_le_prod₀
      · intro i _
        positivity
      · intro i _
        have hi : (1 : ℝ) ≤ N i := by exact_mod_cast hN i
        push_cast
        linarith
    _ = (∏ i, (N i : ℝ))*3^Fintype.card ι := by
      rw [Finset.prod_mul_distrib]
      simp

theorem nearIntegerDensity_interval_differences {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ι → ℕ) (hN : ∀ i, 0 < N i)
    (a : (∀ i, SymmetricIntegerInterval (N i)) → ℝ) (ε : ℝ)
    {η : ℝ} (hη : 0 ≤ η)
    (hdensity : η ≤ 𝔼 y : ∀ i, Fin (N i),
      nearIntegerDensity (fun x => a (intervalBoxDifference N y x)) ε) :
    η/3^Fintype.card ι ≤ nearIntegerDensity a ε := by
  let : ∀ i, Nonempty (Fin (N i)) := fun i => ⟨⟨0, hN i⟩⟩
  have hd := nearIntegerDensity_fiber_injections a ε (intervalBoxDifference N)
    (intervalBoxDifference_injective N) hdensity
  have hr := mul_le_mul_of_nonneg_left (intervalBox_card_ratio N hN) hη
  apply (le_trans ?_ hd)
  simpa only [← mul_div_assoc, mul_one] using hr

end Erdos3

end

end OAI
