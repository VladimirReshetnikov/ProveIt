import OAI.Combinatorics.Progressions.Lattices.ResidueSliceCountingCost

namespace OAI

section

namespace Erdos3

def PhysicalSubbox {σ : Type*} (parent : σ → ℤ) (H : σ → ℕ)
    (lo : σ → ℤ) (N : σ → ℕ) : Prop :=
  ∀ j, parent j ≤ lo j ∧ lo j + N j ≤ parent j + H j

theorem PhysicalSubbox.length_le {σ : Type*} {parent lo : σ → ℤ} {H N : σ → ℕ}
    (h : PhysicalSubbox parent H lo N) (j : σ) : N j ≤ H j := by
  have hj := h j
  omega

theorem PhysicalSubbox.refl {σ : Type*} (lo : σ → ℤ) (N : σ → ℕ) :
    PhysicalSubbox lo N lo N := fun _ => ⟨le_rfl, le_rfl⟩

def ResidueSliceLogCostLE {σ : Type*} (H : σ → ℕ) (lo : σ → ℤ) (N : σ → ℕ)
    (M : ℕ) (a : σ → ℤ) (P : ℝ) : Prop :=
  ∀ j, Real.exp (-P) * (H j : ℝ) ≤ (residueIndexLength (lo j) (lo j + N j) M (a j) : ℝ)

theorem ResidueSliceLogCostLE.mono {σ : Type*} {H N : σ → ℕ} {lo a : σ → ℤ}
    {M : ℕ} {P Q : ℝ} (h : ResidueSliceLogCostLE H lo N M a P) (hPQ : P ≤ Q) :
    ResidueSliceLogCostLE H lo N M a Q := by
  intro j
  exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hPQ))
    (Nat.cast_nonneg (H j))).trans (h j)

theorem residueSliceLogCostLE_of_bounds {σ : Type*}
    (H N : σ → ℕ) (lo a : σ → ℤ) (M : ℕ) (A B : ℝ)
    (hM : 0 < M) (hmodulus : (M : ℝ) ≤ Real.exp B)
    (hwidth : ∀ j, Real.exp (-A) * (H j : ℝ) ≤ (N j : ℝ))
    (hlarge : ∀ j, Real.exp (B + 2) ≤ (N j : ℝ)) :
    ResidueSliceLogCostLE H lo N M a (A + B + 2) := by
  have hMreal : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have htwo : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have htwomodulus : 2 * (M : ℝ) ≤ Real.exp (B + 2) := by
    calc
      2 * (M : ℝ) ≤ 2 * Real.exp B := mul_le_mul_of_nonneg_left hmodulus (by norm_num)
      _ ≤ Real.exp 2 * Real.exp B := mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
      _ = Real.exp (B + 2) := by rw [← Real.exp_add, add_comm]
  have hpaid : 2 * (M : ℝ) * Real.exp (-(A + B + 2)) ≤ Real.exp (-A) := by
    calc
      _ ≤ Real.exp (B + 2) * Real.exp (-(A + B + 2)) :=
        mul_le_mul_of_nonneg_right htwomodulus (Real.exp_pos _).le
      _ = Real.exp (-A) := by rw [← Real.exp_add]; congr 1; ring
  intro j
  have hhalf := (residueIndexLength_half_width (lo j) (a j) (N j) M hM
    (htwomodulus.trans (hlarge j))).2
  have hpaidH := mul_le_mul_of_nonneg_right hpaid (Nat.cast_nonneg (H j))
  apply le_of_mul_le_mul_left (a := 2 * (M : ℝ)) _ (by positivity)
  nlinarith [hwidth j]

end Erdos3

end

end OAI
