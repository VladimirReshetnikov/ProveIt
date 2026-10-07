import OAI.Combinatorics.Progressions.Estimates.ComplexFiniteMeans

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [DecidableEq G]

noncomputable def realUniformMass (A : Finset G) (x : G) : ℝ :=
  if x ∈ A then (A.card : ℝ)⁻¹ else 0

theorem realUniformMass_nonneg (A : Finset G) (x : G) : 0 ≤ realUniformMass A x := by
  unfold realUniformMass
  split_ifs <;> positivity

theorem sum_realUniformMass [Fintype G] {A : Finset G} (hA : A.Nonempty) :
    ∑ x, realUniformMass A x = 1 := by
  have hcard : (A.card : ℝ) ≠ 0 := by exact_mod_cast hA.card_pos.ne'
  simp [realUniformMass, hcard]

theorem uniformMass_translation_le_shell [Fintype G] [AddCommGroup G]
    (A I O : Finset G) (t : G)
    (hinner : ∀ x ∈ I, x ∈ A ∧ x - t ∈ A)
    (houter : ∀ x, x ∈ A ∨ x - t ∈ A → x ∈ O) :
    ∑ x, |realUniformMass A (x - t) - realUniformMass A x| ≤
      ((O.card : ℝ) - I.card) / A.card := by
  have hpoint (x : G) :
      |realUniformMass A (x - t) - realUniformMass A x| ≤
        (if x ∈ O then (A.card : ℝ)⁻¹ else 0) -
          (if x ∈ I then (A.card : ℝ)⁻¹ else 0) := by
    by_cases hi : x ∈ I
    · obtain ⟨ha, ht⟩ := hinner x hi
      have ho := houter x (Or.inl ha)
      simp [realUniformMass, hi, ho, ha, ht]
    · by_cases ha : x ∈ A <;> by_cases ht : x - t ∈ A
      · have ho := houter x (Or.inl ha)
        simp [realUniformMass, hi, ho, ha, ht]
      · have ho := houter x (Or.inl ha)
        simp [realUniformMass, hi, ho, ha, ht]
      · have ho := houter x (Or.inr ht)
        simp [realUniformMass, hi, ho, ha, ht]
      · simp only [realUniformMass, ha, ht, hi, ite_false, sub_zero, abs_zero]
        split_ifs <;> positivity
  calc
    _ ≤ ∑ x, ((if x ∈ O then (A.card : ℝ)⁻¹ else 0) -
        (if x ∈ I then (A.card : ℝ)⁻¹ else 0)) := Finset.sum_le_sum (fun x _ => hpoint x)
    _ = _ := by simp [Finset.sum_sub_distrib, div_eq_mul_inv, sub_mul]

end Erdos3

end

section

open Finset
open scoped BigOperators

namespace Erdos3

noncomputable section

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

def massConvolution (f g : G → ℝ) (x : G) : ℝ :=
  ∑ y : G, f y * g (x - y)

omit [AddCommGroup G] [Fintype G] in
@[simp]
theorem realUniformMass_apply_mem {A : Finset G} {x : G} (hx : x ∈ A) :
    realUniformMass A x = (#A : ℝ)⁻¹ := by
  simp [realUniformMass, hx]

omit [AddCommGroup G] [Fintype G] in
@[simp]
theorem realUniformMass_apply_not_mem {A : Finset G} {x : G} (hx : x ∉ A) :
    realUniformMass A x = 0 := by
  simp [realUniformMass, hx]

omit [AddCommGroup G] [Fintype G] in
theorem realUniformMass_ne_zero_iff {A : Finset G} (hA : A.Nonempty) (x : G) :
    realUniformMass A x ≠ 0 ↔ x ∈ A := by
  unfold realUniformMass
  split_ifs with hx
  · simp [hx, hA.card_ne_zero]
  · simp [hx]

omit [DecidableEq G] in
theorem massConvolution_nonneg {f g : G → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) (z : G) :
    0 ≤ massConvolution f g z := by
  exact sum_nonneg fun x _ ↦ mul_nonneg (hf x) (hg (z - x))

omit [DecidableEq G] in

theorem massConvolution_comm (f g : G → ℝ) :
    massConvolution f g = massConvolution g f := by
  funext x
  rw [massConvolution, massConvolution]
  refine Fintype.sum_equiv (Equiv.subLeft x) _ _ fun y ↦ ?_
  simp [mul_comm]

omit [DecidableEq G] in

theorem sum_massConvolution (f g : G → ℝ) :
    ∑ x : G, massConvolution f g x = (∑ x : G, f x) * ∑ x : G, g x := by
  simp_rw [massConvolution, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [← Finset.mul_sum]
  congr 1
  exact Fintype.sum_equiv (Equiv.subRight y) _ _ fun x ↦ by simp

def convolutionPower (f : G → ℝ) : ℕ → G → ℝ
  | 0 => realUniformMass {0}
  | n + 1 => massConvolution (convolutionPower f n) f

@[simp] theorem convolutionPower_zero (f : G → ℝ) :
    convolutionPower f 0 = realUniformMass {0} := rfl

@[simp] theorem convolutionPower_succ (f : G → ℝ) (n : ℕ) :
    convolutionPower f (n + 1) =
      massConvolution (convolutionPower f n) f := rfl

theorem convolutionPower_nonneg {f : G → ℝ} (hf : ∀ x, 0 ≤ f x) :
    ∀ n x, 0 ≤ convolutionPower f n x := by
  intro n
  induction n with
  | zero =>
      exact realUniformMass_nonneg {0}
  | succ n ihn =>
      exact massConvolution_nonneg ihn hf

theorem sum_convolutionPower {f : G → ℝ} (hf : ∑ x : G, f x = 1) :
    ∀ n, ∑ x : G, convolutionPower f n x = 1 := by
  intro n
  induction n with
  | zero =>
      exact sum_realUniformMass (singleton_nonempty 0)
  | succ n ihn =>
      rw [convolutionPower_succ, sum_massConvolution, ihn, hf, one_mul]

end

end Erdos3

end

end OAI
