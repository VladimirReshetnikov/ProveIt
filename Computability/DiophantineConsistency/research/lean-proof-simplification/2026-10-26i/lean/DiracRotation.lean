import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Tactic

/-! Exact source definitions and convolution congruence from the pinned
NativeCyclicConvolution module; only the Dirac specialization is new. -/
namespace ProofSimplification.DiracRotation
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- The nonnegative coefficient mass, before or after folding the stencil. -/
def mass (a : ZMod n → ℕ) : ℕ := ∑ i, a i

/-- A word indexed by the least representatives of the cyclic positions. -/
def word (ρ : ℕ) (a : ZMod n → ℕ) : ℕ := ∑ i, a i * ρ ^ i.val

/-- Multiplication modulo `X^n - 1`, at the coefficient level. -/
def convolution (a c : ZMod n → ℕ) (k : ZMod n) : ℕ := ∑ i, a i * c (k - i)

theorem convolution_le_mass (a c : ZMod n → ℕ) {D : ℕ}
    (hc : ∀ i, c i ≤ D) (k : ZMod n) : convolution a c k ≤ mass a * D := by
  calc
    convolution a c k ≤ ∑ i, a i * D := by
      apply Finset.sum_le_sum
      intro i _
      exact Nat.mul_le_mul_left _ (hc _)
    _ = mass a * D := by simp only [mass, Finset.sum_mul]

omit [NeZero n] in
theorem base_period {ρ : ℕ} (hρ : 1 ≤ ρ) :
    ρ ^ n ≡ 1 [MOD ρ ^ n - 1] := by
  have hp : 1 ≤ ρ ^ n := one_le_pow₀ hρ
  have he : ρ ^ n = 1 + (ρ ^ n - 1) := by omega
  change ρ ^ n % (ρ ^ n - 1) = 1 % (ρ ^ n - 1)
  exact (congrArg (fun x => x % (ρ ^ n - 1)) he).trans (Nat.add_mod_right _ _)

omit [NeZero n] in
theorem pow_mod_length {ρ : ℕ} (hρ : 1 ≤ ρ) (e : ℕ) :
    ρ ^ e ≡ ρ ^ (e % n) [MOD ρ ^ n - 1] := by
  have he := Nat.mod_add_div e n
  conv_lhs => rw [← he, pow_add, pow_mul]
  simpa only [one_pow, mul_one] using
    (Nat.ModEq.refl (ρ ^ (e % n))).mul ((base_period hρ).pow (e / n))

/-- This congruence holds without any restriction on coefficient size. -/
theorem word_convolution {ρ : ℕ} (hρ : 1 ≤ ρ) (a c : ZMod n → ℕ) :
    word ρ (convolution a c) ≡ word ρ a * word ρ c [MOD ρ ^ n - 1] := by
  have hreindex (i : ZMod n) :
      (∑ k : ZMod n, a i * c (k - i) * ρ ^ k.val) =
        ∑ j : ZMod n, a i * c j * ρ ^ (i + j).val := by
    symm
    apply Fintype.sum_equiv (Equiv.addLeft i)
    intro j
    simp only [Equiv.coe_addLeft, add_sub_cancel_left]
  calc
    word ρ (convolution a c) =
        ∑ i : ZMod n, ∑ j : ZMod n, a i * c j * ρ ^ (i + j).val := by
      simp only [word, convolution, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun i _ => hreindex i)
    _ ≡ ∑ i : ZMod n, ∑ j : ZMod n,
        a i * c j * ρ ^ (i.val + j.val) [MOD ρ ^ n - 1] := by
      apply Nat.ModEq.sum
      intro i _
      apply Nat.ModEq.sum
      intro j _
      have hp := (pow_mod_length (n := n) hρ (i.val + j.val)).symm
      rw [← ZMod.val_add] at hp
      exact hp.mul_left _
    _ = ∑ i : ZMod n, (a i * ρ ^ i.val) * word ρ c := by
      apply Finset.sum_congr rfl
      intro i _
      rw [word, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [pow_add]
      ring
    _ = word ρ a * word ρ c := by rw [← Finset.sum_mul]; rfl


def rotate (c : ZMod n → ℕ) (t k : ZMod n) : ℕ := c (k - t)

/-- A unit point mass acts by translation. -/
theorem convolution_single (c : ZMod n → ℕ) (t : ZMod n) :
    convolution (Pi.single t 1) c = rotate c t := by
  classical
  funext k
  simp [convolution, Pi.single_apply, rotate, ite_mul]

/-- Its word is the corresponding radix power. -/
theorem word_single (ρ : ℕ) (t : ZMod n) :
    word ρ (Pi.single t 1) = ρ ^ t.val := by
  classical
  simp [word, Pi.single_apply, ite_mul]

/-- The original rotation theorem now follows from convolution once. -/
theorem word_rotate {ρ : ℕ} (hρ : 1 ≤ ρ) (c : ZMod n → ℕ) (t : ZMod n) :
    word ρ (rotate c t) ≡ ρ ^ t.val * word ρ c [MOD ρ ^ n - 1] := by
  simpa only [convolution_single, word_single] using
    word_convolution hρ (Pi.single t 1) c

/-- Proof-only replacement requiring no new helper declarations. -/
theorem word_rotate_direct {ρ : ℕ} (hρ : 1 ≤ ρ) (c : ZMod n → ℕ) (t : ZMod n) :
    word ρ (rotate c t) ≡ ρ ^ t.val * word ρ c [MOD ρ ^ n - 1] := by
  classical
  simpa [word, convolution, rotate, Pi.single_apply, ite_mul] using
    word_convolution hρ (Pi.single t 1) c

#print axioms word_rotate_direct
#print axioms convolution_single
#print axioms word_single
#print axioms word_rotate
end ProofSimplification.DiracRotation
