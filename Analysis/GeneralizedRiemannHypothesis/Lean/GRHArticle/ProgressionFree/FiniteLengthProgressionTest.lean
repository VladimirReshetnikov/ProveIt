import GRHArticle.ProgressionFree.GreedyBlockWitnesses

/-!
# Executable tests for finite progression rules

The first two entries determine every later entry of a rational-ratio
progression, or of an affine progression of exponent vectors. The tests
therefore check only finitely many pairs and indices.
-/

namespace GRHArticle.ProgressionFree

open Finset

/-- Check that no two distinct positive initial values start a rational
geometric progression contained in the finite set. -/
def finiteLengthGPTest (k : ℕ) (A : Finset ℕ) : Bool :=
  decide (∀ a ∈ A, ∀ b ∈ A, 0 < a → 0 < b → a ≠ b →
    ¬ ∀ i ∈ range k, ∃ n ∈ A, (n : ℚ) = (a : ℚ)*((b : ℚ)/(a : ℚ))^i)

theorem finiteLengthGPTest_spec {k : ℕ} (hk : 2 ≤ k) (A : Finset ℕ) :
    finiteLengthGPTest k A = true ↔ KTermGPFree k (A : Set ℕ) := by
  rw [finiteLengthGPTest,decide_eq_true_eq]
  constructor
  · intro h x u r hu hr hx hf
    let i₀ : Fin k := ⟨0,by omega⟩
    let i₁ : Fin k := ⟨1,by omega⟩
    have h₀ : (x i₀ : ℚ) = u := by simpa [i₀] using hf i₀
    have h₁ : (x i₁ : ℚ) = u*r := by simpa [i₁] using hf i₁
    have ha₀ : 0 < x i₀ := by exact_mod_cast (show (0 : ℚ) < x i₀ by rwa [h₀])
    have hb₀ : 0 < x i₁ := by
      exact_mod_cast (show (0 : ℚ) < x i₁ by rw [h₁]; exact mul_pos hu hr)
    have hR : (x i₁ : ℚ)/(x i₀ : ℚ) = r := by
      rw [h₀,h₁]
      exact (div_eq_iff hu.ne').mpr (mul_comm _ _)
    by_contra hne
    have hab : x i₀ ≠ x i₁ := by
      intro he
      apply hne
      rw [← hR,← he,div_self (by rw [h₀];exact hu.ne')]
    apply h _ (hx i₀) _ (hx i₁) ha₀ hb₀ hab
    intro i hi
    let j : Fin k := ⟨i,mem_range.mp hi⟩
    refine ⟨x j,hx j,?_⟩
    rw [hR,h₀]
    exact hf j
  · intro h a _ b _ ha₀ hb₀ hab hAll
    choose x hx hx' using fun i : Fin k ↦ hAll i.val (mem_range.mpr i.isLt)
    have ha : (0 : ℚ) < a := by exact_mod_cast ha₀
    have hb : (0 : ℚ) < b := by exact_mod_cast hb₀
    have hRatio := h x (a : ℚ) ((b : ℚ)/(a : ℚ)) ha (div_pos hb ha) hx hx'
    have he := (div_eq_iff ha.ne').mp hRatio
    rw [one_mul] at he
    exact hab (by exact_mod_cast he.symm)

/-- A subset of a progression-free set is progression-free. -/
theorem KTermGPFree.mono {k : ℕ} {A B : Set ℕ} (hB : KTermGPFree k B) (hAB : A ⊆ B) :
    KTermGPFree k A :=
  fun a u r hu hr hm hf ↦ hB a u r hu hr (fun i ↦ hAB (hm i)) hf

/-- Check the affine strings determined by distinct initial vectors. -/
def finiteLengthVectorAPTest {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (A : Finset (ι → ℕ)) : Bool :=
  decide (∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬ ∀ i ∈ range k, ∃ e ∈ A,
    ∀ p : ι, (e p : ℤ) = (a p : ℤ)+(i : ℤ)*((b p : ℤ)-(a p : ℤ)))

theorem finiteLengthVectorAPTest_spec {ι : Type*} [Fintype ι] [DecidableEq ι]
    {k : ℕ} (hk : 2 ≤ k) (A : Finset (ι → ℕ)) :
    finiteLengthVectorAPTest k A = true ↔ KTermVectorAPFree k (A : Set (ι → ℕ)) := by
  rw [finiteLengthVectorAPTest,decide_eq_true_eq]
  constructor
  · intro h x u d hx hf p
    let i₀ : Fin k := ⟨0,by omega⟩
    let i₁ : Fin k := ⟨1,by omega⟩
    have h₀ (q : ι) : (x i₀ q : ℤ) = u q := by simpa [i₀] using hf i₀ q
    have h₁ (q : ι) : (x i₁ q : ℤ) = u q+d q := by simpa [i₁] using hf i₁ q
    by_contra hne
    have he : x i₀ ≠ x i₁ := by
      intro hEq
      have hp := congrArg (fun v : ι → ℕ ↦ (v p : ℤ)) hEq
      rw [h₀ p,h₁ p] at hp
      exact hne (by omega)
    apply h _ (hx i₀) _ (hx i₁) he
    intro j hj
    let i : Fin k := ⟨j,mem_range.mp hj⟩
    refine ⟨x i,hx i,fun q ↦ ?_⟩
    rw [h₀ q,h₁ q,hf i q]
    ring
  · intro h a _ b _ hab hAll
    choose x hx hEq using fun i : Fin k ↦ hAll i.val (mem_range.mpr i.isLt)
    have hz := h x (fun q ↦ (a q : ℤ)) (fun q ↦ (b q : ℤ)-(a q : ℤ)) hx hEq
    apply hab
    funext q
    exact_mod_cast (sub_eq_zero.mp (hz q)).symm

end GRHArticle.ProgressionFree
