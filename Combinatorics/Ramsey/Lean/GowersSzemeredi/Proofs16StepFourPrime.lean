import GowersSzemeredi.Proofs16PrimeSmallRange
import GowersSzemeredi.Proofs16VarietyUnions

/-! Step 4 of Milićević's proof in prime cyclic groups.

Milićević's Proposition 8.1 (arXiv:2601.01682, printed pp. 61–62) turns
bounded images of alternating sums into vanishing on refined domains. It
uses random characters and his Proposition 2.37, and loses an `ε` fraction
of the tuples. In `ℤ/N` with `N` prime no refinement and no loss are
needed:
* `IsFreimanLinearOn.const_mul`, `IsFreimanLinearOn.finset_sum`: Freiman
  linearity is closed under scalar multiples and finite sums;
* `signed_sum_zero_of_small_image`: let `f_j` be normalized and
  Freiman-linear on `B(T_j; ρ)`, and let the combination `∑ s_j·f_j` take
  at most `K < N` values on the common domain `B(⋃ T_j; ρ)`. Then it
  vanishes on `B(⋃ T_j; ρ/K)`.

This holds for *every* tuple with a bounded image. Only the radius shrinks
(by the factor `K`), and no frequencies are added. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem IsFreimanLinearOn.const_mul {N : Nat} {B : Finset (ZMod N)} {f : ZMod N → ZMod N}
    (hf : IsFreimanLinearOn B f) (s : ZMod N) : IsFreimanLinearOn B fun y => s * f y := by
  intro y₁ y₂ y₃ y₄ m₁ m₂ m₃ m₄ h
  have e := hf y₁ y₂ y₃ y₄ m₁ m₂ m₃ m₄ h
  linear_combination s * e

theorem IsFreimanLinearOn.finset_sum {N : Nat} {B : Finset (ZMod N)} {ι : Type*} (S : Finset ι)
    {f : ι → ZMod N → ZMod N} (hf : ∀ j ∈ S, IsFreimanLinearOn B (f j)) :
    IsFreimanLinearOn B fun y => ∑ j ∈ S, f j y := by
  induction S using Finset.induction_on with
  | empty =>
    intro y₁ y₂ y₃ y₄ _ _ _ _ _
    simp
  | @insert a S ha ih =>
    intro y₁ y₂ y₃ y₄ m₁ m₂ m₃ m₄ h
    have e₁ := hf a (Finset.mem_insert_self a S) y₁ y₂ y₃ y₄ m₁ m₂ m₃ m₄ h
    have e₂ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)) y₁ y₂ y₃ y₄ m₁ m₂ m₃ m₄ h
    simp only [Finset.sum_insert ha]
    linear_combination e₁ + e₂

/-- **Step 4 in `ℤ/N`.** -/
theorem signed_sum_zero_of_small_image {N n K : Nat} [NeZero N] [Fact N.Prime]
    (T : Fin n → Finset (ZMod N)) (f : Fin n → ZMod N → ZMod N) (s : Fin n → ZMod N)
    {ρ : Real} (hρ : 0 ≤ ρ) (hf : ∀ j, IsFreimanLinearOn (bohr (T j) ρ) (f j))
    (hf0 : ∀ j, f j 0 = 0)
    (himage : ((bohr (Finset.univ.biUnion T) ρ).image fun y => ∑ j, s j * f j y).card ≤ K)
    (hK : K < N) :
    ∀ y ∈ bohr (Finset.univ.biUnion T) (ρ / K), ∑ j, s j * f j y = 0 := by
  have hg : IsFreimanLinearOn (bohr (Finset.univ.biUnion T) ρ) fun y => ∑ j, s j * f j y := by
    apply IsFreimanLinearOn.finset_sum
    intro j _
    apply IsFreimanLinearOn.const_mul
    exact (hf j).mono (bohr_anti (Finset.subset_biUnion_of_mem T (Finset.mem_univ j)) ρ)
  have hg0 : (∑ j, s j * f j 0) = 0 := by simp [hf0]
  exact freiman_small_image_zero _ hρ _ hg hg0 himage hK

end LeanProofs.GowersSzemeredi
