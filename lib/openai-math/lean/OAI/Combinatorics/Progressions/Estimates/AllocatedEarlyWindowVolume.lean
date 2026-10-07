/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Sampling.AllocatedGridNaturalWindow

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*}
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (α : Type*) [Fintype α] (O : Fin m → Type*) [∀ j, Fintype (O j)]

noncomputable def allocatedGridWindowEarlyCap : ℝ :=
  1 + ∑ j : Fin m, ∑ i : Fin (n j),
    (2 * allocatedNaturalSupportRadius (G := G) B α j i + 3) ^ Fintype.card (O j)

noncomputable def allocatedGridWindowEarlyVolume : ℝ :=
  allocatedGridWindowEarlyCap (G := G) B α O ^ Fintype.card (LayerSamplerAxis I n)

omit [∀ j, Fintype (I j)] in
theorem allocatedGridWindowEarlyCap_one_le :
    1 ≤ allocatedGridWindowEarlyCap (G := G) B α O := by
  have hs : 0 ≤ ∑ j : Fin m, ∑ i : Fin (n j),
      (2 * allocatedNaturalSupportRadius (G := G) B α j i + 3) ^ Fintype.card (O j) := by
    apply Finset.sum_nonneg
    intro j _
    apply Finset.sum_nonneg
    intro i _
    exact pow_nonneg (by linarith [allocatedNaturalSupportRadius_nonneg (G := G) B α j i]) _
  unfold allocatedGridWindowEarlyCap
  linarith

theorem allocatedGridWindowEarlyVolume_nonneg :
    0 ≤ allocatedGridWindowEarlyVolume (G := G) B α O :=
  pow_nonneg (zero_le_one.trans (allocatedGridWindowEarlyCap_one_le (G := G) B α O)) _

variable [Fintype G]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)

theorem allocatedSelectedNaturalWindowVolume_le_early
    (selected : {a // grid a} → Prop) [DecidablePred selected] :
    allocatedSelectedNaturalWindowVolume B U b S α O selected ≤
      allocatedGridWindowEarlyVolume (G := G) B α O := by
  let F (j : Fin m) (i : Fin (n j)) : ℝ :=
    (2 * allocatedNaturalSupportRadius (G := G) B α j i + 3) ^ Fintype.card (O j)
  let C := allocatedGridWindowEarlyCap (G := G) B α O
  have hC : 1 ≤ C := allocatedGridWindowEarlyCap_one_le (G := G) B α O
  have hF (j : Fin m) (i : Fin (n j)) : 0 ≤ F j i :=
    pow_nonneg (by linarith [allocatedNaturalSupportRadius_nonneg (G := G) B α j i]) _
  have hFC (j : Fin m) (i : Fin (n j)) : F j i ≤ C := by
    have hi : F j i ≤ ∑ i' : Fin (n j), F j i' :=
      Finset.single_le_sum (fun i' _ => hF j i') (Finset.mem_univ i)
    have hj : (∑ i' : Fin (n j), F j i') ≤ ∑ j' : Fin m, ∑ i' : Fin (n j'), F j' i' :=
      Finset.single_le_sum (f := fun j' : Fin m => ∑ i' : Fin (n j'), F j' i')
        (fun j' _ => Finset.sum_nonneg (fun i' _ => hF j' i')) (Finset.mem_univ j)
    change F j i ≤ 1 + ∑ j' : Fin m, ∑ i' : Fin (n j'), F j' i'
    linarith
  have hfactor (a : {a // grid a}) :
      (if selected a then (2 * allocatedFrozenNaturalRadius B U b S α a + 3) ^ Fintype.card (O a.val.1) else 1) ≤ C := by
    by_cases ha : selected a
    · simp only [ha, ite_true]
      rcases a with ⟨⟨j, i | i⟩, hgrid⟩
      · exact False.elim hgrid
      · exact hFC j i
    · simpa only [ha, ite_false] using hC
  calc
    allocatedSelectedNaturalWindowVolume B U b S α O selected ≤ ∏ _a : {a // grid a}, C := by
      apply Finset.prod_le_prod₀
      · intro a _
        split_ifs
        · exact pow_nonneg (by linarith [allocatedFrozenNaturalRadius_nonneg B U b S α a]) _
        · exact zero_le_one
      · intro a _
        exact hfactor a
    _ = C ^ Fintype.card {a // grid a} := by simp only [Finset.prod_const, Finset.card_univ]
    _ ≤ C ^ Fintype.card (LayerSamplerAxis I n) :=
      pow_le_pow_right₀ hC (Fintype.card_le_of_injective Subtype.val Subtype.val_injective)
    _ = allocatedGridWindowEarlyVolume (G := G) B α O := rfl

end Erdos3.VectorPolynomial

end

end OAI
