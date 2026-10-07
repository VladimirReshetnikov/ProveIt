/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Measurable
import OAI.Combinatorics.Progressions.Sampling.AllocatedLongGridCoordinates

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))

local notation "integerOutput" => {q : output // allocatedLongIntegerCoordinate B U basis S q}

omit [∀ j, Fintype (O j)] in
theorem allocatedLongLatticeScale_pos (q : integerOutput) :
    0 < allocatedLongLatticeScale B U basis S q := by
  rcases q with ⟨⟨⟨⟨j, i | i⟩, ha⟩, o⟩, hq⟩
  · exact False.elim hq
  · exact Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i)

theorem allocatedLongLatticeScale_product :
    (∏ q : integerOutput, allocatedLongLatticeScale B U basis S q) =
      ∏ a : {a // ¬grid a}, allocatedLongJetOutputScale B U basis S (O := O) a := by
  have hs := Fintype.prod_subtype_mul_prod_subtype
    (allocatedLongIntegerCoordinate B U basis S (O := O))
    (allocatedLongCoordinateScale B U basis S (O := O))
  have hz : (∏ q : {q : output // ¬allocatedLongIntegerCoordinate B U basis S q},
      allocatedLongCoordinateScale B U basis S q.val) = 1 := by
    apply Finset.prod_eq_one
    intro q _
    rcases q with ⟨⟨⟨⟨j, i | i⟩, ha⟩, o⟩, hq⟩
    · rfl
    · exact False.elim (hq True.intro)
  rw [hz, mul_one] at hs
  change (∏ q : integerOutput, allocatedLongCoordinateScale B U basis S q.val) = _
  rw [hs, Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro a _
  rcases a with ⟨⟨j, i | i⟩, ha⟩ <;>
    simp [allocatedLongCoordinateScale, allocatedLongJetOutputScale]

omit [∀ j, Fintype (O j)] in
theorem allocatedLongLatticeScale_mesh (q : integerOutput) :
    1 / allocatedLongLatticeScale B U basis S q ≤
      1 / (S.value : ℝ) ^ (layerTailDegree m + 1) := by
  rcases q with ⟨⟨⟨⟨j, i | i⟩, ha⟩, o⟩, hq⟩
  · exact False.elim hq
  · change 1 / (basisAxisScale (basis j) i : ℝ) ≤ _
    apply one_div_le_one_div_of_le (pow_pos (Nat.cast_pos.mpr S.positive) _)
    exact_mod_cast Nat.le_of_lt (Nat.lt_of_not_ge ha)

omit [∀ j, Fintype (O j)] in
theorem allocatedLongRowsFromGrid_measurable :
    Measurable (fun p :
      (UnselectedColumn (allocatedLongIntegerSelect B U basis S (O := O)) → ℝ) ×
        (integerOutput → ℤ) => allocatedLongRowsFromGrid B U basis S p.1 p.2) := by
  apply Measurable.of_eval
  intro a
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · change Measurable (fun p : (UnselectedColumn (allocatedLongIntegerSelect B U basis S (O := O)) → ℝ) × (integerOutput → ℤ) => fun o : O j => p.1 (allocatedLongRealIndex B U basis S j i ha o))
    exact Measurable.of_eval (fun o =>
      (measurable_pi_apply (allocatedLongRealIndex B U basis S j i ha o)).comp measurable_fst)
  · change Measurable (fun p : (UnselectedColumn (allocatedLongIntegerSelect B U basis S (O := O)) → ℝ) × (integerOutput → ℤ) => fun o : O j => p.2 (allocatedLongIntegerIndex B U basis S j i ha o))
    exact Measurable.of_eval (fun o =>
      (measurable_pi_apply (allocatedLongIntegerIndex B U basis S j i ha o)).comp measurable_snd)

end Erdos3.VectorPolynomial

end

end OAI
