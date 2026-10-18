import GowersSzemeredi.Proofs16MultilinearProduct
import GowersSzemeredi.Proofs16ProductEndpointSide

/-! The converse endpoint: every multilinear graph has unit product property,
with arbitrary nonnegative weights and arbitrarily many parallel lines.

Moved here from `Proofs16MultilinearProduct`, which keeps only what the final
route uses. -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace LeanProofs.GowersSzemeredi

/-- The weighted additive-energy lower bound is the zero-map case of the
proved Fourier product-property criterion. -/
theorem section16_zero_unit_product {N k : Nat} [NeZero N] :
    HasProductProperty (Finset.univ : Finset (Point N k)) (fun _ => 0) 1 := by
  have hzero : HasProductProperty (Finset.univ : Finset (Point N 1)) (fun _ => 0) 1 := by
    apply lemma_14_2_holds N 1 1 (fun _ => 1) Finset.univ (fun _ => 0) zero_lt_one
      (fun _ => by simp)
    intro y _
    have hd : cubeDifference (fun _ : ZMod N => (1 : Complex)) y = fun _ => 1 := by
      funext x
      simp [cubeDifference, List.ofFn_succ, iteratedDifference, difference]
    rw [hd]
    simp [fourier, ZMod.dft_apply_zero]
  intro p j y E theta ht _
  exact hzero p 0 (fun _ => 0) E theta ht (fun _ _ _ => Finset.mem_univ _)

/-- Affine coordinate restrictions automatically preserve every additive
quadruple, so the simultaneous energy is exactly the zero-map energy. -/
theorem HasProductProperty.of_coordinate_linear {N k : Nat} [NeZero N]
    (phi : Point N k → ZMod N)
    (h : ∀ y j, LinearOn Finset.univ (coordinateRestriction phi y j)) :
    HasProductProperty Finset.univ phi 1 := by
  intro p j y E theta ht hE
  have hz := (section16_zero_unit_product (N := N) (k := k)) p j y E theta ht hE
  have heq : weightedSimultaneousAdditiveEnergy E theta
      (fun i => coordinateRestriction phi (y i) j) =
      weightedSimultaneousAdditiveEnergy E theta
        (fun _ : Fin p => fun _ => 0) := by
    unfold weightedSimultaneousAdditiveEnergy
    apply Finset.sum_congr rfl
    intro q _
    have hh (hq : IsAdditiveQuadruple q) (i : Fin p) :
        IsAdditiveQuadruple (fun t => coordinateRestriction phi (y i) j (q t)) := by
      obtain ⟨a, b, hab⟩ := h (y i) j
      unfold IsAdditiveQuadruple at *
      simp only [hab _ (Finset.mem_univ _)]
      linear_combination a * hq
    by_cases hq : IsAdditiveQuadruple q
    · have h0 : IsAdditiveQuadruple (fun _ : Fin 4 => (0 : ZMod N)) := by
        simp [IsAdditiveQuadruple]
      simp only [hq, hh hq, h0, implies_true, and_true]
    · simp only [hq, false_and, and_false, if_false]
  rw [heq]
  exact hz

theorem IsMultilinear.unit_productProperty {N k : Nat} [NeZero N]
    {phi : Point N k → ZMod N} (h : IsMultilinear phi) :
    HasProductProperty Finset.univ phi 1 :=
  HasProductProperty.of_coordinate_linear phi h.linearOn_coordinate

end LeanProofs.GowersSzemeredi

namespace LeanProofs.GowersSzemeredi

/-- Exact full-domain endpoint equivalence, independent of the quantitative
induction and the invalid packaged branch-cover implication. -/
theorem section16_unit_product_iff_multilinear {N k : Nat} [NeZero N] [Fact N.Prime]
    (phi : Point N k → ZMod N) :
    HasProductProperty Finset.univ phi 1 ↔ IsMultilinear phi :=
  ⟨HasProductProperty.unit_multilinear, IsMultilinear.unit_productProperty⟩

end LeanProofs.GowersSzemeredi
