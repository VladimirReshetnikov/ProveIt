/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Lattices.AllocatedSupportedSlicedResidue

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G D : Type*} [Fintype G] [DecidableEq G] [Fintype D] [DecidableEq D]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] (h : D → ℕ)
variable (LG : G → ℕ) (L : PrincipalTupleIndex B h → ℕ)

def kernelZeroTupleFromSumIntegerBox
    (z : integerBox (Sum.elim LG L)) : ∀ g, IntegerScalarCubeBox Empty (LG g) :=
  fun g _ => ⟨z.val (Sum.inl g), Finset.mem_Ico.mpr
    ⟨(neg_nonpos.mpr (Int.natCast_nonneg _)).trans
      ((mem_integerBox (Sum.elim LG L) z.val).mp z.property (Sum.inl g)).1,
      ((mem_integerBox (Sum.elim LG L) z.val).mp z.property (Sum.inl g)).2⟩⟩

def principalZeroTupleFromSumIntegerBox
    (z : integerBox (Sum.elim LG L)) : PrincipalIntegerTuples B h Empty L :=
  fun j _ => ⟨z.val (Sum.inr j), Finset.mem_Ico.mpr
    ⟨(neg_nonpos.mpr (Int.natCast_nonneg _)).trans
      ((mem_integerBox (Sum.elim LG L) z.val).mp z.property (Sum.inr j)).1,
      ((mem_integerBox (Sum.elim LG L) z.val).mp z.property (Sum.inr j)).2⟩⟩

namespace ResidueBoxSlice

variable {B h LG L}
variable {keep : G ⊕ PrincipalTupleIndex B h → Prop} [DecidablePred keep] {q : ℕ}
variable (S : ResidueBoxSlice (fun k : {k // keep k} => Sum.elim LG L k.val) q)
variable (hlen : ∀ k, 0 < S.length k) (fixed : {k // ¬keep k} → ℤ)
variable (hfixed : ∀ k, 0 ≤ fixed k ∧ fixed k < ((Sum.elim LG L k.val : ℕ) : ℤ))
variable (hkernel : ∀ g, keep (Sum.inl g))

omit [Fintype G] [DecidableEq G] [Fintype D] [DecidableEq D]
  [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] [DecidablePred keep] in
theorem fiberKernelProgression_contained (g : G) :
    integerProgressionSupport (S.start ⟨Sum.inl g, hkernel g⟩ : ℤ) (q : ℤ)
        (S.length ⟨Sum.inl g, hkernel g⟩) ⊆ Finset.Ico (0 : ℤ) (LG g : ℤ) := by
  apply integerProgressionSupport_subset_of_fin
  intro t
  constructor
  · positivity
  · exact_mod_cast S.inside ⟨Sum.inl g, hkernel g⟩ t.val t.isLt

include hlen hfixed in
theorem fiberPrincipalParameter_inside (j : PrincipalTupleIndex B h)
    (t : Fin (S.fiberParameterLength (Sum.inr j))) :
    0 ≤ S.fiberParameterStart fixed (Sum.inr j) +
      (fiberParameterStride (keep := keep) (q := q) (Sum.inr j) : ℤ) * t.val ∧
      S.fiberParameterStart fixed (Sum.inr j) +
        (fiberParameterStride (keep := keep) (q := q) (Sum.inr j) : ℤ) * t.val < L j :=
  S.fiberParameter_inside hlen fixed hfixed (Sum.inr j) t

private theorem zeroScalarFinPoint_cube (H : ℕ) (t : Fin H) :
    IntegerScalarCube H (fun i => (zeroScalarFinPoint H t i : ℤ)) := by
  intro row
  have he : row = ∅ := Subsingleton.elim _ _
  simpa only [he, integerScalarCubeValue, Finset.sum_empty, add_zero, zeroScalarFinPoint]
    using And.intro (Int.natCast_nonneg t.val) (show (t.val : ℤ) < H by exact_mod_cast t.isLt)

theorem fiberSliceLaw_kernel_principal_box_complexMean
    (test : integerBox (Sum.elim LG L) → ℂ) :
    (S.fiberSliceLaw hlen fixed hfixed).complexMean test =
      𝔼 g : (∀ i, Fin (S.length ⟨Sum.inl i, hkernel i⟩)),
        𝔼 p : (∀ j, Fin (S.fiberParameterLength (Sum.inr j))),
          test (S.fiberAffinePointInBox fixed hfixed
            (Sum.rec ((S.fiberKernelParameterEquiv hkernel).symm g) p)) := by
  rw [fiberSliceLaw_affine_sum_complexMean]
  apply Fintype.expect_equiv (S.fiberKernelParameterEquiv hkernel)
  intro g
  rw [Equiv.symm_apply_apply]

theorem fiberSliceLaw_kernel_principal_source_complexMean
    (hLG : ∀ g, 0 < LG g)
    (φ : (∀ g, IntegerScalarCubeBox Empty (LG g)) → PrincipalIntegerTuples B h Empty L → ℂ) :
    (S.fiberSliceLaw hlen fixed hfixed).complexMean (fun z =>
      φ (kernelZeroTupleFromSumIntegerBox B h LG L z)
        (principalZeroTupleFromSumIntegerBox B h LG L z)) =
      (FiniteProbabilityWeights.pi (fun g => integerScalarCubeWeights Empty
        (S.length ⟨Sum.inl g, hkernel g⟩) (hlen ⟨Sum.inl g, hkernel g⟩))).complexMean (fun x =>
        (principalAffineIntervalLaw B h L
          (fun j => S.fiberParameterLength (Sum.inr j))
          (fun j => fiberParameterStride (keep := keep) (q := q) (Sum.inr j))
          (fun j => S.fiberParameterStart fixed (Sum.inr j))
          (S.fiberPrincipalParameter_inside hlen fixed hfixed)
          (fun j => S.fiberParameterLength_pos hlen (Sum.inr j))).complexMean (fun y =>
            φ (fun g => containedProgressionCubeMap Empty (LG g)
              (S.length ⟨Sum.inl g, hkernel g⟩) q (S.start ⟨Sum.inl g, hkernel g⟩)
              (hLG g) (S.fiberKernelProgression_contained hkernel g) (x g)) y)) := by
  rw [S.fiberSliceLaw_kernel_principal_box_complexMean hlen fixed hfixed hkernel,
    integerScalarCubeWeights_pi_fin_complexMean]
  apply Finset.expect_congr rfl
  intro g _
  rw [principalAffineIntervalLaw_complexMean]
  apply Finset.expect_congr rfl
  intro p _
  congr 1
  · funext i a
    apply Subtype.ext
    cases a with
    | none =>
      rw [containedProgressionCubeMap_value Empty _ _ _ _ _ _ _ (zeroScalarFinPoint_cube _ _)]
      simp only [kernelZeroTupleFromSumIntegerBox, fiberAffinePointInBox,
        fiberAffineIntegerPoint, fiberParameterStart, fiberParameterStride,
        dite_eq_left (hkernel i), ite_eq_left (hkernel i), fiberKernelParameterEquiv,
        Equiv.coe_fn_symm_mk, zeroScalarFinPoint, ite_true]
    | some a => exact isEmptyElim a

end ResidueBoxSlice
end Erdos3

end

end OAI
