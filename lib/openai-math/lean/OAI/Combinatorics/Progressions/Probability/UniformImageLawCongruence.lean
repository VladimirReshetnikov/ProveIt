import OAI.Combinatorics.Progressions.Lattices.UniformResidueSmallPeriod

namespace OAI

section

namespace Erdos3

open scoped Classical Matrix

theorem uniformPMF_map_hom_eq_of_range_eq {G G' H : Type*}
    [AddCommGroup G] [AddCommGroup G'] [AddCommGroup H]
    [Fintype G] [Fintype G'] [Fintype H]
    (f : G →+ H) (g : G' →+ H) (h : f.range = g.range) :
    (PMF.uniformOfFintype G).map f = (PMF.uniformOfFintype G').map g := by
  ext y
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  simp only [uniformPMF_map_hom_image, h]

theorem integerResidueMatrix_range_eq_of_integer_range_eq
    {I J K : Type*} [Fintype J] [Fintype K]
    (A : Matrix I J ℤ) (B : Matrix I K ℤ)
    (h : A.mulVecLin.range = B.mulVecLin.range) (d : ℕ) :
    (integerResidueMatrix A d).mulVecLin.toAddMonoidHom.range =
      (integerResidueMatrix B d).mulVecLin.toAddMonoidHom.range := by
  ext y
  change (∃ x, integerResidueMatrix A d *ᵥ x = y) ↔
    (∃ x, integerResidueMatrix B d *ᵥ x = y)
  rw [← integerMatrixResidue_mem, ← integerMatrixResidue_mem, h]

theorem uniformResidueMatrix_law_eq_of_integer_range_eq
    {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    (A : Matrix I J ℤ) (B : Matrix I K ℤ)
    (h : A.mulVecLin.range = B.mulVecLin.range) (d : ℕ) [NeZero d] :
    (PMF.uniformOfFintype (J → ZMod d)).map (fun x => integerResidueMatrix A d *ᵥ x) =
      (PMF.uniformOfFintype (K → ZMod d)).map (fun x => integerResidueMatrix B d *ᵥ x) :=
  uniformPMF_map_hom_eq_of_range_eq
    (integerResidueMatrix A d).mulVecLin.toAddMonoidHom
    (integerResidueMatrix B d).mulVecLin.toAddMonoidHom
    (integerResidueMatrix_range_eq_of_integer_range_eq A B h d)

end Erdos3

end

end OAI
