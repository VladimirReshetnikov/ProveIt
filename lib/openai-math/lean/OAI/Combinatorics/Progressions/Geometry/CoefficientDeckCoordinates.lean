import OAI.Combinatorics.Progressions.Fourier.EuclideanCoefficientTorus
import OAI.Combinatorics.Progressions.Lattices.CoverBasisResidues
import OAI.Combinatorics.Progressions.Lattices.IntegerKernelCoordinates

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule

variable {K : Type*} {m : ℕ} {J B : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (B j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

abbrev CoefficientDeckResidues (B : Fin m → Type*) (d : ℕ) :=
  ∀ j : Fin m, BoundedCoefficientExponent K (j.val + 1) → B j → ZMod d

noncomputable def coefficientKernelCoordinates (d : ℕ) :
    (quotientIntegerCover (coefficientIntegerLattice (K := K) U) d).ker ≃+
      ∀ j : Fin m, BoundedCoefficientExponent K (j.val + 1) →
        (quotientIntegerCover
          (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup d).ker :=
  (nsmulKernelCongr (G := CoefficientTorus (K := K) U)
    (H := EuclideanCoefficientLayers (K := K) U) (euclideanCoefficientEquiv (K := K) U) d).trans
    ((nsmulKernelPiEquiv (fun j : Fin m => BoundedCoefficientExponent K (j.val + 1) →
        euclideanSubspace (U j) ⧸
          (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) d).trans
      (AddEquiv.piCongrRight fun j => nsmulKernelPiEquiv
        (fun _ : BoundedCoefficientExponent K (j.val + 1) => euclideanSubspace (U j) ⧸
          (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) d))

theorem coefficientKernelCoordinates_val (d : ℕ)
    (x : (quotientIntegerCover (coefficientIntegerLattice (K := K) U) d).ker)
    (j : Fin m) (e : BoundedCoefficientExponent K (j.val + 1)) :
    (coefficientKernelCoordinates U d x j e).val = euclideanCoefficientEquiv U x.val j e := rfl

variable (bW : ∀ j, Basis (B j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

noncomputable def coefficientDeckKernelEquiv (d : ℕ) (hd : 0 < d) :
    CoefficientDeckResidues (K := K) B d ≃+
      (quotientIntegerCover (coefficientIntegerLattice (K := K) U) d).ker :=
  (AddEquiv.piCongrRight fun j : Fin m => AddEquiv.piCongrRight
    fun _ : BoundedCoefficientExponent K (j.val + 1) =>
      coverKernelBasisEquiv
        (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup
        (bW j) d hd).trans (coefficientKernelCoordinates U d).symm

theorem coefficientDeckKernelEquiv_coordinate (d : ℕ) (hd : 0 < d)
    (r : CoefficientDeckResidues (K := K) B d)
    (j : Fin m) (e : BoundedCoefficientExponent K (j.val + 1)) :
    euclideanCoefficientEquiv U (coefficientDeckKernelEquiv U bW d hd r).val j e =
      (coverKernelBasisEquiv
        (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup
        (bW j) d hd (r j e)).val := by
  change euclideanCoefficientEquiv U ((euclideanCoefficientEquiv U).symm _) j e = _
  rw [AddEquiv.apply_symm_apply]
  rfl

end Erdos3.VectorPolynomial

end

end OAI
