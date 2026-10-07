import OAI.Combinatorics.Progressions.Lattices.JointAffineL1Parameter

namespace OAI

section

namespace Erdos3

open scoped NNReal

noncomputable def kernelCoefficientDensity {I J N : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]
    (A : Matrix I J ℤ) (s : I ↪ J) (hA : (A.submatrix id s).det ≠ 0)
    (S : J → ℝ) (P : I → ℝ) (hS : ∀ j, 0 < S j) (hP : ∀ i, 0 < P i)
    (C : Matrix I N ℤ) (T : N → ℝ) (c w : J ⊕ N → ℝ) : (I → ℝ) → ℝ :=
  pivotOutputDensity
    (normalizedPivotEquiv (A.submatrix id s) hA (fun i => S (s i)) P (fun i => hS (s i)) hP)
    (splitFreeColumns
      (matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns A s) (fun j => S j.val) P))
      (matrixSupCLM (normalizedIntegerColumns C T P)))
    (splitFreeProfile
      (selectedCoefficientProfile s (affineProductProfile (fun j => c (.inl j)) (fun j => w (.inl j))))
      (affineProductProfile (fun n => c (.inr n)) (fun n => w (.inr n))))

theorem selectedCoefficientDensity_eq_kernel {I J N : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]
    (A : Matrix I J ℤ) (s : I ↪ J) (hA : (A.submatrix id s).det ≠ 0)
    (S : J → ℝ) (P : I → ℝ) (hS : ∀ j, 0 < S j) (hP : ∀ i, 0 < P i)
    (C : Matrix I N ℤ) (T : N → ℝ) (hT : ∀ n, 0 < T n)
    (hfull : ((Matrix.fromCols A C).submatrix id (s.trans Function.Embedding.inl)).det ≠ 0)
    (c w : J ⊕ N → ℝ) {δ : ℝ≥0} (hδ : 0 < δ) (hw : ∀ j, (δ : ℝ) ≤ w j)
    (R : ℝ≥0) (hsupport : ∀ j, |c j|+w j ≤ R) :
    selectedCoefficientDensity (Matrix.fromCols A C) (s.trans Function.Embedding.inl) hfull
      (Sum.elim S T) P (Sum.rec hS hT) hP (affineProductProfile c w) =
      kernelCoefficientDensity A s hA S P hS hP C T c w :=
  affineCoefficientDensity_split A C s hA hfull S T P hS hT hP c w hδ hw R hsupport

theorem kernelCoefficientDensity_eq_jet {Z X K α I J N : Type*}
    [Fintype α] [DecidableEq α] [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]
    (A : Matrix I J ℤ) (s : I ↪ J) (hA : (A.submatrix id s).det ≠ 0)
    (S : J → ℝ) (hS : ∀ j, 0 < S j) {H : ℝ} (hH : 0 < H)
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ X) (z : Z → ℝ)
    (rows : I → Finset α) (x : X → ℝ) (vertices : Finset α → K → ℤ) (T : K → ℝ)
    (hcoords : ∀ t k, (vertices t k : ℝ)/T k = normalizedCubeTuple input z x t k)
    (c w : J ⊕ N → ℝ) :
    kernelCoefficientDensity A s hA S (fun _ => H) hS (fun _ => hH)
      (integerJetMatrix (fun n => MvPolynomial.monomial (e n) 1) vertices rows)
      (fun n => H/monomialScale T (e n)) c w =
      affineSelectedJetDensity s
        (normalizedPivotEquiv (A.submatrix id s) hA (fun i => S (s i)) (fun _ => H)
          (fun i => hS (s i)) (fun _ => hH))
        (matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns A s) (fun j => S j.val) (fun _ => H)))
        e input z rows c w x := by
  unfold kernelCoefficientDensity affineSelectedJetDensity normalizedJetDensity
  rw [normalizedIntegerJetColumns_eq e input z rows x vertices T hcoords hH.ne']

end Erdos3

end

end OAI
