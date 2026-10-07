import OAI.Combinatorics.Progressions.Lattices.AllocatedOriginalGenuineAffine

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype activeAmbientAxisDecidableEq

variable {m dim : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) (Fin.val j + 1))
local notation "jetRows" => (fun j : Fin m => (Subtype.val : jets j → Finset (Fin dim)))
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "fullRows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))

theorem allocatedProductCoarseRawData_normalized_box_affine
    {Psp E e pNum Pbase pAccuracy pSampling l F : ℝ} (hP : 0 ≤ Psp) (hE : 0 ≤ E)
    (hPbase : Psp ≤ Pbase) (hpNum : pNum ≤ Pbase)
    (hm : ((m + 1 : ℕ) : ℝ) ≤ Psp) (hdim : ((dim + 1 : ℕ) : ℝ) ≤ Psp)
    (hG : (Fintype.card G : ℝ) ≤ Psp) (hl : Pbase ≤ l) (hF : 0 ≤ F)
    (hnum : ∀ (_o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
      (C V : Fin m → ℝ≥0), (∀ j, (C j : ℝ) ≤ Real.exp pNum) →
      (∀ j, (V j : ℝ) ≤ Real.exp pNum) → AllocatedSourceNumerics B U b S C V Pbase)
    {δ : ℝ≥0} {A Kraw Ksite Knorm : ℕ}
    (hKraw : 1 ≤ Kraw) (hKsite : 1 ≤ Ksite) (hKnorm : 1 ≤ Knorm)
    (hnorm : AllocatedSourceNarrowNormalization.{uG,uI,uB,uJ,uX} m Knorm)
    (witnesses : (q : AllocatedRefinedPeriodIndex m Psp) →
      (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
      AllocatedFullGridResidueWitness (dim := dim) B U b S (q.val : ℕ) r.val)
    (M Dwin : ℕ) (hM : 0 < M) (hDwin : 0 < Dwin) (η : ℝ) (hη : 0 < η) :
    let Qraw := allocatedSourceSamplingBudget m dim A Pbase (E + 2) l F
    AllocatedProductCoarseRawData.{uG,uI,uB,uJ,uQ,uX}
      B U b hR hσ S Psp E e pNum Pbase Qraw pAccuracy pSampling hP δ A Kraw Ksite witnesses →
    AllocatedProductCoarseBoxAffineData.{uG,uI,uB,uJ,uQ,uX}
      B U b hR hσ S Psp E e pNum Pbase Qraw pAccuracy pSampling hP δ A Kraw (max Ksite Knorm) witnesses
      M Dwin hM hDwin η hη := by
  intro Qraw hraw
  have hkernel : AllocatedProductCoarseKernelData.{uG,uI,uB,uJ,uQ,uX}
      B U b hR hσ S Psp E e pNum Pbase Qraw pAccuracy pSampling hP δ A Kraw Ksite witnesses :=
    allocatedProductCoarseKernelData_of_raw B U b hR hσ S hP witnesses hraw
  have hnormalized : AllocatedProductCoarseNormalizedKernelData.{uG,uI,uB,uJ,uQ,uX}
      B U b hR hσ S Psp E e pNum Pbase Qraw pAccuracy pSampling hP δ A Kraw (max Ksite Knorm) witnesses :=
    allocatedProductCoarseKernelData_normalized B U b hR hσ S hP hE hPbase hpNum
      hm hdim hG hl hF hnum hKraw hKsite hKnorm hnorm witnesses hkernel
  have haffine : AllocatedProductCoarseNormalizedAffineData.{uG,uI,uB,uJ,uQ,uX}
      B U b hR hσ S Psp E e pNum Pbase Qraw pAccuracy pSampling hP δ A Kraw (max Ksite Knorm) witnesses
      M Dwin hM hDwin η hη :=
    allocatedProductCoarseNormalizedAffineData_of_kernel B U b hR hσ S hP witnesses
      hnormalized M Dwin hM hDwin η hη
  exact allocatedProductCoarseBoxAffineData_of_normalized B U b hR hσ S hP witnesses M Dwin hM hDwin η hη haffine

end Erdos3.VectorPolynomial

end

end OAI
