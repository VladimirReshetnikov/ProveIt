import OAI.Combinatorics.Progressions.Geometry.AllocatedFullSiteSupport

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "jets" => (fun j : Fin m => BoundedBooleanJet α ((j : ℕ) + 1))
local notation "jetRows" => (fun j => (Subtype.val : jets j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "output" => (Σ a : {a // ¬grid a}, jets (Sigma.fst (Subtype.val a)))
local notation "volume" => (∏ q : output, R (Sigma.fst (Subtype.val (Sigma.fst q))))
local notation "scale" => (∏ a : {a // ¬grid a}, allocatedLongJetOutputScale B U b S (O := jets) a)
local notation "quarter" => (fun j (_ : jets j) => standardLatticeClosedQuarterBox (J j))
local notation "chart" => mixedCoveredJetChart (O := jets) U o b hb bW d
local notation "split" => coefficientJetAxisSplit jets I n grid

variable (modulus : ℕ)

noncomputable def allocatedCoveredSitePrefactor
    (residue : ∀ j : Fin m, Matrix (BoundedBooleanJet α (j.val + 1))
      (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    (z : MixedCoveredJetSource I jets Q n d) : ℂ :=
  (allocatedCoveredFixedFactor B U b hR hσ S x u v jetRows Q d z.1 z.2 : ℂ) *
    ((∏ a, allocatedLongJetMask B U b S x jetRows modulus residue a ((split z.1).2 a) : ℝ) : ℂ) /
      ((volume : ℝ) : ℂ) / ((scale : ℝ) : ℂ)

omit [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))] in
theorem allocatedCoveredSiteTerm_factorization
    (residue : ∀ j : Fin m, Matrix (BoundedBooleanJet α (j.val + 1))
      (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    (f : Finset α → (LayerSamplerAxis I n → ℝ) → ℂ)
    (z : MixedCoveredJetSource I jets Q n d)
    (hz : z ∈ mixedCoveredJetRegion U o b d quarter)
    (hs : ∀ s, mixedCoveredBooleanSiteValue d z s ∈ mixedCoveredJetRegion (E := Q) U o b d
      (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))) :
    allocatedCoveredComplexProfileDensity B U b hR hσ S x u v jetRows hb o bW d quarter
        (allocatedSiteTermDensity B U b S x modulus residue f) (chart z) =
      allocatedCoveredSitePrefactor B U b hR hσ S x u v d modulus residue z *
        ∏ s, allocatedIdealSiteChartFactor B U b S o hb bW d (f s)
          (coveredBooleanSiteValue U (chart z) s) := by
  rw [allocatedCoveredComplexProfileDensity, restrictedComplexChartDensity_apply _ _ _ _
    (mixedCoveredJetChart_injOn U o b hb bW d quarter
      (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))) hz,
    Complex.ofReal_one, one_mul, allocatedSiteTermDensity,
    allocatedIdealSiteChartFactor_product B U b S o hb bW d f z hs]
  unfold allocatedCoveredSitePrefactor
  ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "jets" => (fun j : Fin m => BoundedBooleanJet α ((j : ℕ) + 1))
local notation "jetRows" => (fun j => (Subtype.val : jets j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "output" => (Σ a : {a // ¬grid a}, jets (Sigma.fst (Subtype.val a)))
local notation "volume" => (∏ q : output, R (Sigma.fst (Subtype.val (Sigma.fst q))))
local notation "scale" => (∏ a : {a // ¬grid a}, allocatedLongJetOutputScale B U b S (O := jets) a)
local notation "quarter" => (fun j (_ : jets j) => standardLatticeClosedQuarterBox (J j))
local notation "chart" => mixedCoveredJetChart (O := jets) U o b hb bW d
local notation "split" => coefficientJetAxisSplit jets I n grid

variable (r : ℝ≥0) (hr : 0 < r) (modulus : ℕ)

omit [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))] in
theorem allocatedBufferedCoveredSiteTerm_factorization
    (residue : ∀ j : Fin m, Matrix (BoundedBooleanJet α (j.val + 1))
      (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    (f : Finset α → (LayerSamplerAxis I n → ℝ) → ℂ)
    (z : MixedCoveredJetSource I jets Q n d)
    (hz : z ∈ mixedCoveredJetRegion U o b d quarter)
    (hs : ∀ s, mixedCoveredBooleanSiteValue d z s ∈ mixedCoveredJetRegion (E := Q) U o b d
      (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j)))
    (hbox : ∀ s a, |allocatedFullMixedSiteValue (R := R) U b (mixedBooleanSiteValue z.1 s) a| ≤ (r : ℝ)) :
    allocatedCoveredComplexProfileDensity B U b hR hσ S x u v jetRows hb o bW d quarter
        (allocatedSiteTermDensity B U b S x modulus residue f) (chart z) =
      allocatedCoveredSitePrefactor B U b hR hσ S x u v d modulus residue z *
        ∏ s, allocatedBufferedSiteChartFactor B U b S o hb bW d r hr (f s)
          (coveredBooleanSiteValue U (chart z) s) := by
  rw [allocatedCoveredComplexProfileDensity, restrictedComplexChartDensity_apply _ _ _ _
    (mixedCoveredJetChart_injOn U o b hb bW d quarter
      (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))) hz,
    Complex.ofReal_one, one_mul, allocatedSiteTermDensity,
    allocatedBufferedSiteChartFactor_product B U b S o hb bW d r hr f z hs hbox]
  unfold allocatedCoveredSitePrefactor
  ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set VectorPolynomial
open scoped Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (u : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := Fin dim) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) ((j : ℕ) + 1))
local notation "jetRows" => (fun j => (Subtype.val : jets j → Finset (Fin dim)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "output" => (Σ a : {a // ¬grid a}, jets (Sigma.fst (Subtype.val a)))
local notation "volume" => (∏ q : output, R (Sigma.fst (Subtype.val (Sigma.fst q))))
local notation "scale" => (∏ a : {a // ¬grid a}, allocatedLongJetOutputScale B U b S (O := jets) a)
local notation "quarter" => (fun j (_ : jets j) => standardLatticeClosedQuarterBox (J j))
local notation "chart" => mixedCoveredJetChart (O := jets) U o b hb bW d
local notation "split" => coefficientJetAxisSplit jets I n grid

variable (modulus : ℕ)

omit [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))] in
theorem allocatedCoveredSiteTerm_physical_factorization
    (residue : ∀ j : Fin m, Matrix (BoundedBooleanJet (Fin dim) (j.val + 1))
      (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    (f : Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ)
    {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j)
    (cube : X → (Unit ⊕ Fin dim) → ℤ)
    (z : MixedCoveredJetSource I jets Q n d)
    (hsite : chart z = physicalCubeEuclideanSample U d p hm cube)
    (hz : z ∈ mixedCoveredJetRegion U o b d quarter)
    (c : Fin m → ℝ) (hc : ∀ j, 0 ≤ c j)
    (hcoord : ∀ j r, ‖normalizedLatticePoint (euclideanSubspace (U j)) (b j)
      (mixedCoveredJetCoordinates U o d z j r).1‖ ≤ c j)
    (hbudget : ∀ j, (Fintype.card (jets j) : ℝ) * c j ≤ 1 / 4) :
    allocatedCoveredComplexProfileDensity B U b hR hσ S x u v jetRows hb o bW d quarter
        (allocatedSiteTermDensity B U b S x modulus residue f) (physicalCubeEuclideanSample U d p hm cube) =
      allocatedCoveredSitePrefactor B U b hR hσ S x u v d modulus residue z *
        ∏ s, allocatedIdealSiteChartFactor B U b S o hb bW d (f s)
          (physicalSingleSiteValue U d p hm (fun a => (physicalCubeVertexValue cube s a : ℝ))) := by
  have h := allocatedCoveredSiteTerm_factorization B U b hR hσ S x u v hb o bW d modulus residue f z hz
    (mixedCoveredBooleanSiteValue_mem_quarter U o b d z c hc hcoord hbudget)
  rw [hsite] at h
  simpa only [coveredBooleanSiteValue_physical U d p hm hp cube] using h

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set VectorPolynomial
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (u : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := Fin dim) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) ((j : ℕ) + 1))
local notation "jetRows" => (fun j => (Subtype.val : jets j → Finset (Fin dim)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "output" => (Σ a : {a // ¬grid a}, jets (Sigma.fst (Subtype.val a)))
local notation "volume" => (∏ q : output, R (Sigma.fst (Subtype.val (Sigma.fst q))))
local notation "scale" => (∏ a : {a // ¬grid a}, allocatedLongJetOutputScale B U b S (O := jets) a)
local notation "quarter" => (fun j (_ : jets j) => standardLatticeClosedQuarterBox (J j))
local notation "chart" => mixedCoveredJetChart (O := jets) U o b hb bW d
local notation "split" => coefficientJetAxisSplit jets I n grid

variable (r : ℝ≥0) (hr : 0 < r) (modulus : ℕ)

omit [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))] in
theorem allocatedBufferedCoveredSiteTerm_physical_factorization
    (residue : ∀ j : Fin m, Matrix (BoundedBooleanJet (Fin dim) (j.val + 1))
      (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    (f : Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ)
    {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j)
    (cube : X → (Unit ⊕ Fin dim) → ℤ)
    (z : MixedCoveredJetSource I jets Q n d)
    (hsite : chart z = physicalCubeEuclideanSample U d p hm cube)
    (hz : z ∈ mixedCoveredJetRegion U o b d quarter)
    (c : Fin m → ℝ) (hc : ∀ j, 0 ≤ c j)
    (hcoord : ∀ j r, ‖normalizedLatticePoint (euclideanSubspace (U j)) (b j)
      (mixedCoveredJetCoordinates U o d z j r).1‖ ≤ c j)
    (hbudget : ∀ j, (Fintype.card (jets j) : ℝ) * c j ≤ 1 / 4)
    (hbox : ∀ s a, |allocatedFullMixedSiteValue (R := R) U b (mixedBooleanSiteValue z.1 s) a| ≤ (r : ℝ)) :
    allocatedCoveredComplexProfileDensity B U b hR hσ S x u v jetRows hb o bW d quarter
        (allocatedSiteTermDensity B U b S x modulus residue f) (physicalCubeEuclideanSample U d p hm cube) =
      allocatedCoveredSitePrefactor B U b hR hσ S x u v d modulus residue z *
        ∏ s, allocatedBufferedSiteChartFactor B U b S o hb bW d r hr (f s)
          (physicalSingleSiteValue U d p hm (fun a => (physicalCubeVertexValue cube s a : ℝ))) := by
  have h := allocatedBufferedCoveredSiteTerm_factorization B U b hR hσ S x u v hb o bW d r hr modulus residue f z hz
    (mixedCoveredBooleanSiteValue_mem_quarter U o b d z c hc hcoord hbudget) hbox
  rw [hsite] at h
  simpa only [coveredBooleanSiteValue_physical U d p hm hp cube] using h

end Erdos3.BooleanCubeKernel

end

end OAI
