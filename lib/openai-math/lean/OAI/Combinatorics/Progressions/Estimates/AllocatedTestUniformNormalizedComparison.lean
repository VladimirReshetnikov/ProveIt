import OAI.Combinatorics.Progressions.Estimates.AllocatedTestUniformCoarseJointStatement

namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

variable {m dim : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {P : ℝ} {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (C V : Fin m → ℝ≥0)
variable (d : ℕ) [NeZero d]
variable (g : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S) →
  EuclideanJetLayers U (fun j => BoundedBooleanJet (Fin dim) (j.val + 1)) → ℝ)

def allocatedTestUniformConstructedTupleTail (A Amass : ℕ) : Prop :=
  let O := fun j : Fin m => BoundedBooleanJet (Fin dim) (j.val + 1)
  let rows := fun j => (Subtype.val : O j → Finset (Fin dim))
  let cap := (allocatedAmbientFactorCap (G := G) B R σ S.value V : ℝ) ^
    Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
  ∀ (_hm : (m : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    {X : Type*} [Fintype X] [DecidableEq X]
    {Pmass : ℝ} (_hQ : allocatedJetFourierBudget m dim A P ≤ Pmass)
    (_hX : (Fintype.card X : ℝ) ≤ Pmass)
    (_hXdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ Pmass)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hmem : ∀ j e, coefficients (poly j) e ∈ U j)
    (N stride : X → ℕ) (_hs : ∀ t, 0 < stride t)
    {Rrank W τ ξ₀ ρ C₀ δ mesh Z : ℝ}
    (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ₀) (_hξ1 : ξ₀ ≤ 1) (_hρ : 0 < ρ)
    (_hτP : 1 / τ ≤ Real.exp Pmass) (_hstride : ∀ t, (stride t : ℝ) ≤ Real.exp Pmass)
    (_hsize : ∀ t, Real.exp ((Pmass + Amass) ^ Amass) ≤ (N t : ℝ))
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) Rrank (U j) (poly j))
    (_hRank : Real.exp ((Pmass + Amass) ^ Amass) ≤ Rrank)
    (_hspatial : ∀ t, 8 * (1 + W) * (stride t : ℝ) * ρ ≤ (ξ₀ * τ) * (N t : ℝ))
    (_hρ8 : 8 * (probabilityProfileLipschitz : ℝ) ≤ ρ)
    (_hρshift : 2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) *
      (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0))) ≤ ρ)
    (_hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (_hC₀ : 1 ≤ C₀) (_hLC : (S.value : ℝ) ≤ C₀) (_hWC : W ≤ C₀)
    (_hmeshSize : anisotropicSpatialMeshThreshold selection
      (PrincipalTupleIndex B (layerSamplerDegree I n)) C₀ ≤ ρ)
    (_hδ : 0 ≤ δ)
    (_hρmove : Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) *
      (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0)) ≤ δ * ρ)
    (_hmesh : 0 < mesh) (_hZ : 0 < Z) (base : X → ℤ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
    (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells
      (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ₀ N) z)
    {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
    (bW : ∀ j, Basis (Kcov j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    {Pc E T η : ℝ} (_hPc : 0 ≤ Pc) (_hE : 0 ≤ E) (_hT : 0 ≤ T) (_hη : 0 < η) (_hη1 : η ≤ 1)
    (_hMP : (M : ℝ) ≤ Real.exp Pc) (_hRupper : ∀ j, R j ≤ Real.exp Pc)
    (_hRi : ∀ j, (R j)⁻¹ ≤ Real.exp Pc) (_hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp Pc)
    (_hcountc : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+1 ≤ Real.exp Pc)
    (_hηE : η⁻¹ ≤ Real.exp E) (_hstridec : ∀ t, (stride t : ℝ) ≤ Real.exp T)
    (_hlarge : Real.exp (allocatedRefinedJointLengthLog (G := G) B (Fin dim) O Pc E
      ((m+1 : ℕ)*Pc + Fintype.card X*T)) ≤ S.value),
    ∃ (hN : ∀ t, 0 < N t) (modulus : ℕ) (hmodulus : 0 < modulus),
    let : NeZero modulus := ⟨hmodulus.ne'⟩
    modulus ≤ M^(m+1) ∧
    (∀ root : G → ℤ, integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) selection)) ∧
    (∀ j, integerScalarLattice (O j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val+1) (rows j)).mulVecLin.range) ∧
    ∃ (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
      (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0),
    let refined := residueRefinedPeriod modulus stride
    (∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val+1) (rows j) (s j) (hA j) (1/(M : ℝ))) ∧
    ∃ hRefined : 0 < refined,
    let : NeZero refined := ⟨hRefined.ne'⟩
    (∀ t, stride t * modulus ∣ refined) ∧
    (refined : ℝ) ≤ Real.exp ((m+1 : ℕ)*Pc + Fintype.card X*T) ∧
    ∃ hlengths : ∀ t, (Fintype.card (Fin dim)+1)*refined ≤
      principalAxisLength (fun a => ¬allocatedGridAxis (I := I) U b S.value a) (allocatedPrincipalSides B U b S) t,
    ∃ (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value)
          (allocatedPrincipalSides B U b S) →
        (PrincipalTupleIndex (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
          (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod refined) →
        PrincipalAxisTuples (α := Fin dim) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
          (allocatedPrincipalSides B U b S))
      (residue : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value)
          (allocatedPrincipalSides B U b S) →
        (PrincipalTupleIndex (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
          (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod refined) →
        ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus)),
    (∀ u r, principalResidueLabel refined (reference u r) = r) ∧
    (∀ u r v, (allocatedLongResidueWeights B U b S refined hRefined r hlengths).weight v ≠ 0 → ∀ j,
      integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u rows j v) modulus = residue u r j) ∧
    ∀ (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ) (_htest : ∀ v, ‖test v‖ ≤ 1),
    allocatedRefinedTupleMassEstimate B U b hR hσ S x rows X hM selection hx modulus s hA
      stride reference residue hb o bW d g N hN hW hτ hξ C₀ ρ δ mesh base cells hmass
      (physicalCubeEuclideanSample U d poly hmem) test cap Z η

def allocatedTestUniformConstructedScalarTupleTail (A Amass : ℕ) : Prop :=
  let O := fun j : Fin m => BoundedBooleanJet (Fin dim) (j.val + 1)
  let rows := fun j => (Subtype.val : O j → Finset (Fin dim))
  let cap := (allocatedAmbientFactorCap (G := G) B R σ S.value V : ℝ) ^
    Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
  ∀ (_hm : (m : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    {X : Type*} [Fintype X] [DecidableEq X]
    {Perr Pmass : ℝ} (_hPerr : P ≤ Perr)
    (_hQ : allocatedScalarSamplingBudget m dim A P Perr ≤ Pmass)
    {δf ε : ℝ} (_hδf : 0 < δf) (_hδfP : δf⁻¹ ≤ Real.exp Perr)
    (_hε : 0 < ε) (_hεP : 1 / ε ≤ Real.exp Pmass)
    (_hX : (Fintype.card X : ℝ) ≤ Pmass)
    (_hXdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ Pmass)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hmem : ∀ j e, coefficients (poly j) e ∈ U j)
    (N stride : X → ℕ) (_hs : ∀ t, 0 < stride t)
    {Rrank W τ ξ₀ ρ C₀ δ mesh Z : ℝ}
    (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ₀) (_hξ1 : ξ₀ ≤ 1) (_hρ : 0 < ρ)
    (_hτP : 1 / τ ≤ Real.exp Pmass) (_hstride : ∀ t, (stride t : ℝ) ≤ Real.exp Pmass)
    (_hsize : ∀ t, Real.exp ((Pmass + Amass) ^ Amass) ≤ (N t : ℝ))
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) Rrank (U j) (poly j))
    (_hRank : Real.exp ((Pmass + Amass) ^ Amass) ≤ Rrank)
    (_hspatial : ∀ t, 8 * (1 + W) * (stride t : ℝ) * ρ ≤ (ξ₀ * τ) * (N t : ℝ))
    (_hρ8 : 8 * (probabilityProfileLipschitz : ℝ) ≤ ρ)
    (_hρshift : 2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) *
      (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0))) ≤ ρ)
    (_hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (_hC₀ : 1 ≤ C₀) (_hLC : (S.value : ℝ) ≤ C₀) (_hWC : W ≤ C₀)
    (_hmeshSize : anisotropicSpatialMeshThreshold selection
      (PrincipalTupleIndex B (layerSamplerDegree I n)) C₀ ≤ ρ)
    (_hδ : 0 ≤ δ)
    (_hρmove : Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) *
      (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0)) ≤ δ * ρ)
    (_hmesh : 0 < mesh) (_hZ : 0 < Z) (base : X → ℤ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
    (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells
      (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ₀ N) z)
    {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
    (bW : ∀ j, Basis (Kcov j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    {Pc E T η : ℝ} (_hPc : 0 ≤ Pc) (_hPcErr : Pc ≤ Perr) (_hE : 0 ≤ E) (_hT : 0 ≤ T) (_hη : 0 < η) (_hη1 : η ≤ 1)
    (_hMP : (M : ℝ) ≤ Real.exp Pc) (_hRupper : ∀ j, R j ≤ Real.exp Pc)
    (_hRi : ∀ j, (R j)⁻¹ ≤ Real.exp Pc) (_hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp Pc)
    (_hcountc : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+1 ≤ Real.exp Pc)
    (_hηE : η⁻¹ ≤ Real.exp E) (_hstridec : ∀ t, (stride t : ℝ) ≤ Real.exp T)
    (_hlarge : Real.exp (allocatedRefinedJointLengthLog (G := G) B (Fin dim) O Pc E
      ((m+1 : ℕ)*Pc + Fintype.card X*T)) ≤ S.value),
    ∃ (hN : ∀ t, 0 < N t) (modulus : ℕ) (hmodulus : 0 < modulus),
    let : NeZero modulus := ⟨hmodulus.ne'⟩
    modulus ≤ M^(m+1) ∧
    (∀ root : G → ℤ, integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) selection)) ∧
    (∀ j, integerScalarLattice (O j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val+1) (rows j)).mulVecLin.range) ∧
    ∃ (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
      (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0),
    let refined := residueRefinedPeriod modulus stride
    (∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val+1) (rows j) (s j) (hA j) (1/(M : ℝ))) ∧
    ∃ hRefined : 0 < refined,
    let : NeZero refined := ⟨hRefined.ne'⟩
    (∀ t, stride t * modulus ∣ refined) ∧
    (refined : ℝ) ≤ Real.exp ((m+1 : ℕ)*Pc + Fintype.card X*T) ∧
    ∃ hlengths : ∀ t, (Fintype.card (Fin dim)+1)*refined ≤
      principalAxisLength (fun a => ¬allocatedGridAxis (I := I) U b S.value a) (allocatedPrincipalSides B U b S) t,
    ∃ (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value)
          (allocatedPrincipalSides B U b S) →
        (PrincipalTupleIndex (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
          (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod refined) →
        PrincipalAxisTuples (α := Fin dim) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
          (allocatedPrincipalSides B U b S))
      (residue : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value)
          (allocatedPrincipalSides B U b S) →
        (PrincipalTupleIndex (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
          (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod refined) →
        ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus)),
    (∀ u r, principalResidueLabel refined (reference u r) = r) ∧
    (∀ u r v, (allocatedLongResidueWeights B U b S refined hRefined r hlengths).weight v ≠ 0 → ∀ j,
      integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u rows j v) modulus = residue u r j) ∧
    ∀ (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ) (_htest : ∀ v, ‖test v‖ ≤ 1),
    let Aerr := coefficientDeckPeriodCap O Kcov modulus
    let Cψ := ((modulus : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
      anisotropicSpatialDensityCap selection (1 / (M : ℝ))) ^ Fintype.card X
    let Vsp := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
      (((1 + W) / S.value) ^ dim) ^ Fintype.card X
    let Merr := η * Aerr *
      (2 * (∑ j, (C j : ℝ) * ((Fintype.card (J j) : ℝ) + 1)) + 1) ^
        Fintype.card (Σ a : LayerSamplerAxis I n, O a.1)
    allocatedRefinedTupleScalarEstimate B U b hR hσ S x rows X hM selection hx modulus s hA
      stride reference residue hb o bW d g N hN hW hτ hξ C₀ ρ δ mesh base cells hmass
      (physicalCubeEuclideanSample U d poly hmem) test cap Z (Cψ * (Vsp * (Merr + 2 * δf + ε)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uX uQ

variable {m dim : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] [instI : ∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)] [instB : ∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {P : ℝ} {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (C V : Fin m → ℝ≥0)
variable (d : ℕ) [NeZero d]
variable (g : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S) →
  EuclideanJetLayers U (fun j => BoundedBooleanJet (Fin dim) (j.val + 1)) → ℝ)

theorem allocatedTestUniformConstructedScalarTail_of_original (A Amass K : ℕ)
    (hAmass : 2 ≤ Amass) (hK : 2 ≤ K)
    (hscalar : allocatedPrimitiveScalarStatement.{uG, uI, uB, uJ, uQ, uX} m dim K)
    (hP : 0 ≤ P) (hL : (S.value : ℝ) ≤ Real.exp P) (hdim : dim ≤ m + 1)
    (hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (hdata : allocatedTestUniformConstructedTupleTail.{uG, uI, uB, uJ, uX, uQ}
      B U b S x (P := P) hM selection hx hb o hR hσ C V d g A Amass) :
    allocatedTestUniformConstructedScalarTupleTail.{uG, uI, uB, uJ, uX, uQ}
      B U b S x (P := P) hM selection hx hb o hR hσ C V d g
      A (max Amass K) := by

  have hinstI : instI = (fun j => Classical.typeDecidableEq (I j)) := Subsingleton.elim _ _
  have hinstB : instB = (fun a => Classical.typeDecidableEq (B a)) := Subsingleton.elim _ _
  subst instI instB
  unfold allocatedPrimitiveScalarStatement at hscalar
  unfold allocatedTestUniformConstructedTupleTail at hdata
  unfold allocatedTestUniformConstructedScalarTupleTail
  intro O rows cap hm₀ hvars hRP hσP hcount hI hn hJ hAP hCP hVP X _ _ Perr Pmass hPerr hQtotal
    δf ε hδf hδfP hε hεP hX hXdim poly hpoly hmem N stride hs Rrank W τ ξ₀ ρ C₀ δ mesh Z
    hW hτ hξ hξ1 hρ hτP hstride hsize hrank hRank hspatial hρ8 hρshift hbudget hC₀ hLC hWC
    hmeshSize hδ hρmove hmesh hZ base cells hmass Kcov _ bW Pc E T η
    hPc hPcErr hE hT hη hη1 hMP hRupper hRi hσi hcountc hηE hstridec hlarge
  obtain ⟨hBudget, hJet, hError, _hPerrBudget⟩ :=
    allocatedScalarSamplingBudget_bounds m dim A hP (hP.trans hPerr)
  have hQ := hJet.trans hQtotal
  have hQerr := hError.trans hQtotal
  have hPmass : 0 ≤ Pmass := hBudget.trans hQtotal
  have hold : Real.exp ((Pmass + Amass) ^ Amass) ≤
      Real.exp ((Pmass + (max Amass K : ℕ)) ^ max Amass K) :=
    Real.exp_le_exp.mpr (shifted_power_self_mono hPmass (by omega) (le_max_left _ _))
  have hnew : Real.exp ((Pmass + K) ^ K) ≤
      Real.exp ((Pmass + (max Amass K : ℕ)) ^ max Amass K) :=
    Real.exp_le_exp.mpr (shifted_power_self_mono hPmass (by omega) (le_max_right _ _))
  have hsampling := hdata (X := X) (Pmass := Pmass)
    (Rrank := Rrank) (W := W) (τ := τ) (ξ₀ := ξ₀) (ρ := ρ)
    (C₀ := C₀) (δ := δ) (mesh := mesh) (Z := Z)
    hm₀ hvars hRP hσP hcount hI hn hJ hAP hCP hVP hQ hX hXdim
    poly hpoly hmem N stride hs hW hτ hξ hξ1 hρ hτP hstride
  have hspatialData := hsampling (fun t => hold.trans (hsize t)) hrank (hold.trans hRank) hspatial hρ8
    hρshift hbudget hC₀ hLC hWC hmeshSize hδ hρmove hmesh hZ
  obtain ⟨hN, modulus, hmodulus, hrest⟩ := hspatialData base cells hmass bW
    hPc hE hT hη hη1 hMP hRupper hRi hσi hcountc hηE hstridec hlarge
  let : NeZero modulus := ⟨hmodulus.ne'⟩
  obtain ⟨hmod, hspatialPeriod, hperiod, s, hsA, hi, hrest⟩ := hrest
  obtain ⟨hRefined, hdiv, hbound, hlengths, reference, residue, href, hr, hcompare⟩ := hrest
  let : NeZero (residueRefinedPeriod modulus stride) := ⟨hRefined.ne'⟩
  refine ⟨hN, modulus, hmodulus, hmod, hspatialPeriod, hperiod, s, hsA, hi,
    hRefined, hdiv, hbound, hlengths, reference, residue, href, hr, ?_⟩
  intro test htest
  let ηNN : ℝ≥0 := ⟨η, hη.le⟩
  have hηNN : ηNN ≤ 1 := hη1
  have he := Real.exp_le_exp.mpr hPerr
  dsimp only
  rw [← Real.coe_toNNReal (coefficientDeckPeriodCap O Kcov modulus)
    (coefficientDeckPeriodCap_nonneg O Kcov modulus)]
  have hkernel := hscalar (G := G) (I := I) (n := n) (J := J) (Q := Kcov) (X := X) (M := M)
    B U b hR hσ S x hb o bW d C V hC hV ν hM selection hx modulus
    hmod (hspatialPeriod _) hperiod stride hs
  have hgeometry := hkernel (W := W) (τ := τ) (ξ := ξ₀) (ρ := ρ) (mesh := mesh)
    (P := Pmass) (Perr := Perr) (Rrank := Rrank) (ε := ε)
    reference N hN hW hτ hξ hξ1 hρ hspatial hρ8 hρshift
    hbudget hmesh base cells hmass poly hpoly hmem test htest hPmass hX hXdim hτP hstride
    hε hεP (fun t => hnew.trans (hsize t)) hrank (hnew.trans hRank)
  have hbudgetData := hgeometry (δf := δf)
    (hP.trans hPerr) hdim (hvars.trans hPerr) (fun j => (hI j).trans hPerr)
    (fun j => (hn j).trans hPerr) (fun j => (hJ j).trans hPerr)
    (hMP.trans (Real.exp_le_exp.mpr hPcErr)) (hL.trans he)
    (fun j => (hCP j).trans he) (fun j => (hVP j).trans he) hQerr
    ηNN hηNN hδf hδfP
  have hcomparisonRule := hbudgetData s hsA residue g C₀ δ cap Z hZ
  have hresult := hcomparisonRule (hcompare test htest)
  exact hresult

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

theorem allocatedTestUniformActualScalarTupleComparison (m dim : ℕ) :
    allocatedTestUniformActualScalarTupleStatement m dim true := by
  obtain ⟨A, Amass, hA, hAmass, hactual⟩ := allocatedTestUniformActualTupleComparison m dim
  obtain ⟨K, hK, hscalar⟩ := exists_allocated_primitive_scalar_tuple_comparison m dim
  unfold allocatedTestUniformActualScalarTupleStatement
  refine ⟨A, max Amass K,
    hA, hAmass.trans (le_max_left _ _), ?_⟩
  intro G _ _ I _ _ n B _ _ J _ U b R σ S x P hP hG hL M hM selection hx hdim
  obtain ⟨d, hd, hdb, hconstruct⟩ := hactual B U b S x hP hG hL hM selection hx hdim
  let : NeZero d := ⟨hd.ne'⟩
  refine ⟨d, hd, hdb, ?_⟩
  intro _ _ _ _ _ hb o hR hσ C V hC hV hσ1 Cinv hCinv hchart hsmall μ _ _ ν _ _
    O rows density cap cover ξ
  obtain ⟨g, hgc, hgb, hgi, hgm, hglaw, hprojection, hdata⟩ :=
    hconstruct hb o hR hσ C V hC hV hσ1 Cinv hCinv hchart hsmall μ ν
  refine ⟨g, hgc, hgb, hgi, hgm, hglaw, hprojection, ?_⟩
  exact allocatedTestUniformConstructedScalarTail_of_original B U b S x hM selection hx hb o hR hσ C V d g
    A Amass K hAmass hK hscalar hP hL hdim hC hV ν hdata

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

theorem allocatedTestUniformActualNormalizedTupleComparison (m dim : ℕ) :
    allocatedTestUniformActualNormalizedTupleStatement m dim true := by
  obtain ⟨A, Ac, hA, hAc, hactual⟩ := allocatedTestUniformActualScalarTupleComparison m dim
  obtain ⟨An, hAn, hnorm⟩ := exists_allocated_narrow_normalization m
  unfold allocatedTestUniformActualNormalizedTupleStatement
  refine ⟨A, max Ac An, hA, hAc.trans (le_max_left _ _), ?_⟩
  intro G _ _ I _ _ n B _ _ J _ U b R σ S x P hP hG hL M hM selection hx hdim
  obtain ⟨d, hd, hdb, hconstruct⟩ := hactual B U b S x hP hG hL hM selection hx hdim
  let : NeZero d := ⟨hd.ne'⟩
  refine ⟨d, hd, hdb, ?_⟩
  intro _ _ _ _ _ hb o hR hσ C V hC hV hσ1 Cinv hCinv hchart hsmall μ _ _ ν _ _
    O rows density cap cover ξ
  let _ := coefficientTorus_compact_of_lattice (K := LayerSamplerVariables G I n B) U
  obtain ⟨g, hgc, hgb, hgi, hgm, hglaw, hprojection, hdata⟩ :=
    hconstruct hb o hR hσ C V hC hV hσ1 Cinv hCinv hchart hsmall μ ν
  refine ⟨g, hgc, hgb, hgi, hgm, hglaw, hprojection, ?_⟩
  intro hm hvars hRP hσP hcount hI hn hJ hAP hCP hVP X _ _ p Etarget hp hEtarget
    hvarsp hIp hnp hJp hXp hCp hMp D hD Perr Pmass hPerr hAccuracy hQ
    hnormdim poly hpoly hmem N stride hs Rrank W τ ξ₀ ρ C₀ δ mesh
    hW hτ hξ hξ1 hρ hWScale hWP hξP hτP hstride hsize hrank hRank hspatial hρ8
    hρshift hbudget hC₀ hLC hWC hmeshSize hδ hρmove hmesh base cells hcells bases hbases
    Kcov _ bW Pc T hPc hPcErr hT hMP hRupper hRi hσi hcountc hstridec hlarge
    widths baseDensity Z
  obtain ⟨hBudget, _, _, hPerrBudget⟩ :=
    allocatedScalarSamplingBudget_bounds m dim A hP (hP.trans hPerr)
  have hPmass : 0 ≤ Pmass := hBudget.trans hQ
  have hXcard : Fintype.card X ≤ Fintype.card (Option (LayerSamplerVariables G I n B) × X) :=
    Fintype.card_le_of_injective (fun t : X => ((none : Option (LayerSamplerVariables G I n B)), t))
      (fun _ _ h => congrArg Prod.snd h)
  have hX : (Fintype.card X : ℝ) ≤ Pmass := (Nat.cast_le.mpr hXcard).trans hnormdim
  have hvarsDim : Fintype.card (Fin dim) ≤ Fintype.card (LayerSamplerVariables G I n B) :=
    Fintype.card_le_of_embedding
      (selection.trans (Function.Embedding.inl : G ↪ LayerSamplerVariables G I n B))
  have hdimCard : Fintype.card (Option (Fin dim) × X) ≤
      Fintype.card (Option (LayerSamplerVariables G I n B) × X) := by
    simp only [Fintype.card_prod, Fintype.card_option]
    exact Nat.mul_le_mul_right _ (Nat.add_le_add_right hvarsDim 1)
  have hXdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ Pmass :=
    (Nat.cast_le.mpr hdimCard).trans hnormdim
  have hErrMass : Perr ≤ Pmass := hPerrBudget.trans hQ
  have hPMass : P ≤ Pmass := hPerr.trans hErrMass
  have hexp := Real.exp_le_exp.mpr hPMass
  have hcompCut : Real.exp ((Pmass + Ac) ^ Ac) ≤
      Real.exp ((Pmass + (max Ac An : ℕ)) ^ max Ac An) :=
    Real.exp_le_exp.mpr (shifted_power_self_mono hPmass (by omega) (le_max_left _ _))
  have hnormCut : Real.exp ((Pmass + An) ^ An) ≤
      Real.exp ((Pmass + (max Ac An : ℕ)) ^ max Ac An) :=
    Real.exp_le_exp.mpr (shifted_power_self_mono hPmass (by omega) (le_max_right _ _))
  have hsmallDensity := allocatedPhysicalChartRadius_density_small B (Fin dim) Cinv R
    hCinv (fun j => (hR j).le) hsmall
  obtain ⟨_, hmass, _, hglobal⟩ := hnorm (X := X) B U b S hb o μ ν
    hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmallDensity hPmass
    (hm.trans hPMass) (hvars.trans hPMass) hX hnormdim
    (fun j => (hRP j).trans hexp) (fun j => (hσP j).trans hexp)
    (fun j => (hcount j).trans hPMass) (fun j => (hI j).trans hPMass)
    (fun j => (hn j).trans hPMass) (fun j => (hJ j).trans hPMass)
    (hAP.trans hexp) (hL.trans hexp) (fun j => (hCP j).trans hexp) (fun j => (hVP j).trans hexp)
    poly hpoly hmem stride hs hstride hW hWP hτ (by simpa only [one_div] using hτP)
    hξ hξ1 hξP N (fun t => hnormCut.trans (hsize t)) hrank (hnormCut.trans hRank) cells hcells
  have hnormal := hglobal bases hbases
  change |Z - 1| ≤ Real.exp (-Pmass) ∧ Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧
    0 < Z ∧ Z⁻¹ ≤ 2 at hnormal
  refine ⟨hmass, hnormal, ?_⟩
  let a := allocatedCoefficientAccuracy m p (Etarget + 1)
  have hE1 : 0 ≤ Etarget + 1 := by linarith
  have ha := allocatedCoefficientAccuracy_bounds m hp hE1
  have hainvErr : a⁻¹ ≤ Real.exp Perr := ha.2.2.le.trans (Real.exp_le_exp.mpr hAccuracy)
  have hainvMass : 1 / a ≤ Real.exp Pmass := by
    simpa only [one_div] using hainvErr.trans (Real.exp_le_exp.mpr hErrMass)
  have hlog : 0 ≤ allocatedCoefficientAccuracyLog m p (Etarget + 1) := by
    exact neg_nonpos.mp (Real.exp_le_one_iff.mp ha.2.1)
  have hsampling := hdata (X := X) (Perr := Perr) (Pmass := Pmass) (δf := a) (ε := a)
    (Rrank := Rrank) (W := W) (τ := τ) (ξ₀ := ξ₀) (ρ := ρ) (C₀ := C₀)
    (δ := δ) (mesh := mesh) (Z := Z)
    hm hvars hRP hσP hcount hI hn hJ hAP hCP hVP hPerr hQ
    ha.1 hainvErr ha.1 hainvMass hX hXdim poly hpoly hmem N stride hs
    hW hτ hξ hξ1 hρ hτP hstride
  have hspatialData := hsampling (fun t => hcompCut.trans (hsize t)) hrank
    (hcompCut.trans hRank) hspatial hρ8 hρshift hbudget hC₀ hLC hWC hmeshSize
    hδ hρmove hmesh hnormal.2.2.1
  obtain ⟨hN, modulus, hmodulus, hrest⟩ := hspatialData base cells hmass bW
    hPc hPcErr hlog hT ha.1 ha.2.1 hMP hRupper hRi hσi hcountc ha.2.2.le hstridec hlarge
  let : NeZero modulus := ⟨hmodulus.ne'⟩
  obtain ⟨hmod, hspatialPeriod, hperiod, s, hsA, hi, hrest⟩ := hrest
  obtain ⟨hRefined, hdiv, hbound, hlengths, reference, residue, href, hr, hcompare⟩ := hrest
  let : NeZero (residueRefinedPeriod modulus stride) := ⟨hRefined.ne'⟩
  refine ⟨hN, modulus, hmodulus, hmod, hspatialPeriod, hperiod, s, hsA, hi,
    hRefined, hdiv, hbound, hlengths, reference, residue, href, hr, ?_⟩
  intro test htest
  have htail := allocatedCoefficientErrorAccuracy_bound B U b hb bW rows hdim
    (fun _ => Subtype.val_injective) X selection C hp hE1 hvarsp hIp hnp hJp hXp hCp
    hM hMp hmod hD (by exact_mod_cast S.positive) hW hWScale
  have hnormalized := coefficientError_normalized_exp_bound htail hnormal.2.1.1
  have htailZ := (div_le_iff₀ hnormal.2.2.1).mp hnormalized
  exact allocatedRefinedTupleScalarEstimate_mono B U b hR hσ S x rows X hM selection hx
    modulus s hsA stride reference residue hb o bW d g N hN hW hτ hξ C₀ ρ δ mesh
    base cells hmass (physicalCubeEuclideanSample U d poly hmem) test cap Z
    hnormal.2.2.1.le (hcompare test htest) (htailZ.trans_eq (mul_comm _ _))

end Erdos3.VectorPolynomial

end

end OAI
