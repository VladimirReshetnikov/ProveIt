import OAI.Combinatorics.Progressions.Lattices.AffineIntervalNormalizedBounds
import OAI.Combinatorics.Progressions.Sampling.AllocatedExternalLocalGoodForecastPath
import OAI.Combinatorics.Progressions.Sampling.ForecastLawNativeRawJointMean

namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {X : Type} [Fintype X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {A : Type}
variable {Dmod : ℕ} {selected : A → Σ j : Fin m, Fin (n j)} {τ δslice : ℝ}

namespace ActualFixedSpatialForecastSetup

noncomputable def enlargeP
    (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout) B U b S Dmod selected τ δslice)
    {P' : ℝ} (hP : s.P ≤ P') :
    ActualFixedSpatialForecastSetup (X := X) (Eout := Eout) B U b S Dmod selected τ δslice :=
  { s with
    P := P'
    hP := s.hP.trans hP
    hDP := s.hDP.trans hP
    hX := s.hX.trans hP
    hblocks := s.hblocks.trans hP
    hδsliceInv := s.hδsliceInv.trans (Real.exp_le_exp.mpr hP) }

variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout) B U b S Dmod selected τ δslice)
variable {P' : ℝ} (hP : s.P ≤ P')

@[simp] theorem enlargeP_P : (s.enlargeP hP).P = P' := rfl
@[simp] theorem enlargeP_D : (s.enlargeP hP).D = s.D := rfl
@[simp] theorem enlargeP_κ : (s.enlargeP hP).κ = s.κ := rfl
@[simp] theorem enlargeP_Pbad : (s.enlargeP hP).Pbad = s.Pbad := rfl
@[simp] theorem enlargeP_Ppres : (s.enlargeP hP).Ppres = s.Ppres := rfl

noncomputable def withSliceWidth
    (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout) B U b S Dmod selected τ δslice)
    {δ' : ℝ} (hδ' : 0 < δ') (hδinv : δ'⁻¹ ≤ Real.exp s.P) :
    ActualFixedSpatialForecastSetup (X := X) (Eout := Eout) B U b S Dmod selected τ δ' :=
  { s with
    hδslice := hδ'
    hδsliceInv := hδinv }

variable {δ' : ℝ} (hδ' : 0 < δ') (hδinv : δ'⁻¹ ≤ Real.exp s.P)

@[simp] theorem withSliceWidth_P : (s.withSliceWidth hδ' hδinv).P = s.P := rfl
@[simp] theorem withSliceWidth_κ : (s.withSliceWidth hδ' hδinv).κ = s.κ := rfl
@[simp] theorem withSliceWidth_Pbad : (s.withSliceWidth hδ' hδinv).Pbad = s.Pbad := rfl
@[simp] theorem withSliceWidth_Ppres : (s.withSliceWidth hδ' hδinv).Ppres = s.Ppres := rfl

end ActualFixedSpatialForecastSetup

variable [DecidableEq X]
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {Lrank : ℕ} {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j, a.val⟩}
variable {Tsp : Type}
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {P Pbad Ppres : ℝ}

namespace ActualFixedSpatialForecastPath

noncomputable def enlargeP
    (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
      Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)
    {P' : ℝ} (hP : P ≤ P') :
    ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
      Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P' Pbad Ppres :=
  { path with
    hjac := path.hjac.trans (Real.exp_le_exp.mpr hP)
    hinverse := path.hinverse.trans (Real.exp_le_exp.mpr hP) }

variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)
variable {P' : ℝ} (hP : P ≤ P')

@[simp] theorem enlargeP_base : (path.enlargeP hP).base = path.base := rfl
@[simp] theorem enlargeP_noise : (path.enlargeP hP).noise = path.noise := rfl
@[simp] theorem enlargeP_sample : (path.enlargeP hP).sample = path.sample := rfl
@[simp] theorem enlargeP_read : (path.enlargeP hP).read = path.read := rfl
@[simp] theorem enlargeP_center : (path.enlargeP hP).center = path.center := rfl
@[simp] theorem enlargeP_commonTuple : (path.enlargeP hP).commonTuple = path.commonTuple := rfl
@[simp] theorem enlargeP_primes : (path.enlargeP hP).primes = path.primes := rfl
@[simp] theorem enlargeP_exponent : (path.enlargeP hP).exponent = path.exponent := rfl
@[simp] theorem enlargeP_prescribed : (path.enlargeP hP).prescribed = path.prescribed := rfl
@[simp] theorem enlargeP_origin : (path.enlargeP hP).origin = path.origin := rfl
@[simp] theorem enlargeP_lower : (path.enlargeP hP).lower = path.lower := rfl
@[simp] theorem enlargeP_width : (path.enlargeP hP).width = path.width := rfl

@[simp] theorem target_enlargeP [Fintype A] [Fintype Tsp]
    (selected : A → Σ j : Fin m, Fin (n j))
    (hBactive : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      4 ≤ Fintype.card (B a.val))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Module.Basis (Eout j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
      projectedIntegerLattice (euclideanSubspace (U j)))
    (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j) (κ : ℝ) :
    (path.enlargeP hP).target selected hBactive o bW hb originalpoly hmem κ =
      path.target selected hBactive o bW hb originalpoly hmem κ := rfl

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)) (Wsp Lsp : ℝ)
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

structure ActualFixedSpatialSlicedForecastPath where
  path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
    Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres
  step : ℕ
  step_pos : 0 < step
  kernelLength : G → ℕ
  kernelStart : G → ℤ
  kernelLength_two : ∀ g, 2 ≤ kernelLength g
  kernelInside : ∀ g (t : Fin (kernelLength g)),
    0 ≤ kernelStart g + (step : ℤ) * t.val ∧
      kernelStart g + (step : ℤ) * t.val < S.value
  principalLength : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ
  principalStep : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ
  principalStart : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ
  principalLength_pos : ∀ j, 0 < principalLength j
  principalInside : ∀ j (t : Fin (principalLength j)),
    0 ≤ principalStart j + (principalStep j : ℤ) * t.val ∧
      principalStart j + (principalStep j : ℤ) * t.val < allocatedPrincipalSides B U b S j
  principalStep_active : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
    ∀ p : B a.val × Fin (layerSamplerDegree I n a.val), principalStep ⟨a.val,p⟩ = step
  prescribed_eq : ∀ p, path.prescribed p = padicValNat p step
  origin_eq : ∀ (p : path.primes) (v : LayerSamplerLongVariables
      (allocatedShortAxis (I := I) U b S.value) G B),
    path.origin p v = ((Sum.elim kernelStart
      (fun a => principalStart ⟨a.1.val,a.2⟩) v : ℤ) : ZMod (p.val ^ path.exponent p.val))
  lower_eq : ∀ a p, path.lower a p =
    (principalStart ⟨a.val,p⟩ : ℝ) / allocatedPrincipalSides B U b S ⟨a.val,p⟩
  width_eq : ∀ a p, path.width a p =
    (principalStep ⟨a.val,p⟩ : ℝ) * (principalLength ⟨a.val,p⟩ - 1 : ℕ) /
      allocatedPrincipalSides B U b S ⟨a.val,p⟩

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

noncomputable def kernelLower (g : G) : ℝ := (slice.kernelStart g : ℝ) / S.value
noncomputable def kernelWidth (g : G) : ℝ :=
  (slice.step : ℝ) * (slice.kernelLength g - 1 : ℕ) / S.value

omit [Fintype Tsp] in
theorem kernelWidth_pos (g : G) : 0 < slice.kernelWidth g := by
  have hstep : (0 : ℝ) < slice.step := Nat.cast_pos.mpr slice.step_pos
  have hlength : (0 : ℝ) < (slice.kernelLength g - 1 : ℕ) :=
    Nat.cast_pos.mpr (by have := slice.kernelLength_two g; omega)
  exact div_pos (mul_pos hstep hlength) (Nat.cast_pos.mpr S.positive)

omit [Fintype Tsp] in
theorem kernelWidth_ne_zero (g : G) : slice.kernelWidth g ≠ 0 :=
  (slice.kernelWidth_pos g).ne'

noncomputable def principalLaw : FiniteProbabilityWeights
    (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U b S)) :=
  principalAffineIntervalLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U b S)
    slice.principalLength slice.principalStep slice.principalStart slice.principalInside
    slice.principalLength_pos

private theorem det_ne_zero_change_decidable {Y : Type} [Fintype Y]
    (d₀ d₁ : DecidableEq Y) (A : Matrix Y Y ℝ) :
    (letI := d₀; A.det ≠ 0) → (letI := d₁; A.det ≠ 0) := by
  cases Subsingleton.elim d₀ d₁
  exact id

noncomputable def density
    (hBactive : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      4 ≤ Fintype.card (B a.val)) :
    (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
      ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a}, Unit) → ℝ)) → ℝ := by
  have h0 := det_ne_zero_change_decidable (inferInstance : DecidableEq X) (Classical.decEq X)
    (fixedSpatialKernelBlock spatialEquiv Wsp Lsp slice.path.normalizedNoise false) slice.path.detFalse
  have h1 := det_ne_zero_change_decidable (inferInstance : DecidableEq X) (Classical.decEq X)
    (fixedSpatialKernelBlock spatialEquiv Wsp Lsp slice.path.normalizedNoise true) slice.path.detTrue
  exact fixedSpatialKernelSliceOriginalForecastDensity
    (m := m) (G := G) (X := X) (T := Tsp) (I := I) (n := n) (J := J)
    B U b S spatialEquiv Wsp Lsp slice.path.normalizedNoise slice.kernelLower slice.kernelWidth
    h0 h1 slice.kernelWidth_ne_zero hBactive slice.path.lower slice.path.width slice.path.sample

variable {A : Type} [Fintype A]

noncomputable def target
    (selected : A → Σ j : Fin m, Fin (n j))
    (hBactive : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      4 ≤ Fintype.card (B a.val))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Module.Basis (Eout j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j) (κ : ℝ)
    (u : integerBox physicalN) : ℂ := by
  let : ∀ p : slice.path.primes, NeZero p.val := slice.path.primeNeZero
  let N := ∏ p : slice.path.primes, p.val ^ slice.path.exponent p.val
  let : NeZero N := ⟨Finset.prod_ne_zero_iff.mpr
    (fun p _ => pow_ne_zero _ (NeZero.ne p.val))⟩
  let poly := allocatedForecastPolynomial (allocatedShortAxis (I := I) U b S.value)
    slice.path.base slice.path.noise (allocatedReadDeck slice.path.read)
    (fun j a => allocatedReadProjection slice.path.read ⟨j,a.val⟩)
  let pRat := crtPolynomialInputLaw (fun p : slice.path.primes => p.val)
    (fun p : slice.path.primes => slice.path.exponent p.val)
    (fun p : slice.path.primes => slice.path.prescribed p.val)
    (primePower_crt_coprime (fun p : slice.path.primes => p.val)
      (fun p : slice.path.primes => slice.path.exponent p.val)
      (fun p => slice.path.prime p.val p.property) Subtype.val_injective) slice.path.origin
  exact (κ : ℂ) * forecastLawDensityPhysicalTarget B U b S slice.principalLaw
    (slice.density hBactive) selected slice.path.sample slice.path.commonTuple (fun _ => pRat)
    (fun y t j => integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j)
    N (∏ a, (basisAxisScale (b (selected a).1) (selected a).2 : ℝ))
    slice.path.base physicalN τ o hb bW (slice.path.physicalPolynomial originalpoly)
    (slice.path.physicalPolynomial_mem originalpoly hmem) u.val

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {X : Type} [Fintype X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {A : Type}
variable {Dmod : ℕ} {selected : A → Σ j : Fin m, Fin (n j)} {τ δslice : ℝ}

variable [DecidableEq X]
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {Lrank : ℕ} {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j, a.val⟩}
variable {Tsp : Type}
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {P Pbad Ppres : ℝ}

namespace ActualFixedSpatialForecastPath

noncomputable def weakenSliceWidth
    (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
      Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)
    {δ' : ℝ} (hδ : δ' ≤ δslice) :
    ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
      Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δ' P Pbad Ppres :=
  { path with hwidth := fun a p => hδ.trans (path.hwidth a p) }

variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)
variable {δ' : ℝ} (hδ : δ' ≤ δslice)

@[simp] theorem weakenSliceWidth_lower : (path.weakenSliceWidth hδ).lower = path.lower := rfl
@[simp] theorem weakenSliceWidth_width : (path.weakenSliceWidth hδ).width = path.width := rfl

@[simp] theorem target_weakenSliceWidth [Fintype A] [Fintype Tsp]
    (selected : A → Σ j : Fin m, Fin (n j))
    (hBactive : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      4 ≤ Fintype.card (B a.val))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Module.Basis (Eout j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
      projectedIntegerLattice (euclideanSubspace (U j)))
    (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j) (κ : ℝ) :
    (path.weakenSliceWidth hδ).target selected hBactive o bW hb originalpoly hmem κ =
      path.target selected hBactive o bW hb originalpoly hmem κ := rfl

end ActualFixedSpatialForecastPath

namespace ActualFixedSpatialSlicedForecastPath

noncomputable def enlargeP
    (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
      Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)
    {P' : ℝ} (hP : P ≤ P') :
    ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
      Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P' Pbad Ppres :=
  { slice with path := slice.path.enlargeP hP }

noncomputable def weakenSliceWidth
    (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
      Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)
    {δ' : ℝ} (hδ : δ' ≤ δslice) :
    ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
      Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δ' P Pbad Ppres :=
  { slice with path := slice.path.weakenSliceWidth hδ }

variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)
variable {P' δ' : ℝ} (hP : P ≤ P') (hδ : δ' ≤ δslice)

@[simp] theorem enlargeP_path : (slice.enlargeP hP).path = slice.path.enlargeP hP := rfl
@[simp] theorem weakenSliceWidth_path :
    (slice.weakenSliceWidth hδ).path = slice.path.weakenSliceWidth hδ := rfl
@[simp] theorem enlargeP_kernelLower : (slice.enlargeP hP).kernelLower = slice.kernelLower := rfl
@[simp] theorem enlargeP_kernelWidth : (slice.enlargeP hP).kernelWidth = slice.kernelWidth := rfl
@[simp] theorem weakenSliceWidth_kernelLower :
    (slice.weakenSliceWidth hδ).kernelLower = slice.kernelLower := rfl
@[simp] theorem weakenSliceWidth_kernelWidth :
    (slice.weakenSliceWidth hδ).kernelWidth = slice.kernelWidth := rfl
@[simp] theorem enlargeP_principalLaw : (slice.enlargeP hP).principalLaw = slice.principalLaw := rfl
@[simp] theorem weakenSliceWidth_principalLaw :
    (slice.weakenSliceWidth hδ).principalLaw = slice.principalLaw := rfl

@[simp] theorem density_enlargeP [Fintype Tsp]
    (hBactive : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      4 ≤ Fintype.card (B a.val)) :
    (slice.enlargeP hP).density hBactive = slice.density hBactive := rfl

@[simp] theorem density_weakenSliceWidth [Fintype Tsp]
    (hBactive : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      4 ≤ Fintype.card (B a.val)) :
    (slice.weakenSliceWidth hδ).density hBactive = slice.density hBactive := rfl

@[simp] theorem target_enlargeP [Fintype A] [Fintype Tsp]
    (selected : A → Σ j : Fin m, Fin (n j))
    (hBactive : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      4 ≤ Fintype.card (B a.val))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Module.Basis (Eout j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
      projectedIntegerLattice (euclideanSubspace (U j)))
    (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j) (κ : ℝ) :
    (slice.enlargeP hP).target selected hBactive o bW hb originalpoly hmem κ =
      slice.target selected hBactive o bW hb originalpoly hmem κ := rfl

@[simp] theorem target_weakenSliceWidth [Fintype A] [Fintype Tsp]
    (selected : A → Σ j : Fin m, Fin (n j))
    (hBactive : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      4 ≤ Fintype.card (B a.val))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Module.Basis (Eout j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
      projectedIntegerLattice (euclideanSubspace (U j)))
    (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j) (κ : ℝ) :
    (slice.weakenSliceWidth hδ).target selected hBactive o bW hb originalpoly hmem κ =
      slice.target selected hBactive o bW hb originalpoly hmem κ := rfl

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)) (Wsp Lsp : ℝ)
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

omit [Fintype Tsp] in
theorem principalSupport (j : PrincipalTupleIndex B (layerSamplerDegree I n)) :
    integerProgressionSupport (slice.principalStart j) (slice.principalStep j : ℤ)
      (slice.principalLength j) ⊆ Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ) :=
  integerProgressionSupport_subset_of_fin _ _ _ _ (slice.principalInside j)

omit [Fintype Tsp] in
theorem principalLaw_eq_contained :
    slice.principalLaw =
      (principalTupleWeights (α := Empty) B (layerSamplerDegree I n)
        slice.principalLength slice.principalLength_pos).fiberLaw
      (containedProgressionTupleMap B (layerSamplerDegree I n)
        (allocatedPrincipalSides B U b S) slice.principalLength slice.principalStep
        slice.principalStart (allocatedPrincipalSides_pos B U b S) slice.principalSupport) := by
  exact principalAffineIntervalLaw_eq_contained B (layerSamplerDegree I n)
    slice.principalLength slice.principalLength_pos (allocatedPrincipalSides B U b S)
    slice.principalStep slice.principalStart (allocatedPrincipalSides_pos B U b S)
    slice.principalInside slice.principalSupport

omit [Fintype Tsp] in
theorem kernel_bounds (g : G) :
    0 ≤ slice.kernelLower g ∧ 0 < slice.kernelWidth g ∧
      slice.kernelLower g + slice.kernelWidth g < 1 ∧ slice.kernelWidth g ≤ 1 := by
  exact affineInterval_normalized_bounds S.positive (slice.kernelLength_two g)
    slice.step_pos (slice.kernelInside g)

omit [Fintype Tsp] in

theorem kernelWidth_ge_half_density {δ : ℝ} (g : G)
    (hsize : δ * S.value ≤ (slice.kernelLength g : ℝ)) :
    δ / 2 ≤ slice.kernelWidth g := by
  have hS : (0 : ℝ) < S.value := Nat.cast_pos.mpr S.positive
  have hstep : (1 : ℝ) ≤ slice.step := by exact_mod_cast slice.step_pos
  have hlen : (2 : ℝ) ≤ slice.kernelLength g := by exact_mod_cast slice.kernelLength_two g
  have hone : 1 ≤ slice.kernelLength g := (by norm_num : 1 ≤ 2).trans (slice.kernelLength_two g)
  have hpred : ((slice.kernelLength g - 1 : ℕ) : ℝ) = (slice.kernelLength g : ℝ) - 1 := by
    rw [Nat.cast_sub hone, Nat.cast_one]
  change δ / 2 ≤ (slice.step : ℝ) * (slice.kernelLength g - 1 : ℕ) / S.value
  apply (le_div_iff₀ hS).mpr
  rw [hpred]
  have hmul := mul_le_mul_of_nonneg_right hstep (by linarith only [hlen] : 0 ≤ (slice.kernelLength g : ℝ) - 1)
  nlinarith only [hsize, hlen, hmul]

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
