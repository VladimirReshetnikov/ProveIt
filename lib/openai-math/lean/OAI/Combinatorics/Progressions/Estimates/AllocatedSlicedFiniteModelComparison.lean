import OAI.Combinatorics.Progressions.Geometry.AllocatedChartIdealModelBound
import OAI.Combinatorics.Progressions.Geometry.AllocatedSlicedOneCubeRowTransport
import OAI.Combinatorics.Progressions.Geometry.AllocatedSlicedRowIdealSupport
import OAI.Combinatorics.Progressions.Probability.AllocatedSlicedCoveredExpectation

namespace OAI

section

namespace Erdos3
open MeasureTheory

theorem uniform_complex_approximation_test {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (f g : X → ℂ) (hf : Integrable f μ) (hg : Measurable g)
    {ε : ℝ} (he : ∀ x, ‖f x - g x‖ ≤ ε)
    (φ : X → ℂ) (hφ : Measurable φ) (hb : ∀ x, ‖φ x‖ ≤ 1) :
    Integrable g μ ∧
      ‖(∫ x, f x * φ x ∂μ) - ∫ x, g x * φ x ∂μ‖ ≤ ε := by
  have hd : Integrable (fun x => f x - g x) μ :=
    Integrable.of_bound (hf.aestronglyMeasurable.sub hg.aestronglyMeasurable) ε
      (Filter.Eventually.of_forall he)
  have hgi : Integrable g μ :=
    (hf.sub hd).congr (Filter.Eventually.of_forall (fun x => sub_sub_cancel (f x) (g x)))
  refine ⟨hgi, ?_⟩
  have hfiφ := hf.mul_bdd hφ.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  have hgiφ := hgi.mul_bdd hφ.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  rw [← integral_sub hfiφ hgiφ]
  have hp (x) : ‖f x * φ x - g x * φ x‖ ≤ ε := by
    rw [← sub_mul, norm_mul]
    exact ((mul_le_mul_of_nonneg_left (hb x) (norm_nonneg _)).trans_eq (mul_one _)).trans (he x)
  simpa only [probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (ae_of_all μ hp)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "quarter" => (fun j (_ : O j) => standardLatticeClosedQuarterBox (J j))

omit [∀ index, DecidableEq (I index)] [∀ axis, DecidableEq (B axis)] [Fintype α] in
theorem allocatedWholeMaskedCoveredProfile_join
    (u : PrincipalAxisTuples (α := α) grid (allocatedPrincipalSides B U b S))
    (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) (allocatedPrincipalSides B U b S))
    (q : ℕ) (f : ((Σ a : {a // ¬grid a}, O a.val.1) → ℝ) → ℝ) :
    allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d
      (principalAxisJoin grid u v) q f =
    allocatedCoveredProfileDensity B U b hR hσ S x u v rows hb o bW d quarter
      (allocatedLongProfileDensity B U b S x rows q
        (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u rows j v) q) f) := by
  simp only [allocatedWholeMaskedCoveredProfile, principalAxisRestrict_join_left,
    principalAxisRestrict_join_right]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (x : G → IntegerScalarCubeBox (Fin 1) S.value)
variable (s : ∀ j : Fin m, Finset (Fin 1) ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) id).submatrix id (s j)).det ≠ 0)
variable {Mk : ℕ} (hMk : 0 < Mk)
variable (hi : ∀ j : Fin m, fixedKernelInverseBound (O := Finset (Fin 1))
  S.positive x (j.val + 1) id (s j) (hA j) (1 / (Mk : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMkP : (Mk : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a)) (fun a => degree (Subtype.val a))
local notation "Jet" => (Σ _a : {a // ¬grid a}, Finset (Fin 1))
local notation "bound" => NNReal.mk
  (Real.exp (allocatedDensityLog (G := G) B (Fin 1) (fun _ => Finset (Fin 1)) P)) (Real.exp_nonneg _)
local notation "cap" => bound ^ Fintype.card (LayerSamplerAxis I n)
local notation "lip" => (Fintype.card (LayerSamplerAxis I n) : ℝ≥0) * bound * cap

local notation "Endpoint" => OneCubeActiveEndpoint (B := B) degree grid
local notation "Row" => OneCubeActiveRow grid

local notation "Output" => (Σ _e : Row, Unit)
local notation "jetRows" => (fun _ : Fin m => Finset (Fin 1))

local notation "activeB" => (fun a : {a // ¬grid a} => B (Subtype.val a))
local notation "activeDegree" => (fun a : {a // ¬grid a} => degree (Subtype.val a))
local notation "L" => principalAxisLength (fun a => ¬grid a) (allocatedPrincipalSides B U basis S)
local notation "positiveLengths" => (fun j : Tuple => allocatedPrincipalSides_pos B U basis S
  (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j)))

variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (F : AllocatedFrozenCoefficients B U basis S × EuclideanJetLayers U (fun _ : Fin m => Finset (Fin 1)) → ℂ)

local notation "source" => allocatedCoefficientSource B U basis hR hσ S
local notation "frozenSource" => allocatedFrozenCoefficientSource B U basis hR hσ S
local notation "reference" => allocatedLongJetReference B U basis S jetRows
variable (H₀ step₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH₀ : ∀ t, 0 < H₀ t)
variable (hsubset₀ : ∀ t, integerProgressionSupport (c₀ t) (step₀ t : ℤ) (H₀ t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (modulus : ℕ) (r₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin 1) → ZMod modulus)
variable (hcell : 0 < (principalTupleWeights (α := Fin 1) B (layerSamplerDegree I n) H₀ hH₀).mass
  (Finset.univ.filter (fun y => principalResidueLabel modulus y = r₀)))
local notation "embed" => (fun j : Tuple => (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j) : PrincipalTupleIndex B (layerSamplerDegree I n)))
local notation "H" => (fun j : Tuple => H₀ (embed j))
local notation "step" => (fun j : Tuple => step₀ (embed j))
local notation "c" => (fun j : Tuple => c₀ (embed j))
local notation "hsubset" => (fun j : Tuple => hsubset₀ (embed j))
local notation "residue" => (fun j : Tuple => r₀ (embed j))
local notation "GridTuples" => PrincipalAxisTuples (α := Fin 1) grid (allocatedPrincipalSides B U basis S)
local notation "wholeLaw" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S) hH₀ hsubset₀ modulus r₀ hcell
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S) hH₀ hsubset₀ modulus r₀ hcell grid
local notation "wholeRoot" y => allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y
local notation "wholeDirs" y => allocatedPhysicalCubeDirections B U basis S x y
local notation "deck" => PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)
local notation "actual" => allocatedSlicedCoveredExpectation B U basis hR hσ S x Q hb o bW d F
  H₀ step₀ c₀ hH₀ hsubset₀ modulus r₀ hcell

include hR hσ hMk hi hP hMkP hRP hRi hσi hcount in
theorem allocatedSlicedWholeCovered_point_comparison
    (u : GridTuples)
    (hucube : ∀ j, IntegerScalarCube (principalAxisLength grid (allocatedPrincipalSides B U basis S) j)
      (fun a => (u j a : ℤ)))
    (hstep : ∀ j : Tuple, 0 < step j) (hH : ∀ j : Tuple, 2 ≤ H j)
    {δ : ℝ} (hδ : 0 < δ)
    (hdense : ∀ j : Tuple, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (hm : 0 < modulus)
    (hsize : ∀ j : Tuple, (Fintype.card (Fin 1) + 1) * modulus ≤ H j)
    (hsmall : ∀ j : Tuple, scalarCubeGridBoundaryConstant (Fin 1) * ((modulus : ℝ) / H j) <
      volume.real (scalarCubeDomain (Fin 1)))
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j : Tuple, (step j : ℝ) / L j ≤ ε)
    (N O : ℕ) (hN : Fintype.card Endpoint ≤ N) (hO : Fintype.card Row ≤ O)
    (hB : ∀ a : {a // ¬grid a}, 4 ≤ Fintype.card (B a.val))
    (hx : ∀ g, IntegerScalarCube S.value (fun i => (x g i : ℤ)))
    {a η : ℝ} (ha : 0 < a) (hδone : δ ≤ 1) (hη : 0 < η)
    (hprincipal : ∀ j : {a // ¬grid a}, a ≤ unitProfilePrincipalSize (B := B) j.val)
    (A : ℝ≥0) (hTransition : LipschitzWith A Real.smoothTransition)
    (hσsmall : ∀ j, |σ j| ≤ slicedPolynomialScale N O N m m 1 1 a (δ / 2) A η)
    (haP : a⁻¹ ≤ Real.exp P) (hδP : (δ / 2)⁻¹ ≤ Real.exp P)
    (selection : Fin 1 ↪ G)
    (hgood : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
    (hσ1 : ∀ j, σ j ≤ 1)
    {e εcoef : ℝ} (he : 0 ≤ e) (hεcoef : 0 < εcoef) (hεe : εcoef⁻¹ ≤ Real.exp e)
    (hlarge : Real.exp (allocatedKernelReplacementLog (G := G) B (Fin 1) jetRows P e) ≤ S.value)
    (hperiod : ∀ j : Fin m, integerScalarLattice (Finset (Fin 1)) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) id).mulVecLin.range)
    (v₀ : PrincipalAxisTuples (α := Fin 1) (fun a => ¬grid a) (allocatedPrincipalSides B U basis S))
    (hv₀ : (containedProgressionResidueLaw activeB activeDegree L H step c positiveLengths
      (fun j : Tuple => hH₀ (embed j)) hsubset modulus hm residue hsize).weight v₀ ≠ 0)
    {mesh Cmask : ℝ} (hmesh0 : 0 ≤ mesh) (hmesh1 : mesh ≤ 1)
    (hscaleMesh : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ mesh)
    (hCmask : 1 ≤ Cmask)
    (hmask : ∀ (u : GridTuples) j z, 0 ≤ allocatedIntegerKernelMask B U basis S x (fun _ => id) j
      modulus
      (integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u (fun _ => id) j v₀) modulus) z ∧ allocatedIntegerKernelMask B U basis S x (fun _ => id) j
      modulus
      (integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u (fun _ => id) j v₀) modulus) z ≤ Cmask)
    (hF : Measurable F) (hFbound : ∀ p, ‖F p‖ ≤ 1) :
    let lower := fun (a : {a // ¬grid a}) (p : B a.val × Fin (degree a.val)) => (c ⟨a,p⟩ : ℝ) / L ⟨a,p⟩
    let width := fun (a : {a // ¬grid a}) (p : B a.val × Fin (degree a.val)) =>
      (step ⟨a,p⟩ : ℝ) * ((H ⟨a,p⟩ : ℝ) - 1) / L ⟨a,p⟩
    let ideal := allocatedSlicedPhysicalJetIdeal B U basis S hR hB lower width
    let law := containedProgressionResidueLaw activeB activeDegree L H step c positiveLengths
      (fun j : Tuple => hH₀ (embed j)) hsubset modulus hm residue hsize
    let outputResidue := fun (u : GridTuples) j => integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u (fun _ => id) j v₀) modulus
    let radius := max (4 * Real.exp P) (Real.exp (allocatedJetSupportLog (G := G) B (Fin 1) jetRows P))
    let Ki : ℝ≥0 := (‖(∏ o : Output, R o.1.2.val.1)⁻¹‖₊ *
      (NNReal.mk (Real.exp (slicedJointDensityLogBudget O m P)) (Real.exp_nonneg _) *
        NNReal.mk (Real.exp P) (Real.exp_nonneg _))) * 2
    let select := allocatedLongIntegerSelect B U basis S (O := jetRows)
    ‖(∫ p, law.complexMean (fun v =>
        F (Prod.fst ((allocatedCoefficientSplit B U basis S) (Prod.fst p)),
          euclideanCoefficientJetMap U (wholeRoot (principalAxisJoin grid u v)) (wholeDirs (principalAxisJoin grid u v)) (fun _ => id)
            (canonicalCoefficientDeckSample U bW basis hb o d (Nat.pos_of_ne_zero (NeZero.ne d)) (Prod.fst p) (Prod.snd p))))
        ∂(Measure.prod source (PMF.toMeasure deck))) - ∫ a₀, ∫ z,
      (allocatedLongProfileDensity B U basis S x (fun _ => id) modulus (outputResidue u) ideal z : ℂ) *
        allocatedCoveredFixedTest B U basis S x u v₀ (fun _ => id) Q hb o bW d F a₀ z
      ∂reference ∂frozenSource‖ ≤
      (2 * Real.exp (allocatedJetSupportLog (G := G) B (Fin 1) jetRows P) + 1)^
        Fintype.card (Σ _ : LayerSamplerAxis I n, Finset (Fin 1)) *
        (Fintype.card {a // ¬grid a} * εcoef *
          (1 + (layerKernelIndexBound m Mk : ℝ) * (bound : ℝ) + εcoef)^Fintype.card {a // ¬grid a}) +
      Cmask ^ Fintype.card (LayerSamplerAxis I n) *
        (η +
      ((2 * (cap : ℝ) * scalarCubeGridBoundaryConstant (Fin 1) / volume.real (scalarCubeDomain (Fin 1)) +
        (lip : ℝ) * 2) * ∑ j, (modulus : ℝ) / H j + (lip : ℝ) * ε) *
        (2 * Real.exp (allocatedJetSupportLog (G := G) B (Fin 1) (fun _ => Finset (Fin 1)) P)) ^ Fintype.card Jet + (2 * radius) ^ Fintype.card (UnselectedColumn select) *
          ((2 * radius + 2) ^ Fintype.card {o : Jet // allocatedLongIntegerCoordinate B U basis S (O := jetRows) o} *
            ((Ki : ℝ) + lip) * mesh)) := by
  intro lower width ideal law outputResidue radius Ki select
  have hc := allocatedSlicedOriginalCovered_ideal_comparison B U basis hR hσ S x u s hA hMk hi
    hP hMkP hRP hRi hσi hcount Q hb o bW d F
  have hc := hc step H c hstep hH hδ hsubset hdense modulus hm residue hsize hsmall hε hmesh
  have hc := hc N O hN hO hB hx hucube ha hδone hη hprincipal A hTransition hσsmall haP hδP selection hgood hσ1 (e := e) (εcoef := εcoef)
  have hc := hc he hεcoef hεe hlarge hperiod
  have hc := hc v₀ hv₀ (mesh := mesh) (Cmask := Cmask)
  have hc := hc hmesh0 hmesh1 hscaleMesh hCmask (hmask u) hF hFbound
  exact hc

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (x : G → IntegerScalarCubeBox (Fin 1) S.value)
variable (s : ∀ j : Fin m, Finset (Fin 1) ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) id).submatrix id (s j)).det ≠ 0)
variable {Mk : ℕ} (hMk : 0 < Mk)
variable (hi : ∀ j : Fin m, fixedKernelInverseBound (O := Finset (Fin 1))
  S.positive x (j.val + 1) id (s j) (hA j) (1 / (Mk : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMkP : (Mk : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a)) (fun a => degree (Subtype.val a))
local notation "Jet" => (Σ _a : {a // ¬grid a}, Finset (Fin 1))
local notation "bound" => NNReal.mk
  (Real.exp (allocatedDensityLog (G := G) B (Fin 1) (fun _ => Finset (Fin 1)) P)) (Real.exp_nonneg _)
local notation "cap" => bound ^ Fintype.card (LayerSamplerAxis I n)
local notation "lip" => (Fintype.card (LayerSamplerAxis I n) : ℝ≥0) * bound * cap

local notation "Endpoint" => OneCubeActiveEndpoint (B := B) degree grid
local notation "Row" => OneCubeActiveRow grid

local notation "Output" => (Σ _e : Row, Unit)
local notation "jetRows" => (fun _ : Fin m => Finset (Fin 1))

local notation "activeB" => (fun a : {a // ¬grid a} => B (Subtype.val a))
local notation "activeDegree" => (fun a : {a // ¬grid a} => degree (Subtype.val a))
local notation "L" => principalAxisLength (fun a => ¬grid a) (allocatedPrincipalSides B U basis S)
local notation "positiveLengths" => (fun j : Tuple => allocatedPrincipalSides_pos B U basis S
  (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j)))

variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (F : AllocatedFrozenCoefficients B U basis S × EuclideanJetLayers U (fun _ : Fin m => Finset (Fin 1)) → ℂ)

local notation "source" => allocatedCoefficientSource B U basis hR hσ S
local notation "frozenSource" => allocatedFrozenCoefficientSource B U basis hR hσ S
local notation "reference" => allocatedLongJetReference B U basis S jetRows
variable (H₀ step₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH₀ : ∀ t, 0 < H₀ t)
variable (hsubset₀ : ∀ t, integerProgressionSupport (c₀ t) (step₀ t : ℤ) (H₀ t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (modulus : ℕ) (r₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin 1) → ZMod modulus)
variable (hcell : 0 < (principalTupleWeights (α := Fin 1) B (layerSamplerDegree I n) H₀ hH₀).mass
  (Finset.univ.filter (fun y => principalResidueLabel modulus y = r₀)))
local notation "embed" => (fun j : Tuple => (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j) : PrincipalTupleIndex B (layerSamplerDegree I n)))
local notation "H" => (fun j : Tuple => H₀ (embed j))
local notation "step" => (fun j : Tuple => step₀ (embed j))
local notation "c" => (fun j : Tuple => c₀ (embed j))
local notation "hsubset" => (fun j : Tuple => hsubset₀ (embed j))
local notation "residue" => (fun j : Tuple => r₀ (embed j))
local notation "GridTuples" => PrincipalAxisTuples (α := Fin 1) grid (allocatedPrincipalSides B U basis S)
local notation "wholeLaw" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S) hH₀ hsubset₀ modulus r₀ hcell
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S) hH₀ hsubset₀ modulus r₀ hcell grid
local notation "wholeRoot" y => allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y
local notation "wholeDirs" y => allocatedPhysicalCubeDirections B U basis S x y
local notation "deck" => PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)
local notation "actual" => allocatedSlicedCoveredExpectation B U basis hR hσ S x Q hb o bW d F
  H₀ step₀ c₀ hH₀ hsubset₀ modulus r₀ hcell

include hR hσ hMk hi hP hMkP hRP hRi hσi hcount in
theorem allocatedSlicedWholeCovered_ideal_comparison
    (hstep : ∀ j : Tuple, 0 < step j) (hH : ∀ j : Tuple, 2 ≤ H j)
    {δ : ℝ} (hδ : 0 < δ)
    (hdense : ∀ j : Tuple, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (hm : 0 < modulus)
    (hsize : ∀ j : Tuple, (Fintype.card (Fin 1) + 1) * modulus ≤ H j)
    (hsmall : ∀ j : Tuple, scalarCubeGridBoundaryConstant (Fin 1) * ((modulus : ℝ) / H j) <
      volume.real (scalarCubeDomain (Fin 1)))
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j : Tuple, (step j : ℝ) / L j ≤ ε)
    (N O : ℕ) (hN : Fintype.card Endpoint ≤ N) (hO : Fintype.card Row ≤ O)
    (hB : ∀ a : {a // ¬grid a}, 4 ≤ Fintype.card (B a.val))
    (hx : ∀ g, IntegerScalarCube S.value (fun i => (x g i : ℤ)))
    {a η : ℝ} (ha : 0 < a) (hδone : δ ≤ 1) (hη : 0 < η)
    (hprincipal : ∀ j : {a // ¬grid a}, a ≤ unitProfilePrincipalSize (B := B) j.val)
    (A : ℝ≥0) (hTransition : LipschitzWith A Real.smoothTransition)
    (hσsmall : ∀ j, |σ j| ≤ slicedPolynomialScale N O N m m 1 1 a (δ / 2) A η)
    (haP : a⁻¹ ≤ Real.exp P) (hδP : (δ / 2)⁻¹ ≤ Real.exp P)
    (selection : Fin 1 ↪ G)
    (hgood : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
    (hσ1 : ∀ j, σ j ≤ 1)
    {e εcoef : ℝ} (he : 0 ≤ e) (hεcoef : 0 < εcoef) (hεe : εcoef⁻¹ ≤ Real.exp e)
    (hlarge : Real.exp (allocatedKernelReplacementLog (G := G) B (Fin 1) jetRows P e) ≤ S.value)
    (hperiod : ∀ j : Fin m, integerScalarLattice (Finset (Fin 1)) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) id).mulVecLin.range)
    (v₀ : PrincipalAxisTuples (α := Fin 1) (fun a => ¬grid a) (allocatedPrincipalSides B U basis S))
    (hv₀ : (containedProgressionResidueLaw activeB activeDegree L H step c positiveLengths
      (fun j : Tuple => hH₀ (embed j)) hsubset modulus hm residue hsize).weight v₀ ≠ 0)
    {mesh Cmask : ℝ} (hmesh0 : 0 ≤ mesh) (hmesh1 : mesh ≤ 1)
    (hscaleMesh : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ mesh)
    (hCmask : 1 ≤ Cmask)
    (hmask : ∀ (u : GridTuples) j z, 0 ≤ allocatedIntegerKernelMask B U basis S x (fun _ => id) j
      modulus
      (integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u (fun _ => id) j v₀) modulus) z ∧ allocatedIntegerKernelMask B U basis S x (fun _ => id) j
      modulus
      (integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u (fun _ => id) j v₀) modulus) z ≤ Cmask)
    (hF : Measurable F) (hFbound : ∀ p, ‖F p‖ ≤ 1) :
    let lower := fun (a : {a // ¬grid a}) (p : B a.val × Fin (degree a.val)) => (c ⟨a,p⟩ : ℝ) / L ⟨a,p⟩
    let width := fun (a : {a // ¬grid a}) (p : B a.val × Fin (degree a.val)) =>
      (step ⟨a,p⟩ : ℝ) * ((H ⟨a,p⟩ : ℝ) - 1) / L ⟨a,p⟩
    let ideal := allocatedSlicedPhysicalJetIdeal B U basis S hR hB lower width
    let _ := containedProgressionResidueLaw activeB activeDegree L H step c positiveLengths
      (fun j : Tuple => hH₀ (embed j)) hsubset modulus hm residue hsize
    let outputResidue := fun (u : GridTuples) j => integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u (fun _ => id) j v₀) modulus
    let radius := max (4 * Real.exp P) (Real.exp (allocatedJetSupportLog (G := G) B (Fin 1) jetRows P))
    let Ki : ℝ≥0 := (‖(∏ o : Output, R o.1.2.val.1)⁻¹‖₊ *
      (NNReal.mk (Real.exp (slicedJointDensityLogBudget O m P)) (Real.exp_nonneg _) *
        NNReal.mk (Real.exp P) (Real.exp_nonneg _))) * 2
    let select := allocatedLongIntegerSelect B U basis S (O := jetRows)
    ‖actual - FiniteProbabilityWeights.complexMean gridLaw (fun u => ∫ a₀, ∫ z,
      (allocatedLongProfileDensity B U basis S x (fun _ => id) modulus (outputResidue u) ideal z : ℂ) *
        allocatedCoveredFixedTest B U basis S x u v₀ (fun _ => id) Q hb o bW d F a₀ z
      ∂reference ∂frozenSource)‖ ≤
      (2 * Real.exp (allocatedJetSupportLog (G := G) B (Fin 1) jetRows P) + 1)^
        Fintype.card (Σ _ : LayerSamplerAxis I n, Finset (Fin 1)) *
        (Fintype.card {a // ¬grid a} * εcoef *
          (1 + (layerKernelIndexBound m Mk : ℝ) * (bound : ℝ) + εcoef)^Fintype.card {a // ¬grid a}) +
      Cmask ^ Fintype.card (LayerSamplerAxis I n) *
        (η +
      ((2 * (cap : ℝ) * scalarCubeGridBoundaryConstant (Fin 1) / volume.real (scalarCubeDomain (Fin 1)) +
        (lip : ℝ) * 2) * ∑ j, (modulus : ℝ) / H j + (lip : ℝ) * ε) *
        (2 * Real.exp (allocatedJetSupportLog (G := G) B (Fin 1) (fun _ => Finset (Fin 1)) P)) ^ Fintype.card Jet + (2 * radius) ^ Fintype.card (UnselectedColumn select) *
          ((2 * radius + 2) ^ Fintype.card {o : Jet // allocatedLongIntegerCoordinate B U basis S (O := jetRows) o} *
            ((Ki : ℝ) + lip) * mesh)) := by
  intro lower width ideal law outputResidue radius Ki select
  let f := fun (p : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n ×
      CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)
      (y : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin 1) (allocatedPrincipalSides B U basis S)) =>
    F (((allocatedCoefficientSplit B U basis S) p.1).1,
      euclideanCoefficientJetMap U (wholeRoot y) (wholeDirs y) (fun _ => id)
        (canonicalCoefficientDeckSample U bW basis hb o d (Nat.pos_of_ne_zero (NeZero.ne d)) p.1 p.2))
  have hf (y) : Integrable (fun p => f p y) ((source).prod (deck).toMeasure) :=
    allocatedSlicedCoveredIntegrand_integrable B U basis hR hσ S x Q hb o bW d F y hF hFbound
  apply containedSupportedProgressionLaw_integral_comparison B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S) hH₀ hsubset₀ modulus r₀ hcell grid
    ((source).prod (deck).toMeasure) f hf
  intro u hu
  have hucube := containedSupportedProgressionAxisLaw_cube_support B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S) hH₀ hsubset₀ modulus r₀ hcell grid u hu
  have heq := containedSupportedProgressionAxisLaw_eq_of_size B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S) hH₀ hsubset₀ modulus hm r₀ hcell
    (fun a => ¬grid a) hsize
  rw [heq]
  exact allocatedSlicedWholeCovered_point_comparison B U basis hR hσ S x s hA hMk hi
    hP hMkP hRP hRi hσi hcount Q hb o bW d F H₀ step₀ c₀ hH₀ hsubset₀ modulus r₀ u hucube
    hstep hH hδ hdense hm hsize hsmall hε hmesh N O hN hO hB hx
    ha hδone hη hprincipal A hTransition hσsmall haP hδP selection hgood hσ1
    he hεcoef hεe hlarge hperiod v₀ hv₀ hmesh0 hmesh1 hscaleMesh hCmask hmask hF hFbound

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (x : G → IntegerScalarCubeBox (Fin 1) S.value)
variable (s : ∀ j : Fin m, Finset (Fin 1) ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) id).submatrix id (s j)).det ≠ 0)
variable {Mk : ℕ} (hMk : 0 < Mk)
variable (hi : ∀ j : Fin m, fixedKernelInverseBound (O := Finset (Fin 1))
  S.positive x (j.val + 1) id (s j) (hA j) (1 / (Mk : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMkP : (Mk : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a)) (fun a => degree (Subtype.val a))
local notation "Jet" => (Σ _a : {a // ¬grid a}, Finset (Fin 1))
local notation "bound" => NNReal.mk
  (Real.exp (allocatedDensityLog (G := G) B (Fin 1) (fun _ => Finset (Fin 1)) P)) (Real.exp_nonneg _)
local notation "cap" => bound ^ Fintype.card (LayerSamplerAxis I n)
local notation "lip" => (Fintype.card (LayerSamplerAxis I n) : ℝ≥0) * bound * cap

local notation "Endpoint" => OneCubeActiveEndpoint (B := B) degree grid
local notation "Row" => OneCubeActiveRow grid

local notation "Output" => (Σ _e : Row, Unit)
local notation "jetRows" => (fun _ : Fin m => Finset (Fin 1))

local notation "activeB" => (fun a : {a // ¬grid a} => B (Subtype.val a))
local notation "activeDegree" => (fun a : {a // ¬grid a} => degree (Subtype.val a))
local notation "L" => principalAxisLength (fun a => ¬grid a) (allocatedPrincipalSides B U basis S)
local notation "positiveLengths" => (fun j : Tuple => allocatedPrincipalSides_pos B U basis S
  (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j)))

variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (F : EuclideanJetLayers U (fun _ : Fin m => Finset (Fin 1)) → ℂ)

local notation "source" => allocatedCoefficientSource B U basis hR hσ S
local notation "frozenSource" => allocatedFrozenCoefficientSource B U basis hR hσ S
local notation "reference" => allocatedLongJetReference B U basis S jetRows
variable (H₀ step₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH₀ : ∀ t, 0 < H₀ t)
variable (hsubset₀ : ∀ t, integerProgressionSupport (c₀ t) (step₀ t : ℤ) (H₀ t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (modulus : ℕ) (r₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin 1) → ZMod modulus)
variable (hcell : 0 < (principalTupleWeights (α := Fin 1) B (layerSamplerDegree I n) H₀ hH₀).mass
  (Finset.univ.filter (fun y => principalResidueLabel modulus y = r₀)))
local notation "embed" => (fun j : Tuple => (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j) : PrincipalTupleIndex B (layerSamplerDegree I n)))
local notation "H" => (fun j : Tuple => H₀ (embed j))
local notation "step" => (fun j : Tuple => step₀ (embed j))
local notation "c" => (fun j : Tuple => c₀ (embed j))
local notation "hsubset" => (fun j : Tuple => hsubset₀ (embed j))
local notation "residue" => (fun j : Tuple => r₀ (embed j))
local notation "GridTuples" => PrincipalAxisTuples (α := Fin 1) grid (allocatedPrincipalSides B U basis S)
local notation "wholeLaw" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S) hH₀ hsubset₀ modulus r₀ hcell
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S) hH₀ hsubset₀ modulus r₀ hcell grid
local notation "wholeRoot" y => allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y
local notation "wholeDirs" y => allocatedPhysicalCubeDirections B U basis S x y
local notation "deck" => PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)
local notation "actual" => allocatedSlicedCoveredExpectation B U basis hR hσ S x Q hb o bW d (F ∘ Prod.snd)
  H₀ step₀ c₀ hH₀ hsubset₀ modulus r₀ hcell

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

include hR hσ hMk hi hP hMkP hRP hRi hσi hcount in
theorem allocatedSlicedWholeCovered_profile_comparison
    (hstep : ∀ j : Tuple, 0 < step j) (hH : ∀ j : Tuple, 2 ≤ H j)
    {δ : ℝ} (hδ : 0 < δ)
    (hdense : ∀ j : Tuple, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (hm : 0 < modulus)
    (hsize : ∀ j : Tuple, (Fintype.card (Fin 1) + 1) * modulus ≤ H j)
    (hsmall : ∀ j : Tuple, scalarCubeGridBoundaryConstant (Fin 1) * ((modulus : ℝ) / H j) <
      volume.real (scalarCubeDomain (Fin 1)))
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j : Tuple, (step j : ℝ) / L j ≤ ε)
    (N O : ℕ) (hN : Fintype.card Endpoint ≤ N) (hO : Fintype.card Row ≤ O)
    (hB : ∀ a : {a // ¬grid a}, 4 ≤ Fintype.card (B a.val))
    (hx : ∀ g, IntegerScalarCube S.value (fun i => (x g i : ℤ)))
    {a η : ℝ} (ha : 0 < a) (hδone : δ ≤ 1) (hη : 0 < η)
    (hprincipal : ∀ j : {a // ¬grid a}, a ≤ unitProfilePrincipalSize (B := B) j.val)
    (A : ℝ≥0) (hTransition : LipschitzWith A Real.smoothTransition)
    (hσsmall : ∀ j, |σ j| ≤ slicedPolynomialScale N O N m m 1 1 a (δ / 2) A η)
    (haP : a⁻¹ ≤ Real.exp P) (hδP : (δ / 2)⁻¹ ≤ Real.exp P)
    (selection : Fin 1 ↪ G)
    (hgood : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
    (hσ1 : ∀ j, σ j ≤ 1)
    {e εcoef : ℝ} (he : 0 ≤ e) (hεcoef : 0 < εcoef) (hεe : εcoef⁻¹ ≤ Real.exp e)
    (hlarge : Real.exp (allocatedKernelReplacementLog (G := G) B (Fin 1) jetRows P e) ≤ S.value)
    (hperiod : ∀ j : Fin m, integerScalarLattice (Finset (Fin 1)) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) id).mulVecLin.range)
    (v₀ : PrincipalAxisTuples (α := Fin 1) (fun a => ¬grid a) (allocatedPrincipalSides B U basis S))
    (hv₀ : (containedProgressionResidueLaw activeB activeDegree L H step c positiveLengths
      (fun j : Tuple => hH₀ (embed j)) hsubset modulus hm residue hsize).weight v₀ ≠ 0)
    {mesh Cmask : ℝ} (hmesh0 : 0 ≤ mesh) (hmesh1 : mesh ≤ 1)
    (hscaleMesh : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ mesh)
    (hCmask : 1 ≤ Cmask)
    (hmask : ∀ (u : GridTuples) j z, 0 ≤ allocatedIntegerKernelMask B U basis S x (fun _ => id) j
      modulus
      (integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u (fun _ => id) j v₀) modulus) z ∧ allocatedIntegerKernelMask B U basis S x (fun _ => id) j
      modulus
      (integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u (fun _ => id) j v₀) modulus) z ≤ Cmask)
    (T : Fin m → ℝ) (hT : ∀ j, 4 ≤ T j)
    (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
        ((2 : ℝ) ^ Fintype.card (Fin 1) * ((Fintype.card (Fin 1) : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4)
    (hF : Measurable F) (hFbound : ∀ p, ‖F p‖ ≤ 1) :
    let lower := fun (a : {a // ¬grid a}) (p : B a.val × Fin (degree a.val)) => (c ⟨a,p⟩ : ℝ) / L ⟨a,p⟩
    let width := fun (a : {a // ¬grid a}) (p : B a.val × Fin (degree a.val)) =>
      (step ⟨a,p⟩ : ℝ) * ((H ⟨a,p⟩ : ℝ) - 1) / L ⟨a,p⟩
    let ideal := allocatedSlicedPhysicalJetIdeal B U basis S hR hB lower width
    let _ := containedProgressionResidueLaw activeB activeDegree L H step c positiveLengths
      (fun j : Tuple => hH₀ (embed j)) hsubset modulus hm residue hsize
    let _ := fun (u : GridTuples) j => integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u (fun _ => id) j v₀) modulus
    let radius := max (4 * Real.exp P) (Real.exp (allocatedJetSupportLog (G := G) B (Fin 1) jetRows P))
    let Ki : ℝ≥0 := (‖(∏ o : Output, R o.1.2.val.1)⁻¹‖₊ *
      (NNReal.mk (Real.exp (slicedJointDensityLogBudget O m P)) (Real.exp_nonneg _) *
        NNReal.mk (Real.exp P) (Real.exp_nonneg _))) * 2
    let select := allocatedLongIntegerSelect B U basis S (O := jetRows)
    ‖actual - (∫ y, ((gridLaw).mean (fun u => allocatedWholeMaskedCoveredProfile
        B U basis hR hσ S x (fun _ => id) hb o bW d (principalAxisJoin grid u v₀) modulus ideal y) : ℂ) * F y
      ∂Measure.pi (fun j => Measure.pi (fun _ : Finset (Fin 1) => ν j)))‖ ≤
      (2 * Real.exp (allocatedJetSupportLog (G := G) B (Fin 1) jetRows P) + 1)^
        Fintype.card (Σ _ : LayerSamplerAxis I n, Finset (Fin 1)) *
        (Fintype.card {a // ¬grid a} * εcoef *
          (1 + (layerKernelIndexBound m Mk : ℝ) * (bound : ℝ) + εcoef)^Fintype.card {a // ¬grid a}) +
      Cmask ^ Fintype.card (LayerSamplerAxis I n) *
        (η +
      ((2 * (cap : ℝ) * scalarCubeGridBoundaryConstant (Fin 1) / volume.real (scalarCubeDomain (Fin 1)) +
        (lip : ℝ) * 2) * ∑ j, (modulus : ℝ) / H j + (lip : ℝ) * ε) *
        (2 * Real.exp (allocatedJetSupportLog (G := G) B (Fin 1) (fun _ => Finset (Fin 1)) P)) ^ Fintype.card Jet + (2 * radius) ^ Fintype.card (UnselectedColumn select) *
          ((2 * radius + 2) ^ Fintype.card {o : Jet // allocatedLongIntegerCoordinate B U basis S (O := jetRows) o} *
            ((Ki : ℝ) + lip) * mesh)) := by
  intro lower width ideal law outputResidue radius Ki select
  have hg (a) (p) := progression_slice_endpoint_geometry (c ⟨a,p⟩)
    (positiveLengths _) (hstep _) (hH _) hδ (hsubset _) (hdense _)
  have hw (a) (p) : |lower a p| + |width a p| ≤ 1 := (hg a p).2.2.1
  have hl (a) (p) : 0 ≤ lower a p := (hg a p).1
  have hwδ (a) (p) : δ / 2 ≤ width a p := (hg a p).2.1
  have ht := allocatedSlicedCoveredProfile_mean_test_integral B U basis S x hR hB lower width hσ v₀ Q hb o bW d ν
    O hO hw ha (half_pos hδ) hP haP hδP hprincipal hwδ hl hRP hRi modulus gridLaw outputResidue
    hCmask hmask hσ1 T hT hsource C hC hchart hbudget F hF hFbound
  have h := allocatedSlicedWholeCovered_ideal_comparison B U basis hR hσ S x s hA hMk hi
    hP hMkP hRP hRi hσi hcount Q hb o bW d (fun p => F p.2)
    H₀ step₀ c₀ hH₀ hsubset₀ modulus r₀ hcell hstep hH hδ hdense hm hsize hsmall hε hmesh
    N O hN hO hB hx ha hδone hη hprincipal A hTransition hσsmall haP hδP selection hgood hσ1
    he hεcoef hεe hlarge hperiod v₀ hv₀ hmesh0 hmesh1 hscaleMesh hCmask hmask
    (hF.comp measurable_snd) (fun p => hFbound p.2)
  change ‖actual - (gridLaw).complexMean (fun u => ∫ a₀, ∫ z,
    (allocatedLongProfileDensity B U basis S x (fun _ => id) modulus (outputResidue u) ideal z : ℂ) *
      allocatedCoveredFixedTest B U basis S x u v₀ (fun _ => id) Q hb o bW d (fun p => F p.2) a₀ z
        ∂reference ∂frozenSource)‖ ≤ _ at h
  rw [ht] at h
  simpa only [allocatedWholeMaskedCoveredProfile_join] using h

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rowTypes I n grid
local notation "baseVolume" => (allocatedFullGridNaturalVolume B U b S rowSets *
  coveredJetArrayScale (O := rowTypes) U * ∏ a, allocatedLongJetOutputScale B U b S (O := rowTypes) a)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

theorem allocatedFiniteSourceModel_integrable
    (μ : Measure (EuclideanJetLayers U rowTypes)) [IsProbabilityMeasure μ]
    {K : Type*} [Fintype K]
    (a : K → ℂ) (f : K → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ)
    {L : ℝ≥0} (hLf : ∀ k s, LipschitzWith L (f k s)) (hf : ∀ k s v, ‖f k s v‖ ≤ 1)
    (e : {a // grid a} → ScalarSiteExpansion (Finset α))
    {Nt V Cc Hs : {a // grid a} → ℝ} {Lg : ℝ≥0}
    (he : ∀ a, (e a).Bounds (Nt a) (V a) (Cc a) Lg (Hs a)) :
    Integrable (fun y =>
      allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f y *
        allocatedFullGridChartModel B U b S rowSets d hb o bW e y) μ := by
  let model := fun y =>
    allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f y *
      allocatedFullGridChartModel B U b S rowSets d hb o bW e y
  have hm : Measurable model :=
    (allocatedProductChartIdealApproximation_measurable B U b S rowSets x y₀ q d period r hr hb o bW a f hLf hf).mul
      (allocatedFullGridChartModel_measurable B U b S rowSets d hb o bW e)
  let Csum := ∑ label : Finset α → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)), ∑ k,
    ‖allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label k‖
  have hmBound (y) : ‖model y‖ ≤ Csum * ∏ a, Cc a := by
    dsimp only [model]
    rw [norm_mul]
    exact mul_le_mul
      (allocatedProductChartIdealApproximation_norm_le B U b S rowSets x y₀ q d period r hr hb o bW a f hf y)
      (allocatedFullGridChartModel_norm_le B U b S rowSets d hb o bW e he y)
      (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _)))
  have hmi : Integrable model μ := Integrable.of_bound hm.aestronglyMeasurable
    (Csum * ∏ a, Cc a) (Filter.Eventually.of_forall hmBound)
  exact hmi

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rowTypes I n grid
local notation "baseVolume" => (allocatedFullGridNaturalVolume B U b S rowSets *
  coveredJetArrayScale (O := rowTypes) U * ∏ a, allocatedLongJetOutputScale B U b S (O := rowTypes) a)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

theorem allocatedFiniteSourceModel_test_error
    (μ : Measure (EuclideanJetLayers U rowTypes)) [IsProbabilityMeasure μ]
    {K : Type*} [Fintype K]
    (a : K → ℂ) (f : K → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ)
    {L : ℝ≥0} (hLf : ∀ k s, LipschitzWith L (f k s)) (hf : ∀ k s v, ‖f k s v‖ ≤ 1)
    (e : {a // grid a} → ScalarSiteExpansion (Finset α))
    {Nt V Cc Hs : {a // grid a} → ℝ} {Lg : ℝ≥0}
    (he : ∀ a, (e a).Bounds (Nt a) (V a) (Cc a) Lg (Hs a))
    (source : EuclideanJetLayers U rowTypes → ℂ) (hsource : Measurable source)
    {ε : ℝ}
    (herr : ∀ y, ‖source y -
      allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f y *
        allocatedFullGridChartModel B U b S rowSets d hb o bW e y‖ ≤ ε)
    (φ : EuclideanJetLayers U rowTypes → ℂ) (hφ : Measurable φ) (hφb : ∀ y, ‖φ y‖ ≤ 1) :
    Integrable source μ ∧
      ‖(∫ y, source y * φ y ∂μ) - ∫ y,
        (allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f y *
          allocatedFullGridChartModel B U b S rowSets d hb o bW e y) * φ y ∂μ‖ ≤ ε := by
  let model := fun y =>
    allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f y *
      allocatedFullGridChartModel B U b S rowSets d hb o bW e y
  have hm : Measurable model :=
    (allocatedProductChartIdealApproximation_measurable B U b S rowSets x y₀ q d period r hr hb o bW a f hLf hf).mul
      (allocatedFullGridChartModel_measurable B U b S rowSets d hb o bW e)
  let Csum := ∑ label : Finset α → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)), ∑ k,
    ‖allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label k‖
  have hmBound (y) : ‖model y‖ ≤ Csum * ∏ a, Cc a := by
    dsimp only [model]
    rw [norm_mul]
    exact mul_le_mul
      (allocatedProductChartIdealApproximation_norm_le B U b S rowSets x y₀ q d period r hr hb o bW a f hf y)
      (allocatedFullGridChartModel_norm_le B U b S rowSets d hb o bW e he y)
      (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _)))
  have hmi : Integrable model μ := Integrable.of_bound hm.aestronglyMeasurable
    (Csum * ∏ a, Cc a) (Filter.Eventually.of_forall hmBound)
  obtain ⟨hs, ht⟩ := uniform_complex_approximation_test μ model source hmi hsource
    (fun y => by simpa only [norm_sub_rev] using herr y) φ hφ hφb
  exact ⟨hs, by simpa only [norm_sub_rev] using ht⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (x : G → IntegerScalarCubeBox (Fin 1) S.value)
variable (s : ∀ j : Fin m, Finset (Fin 1) ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) id).submatrix id (s j)).det ≠ 0)
variable {Mk : ℕ} (hMk : 0 < Mk)
variable (hi : ∀ j : Fin m, fixedKernelInverseBound (O := Finset (Fin 1))
  S.positive x (j.val + 1) id (s j) (hA j) (1 / (Mk : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMkP : (Mk : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a)) (fun a => degree (Subtype.val a))
local notation "Jet" => (Σ _a : {a // ¬grid a}, Finset (Fin 1))
local notation "bound" => NNReal.mk
  (Real.exp (allocatedDensityLog (G := G) B (Fin 1) (fun _ => Finset (Fin 1)) P)) (Real.exp_nonneg _)
local notation "cap" => bound ^ Fintype.card (LayerSamplerAxis I n)
local notation "lip" => (Fintype.card (LayerSamplerAxis I n) : ℝ≥0) * bound * cap

local notation "Endpoint" => OneCubeActiveEndpoint (B := B) degree grid
local notation "Row" => OneCubeActiveRow grid

local notation "Output" => (Σ _e : Row, Unit)
local notation "jetRows" => (fun _ : Fin m => Finset (Fin 1))

local notation "activeB" => (fun a : {a // ¬grid a} => B (Subtype.val a))
local notation "activeDegree" => (fun a : {a // ¬grid a} => degree (Subtype.val a))
local notation "L" => principalAxisLength (fun a => ¬grid a) (allocatedPrincipalSides B U basis S)
local notation "positiveLengths" => (fun j : Tuple => allocatedPrincipalSides_pos B U basis S
  (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j)))

variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (rowSets : Fin m → Finset (Finset (Fin 1))) (hrows : ∀ j t, t ∈ rowSets j)
local notation "selectedRows" => (fun j : Fin m => {t : Finset (Fin 1) // t ∈ rowSets j})
local notation "rowEquiv" => (fun j => Equiv.symm (oneCubeRowsEquiv (rowSets j) (hrows j)))
variable (F : EuclideanJetLayers U (fun j : Fin m => {t : Finset (Fin 1) // t ∈ rowSets j}) → ℂ)
local notation "fullTest" => (fun y => F (euclideanJetRowsReindex rowEquiv U y))

local notation "source" => allocatedCoefficientSource B U basis hR hσ S
local notation "frozenSource" => allocatedFrozenCoefficientSource B U basis hR hσ S
local notation "reference" => allocatedLongJetReference B U basis S jetRows
variable (H₀ step₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH₀ : ∀ t, 0 < H₀ t)
variable (hsubset₀ : ∀ t, integerProgressionSupport (c₀ t) (step₀ t : ℤ) (H₀ t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (modulus : ℕ) (r₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin 1) → ZMod modulus)
variable (hcell : 0 < (principalTupleWeights (α := Fin 1) B (layerSamplerDegree I n) H₀ hH₀).mass
  (Finset.univ.filter (fun y => principalResidueLabel modulus y = r₀)))
local notation "embed" => (fun j : Tuple => (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j) : PrincipalTupleIndex B (layerSamplerDegree I n)))
local notation "H" => (fun j : Tuple => H₀ (embed j))
local notation "step" => (fun j : Tuple => step₀ (embed j))
local notation "c" => (fun j : Tuple => c₀ (embed j))
local notation "hsubset" => (fun j : Tuple => hsubset₀ (embed j))
local notation "residue" => (fun j : Tuple => r₀ (embed j))
local notation "GridTuples" => PrincipalAxisTuples (α := Fin 1) grid (allocatedPrincipalSides B U basis S)
local notation "wholeLaw" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S) hH₀ hsubset₀ modulus r₀ hcell
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S) hH₀ hsubset₀ modulus r₀ hcell grid
local notation "wholeRoot" y => allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y
local notation "wholeDirs" y => allocatedPhysicalCubeDirections B U basis S x y
local notation "deck" => PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)
local notation "actual" => allocatedSlicedCoveredExpectation B U basis hR hσ S x Q hb o bW d (fullTest ∘ Prod.snd)
  H₀ step₀ c₀ hH₀ hsubset₀ modulus r₀ hcell

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

include hR hσ hMk hi hP hMkP hRP hRi hσi hcount in
theorem allocatedSlicedWholeCovered_selected_profile_comparison
    (hstep : ∀ j : Tuple, 0 < step j) (hH : ∀ j : Tuple, 2 ≤ H j)
    {δ : ℝ} (hδ : 0 < δ)
    (hdense : ∀ j : Tuple, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (hm : 0 < modulus)
    (hsize : ∀ j : Tuple, (Fintype.card (Fin 1) + 1) * modulus ≤ H j)
    (hsmall : ∀ j : Tuple, scalarCubeGridBoundaryConstant (Fin 1) * ((modulus : ℝ) / H j) <
      volume.real (scalarCubeDomain (Fin 1)))
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j : Tuple, (step j : ℝ) / L j ≤ ε)
    (N O : ℕ) (hN : Fintype.card Endpoint ≤ N) (hO : Fintype.card Row ≤ O)
    (hB : ∀ a : {a // ¬grid a}, 4 ≤ Fintype.card (B a.val))
    (hx : ∀ g, IntegerScalarCube S.value (fun i => (x g i : ℤ)))
    {a η : ℝ} (ha : 0 < a) (hδone : δ ≤ 1) (hη : 0 < η)
    (hprincipal : ∀ j : {a // ¬grid a}, a ≤ unitProfilePrincipalSize (B := B) j.val)
    (A : ℝ≥0) (hTransition : LipschitzWith A Real.smoothTransition)
    (hσsmall : ∀ j, |σ j| ≤ slicedPolynomialScale N O N m m 1 1 a (δ / 2) A η)
    (haP : a⁻¹ ≤ Real.exp P) (hδP : (δ / 2)⁻¹ ≤ Real.exp P)
    (selection : Fin 1 ↪ G)
    (hgood : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
    (hσ1 : ∀ j, σ j ≤ 1)
    {e εcoef : ℝ} (he : 0 ≤ e) (hεcoef : 0 < εcoef) (hεe : εcoef⁻¹ ≤ Real.exp e)
    (hlarge : Real.exp (allocatedKernelReplacementLog (G := G) B (Fin 1) jetRows P e) ≤ S.value)
    (hperiod : ∀ j : Fin m, integerScalarLattice (Finset (Fin 1)) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) id).mulVecLin.range)
    (v₀ : PrincipalAxisTuples (α := Fin 1) (fun a => ¬grid a) (allocatedPrincipalSides B U basis S))
    (hv₀ : (containedProgressionResidueLaw activeB activeDegree L H step c positiveLengths
      (fun j : Tuple => hH₀ (embed j)) hsubset modulus hm residue hsize).weight v₀ ≠ 0)
    {mesh Cmask : ℝ} (hmesh0 : 0 ≤ mesh) (hmesh1 : mesh ≤ 1)
    (hscaleMesh : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ mesh)
    (hCmask : 1 ≤ Cmask)
    (hmask : ∀ (u : GridTuples) j z, 0 ≤ allocatedIntegerKernelMask B U basis S x (fun _ => id) j
      modulus
      (integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u (fun _ => id) j v₀) modulus) z ∧ allocatedIntegerKernelMask B U basis S x (fun _ => id) j
      modulus
      (integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u (fun _ => id) j v₀) modulus) z ≤ Cmask)
    (T : Fin m → ℝ) (hT : ∀ j, 4 ≤ T j)
    (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
        ((2 : ℝ) ^ Fintype.card (Fin 1) * ((Fintype.card (Fin 1) : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4)
    (hF : Measurable F) (hFbound : ∀ p, ‖F p‖ ≤ 1) :
    let lower := fun (a : {a // ¬grid a}) (p : B a.val × Fin (degree a.val)) => (c ⟨a,p⟩ : ℝ) / L ⟨a,p⟩
    let width := fun (a : {a // ¬grid a}) (p : B a.val × Fin (degree a.val)) =>
      (step ⟨a,p⟩ : ℝ) * ((H ⟨a,p⟩ : ℝ) - 1) / L ⟨a,p⟩
    let ideal := allocatedSlicedRowIdeal B U basis S rowSets hR hrows hB lower width
    let _ := containedProgressionResidueLaw activeB activeDegree L H step c positiveLengths
      (fun j : Tuple => hH₀ (embed j)) hsubset modulus hm residue hsize
    let _ := fun (u : GridTuples) j => integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u (fun _ => id) j v₀) modulus
    let radius := max (4 * Real.exp P) (Real.exp (allocatedJetSupportLog (G := G) B (Fin 1) jetRows P))
    let Ki : ℝ≥0 := (‖(∏ o : Output, R o.1.2.val.1)⁻¹‖₊ *
      (NNReal.mk (Real.exp (slicedJointDensityLogBudget O m P)) (Real.exp_nonneg _) *
        NNReal.mk (Real.exp P) (Real.exp_nonneg _))) * 2
    let select := allocatedLongIntegerSelect B U basis S (O := jetRows)
    ‖actual - (∫ y, ((gridLaw).mean (fun u => allocatedWholeMaskedCoveredProfile
        B U basis hR hσ S x (fun j => (Subtype.val : selectedRows j → Finset (Fin 1))) hb o bW d (principalAxisJoin grid u v₀) modulus ideal y) : ℂ) * F y
      ∂Measure.pi (fun j => Measure.pi (fun _ : selectedRows j => ν j)))‖ ≤
      (2 * Real.exp (allocatedJetSupportLog (G := G) B (Fin 1) jetRows P) + 1)^
        Fintype.card (Σ _ : LayerSamplerAxis I n, Finset (Fin 1)) *
        (Fintype.card {a // ¬grid a} * εcoef *
          (1 + (layerKernelIndexBound m Mk : ℝ) * (bound : ℝ) + εcoef)^Fintype.card {a // ¬grid a}) +
      Cmask ^ Fintype.card (LayerSamplerAxis I n) *
        (η +
      ((2 * (cap : ℝ) * scalarCubeGridBoundaryConstant (Fin 1) / volume.real (scalarCubeDomain (Fin 1)) +
        (lip : ℝ) * 2) * ∑ j, (modulus : ℝ) / H j + (lip : ℝ) * ε) *
        (2 * Real.exp (allocatedJetSupportLog (G := G) B (Fin 1) (fun _ => Finset (Fin 1)) P)) ^ Fintype.card Jet + (2 * radius) ^ Fintype.card (UnselectedColumn select) *
          ((2 * radius + 2) ^ Fintype.card {o : Jet // allocatedLongIntegerCoordinate B U basis S (O := jetRows) o} *
            ((Ki : ℝ) + lip) * mesh)) := by
  intro lower width ideal law outputResidue radius Ki select
  have ht := allocatedWholeMaskedSlicedProfile_oneCube_mean_integral B U basis hR hσ S rowSets hrows x
    hb o bW d hB lower width ν gridLaw (fun u => principalAxisJoin grid u v₀) modulus F
  have hc := allocatedSlicedWholeCovered_profile_comparison B U basis hR hσ S x s hA hMk hi
    hP hMkP hRP hRi hσi hcount Q hb o bW d fullTest
    H₀ step₀ c₀ hH₀ hsubset₀ modulus r₀ hcell ν hstep hH hδ hdense hm hsize hsmall hε hmesh
    N O hN hO hB hx ha hδone hη hprincipal A hTransition hσsmall haP hδP selection hgood hσ1
    he hεcoef hεe hlarge hperiod v₀ hv₀ hmesh0 hmesh1 hscaleMesh hCmask hmask
    T hT hsource C hC hchart hbudget
    (hF.comp (euclideanJetRowsReindex rowEquiv U).measurable) (fun y => hFbound _)

  exact (congrArg (fun z : ℂ => ‖actual - z‖) ht).trans_le hc

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (x : G → IntegerScalarCubeBox (Fin 1) S.value)
variable (s : ∀ j : Fin m, Finset (Fin 1) ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) id).submatrix id (s j)).det ≠ 0)
variable {Mk : ℕ} (hMk : 0 < Mk)
variable (hi : ∀ j : Fin m, fixedKernelInverseBound (O := Finset (Fin 1))
  S.positive x (j.val + 1) id (s j) (hA j) (1 / (Mk : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMkP : (Mk : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a)) (fun a => degree (Subtype.val a))
local notation "Jet" => (Σ _a : {a // ¬grid a}, Finset (Fin 1))
local notation "bound" => NNReal.mk
  (Real.exp (allocatedDensityLog (G := G) B (Fin 1) (fun _ => Finset (Fin 1)) P)) (Real.exp_nonneg _)
local notation "cap" => bound ^ Fintype.card (LayerSamplerAxis I n)
local notation "lip" => (Fintype.card (LayerSamplerAxis I n) : ℝ≥0) * bound * cap

local notation "Endpoint" => OneCubeActiveEndpoint (B := B) degree grid
local notation "Row" => OneCubeActiveRow grid

local notation "Output" => (Σ _e : Row, Unit)
local notation "jetRows" => (fun _ : Fin m => Finset (Fin 1))

local notation "activeB" => (fun a : {a // ¬grid a} => B (Subtype.val a))
local notation "activeDegree" => (fun a : {a // ¬grid a} => degree (Subtype.val a))
local notation "L" => principalAxisLength (fun a => ¬grid a) (allocatedPrincipalSides B U basis S)
local notation "positiveLengths" => (fun j : Tuple => allocatedPrincipalSides_pos B U basis S
  (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j)))

variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (rowSets : Fin m → Finset (Finset (Fin 1))) (hrows : ∀ j t, t ∈ rowSets j)
local notation "selectedRows" => (fun j : Fin m => {t : Finset (Fin 1) // t ∈ rowSets j})
local notation "rowEquiv" => (fun j => Equiv.symm (oneCubeRowsEquiv (rowSets j) (hrows j)))
variable (F : EuclideanJetLayers U (fun j : Fin m => {t : Finset (Fin 1) // t ∈ rowSets j}) → ℂ)
local notation "fullTest" => (fun y => F (euclideanJetRowsReindex rowEquiv U y))

local notation "source" => allocatedCoefficientSource B U basis hR hσ S
local notation "frozenSource" => allocatedFrozenCoefficientSource B U basis hR hσ S
local notation "reference" => allocatedLongJetReference B U basis S jetRows
variable (H₀ step₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH₀ : ∀ t, 0 < H₀ t)
variable (hsubset₀ : ∀ t, integerProgressionSupport (c₀ t) (step₀ t : ℤ) (H₀ t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (modulus : ℕ) (r₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin 1) → ZMod modulus)
variable (hcell : 0 < (principalTupleWeights (α := Fin 1) B (layerSamplerDegree I n) H₀ hH₀).mass
  (Finset.univ.filter (fun y => principalResidueLabel modulus y = r₀)))
local notation "embed" => (fun j : Tuple => (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j) : PrincipalTupleIndex B (layerSamplerDegree I n)))
local notation "H" => (fun j : Tuple => H₀ (embed j))
local notation "step" => (fun j : Tuple => step₀ (embed j))
local notation "c" => (fun j : Tuple => c₀ (embed j))
local notation "hsubset" => (fun j : Tuple => hsubset₀ (embed j))
local notation "residue" => (fun j : Tuple => r₀ (embed j))
local notation "GridTuples" => PrincipalAxisTuples (α := Fin 1) grid (allocatedPrincipalSides B U basis S)
local notation "wholeLaw" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S) hH₀ hsubset₀ modulus r₀ hcell
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S) hH₀ hsubset₀ modulus r₀ hcell grid
local notation "wholeRoot" y => allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y
local notation "wholeDirs" y => allocatedPhysicalCubeDirections B U basis S x y
local notation "deck" => PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)
local notation "actual" => allocatedSlicedCoveredExpectation B U basis hR hσ S x Q hb o bW d (fullTest ∘ Prod.snd)
  H₀ step₀ c₀ hH₀ hsubset₀ modulus r₀ hcell

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

include hR hσ hMk hi hP hMkP hRP hRi hσi hcount in
theorem allocatedSlicedWholeCovered_finite_model_comparison
    (hstep : ∀ j : Tuple, 0 < step j) (hH : ∀ j : Tuple, 2 ≤ H j)
    {δ : ℝ} (hδ : 0 < δ)
    (hdense : ∀ j : Tuple, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (hm : 0 < modulus)
    (hsize : ∀ j : Tuple, (Fintype.card (Fin 1) + 1) * modulus ≤ H j)
    (hsmall : ∀ j : Tuple, scalarCubeGridBoundaryConstant (Fin 1) * ((modulus : ℝ) / H j) <
      volume.real (scalarCubeDomain (Fin 1)))
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j : Tuple, (step j : ℝ) / L j ≤ ε)
    (N O : ℕ) (hN : Fintype.card Endpoint ≤ N) (hO : Fintype.card Row ≤ O)
    (hB : ∀ a : {a // ¬grid a}, 4 ≤ Fintype.card (B a.val))
    (hx : ∀ g, IntegerScalarCube S.value (fun i => (x g i : ℤ)))
    {a η : ℝ} (ha : 0 < a) (hδone : δ ≤ 1) (hη : 0 < η)
    (hprincipal : ∀ j : {a // ¬grid a}, a ≤ unitProfilePrincipalSize (B := B) j.val)
    (A : ℝ≥0) (hTransition : LipschitzWith A Real.smoothTransition)
    (hσsmall : ∀ j, |σ j| ≤ slicedPolynomialScale N O N m m 1 1 a (δ / 2) A η)
    (haP : a⁻¹ ≤ Real.exp P) (hδP : (δ / 2)⁻¹ ≤ Real.exp P)
    (selection : Fin 1 ↪ G)
    (hgood : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
    (hσ1 : ∀ j, σ j ≤ 1)
    {e εcoef : ℝ} (he : 0 ≤ e) (hεcoef : 0 < εcoef) (hεe : εcoef⁻¹ ≤ Real.exp e)
    (hlarge : Real.exp (allocatedKernelReplacementLog (G := G) B (Fin 1) jetRows P e) ≤ S.value)
    (hperiod : ∀ j : Fin m, integerScalarLattice (Finset (Fin 1)) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) id).mulVecLin.range)
    (v₀ : PrincipalAxisTuples (α := Fin 1) (fun a => ¬grid a) (allocatedPrincipalSides B U basis S))
    (hv₀ : (containedProgressionResidueLaw activeB activeDegree L H step c positiveLengths
      (fun j : Tuple => hH₀ (embed j)) hsubset modulus hm residue hsize).weight v₀ ≠ 0)
    {mesh Cmask : ℝ} (hmesh0 : 0 ≤ mesh) (hmesh1 : mesh ≤ 1)
    (hscaleMesh : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ mesh)
    (hCmask : 1 ≤ Cmask)
    (hmask : ∀ (u : GridTuples) j z, 0 ≤ allocatedIntegerKernelMask B U basis S x (fun _ => id) j
      modulus
      (integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u (fun _ => id) j v₀) modulus) z ∧ allocatedIntegerKernelMask B U basis S x (fun _ => id) j
      modulus
      (integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u (fun _ => id) j v₀) modulus) z ≤ Cmask)
    (T : Fin m → ℝ) (hT : ∀ j, 4 ≤ T j)
    (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
        ((2 : ℝ) ^ Fintype.card (Fin 1) * ((Fintype.card (Fin 1) : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4)
    (hF : Measurable F) (hFbound : ∀ p, ‖F p‖ ≤ 1) :
    let lower := fun (a : {a // ¬grid a}) (p : B a.val × Fin (degree a.val)) => (c ⟨a,p⟩ : ℝ) / L ⟨a,p⟩
    let width := fun (a : {a // ¬grid a}) (p : B a.val × Fin (degree a.val)) =>
      (step ⟨a,p⟩ : ℝ) * ((H ⟨a,p⟩ : ℝ) - 1) / L ⟨a,p⟩
    let ideal := allocatedSlicedRowIdeal B U basis S rowSets hR hrows hB lower width
    let _ := containedProgressionResidueLaw activeB activeDegree L H step c positiveLengths
      (fun j : Tuple => hH₀ (embed j)) hsubset modulus hm residue hsize
    let _ := fun (u : GridTuples) j => integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u (fun _ => id) j v₀) modulus
    let radius := max (4 * Real.exp P) (Real.exp (allocatedJetSupportLog (G := G) B (Fin 1) jetRows P))
    let Ki : ℝ≥0 := (‖(∏ o : Output, R o.1.2.val.1)⁻¹‖₊ *
      (NNReal.mk (Real.exp (slicedJointDensityLogBudget O m P)) (Real.exp_nonneg _) *
        NNReal.mk (Real.exp P) (Real.exp_nonneg _))) * 2
    let select := allocatedLongIntegerSelect B U basis S (O := jetRows)
    ∀ (period : ℕ) [NeZero period] (r : ℝ≥0) (hr : 0 < r)
      (u₀ : GridTuples) {Kmodel : Type*} [Fintype Kmodel]
      (am : Kmodel → ℂ) (fm : Kmodel → Finset (Fin 1) → (LayerSamplerAxis I n → ℝ) → ℂ)
      {Lm : ℝ≥0} (_ : ∀ k t, LipschitzWith Lm (fm k t))
      (_ : ∀ k t z, ‖fm k t z‖ ≤ 1)
      (eg : {a // grid a} → ScalarSiteExpansion (Finset (Fin 1)))
      {Nt V Cc Hs : {a // grid a} → ℝ} {Lg : ℝ≥0}
      (_ : ∀ a, (eg a).Bounds (Nt a) (V a) (Cc a) Lg (Hs a))
      {εmodel : ℝ},
      (∀ y : EuclideanJetLayers U selectedRows,
        ‖((gridLaw).mean (fun u => allocatedWholeMaskedCoveredProfile
        B U basis hR hσ S x (fun j => (Subtype.val : selectedRows j → Finset (Fin 1))) hb o bW d
          (principalAxisJoin grid u v₀) modulus ideal y) : ℂ) - (allocatedProductChartIdealApproximation B U basis S rowSets x
          (principalAxisJoin grid u₀ v₀) modulus d period r hr hb o bW am fm y *
        allocatedFullGridChartModel B U basis S rowSets d hb o bW eg y)‖ ≤ εmodel) →
      ‖actual - ∫ y, (allocatedProductChartIdealApproximation B U basis S rowSets x
          (principalAxisJoin grid u₀ v₀) modulus d period r hr hb o bW am fm y *
        allocatedFullGridChartModel B U basis S rowSets d hb o bW eg y) * F y
        ∂Measure.pi (fun j => Measure.pi (fun _ : selectedRows j => ν j))‖ ≤
      (     (2 * Real.exp (allocatedJetSupportLog (G := G) B (Fin 1) jetRows P) + 1)^
        Fintype.card (Σ _ : LayerSamplerAxis I n, Finset (Fin 1)) *
        (Fintype.card {a // ¬grid a} * εcoef *
          (1 + (layerKernelIndexBound m Mk : ℝ) * (bound : ℝ) + εcoef)^Fintype.card {a // ¬grid a}) +
      Cmask ^ Fintype.card (LayerSamplerAxis I n) *
        (η +
      ((2 * (cap : ℝ) * scalarCubeGridBoundaryConstant (Fin 1) / volume.real (scalarCubeDomain (Fin 1)) +
        (lip : ℝ) * 2) * ∑ j, (modulus : ℝ) / H j + (lip : ℝ) * ε) *
        (2 * Real.exp (allocatedJetSupportLog (G := G) B (Fin 1) (fun _ => Finset (Fin 1)) P)) ^ Fintype.card Jet + (2 * radius) ^ Fintype.card (UnselectedColumn select) *
          ((2 * radius + 2) ^ Fintype.card {o : Jet // allocatedLongIntegerCoordinate B U basis S (O := jetRows) o} *
            ((Ki : ℝ) + lip) * mesh))) + εmodel := by
  intro lower width ideal law outputResidue radius Ki select period hperiodNZ r hr u₀ Kmodel hKmodel
    am fm Lm hLm hfm eg Nt V Cc Hs Lg heg εmodel happrox
  have hc := allocatedSlicedWholeCovered_selected_profile_comparison B U basis hR hσ S x s hA hMk hi
    hP hMkP hRP hRi hσi hcount Q hb o bW d rowSets hrows F
    H₀ step₀ c₀ hH₀ hsubset₀ modulus r₀ hcell ν hstep hH hδ hdense hm hsize hsmall hε hmesh
    N O hN hO hB hx ha hδone hη hprincipal A hTransition hσsmall haP hδP selection hgood hσ1
    he hεcoef hεe hlarge hperiod v₀ hv₀ hmesh0 hmesh1 hscaleMesh hCmask hmask
    T hT hsource C hC hchart hbudget hF hFbound
  have hs := allocatedWholeMaskedSlicedProfile_mean_measurable B U basis hR hσ S rowSets hrows
    x hb o bW d hB lower width gridLaw (fun u => principalAxisJoin grid u v₀) modulus
  have ht := allocatedFiniteSourceModel_test_error B U basis S rowSets x
    (principalAxisJoin grid u₀ v₀) modulus d period r hr hb o bW
    (Measure.pi (fun j => Measure.pi (fun _ : selectedRows j => ν j))) am fm hLm hfm eg heg
    _ hs happrox F hF hFbound
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hc ht.2)

end Erdos3.VectorPolynomial

end

end OAI
