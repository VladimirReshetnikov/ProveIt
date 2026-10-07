import OAI.Combinatorics.Progressions.Estimates.AllocatedActualHaarComparison
import OAI.Combinatorics.Progressions.Lattices.AllocatedResidueCoefficientL1

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable [DecidableEq G] [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
variable [∀ j : Fin m, DecidableEq (AllocatedNonkernelCoefficient (G := G) B j)]
variable (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S

local notation "activeB" => (fun a : {a // ¬grid a} => B (Subtype.val a))
local notation "activeDegree" => (fun a : {a // ¬grid a} => layerSamplerDegree I n (Subtype.val a))
local notation "lengths" => principalAxisLength (fun a => ¬grid a) sides
local notation "tupleIndex" => PrincipalTupleIndex activeB activeDegree
local notation "positiveLengths" => (fun j : tupleIndex => allocatedPrincipalSides_pos B U basis S
  (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j)))

theorem allocatedSlicedLongJet_coefficient_l1 {M : ℕ} (hM : 0 < M)
    (selection : α ↪ G) (hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
    (hq : Fintype.card α ≤ m+1) (hinj : ∀ j, Function.Injective (rows j))
    (hrows : ∀ j o, (rows j o).card ≤ j.val+1) (hσ1 : ∀ j, σ j ≤ 1)
    {P e ε : ℝ} (hP : 0 ≤ P) (he : 0 ≤ e) (hε : 0 < ε)
    (hMP : (M : ℝ) ≤ Real.exp P) (hRP : ∀ j, R j ≤ Real.exp P)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+1 ≤ Real.exp P)
    (hεe : ε⁻¹ ≤ Real.exp e)
    (hlarge : Real.exp (allocatedKernelReplacementLog (G := G) B α O P e) ≤ S.value)
    (modulus : ℕ)
    (hperiod : ∀ j, integerScalarLattice (O j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val+1) (rows j)).mulVecLin.range)
    (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
    (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
    (hi : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val+1) (rows j) (s j) (hA j) (1/(M : ℝ)))
    (u : PrincipalAxisTuples (α := α) grid sides)
    (H step : tupleIndex → ℕ) (c : tupleIndex → ℤ) (hH : ∀ j, 0 < H j)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (lengths j : ℤ))
    (hm : 0 < modulus) (r : tupleIndex → Option α → ZMod modulus)
    (hsize : ∀ j, (Fintype.card α + 1) * modulus ≤ H j)
    (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides)
    (hv₀ : (containedProgressionResidueLaw activeB activeDegree lengths H step c positiveLengths hH
      hsubset modulus hm r hsize).weight v₀ ≠ 0) :
    let C := Real.exp (allocatedDensityLog (G := G) B α O P)
    let CM : ℝ := layerKernelIndexBound m M
    let T := Real.exp (allocatedJetSupportLog (G := G) B α O P)
    let law := containedProgressionResidueLaw activeB activeDegree lengths H step c positiveLengths hH
      hsubset modulus hm r hsize
    let residue := fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v₀) modulus
    let proxy := fun z => (principalResidueWeights activeB activeDegree H hH modulus hm r hsize).mean
      (fun v => allocatedNormalizedLongJetDensity B U basis S x u rows s hA
        (principalTupleFlatten activeB activeDegree α
          (fun j i => ((if i = none then (c j : ℝ) else 0) + (step j : ℝ) * (v j i : ℝ)) / lengths j)) z)
    Integrable (allocatedLongProfileDensity B U basis S x rows modulus residue proxy)
      (allocatedLongJetReference B U basis S O) ∧
    (∫ z, |law.mean (fun v => allocatedLongJetDensity B U basis hR hσ S x u v rows s hA hσ1 z) -
        allocatedLongProfileDensity B U basis S x rows modulus residue proxy z|
      ∂allocatedLongJetReference B U basis S O) ≤
      (2*T+1)^Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) *
        (Fintype.card {a // ¬grid a} * ε * (1 + CM * C + ε)^Fintype.card {a // ¬grid a}) := by
  intro C CM T law residue proxy
  have hr (v) (hv : law.weight v ≠ 0) (j : Fin m) :
      integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v) modulus = residue j := by
    exact containedProgressionResidueLaw_matrix activeB activeDegree lengths H step c positiveLengths hH
      hsubset modulus hm r hsize (allocatedNonkernelExponent B j)
      (partitionedPrincipalInput grid (fun g a => (g,a)))
      (Sum.elim (fun ga : G × Option α => (x ga.1 ga.2 : ℤ)) (principalTupleIntegers u))
      (rows j) v v₀ hv hv₀
  have he := allocatedLongJet_residue_coefficient_l1 B U basis hR hσ S x rows
    hM selection hx hq hinj hrows hσ1 hP he hε hMP hRP hRi hσi hcount hεe hlarge
    modulus hperiod s hA hi u law residue hr
  have hp : (fun z => law.mean (fun v => allocatedNormalizedLongJetDensity B U basis S x u rows s hA
      (principalTupleNormalized lengths v) z)) = proxy := by
    funext z
    exact containedProgressionResidueLaw_mean activeB activeDegree lengths H step c positiveLengths hH
      hsubset modulus hm r hsize (fun y => allocatedNormalizedLongJetDensity B U basis S x u rows s hA y z)
  dsimp only at he
  rw [hp] at he
  exact he

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable [DecidableEq G] [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
variable [∀ j : Fin m, DecidableEq (AllocatedNonkernelCoefficient (G := G) B j)]
variable (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S

local notation "activeB" => (fun a : {a // ¬grid a} => B (Subtype.val a))
local notation "activeDegree" => (fun a : {a // ¬grid a} => layerSamplerDegree I n (Subtype.val a))
local notation "lengths" => principalAxisLength (fun a => ¬grid a) sides
local notation "tupleIndex" => PrincipalTupleIndex activeB activeDegree
local notation "positiveLengths" => (fun j : tupleIndex => allocatedPrincipalSides_pos B U basis S
  (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j)))

theorem allocatedSlicedLongJet_ideal_transfer {M : ℕ} (hM : 0 < M)
    (selection : α ↪ G) (hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
    (hq : Fintype.card α ≤ m+1) (hinj : ∀ j, Function.Injective (rows j))
    (hrows : ∀ j o, (rows j o).card ≤ j.val+1) (hσ1 : ∀ j, σ j ≤ 1)
    {P e ε : ℝ} (hP : 0 ≤ P) (he : 0 ≤ e) (hε : 0 < ε)
    (hMP : (M : ℝ) ≤ Real.exp P) (hRP : ∀ j, R j ≤ Real.exp P)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+1 ≤ Real.exp P)
    (hεe : ε⁻¹ ≤ Real.exp e)
    (hlarge : Real.exp (allocatedKernelReplacementLog (G := G) B α O P e) ≤ S.value)
    (modulus : ℕ)
    (hperiod : ∀ j, integerScalarLattice (O j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val+1) (rows j)).mulVecLin.range)
    (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
    (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
    (hi : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val+1) (rows j) (s j) (hA j) (1/(M : ℝ)))
    (u : PrincipalAxisTuples (α := α) grid sides)
    (H step : tupleIndex → ℕ) (c : tupleIndex → ℤ) (hH : ∀ j, 0 < H j)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (lengths j : ℤ))
    (hm : 0 < modulus) (r : tupleIndex → Option α → ZMod modulus)
    (hsize : ∀ j, (Fintype.card α + 1) * modulus ≤ H j)
    (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides)
    (hv₀ : (containedProgressionResidueLaw activeB activeDegree lengths H step c positiveLengths hH
      hsubset modulus hm r hsize).weight v₀ ≠ 0)
    (g : AllocatedLongJetRows B U basis S O → ℝ)
    (hg : Integrable g (allocatedLongJetReference B U basis S O)) {Eref : ℝ} :
    let C := Real.exp (allocatedDensityLog (G := G) B α O P)
    let CM : ℝ := layerKernelIndexBound m M
    let T := Real.exp (allocatedJetSupportLog (G := G) B α O P)
    let law := containedProgressionResidueLaw activeB activeDegree lengths H step c positiveLengths hH
      hsubset modulus hm r hsize
    let residue := fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v₀) modulus
    let proxy := fun z => (FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights α
      (H j) modulus (hH j) (fun _ => modulus) (r j) (fun _ => hm) (fun _ => le_rfl) (hsize j))).mean
      (fun v => allocatedNormalizedLongJetDensity B U basis S x u rows s hA
        (principalTupleFlatten activeB activeDegree α
          (fun j i => ((if i = none then (c j : ℝ) else 0) + (step j : ℝ) * (v j i : ℝ)) / lengths j)) z)
    (∫ z, |g z - allocatedLongProfileDensity B U basis S x rows modulus residue proxy z|
      ∂allocatedLongJetReference B U basis S O) ≤ Eref →
    (∫ z, |law.mean (fun v => allocatedLongJetDensity B U basis hR hσ S x u v rows s hA hσ1 z) - g z|
      ∂allocatedLongJetReference B U basis S O) ≤
      (2*T+1)^Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) *
        (Fintype.card {a // ¬grid a} * ε * (1 + CM * C + ε)^Fintype.card {a // ¬grid a}) + Eref := by
  intro C CM T law residue proxy href
  have hcoef := allocatedSlicedLongJet_coefficient_l1 B U basis hR hσ S x rows
    hM selection hx hq hinj hrows hσ1 hP he hε hMP hRP hRi hσi hcount hεe hlarge
    modulus hperiod s hA hi u H step c hH hsubset hm r hsize v₀ hv₀
  have hfi : Integrable (fun z => law.mean
      (fun v => allocatedLongJetDensity B U basis hR hσ S x u v rows s hA hσ1 z))
      (allocatedLongJetReference B U basis S O) :=
    law.mean_integrable _ _ (fun v =>
      (allocatedLongJetDensity_probability_data B U basis hR hσ S x u v rows s hA hσ1).2.1)
  exact density_l1_triangle_bound_reverse (allocatedLongJetReference B U basis S O)
    _ _ _ hfi hcoef.1 hg hcoef.2 href

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
variable (u : PrincipalAxisTuples (α := Fin 1) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
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
local notation "root" v => allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x (principalAxisJoin grid u v)
local notation "dirs" v => allocatedPhysicalCubeDirections B U basis S x (principalAxisJoin grid u v)
local notation "deck" => PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)
local notation "actual" weights:max => (∫ p, FiniteProbabilityWeights.complexMean weights (fun v =>
  F (Prod.fst ((allocatedCoefficientSplit B U basis S) (Prod.fst p)),
    euclideanCoefficientJetMap U (root v) (dirs v) (fun _ => id)
      (canonicalCoefficientDeckSample U bW basis hb o d (Nat.pos_of_ne_zero (NeZero.ne d)) (Prod.fst p) (Prod.snd p))))
  ∂(Measure.prod source (PMF.toMeasure deck)))

include hR hσ hMk hi hP hMkP hRP hRi hσi hcount in
theorem allocatedSlicedOriginalCovered_ideal_comparison
    (step H : Tuple → ℕ) (c : Tuple → ℤ)
    (hstep : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
    {δ : ℝ} (hδ : 0 < δ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
    (hdense : ∀ j, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (modulus : ℕ) (hm : 0 < modulus) (residue : Tuple → Option (Fin 1) → ZMod modulus)
    (hsize : ∀ j, (Fintype.card (Fin 1) + 1) * modulus ≤ H j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant (Fin 1) * ((modulus : ℝ) / H j) <
      volume.real (scalarCubeDomain (Fin 1)))
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j, (step j : ℝ) / L j ≤ ε)
    (N O : ℕ) (hN : Fintype.card Endpoint ≤ N) (hO : Fintype.card Row ≤ O)
    (hB : ∀ a : {a // ¬grid a}, 4 ≤ Fintype.card (B a.val))
    (hx : ∀ g, IntegerScalarCube S.value (fun i => (x g i : ℤ)))
    (hu : ∀ j, IntegerScalarCube (principalAxisLength grid (allocatedPrincipalSides B U basis S) j)
      (fun i => (u j i : ℤ)))
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
      (fun j => by have := hH j; omega) hsubset modulus hm residue hsize).weight v₀ ≠ 0)
    {mesh Cmask : ℝ} (hmesh0 : 0 ≤ mesh) (hmesh1 : mesh ≤ 1)
    (hscaleMesh : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ mesh)
    (hCmask : 1 ≤ Cmask)
    (hmask : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U basis S x (fun _ => id) j
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
      (fun j => by have := hH j; omega) hsubset modulus hm residue hsize
    let outputResidue := fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u (fun _ => id) j v₀) modulus
    let radius := max (4 * Real.exp P) (Real.exp (allocatedJetSupportLog (G := G) B (Fin 1) jetRows P))
    let Ki : ℝ≥0 := (‖(∏ o : Output, R o.1.2.val.1)⁻¹‖₊ *
      (NNReal.mk (Real.exp (slicedJointDensityLogBudget O m P)) (Real.exp_nonneg _) *
        NNReal.mk (Real.exp P) (Real.exp_nonneg _))) * 2
    let select := allocatedLongIntegerSelect B U basis S (O := jetRows)
    ‖actual law - ∫ a₀, ∫ z,
      (allocatedLongProfileDensity B U basis S x (fun _ => id) modulus outputResidue ideal z : ℂ) *
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
  have hHpos (j) : 0 < H j := by have := hH j; omega
  have hrows (j : Fin m) (t : Finset (Fin 1)) : t.card ≤ j.val + 1 :=
    (Finset.card_le_univ t).trans (by simp)
  have href := allocatedSlicedDiscreteIdeal_reference_l1 B U basis hR hσ S x u s hA hMk hi hP hMkP
    hRP hRi hσi hcount L step H (fun _ => modulus) c positiveLengths hstep hH hδ hsubset hdense
    (fun _ _ => modulus) residue (fun _ _ => hm) (fun _ _ => le_rfl) hsize hsmall hε hmesh
    N O hN hO hB hx hu ha hδone hη hprincipal A hTransition hσsmall haP hδP
    modulus outputResidue hmesh0 hmesh1 hscaleMesh hCmask hmask
  have hg (a) (p) := progression_slice_endpoint_geometry (c ⟨a,p⟩)
    (positiveLengths _) (hstep _) (hH _) hδ (hsubset _) (hdense _)
  have hw (a) (p) : |lower a p| + |width a p| ≤ 1 := (hg a p).2.2.1
  have hl (a) (p) : 0 ≤ lower a p := (hg a p).1
  have hwδ (a) (p) : δ / 2 ≤ width a p := (hg a p).2.1
  have hIi := allocatedSlicedLongProfile_integrable B U basis S x hR hB lower width O hO hw
    ha (half_pos hδ) hP haP hδP hprincipal hwδ hl hRP hRi modulus outputResidue hCmask hmask
  have hlong := allocatedSlicedLongJet_ideal_transfer B U basis hR hσ S x (fun _ => id)
    hMk selection hgood (by simp) (fun _ => Function.injective_id) hrows hσ1
    hP he hεcoef hMkP hRP hRi hσi hcount hεe hlarge modulus hperiod s hA hi u
    H step c hHpos hsubset hm residue hsize v₀ hv₀ _ hIi href

  exact allocatedSlicedPhysicalCovered_test_comparison_of_l1 B U basis hR hσ S x u v₀
    (fun _ => id) Q hb o bW d s hA hσ1 modulus hperiod F H step c hHpos hsubset
    hm residue hsize hv₀ _ hIi hlong hF hFbound

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
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
variable (u : PrincipalAxisTuples (α := Fin 1) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
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

include hR hσ hMk hi hP hMkP hRP hRi hσi hcount in
theorem allocatedSlicedOriginalLongJet_ideal_l1
    (step H : Tuple → ℕ) (c : Tuple → ℤ)
    (hstep : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
    {δ : ℝ} (hδ : 0 < δ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
    (hdense : ∀ j, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (modulus : ℕ) (hm : 0 < modulus) (residue : Tuple → Option (Fin 1) → ZMod modulus)
    (hsize : ∀ j, (Fintype.card (Fin 1) + 1) * modulus ≤ H j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant (Fin 1) * ((modulus : ℝ) / H j) <
      volume.real (scalarCubeDomain (Fin 1)))
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j, (step j : ℝ) / L j ≤ ε)
    (N O : ℕ) (hN : Fintype.card Endpoint ≤ N) (hO : Fintype.card Row ≤ O)
    (hB : ∀ a : {a // ¬grid a}, 4 ≤ Fintype.card (B a.val))
    (hx : ∀ g, IntegerScalarCube S.value (fun i => (x g i : ℤ)))
    (hu : ∀ j, IntegerScalarCube (principalAxisLength grid (allocatedPrincipalSides B U basis S) j)
      (fun i => (u j i : ℤ)))
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
      (fun j => by have := hH j; omega) hsubset modulus hm residue hsize).weight v₀ ≠ 0)
    {mesh Cmask : ℝ} (hmesh0 : 0 ≤ mesh) (hmesh1 : mesh ≤ 1)
    (hscaleMesh : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ mesh)
    (hCmask : 1 ≤ Cmask)
    (hmask : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U basis S x (fun _ => id) j
      modulus
      (integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u (fun _ => id) j v₀) modulus) z ∧ allocatedIntegerKernelMask B U basis S x (fun _ => id) j
      modulus
      (integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u (fun _ => id) j v₀) modulus) z ≤ Cmask) :
    let lower := fun (a : {a // ¬grid a}) (p : B a.val × Fin (degree a.val)) => (c ⟨a,p⟩ : ℝ) / L ⟨a,p⟩
    let width := fun (a : {a // ¬grid a}) (p : B a.val × Fin (degree a.val)) =>
      (step ⟨a,p⟩ : ℝ) * ((H ⟨a,p⟩ : ℝ) - 1) / L ⟨a,p⟩
    let ideal := allocatedSlicedPhysicalJetIdeal B U basis S hR hB lower width
    let law := containedProgressionResidueLaw activeB activeDegree L H step c positiveLengths
      (fun j => by have := hH j; omega) hsubset modulus hm residue hsize
    let outputResidue := fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u (fun _ => id) j v₀) modulus
    let radius := max (4 * Real.exp P) (Real.exp (allocatedJetSupportLog (G := G) B (Fin 1) jetRows P))
    let Ki : ℝ≥0 := (‖(∏ o : Output, R o.1.2.val.1)⁻¹‖₊ *
      (NNReal.mk (Real.exp (slicedJointDensityLogBudget O m P)) (Real.exp_nonneg _) *
        NNReal.mk (Real.exp P) (Real.exp_nonneg _))) * 2
    let select := allocatedLongIntegerSelect B U basis S (O := jetRows)
    (∫ z, |law.mean (fun v => allocatedLongJetDensity B U basis hR hσ S x u v (fun _ => id) s hA hσ1 z) -
      allocatedLongProfileDensity B U basis S x (fun _ => id) modulus outputResidue ideal z|
      ∂allocatedLongJetReference B U basis S jetRows) ≤
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
  have hHpos (j) : 0 < H j := by have := hH j; omega
  have hrows (j : Fin m) (t : Finset (Fin 1)) : t.card ≤ j.val + 1 :=
    (Finset.card_le_univ t).trans (by simp)
  have href := allocatedSlicedDiscreteIdeal_reference_l1 B U basis hR hσ S x u s hA hMk hi hP hMkP
    hRP hRi hσi hcount L step H (fun _ => modulus) c positiveLengths hstep hH hδ hsubset hdense
    (fun _ _ => modulus) residue (fun _ _ => hm) (fun _ _ => le_rfl) hsize hsmall hε hmesh
    N O hN hO hB hx hu ha hδone hη hprincipal A hTransition hσsmall haP hδP
    modulus outputResidue hmesh0 hmesh1 hscaleMesh hCmask hmask
  have hg (a) (p) := progression_slice_endpoint_geometry (c ⟨a,p⟩)
    (positiveLengths _) (hstep _) (hH _) hδ (hsubset _) (hdense _)
  have hw (a) (p) : |lower a p| + |width a p| ≤ 1 := (hg a p).2.2.1
  have hl (a) (p) : 0 ≤ lower a p := (hg a p).1
  have hwδ (a) (p) : δ / 2 ≤ width a p := (hg a p).2.1
  have hIi := allocatedSlicedLongProfile_integrable B U basis S x hR hB lower width O hO hw
    ha (half_pos hδ) hP haP hδP hprincipal hwδ hl hRP hRi modulus outputResidue hCmask hmask
  exact allocatedSlicedLongJet_ideal_transfer B U basis hR hσ S x (fun _ => id)
    hMk selection hgood (by simp) (fun _ => Function.injective_id) hrows hσ1
    hP he hεcoef hMkP hRP hRi hσi hcount hεe hlarge modulus hperiod s hA hi u
    H step c hHpos hsubset hm residue hsize v₀ hv₀ _ hIi href

end Erdos3.VectorPolynomial

end

end OAI
