import OAI.Combinatorics.Progressions.Dynamics.AllocatedRefinedLengthBudget
import OAI.Combinatorics.Progressions.Estimates.AllocatedCoveredFixedTest
import OAI.Combinatorics.Progressions.Geometry.AllocatedAmbientLongBox
import OAI.Combinatorics.Progressions.Lattices.AllocatedSupportedSlicedResidue
import OAI.Combinatorics.Progressions.Linear.AllocatedRefinedKernelComparison
import OAI.Combinatorics.Progressions.Probability.FiniteBoxDensityComparison
import OAI.Combinatorics.Progressions.Probability.RetainedDensityNestedTest

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
variable [∀ j : Fin m, DecidableEq (AllocatedNonkernelCoefficient (G := G) B j)]
variable (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "lengths" => principalAxisLength (fun a => ¬grid a) sides

theorem allocatedFixedKernel_refined_principal_comparison {M : ℕ} (hM : 0 < M)
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
    (refined : ℕ) (hRefined : 0 < refined)
    (u : PrincipalAxisTuples (α := α) grid sides)
    (r : PrincipalTupleIndex (fun a : {a // ¬grid a} => B a.val)
      (fun a => layerSamplerDegree I n a.val) → Option α → ZMod refined)
    (hsize : ∀ d, (Fintype.card α+1)*refined ≤ lengths d)
    (hsmall : ∀ d, scalarCubeGridBoundaryConstant α * ((refined : ℝ)/lengths d) <
      volume.real (scalarCubeDomain α))
    (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    (hr : ∀ v, (allocatedLongResidueWeights B U basis S refined hRefined r hsize).weight v ≠ 0 → ∀ j,
      integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v) modulus = residue j) :
    let C : ℝ≥0 := ⟨Real.exp (allocatedDensityLog (G := G) B α O P), (Real.exp_pos _).le⟩
    let W : ℝ := layerKernelIndexBound m M
    ∀ z : AllocatedLongJetRows B U basis S O,
        |(allocatedLongResidueWeights B U basis S refined hRefined r hsize).mean
            (fun v => (∏ a, allocatedLongJetOutputScale B U basis S (O := O) a) *
              allocatedLongJetDensity B U basis hR hσ S x u v rows s hA hσ1 z) -
          (∏ a, allocatedLongJetMask B U basis S x rows modulus residue a (z a)) *
            (∫ y, (∏ a, allocatedLongJetTarget B U basis S x u rows s hA y a (z a))
              ∂jointBooleanSource (fun a : {a // ¬grid a} => layerSamplerDegree I n a.val))| ≤
          Fintype.card {a // ¬grid a} * ε * (1+W*C+ε)^Fintype.card {a // ¬grid a} +
            W^Fintype.card {a // ¬grid a} * jointTupleQuadratureError (α := α)
              (fun a : {a // ¬grid a} => B a.val) (fun a : {a // ¬grid a} => layerSamplerDegree I n a.val)
              (Fintype.card {a // ¬grid a}) C C lengths refined := by
  dsimp only
  have herror := allocatedFixedKernel_replacement B U basis hR hσ S x rows
    hM selection hx hq hinj hrows hσ1 hP he hε hMP hRP hRi hσi hcount hεe hlarge
    modulus hperiod s hA hi u (allocatedLongResidueWeights B U basis S refined hRefined r hsize) residue hr
  obtain ⟨hC, hcap, hLip⟩ := allocatedLongJetTarget_exp_bounds B U basis hR hσ S x rows s hA
    hM hi hP hMP hRP hRi hσi hcount u hσ1
  have hW : (1 : ℝ) ≤ layerKernelIndexBound m M := by
    exact_mod_cast Nat.succ_le_of_lt (show 0 < layerKernelIndexBound m M from pow_pos hM _)
  intro z
  exact allocatedLongJet_refined_principal_comparison B U basis hR hσ S refined hRefined r hsize x u rows s hA hσ1
    modulus residue hsmall _ _ hC hW hε.le hcap hLip
    (fun j i hj => (herror j i hj).1) (fun v hv j i hj z => (herror j i hj).2 v hv z) z

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix

theorem measurable_dependent_row_product {A Y : Type*} [Fintype A] [MeasurableSpace Y]
    {Z : A → Type*} [∀ a, MeasurableSpace (Z a)] (F : Y → ∀ a, Z a → ℝ)
    (hF : ∀ a, Measurable (fun p : Y × Z a => F p.1 a p.2)) :
    Measurable (fun p : Y × (∀ a, Z a) => ∏ a, F p.1 a (p.2 a)) := by
  classical
  exact Finset.measurable_prod _ (fun a _ =>
    (hF a).comp (measurable_fst.prodMk ((measurable_pi_apply a).comp measurable_snd)))

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S

include hR hσ in
theorem allocatedLongJetTarget_row_measurable (hσ1 : ∀ j, σ j ≤ 1) (a : {a // ¬grid a}) :
    Measurable (fun p :
      (PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a) → ℝ) ×
        CoefficientJetAxisRow O a.val =>
      allocatedLongJetTarget B U basis S x u rows s hA p.1 a p.2) := by
  rcases a with ⟨⟨j, a⟩, ha⟩
  cases a with
  | inl i =>
    change Measurable (Function.uncurry
      (allocatedContinuousKernelDensity B U basis S j i x u (rows j) (s j) (hA j)))
    exact allocatedContinuousKernelDensity_measurable B U basis hR hσ S j i x u (rows j) (s j) (hA j) (hσ1 j)
  | inr i =>
    change Measurable ((Function.uncurry
      (allocatedIntegerKernelDensity B U basis S j i x u (rows j) (s j) (hA j))) ∘
        (fun p : (PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
          (α := α) (fun a => ¬grid a) → ℝ) × (O j → ℤ) =>
          (p.1, fun o => (p.2 o : ℝ)/(basisAxisScale (basis j) i : ℝ))))
    have hn : Measurable (fun z : O j → ℤ => fun o => (z o : ℝ)/(basisAxisScale (basis j) i : ℝ)) :=
      measurable_of_countable _
    apply (allocatedIntegerKernelDensity_measurable B U basis hR hσ S j i x u (rows j) (s j) (hA j) (hσ1 j)).comp
    exact measurable_fst.prodMk (hn.comp measurable_snd)

variable (modulus : ℕ)
variable (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))

noncomputable def allocatedLongJetProxy (z : AllocatedLongJetRows B U basis S O) : ℝ :=
  (∏ a, allocatedLongJetMask B U basis S x rows modulus residue a (z a)) *
    ∫ y, (∏ a, allocatedLongJetTarget B U basis S x u rows s hA y a (z a))
      ∂jointBooleanSource (fun a : {a // ¬grid a} => layerSamplerDegree I n a.val)

include hR hσ in
theorem allocatedLongJetProxy_measurable (hσ1 : ∀ j, σ j ≤ 1) :
    Measurable (allocatedLongJetProxy B U basis S x u rows s hA modulus residue) := by
  have hm (a : {a // ¬grid a}) : Measurable (allocatedLongJetMask B U basis S x rows modulus residue a) := by
    rcases a with ⟨⟨j, a⟩, ha⟩
    cases a with
    | inl i => exact measurable_const
    | inr i =>
      change Measurable (allocatedIntegerKernelMask B U basis S x rows j modulus (residue j))
      exact measurable_of_countable _
  have hj : Measurable (fun p :
      (PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a) → ℝ) ×
        AllocatedLongJetRows B U basis S O =>
      ∏ a, allocatedLongJetTarget B U basis S x u rows s hA p.1 a (p.2 a)) :=
    measurable_dependent_row_product (allocatedLongJetTarget B U basis S x u rows s hA)
      (allocatedLongJetTarget_row_measurable B U basis hR hσ S x u rows s hA hσ1)
  exact (Finset.measurable_prod _ (fun a _ => (hm a).comp (measurable_pi_apply a))).mul
    hj.stronglyMeasurable.integral_prod_left'.measurable

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "activeInput" => PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a)
local notation "realOutput" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))

noncomputable def allocatedLongJetRealCoordinates (z : AllocatedLongJetRows B U basis S O) :
    realOutput → ℝ
  | ⟨⟨⟨j, .inl i⟩, ha⟩, o⟩ => z ⟨⟨j, .inl i⟩, ha⟩ o
  | ⟨⟨⟨j, .inr i⟩, ha⟩, o⟩ => (z ⟨⟨j, .inr i⟩, ha⟩ o : ℝ) / (basisAxisScale (basis j) i : ℝ)

theorem allocatedLongJetTarget_normalized (y : activeInput → ℝ)
    (z : AllocatedLongJetRows B U basis S O) (a : {a // ¬grid a}) :
    allocatedLongJetTarget B U basis S x u rows s hA y a (z a) =
      allocatedNormalizedLongJetFactor B U basis S x u rows s hA y a
        (fun o => allocatedLongJetRealCoordinates B U basis S z ⟨a, o⟩) := by
  rcases a with ⟨⟨j, a⟩, ha⟩
  cases a <;> rfl

theorem allocatedLongJetProxy_continuous (modulus : ℕ)
    (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    (z : AllocatedLongJetRows B U basis S O) :
    allocatedLongJetProxy B U basis S x u rows s hA modulus residue z =
      (∏ a, allocatedLongJetMask B U basis S x rows modulus residue a (z a)) *
        allocatedContinuousLongJetProxy B U basis S x u rows s hA
          (allocatedLongJetRealCoordinates B U basis S z) := by
  unfold allocatedLongJetProxy allocatedContinuousLongJetProxy densityMixture
  congr 1
  apply integral_congr_ae
  filter_upwards [] with y
  change (∏ a, allocatedLongJetTarget B U basis S x u rows s hA y a (z a)) =
    ∏ a, allocatedNormalizedLongJetFactor B U basis S x u rows s hA y a
      (fun o => allocatedLongJetRealCoordinates B U basis S z ⟨a, o⟩)
  exact Finset.prod_congr rfl (fun a _ => allocatedLongJetTarget_normalized B U basis S x u rows s hA y z a)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
variable {M : ℕ} (hM : 0 < M)
variable (hi : ∀ j : Fin m,
  fixedKernelInverseBound S.positive x (j.val+1) (rows j) (s j) (hA j) (1/(M : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMP : (M : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m,
  (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+1 ≤ Real.exp P)
variable (hσ1 : ∀ j, σ j ≤ 1)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "T" => Real.exp (allocatedJetSupportLog (G := G) B α O P)
local notation "Q" => ∏ a, allocatedLongJetOutputScale B U basis S (O := O) a
local notation "V" => (2*T+1)^Fintype.card (Σ a : LayerSamplerAxis I n, O (Sigma.fst a))
local notation "reference" => allocatedLongJetReference B U basis S O

variable (w : FiniteProbabilityWeights (PrincipalAxisTuples (α := α)
  (fun a => ¬allocatedGridAxis (I := I) U basis S.value a) (allocatedPrincipalSides B U basis S)))
variable (modulus : ℕ)
variable (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))

local notation "density" => (fun v => allocatedLongJetDensity B U basis hR hσ S x u v rows s hA hσ1)
local notation "proxy" => allocatedLongJetProxy B U basis S x u rows s hA modulus residue

include hM hi hP hMP hRP hRi hσi hcount

theorem allocatedLongJet_l1_comparison {ε : ℝ} (hε : 0 ≤ ε)
    (he : ∀ z, |w.mean (fun v => Q * density v z) - proxy z| ≤ ε) :
    Integrable (fun z => proxy z/Q) reference ∧
      (∫ z, |w.mean (fun v => density v z)-proxy z/Q| ∂reference) ≤ V*ε := by
  have hQ : 0 < Q := Finset.prod_pos (fun a _ => allocatedLongJetOutputScale_pos B U basis S a)
  have hf : Measurable (fun z => w.mean (fun v => density v z)) :=
    w.mean_measurable _ (fun v => allocatedLongJetDensity_measurable B U basis hR hσ S x u v rows s hA hσ1)
  have hfi : Integrable (fun z => w.mean (fun v => density v z)) reference :=
    integrable_finsetSum _ (fun v _ =>
      ((allocatedLongJetDensity_probability_data B U basis hR hσ S x u v rows s hA hσ1).2.1).const_mul (w.weight v))
  have hzero (z) (hz : z ∉ allocatedLongJetBox B U basis S O T) : w.mean (fun v => density v z) = 0 := by
    have hh : (fun v => density v z) = fun _ => 0 := by
      funext v
      exact allocatedLongJetDensity_zero_off_box B U basis S hR hσ x rows s hA hM hi hP hMP hRP hRi hσi hcount u hσ1 v z hz
    rw [hh, w.mean_const]
  have hgzero (z) (hz : z ∉ allocatedLongJetBox B U basis S O T) : proxy z = 0 := by
    unfold allocatedLongJetProxy
    rw [allocatedLongJetTarget_integral_zero_off_box B U basis S hR hσ x rows s hA
      hM hi hP hMP hRP hRi hσi hcount u hσ1 z hz, mul_zero]
  apply normalized_box_density_l1 reference (allocatedLongJetBox B U basis S O T)
    (allocatedLongJetBox_measurable B U basis S O T) (allocatedLongJetBox_measure_lt_top B U basis S O T)
    _ _ hf (allocatedLongJetProxy_measurable B U basis hR hσ S x u rows s hA modulus residue hσ1)
    hfi hzero hgzero hQ hε (allocatedLongJetBox_measure_bound B U basis S O (Real.exp_pos _).le)
  intro z
  have hscale : Q*w.mean (fun v => density v z) = w.mean (fun v => Q*density v z) := by
    unfold FiniteProbabilityWeights.mean
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [hscale]
  exact he z

theorem allocatedLongJet_test_comparison {ε : ℝ} (hε : 0 ≤ ε)
    (he : ∀ z, |w.mean (fun v => Q * density v z) - proxy z| ≤ ε)
    (φ : AllocatedLongJetRows B U basis S O → ℂ) (hφ : Measurable φ) (hb : ∀ z, ‖φ z‖ ≤ 1) :
    ‖(∫ c, w.complexMean (fun v => φ (allocatedLongJetMap B U basis S x u v rows c))
        ∂allocatedLongCoefficientSource B U basis hR hσ S) -
      ∫ z, ((proxy z/Q : ℝ) : ℂ)*φ z ∂reference‖ ≤ V*ε := by
  obtain ⟨hgi, herr⟩ := allocatedLongJet_l1_comparison B U basis hR hσ S x u rows s hA
    hM hi hP hMP hRP hRi hσi hcount hσ1 w modulus residue hε he
  have hfi : Integrable (fun z => w.mean (fun v => density v z)) reference :=
    integrable_finsetSum _ (fun v _ =>
      ((allocatedLongJetDensity_probability_data B U basis hR hσ S x u v rows s hA hσ1).2.1).const_mul (w.weight v))
  rw [allocatedLongJet_test_mean B U basis hR hσ S x u rows s hA hσ1 w φ hφ hb]
  have ht := density_bounded_complex_test_error reference _ _ hfi hgi φ hφ hb
  simpa only [one_mul] using ht.trans (mul_le_mul_of_nonneg_left herr zero_le_one)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S

omit [Fintype α] [∀ j, DecidableEq (O j)] in
theorem allocatedLongJetMask_eq_of_periods
    (u : PrincipalAxisTuples (α := α) grid sides)
    (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides)
    (M N : ℕ)
    (r : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod M))
    (s : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod N))
    (hM : ∀ j, integerScalarLattice (O j) (M : ℤ) ≤ (scalarKernelIntegerJet x (j.val+1) (rows j)).mulVecLin.range)
    (hN : ∀ j, integerScalarLattice (O j) (N : ℤ) ≤ (scalarKernelIntegerJet x (j.val+1) (rows j)).mulVecLin.range)
    (hr : ∀ j, integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u rows j v₀) M = r j)
    (hs : ∀ j, integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u rows j v₀) N = s j)
    (a : {a // ¬grid a}) (z : CoefficientJetAxisRow O a.val) :
    allocatedLongJetMask B U b S x rows M r a z = allocatedLongJetMask B U b S x rows N s a z := by
  rcases a with ⟨⟨j,a⟩,ha⟩
  cases a with
  | inl i => rfl
  | inr i =>
    exact coefficientResidueMultiplier_eq_of_periods
      (scalarKernelIntegerJet x (j.val+1) (rows j))
      (allocatedNonkernelJetMatrix B U b S x u rows j v₀) M N (r j) (s j)
      (hM j) (hN j) (hr j) (hs j) z

theorem allocatedLongJetProxy_eq_of_periods
    (u : PrincipalAxisTuples (α := α) grid sides)
    (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides)
    (pivot : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
    (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (pivot j)).det ≠ 0)
    (M N : ℕ)
    (r : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod M))
    (s : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod N))
    (hM : ∀ j, integerScalarLattice (O j) (M : ℤ) ≤ (scalarKernelIntegerJet x (j.val+1) (rows j)).mulVecLin.range)
    (hN : ∀ j, integerScalarLattice (O j) (N : ℤ) ≤ (scalarKernelIntegerJet x (j.val+1) (rows j)).mulVecLin.range)
    (hr : ∀ j, integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u rows j v₀) M = r j)
    (hs : ∀ j, integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u rows j v₀) N = s j) :
    allocatedLongJetProxy B U b S x u rows pivot hA M r =
      allocatedLongJetProxy B U b S x u rows pivot hA N s := by
  classical
  funext z
  unfold allocatedLongJetProxy
  congr 1
  exact Finset.prod_congr rfl (fun a _ => allocatedLongJetMask_eq_of_periods B U b S x rows
    u v₀ M N r s hM hN hr hs a (z a))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
variable [∀ j : Fin m, DecidableEq (AllocatedNonkernelCoefficient (G := G) B j)]
variable (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S
local notation "lengths" => principalAxisLength (fun a => ¬grid a) sides

theorem allocatedFixedKernel_refined_pointwise {M : ℕ} (hM : 0 < M)
    (selection : α ↪ G) (hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
    (hq : Fintype.card α ≤ m+1) (hinj : ∀ j, Function.Injective (rows j))
    (hrows : ∀ j o, (rows j o).card ≤ j.val+1) (hσ1 : ∀ j, σ j ≤ 1)
    {P E T η : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E) (hT : 0 ≤ T) (hη : 0 < η) (hη1 : η ≤ 1)
    (hMP : (M : ℝ) ≤ Real.exp P) (hRP : ∀ j, R j ≤ Real.exp P)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+1 ≤ Real.exp P)
    (hηE : η⁻¹ ≤ Real.exp E)
    (hlarge : Real.exp (allocatedRefinedJointLengthLog (G := G) B α O P E T) ≤ S.value)
    (modulus : ℕ)
    (hperiod : ∀ j, integerScalarLattice (O j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val+1) (rows j)).mulVecLin.range)
    (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
    (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
    (hi : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val+1) (rows j) (s j) (hA j) (1/(M : ℝ)))
    (refined : ℕ) (hRefined : 0 < refined) (hbound : (refined : ℝ) ≤ Real.exp T)
    (u : PrincipalAxisTuples (α := α) grid sides)
    (r : PrincipalTupleIndex (fun a : {a // ¬grid a} => B a.val)
      (fun a => layerSamplerDegree I n a.val) → Option α → ZMod refined)
    (hsize : ∀ d, (Fintype.card α+1)*refined ≤ lengths d)
    (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    (hr : ∀ v, (allocatedLongResidueWeights B U b S refined hRefined r hsize).weight v ≠ 0 → ∀ j,
      integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u rows j v) modulus = residue j) :
    ∀ z : AllocatedLongJetRows B U b S O,
      |(allocatedLongResidueWeights B U b S refined hRefined r hsize).mean
          (fun v => (∏ a, allocatedLongJetOutputScale B U b S (O := O) a) *
            allocatedLongJetDensity B U b hR hσ S x u v rows s hA hσ1 z) -
        allocatedLongJetProxy B U b S x u rows s hA modulus residue z| ≤ η := by
  obtain ⟨hcoefficient, htuple⟩ := allocatedRefinedJointLengthLog_spec (G := G) B α O
    hP hE hT hbound hMP hη hηE hlarge
  obtain ⟨hε, _, hεe⟩ := allocatedJointAccuracy_spec (G := G) B α O hP hMP hη hη1 hηE
  have he := allocatedJointAccuracyLog_nonneg (G := G) B α O hP hE
  obtain ⟨_, hsmall, herror⟩ :=
    allocatedRefinedJointTupleCutoff_spec B U b S O hP hM hη hη1 (le_refl refined) htuple
  have hcompare := allocatedFixedKernel_refined_principal_comparison B U b hR hσ S x rows
    hM selection hx hq hinj hrows hσ1 hP he hε hMP hRP hRi hσi hcount hεe hcoefficient
    modulus hperiod s hA hi refined hRefined u r hsize hsmall residue hr
  intro z
  exact (hcompare z).trans herror

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (hσ1 : ∀ j, σ j ≤ 1)
variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable (weights : FiniteProbabilityWeights (PrincipalAxisTuples (α := α)
  (fun a => ¬allocatedGridAxis (I := I) U b S.value a) (allocatedPrincipalSides B U b S)))
variable (period : ℕ) (hperiod : ∀ j, integerScalarLattice (O j) (period : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
variable (hresidue : ∀ v, weights.weight v ≠ 0 → principalResidueLabel period v = principalResidueLabel period v₀)
variable (F : AllocatedFrozenCoefficients B U b S × EuclideanJetLayers U O → ℂ)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "source" => allocatedCoefficientSource B U b hR hσ S
local notation "frozenSource" => allocatedFrozenCoefficientSource B U b hR hσ S
local notation "reference" => allocatedLongJetReference B U b S O
local notation "density" => (fun v z => allocatedLongJetDensity B U b hR hσ S x u v rows s hA hσ1 z)
local notation "root" v => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v)
local notation "dirs" v => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)
local notation "deck" => PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)
local notation "test" => allocatedCoveredFixedTest B U b S x u v₀ rows Q hb o bW d F
local notation "actual" => (∫ p, weights.complexMean (fun v => F (Prod.fst ((allocatedCoefficientSplit B U b S) (Prod.fst p)),
  euclideanCoefficientJetMap U (root v) (dirs v) rows
    (canonicalCoefficientDeckSample U bW b hb o d (Nat.pos_of_ne_zero (NeZero.ne d)) (Prod.fst p) (Prod.snd p))))
    ∂(Measure.prod source (PMF.toMeasure deck)))

include hperiod hresidue

omit [DecidableEq G] in
theorem allocatedPhysicalCovered_test_comparison_of_l1
    (g : AllocatedLongJetRows B U b S O → ℝ) (hg : Integrable g reference)
    {ε : ℝ} (he : (∫ z, |weights.mean (fun v => density v z) - g z| ∂reference) ≤ ε)
    (hF : Measurable F) (hbound : ∀ p, ‖F p‖ ≤ 1) :
    ‖actual - ∫ a₀, ∫ z, (g z : ℂ) * test a₀ z ∂reference ∂frozenSource‖ ≤ ε := by
  let : IsProbabilityMeasure frozenSource := allocatedFrozenCoefficientSource_probability B U b hR hσ S
  have hf : Integrable (fun z => weights.mean (fun v => density v z)) reference :=
    integrable_finsetSum _ (fun v _ =>
      ((allocatedLongJetDensity_probability_data B U b hR hσ S x u v rows s hA hσ1).2.1).const_mul
        (weights.weight v))
  rw [allocatedPhysicalCovered_test_mean B U b hR hσ S x u v₀ rows Q hb o bW d F
    s hA hσ1 weights period hperiod hresidue hF hbound]
  have h := retained_density_nested_test_error frozenSource reference _ g hf hg
    (fun p => test p.1 p.2)
    (allocatedCoveredFixedTest_measurable B U b S x u v₀ rows Q hb o bW d F hF)
    (fun p => allocatedCoveredFixedTest_norm_le B U b S x u v₀ rows Q hb o bW d F hbound p.1 p.2)
  exact le_trans h (by simpa only [one_mul] using he)

variable (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod period))

local notation "scale" => (∏ a, allocatedLongJetOutputScale B U b S (O := O) a)
local notation "proxy" => allocatedLongJetProxy B U b S x u rows s hA period residue

theorem allocatedPhysicalCovered_test_comparison
    {M : ℕ} (hM : 0 < M)
    (hi : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val + 1) (rows j) (s j) (hA j) (1 / (M : ℝ)))
    {P : ℝ} (hP : 0 ≤ P) (hMP : (M : ℝ) ≤ Real.exp P)
    (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
    (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ)
      + 1 ≤ Real.exp P)
    {ε : ℝ} (hε : 0 ≤ ε) (he : ∀ z, |weights.mean (fun v => scale * density v z) - proxy z| ≤ ε)
    (hF : Measurable F) (hbound : ∀ p, ‖F p‖ ≤ 1) :
    ‖actual - ∫ a₀, ∫ z, ((proxy z / scale : ℝ) : ℂ) * test a₀ z ∂reference ∂frozenSource‖ ≤
      (2 * Real.exp (allocatedJetSupportLog (G := G) B α O P) + 1) ^
        Fintype.card (Σ a : LayerSamplerAxis I n, O (Sigma.fst a)) * ε := by
  obtain ⟨hg, hl1⟩ := allocatedLongJet_l1_comparison B U b hR hσ S x u rows s hA
    hM hi hP hMP hRP hRi hσi hcount hσ1 weights period residue hε he
  exact allocatedPhysicalCovered_test_comparison_of_l1 B U b hR hσ S x u v₀ rows Q hb o bW d
    s hA hσ1 weights period hperiod hresidue F (fun z => proxy z / scale) hg hl1 hF hbound

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (hσ1 : ∀ j, σ j ≤ 1)
variable [∀ a, DecidableEq (B a)]
variable (period : ℕ) (hperiod : ∀ j, integerScalarLattice (O j) (period : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
variable (F : AllocatedFrozenCoefficients B U b S × EuclideanJetLayers U O → ℂ)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "activeB" => (fun a : {a // ¬grid a} => B (Subtype.val a))
local notation "activeDegree" => (fun a : {a // ¬grid a} => layerSamplerDegree I n (Subtype.val a))
local notation "lengths" => principalAxisLength (fun a => ¬grid a) (allocatedPrincipalSides B U b S)
local notation "tupleIndex" => PrincipalTupleIndex activeB activeDegree
local notation "positiveLengths" => (fun j : tupleIndex => allocatedPrincipalSides_pos B U b S
  (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j)))

local notation "source" => allocatedCoefficientSource B U b hR hσ S
local notation "frozenSource" => allocatedFrozenCoefficientSource B U b hR hσ S
local notation "reference" => allocatedLongJetReference B U b S O
local notation "density" => (fun v z => allocatedLongJetDensity B U b hR hσ S x u v rows s hA hσ1 z)
local notation "root" v => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v)
local notation "dirs" v => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)
local notation "deck" => PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)
local notation "test" => allocatedCoveredFixedTest B U b S x u v₀ rows Q hb o bW d F
local notation "actual" weights:max => (∫ p, FiniteProbabilityWeights.complexMean weights (fun v => F (Prod.fst ((allocatedCoefficientSplit B U b S) (Prod.fst p)),
  euclideanCoefficientJetMap U (root v) (dirs v) rows
    (canonicalCoefficientDeckSample U bW b hb o d (Nat.pos_of_ne_zero (NeZero.ne d)) (Prod.fst p) (Prod.snd p))))
    ∂(Measure.prod source (PMF.toMeasure deck)))

include hperiod in
theorem allocatedSlicedPhysicalCovered_test_comparison_of_l1 [DecidableEq G]
    (H step : tupleIndex → ℕ) (c : tupleIndex → ℤ) (hH : ∀ j, 0 < H j)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (lengths j : ℤ))
    (hp : 0 < period) (r : tupleIndex → Option α → ZMod period)
    (hsize : ∀ j, (Fintype.card α + 1) * period ≤ H j)
    (hv₀ : (containedProgressionResidueLaw activeB activeDegree lengths H step c positiveLengths hH
      hsubset period hp r hsize).weight v₀ ≠ 0)
    (g : AllocatedLongJetRows B U b S O → ℝ) (hg : Integrable g reference)
    {ε : ℝ} (he : (∫ z, |(containedProgressionResidueLaw activeB activeDegree lengths H step c positiveLengths hH
      hsubset period hp r hsize).mean (fun v => density v z) - g z| ∂reference) ≤ ε)
    (hF : Measurable F) (hbound : ∀ p, ‖F p‖ ≤ 1) :
    ‖actual (containedProgressionResidueLaw activeB activeDegree lengths H step c positiveLengths hH
      hsubset period hp r hsize) - ∫ a₀, ∫ z, (g z : ℂ) * test a₀ z ∂reference ∂frozenSource‖ ≤ ε := by
  let weights := containedProgressionResidueLaw activeB activeDegree lengths H step c positiveLengths hH
    hsubset period hp r hsize
  have hr (v) (hv : weights.weight v ≠ 0) :
      principalResidueLabel period v = principalResidueLabel period v₀ :=
    containedProgressionResidueLaw_label_eq activeB activeDegree lengths H step c positiveLengths hH
      hsubset period hp r hsize v v₀ hv hv₀
  exact allocatedPhysicalCovered_test_comparison_of_l1 B U b hR hσ S x u v₀ rows Q hb o bW d
    s hA hσ1 weights period hperiod hr F g hg he hF hbound

end Erdos3.VectorPolynomial

end

end OAI
