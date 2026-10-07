import OAI.Combinatorics.Progressions.Estimates.AllocatedFiniteCoefficientL1

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

theorem allocatedLongJet_residue_coefficient_l1 {M : ℕ} (hM : 0 < M)
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
    (p : FiniteProbabilityWeights (PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides))
    (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    (hr : ∀ v, p.weight v ≠ 0 → ∀ j,
      integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v) modulus = residue j)
 :
    let C := Real.exp (allocatedDensityLog (G := G) B α O P)
    let CM : ℝ := layerKernelIndexBound m M
    let T := Real.exp (allocatedJetSupportLog (G := G) B α O P)
    let normalized := fun v => principalTupleNormalized (principalAxisLength (fun a => ¬grid a) sides) v
    let proxy := fun z => p.mean (fun v => allocatedNormalizedLongJetDensity B U basis S x u rows s hA (normalized v) z)
    Integrable (allocatedLongProfileDensity B U basis S x rows modulus residue proxy)
      (allocatedLongJetReference B U basis S O) ∧
    (∫ z, |p.mean (fun v => allocatedLongJetDensity B U basis hR hσ S x u v rows s hA hσ1 z) -
        allocatedLongProfileDensity B U basis S x rows modulus residue proxy z|
      ∂allocatedLongJetReference B U basis S O) ≤
      (2*T+1)^Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) *
        (Fintype.card {a // ¬grid a} * ε * (1 + CM * C + ε)^Fintype.card {a // ¬grid a}) := by
  intro C CM T normalized proxy
  have hid (v) (z : AllocatedLongJetRows B U basis S O) :
      allocatedNormalizedLongJetDensity B U basis S x u rows s hA
        (normalized v) (allocatedLongJetRealCoordinates B U basis S z) =
      ∏ a, allocatedLongJetTarget B U basis S x u rows s hA (normalized v) a (z a) := by
    exact Finset.prod_congr rfl (fun a _ =>
      (allocatedLongJetTarget_normalized B U basis S x u rows s hA (normalized v) z a).symm)
  have he (z) := allocatedLongJet_residue_coefficient_comparison B U basis hR hσ S x rows
    hM selection hx hq hinj hrows hσ1 hP he hε hMP hRP hRi hσi hcount hεe hlarge
    modulus hperiod s hA hi u p residue hr z
  change ∀ z, |_ - _ * p.mean (fun v => allocatedNormalizedLongJetDensity B U basis S x u rows s hA
    (normalized v) (allocatedLongJetRealCoordinates B U basis S z))| ≤
      Fintype.card {a // ¬grid a} * ε * (1 + CM * C + ε)^Fintype.card {a // ¬grid a} at he
  simp_rw [hid] at he
  have hε0 : 0 ≤ Fintype.card {a // ¬grid a} * ε *
      (1 + CM * C + ε)^Fintype.card {a // ¬grid a} := by
    dsimp [CM,C]
    positivity
  have hh := allocatedFiniteLongJet_l1_comparison B U basis hR hσ S x u rows s hA
    hM hi hP hMP hRP hRi hσi hcount hσ1 p modulus residue hε0 he
  have hprofile : allocatedLongProfileDensity B U basis S x rows modulus residue proxy =
      fun z => (∏ a, allocatedLongJetMask B U basis S x rows modulus residue a (z a)) *
        p.mean (fun v => ∏ a, allocatedLongJetTarget B U basis S x u rows s hA (normalized v) a (z a)) /
        (∏ a, allocatedLongJetOutputScale B U basis S (O := O) a) := by
    funext z
    dsimp only [allocatedLongProfileDensity, proxy]
    simp_rw [hid]
  rw [hprofile]
  exact hh

end Erdos3.VectorPolynomial

end

end OAI
