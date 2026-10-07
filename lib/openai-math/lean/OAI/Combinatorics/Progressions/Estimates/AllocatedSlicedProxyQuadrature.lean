import OAI.Combinatorics.Progressions.Probability.AllocatedSlicedProxyLaw

namespace OAI

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

include hR hσ hMk hi hP hMkP hRP hRi hσi hcount in
theorem allocatedSlicedLongJetProxy_residue_error (hσ1 : ∀ j, σ j ≤ 1)
    (L step H M : Tuple → ℕ) (c : Tuple → ℤ)
    (hL : ∀ j, 0 < L j) (hstep : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
    {δ : ℝ} (hδ : 0 < δ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
    (hdense : ∀ j, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (modulus : Tuple → Option (Fin 1) → ℕ) (residue : ∀ j i, ZMod (modulus j i))
    (hm : ∀ j i, 0 < modulus j i) (hmM : ∀ j i, modulus j i ≤ M j)
    (hsize : ∀ j, (Fintype.card (Fin 1) + 1) * M j ≤ H j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant (Fin 1) * ((M j : ℝ) / H j) <
      volume.real (scalarCubeDomain (Fin 1)))
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j, (step j : ℝ) / L j ≤ ε) (z : Jet → ℝ) :
    |(FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights (Fin 1) (H j) (M j)
        (by have := hH j; omega) (modulus j) (residue j) (hm j) (hmM j) (hsize j))).mean
        (fun v => allocatedNormalizedLongJetDensity B U basis S x u (fun _ => id) s hA
          (principalTupleFlatten (fun a : {a // ¬grid a} => B a.val) (fun a => degree a.val) (Fin 1)
            (fun j i => ((if i = none then (c j : ℝ) else 0) + (step j : ℝ) * (v j i : ℝ)) / L j)) z) -
      allocatedSlicedLongJetProxy B U basis S x u s hA
        (fun a p => (c ⟨a,p⟩ : ℝ) / L ⟨a,p⟩)
        (fun a p => (step ⟨a,p⟩ : ℝ) * ((H ⟨a,p⟩ : ℝ) - 1) / L ⟨a,p⟩) z| ≤
      (2 * (cap : ℝ) * scalarCubeGridBoundaryConstant (Fin 1) / volume.real (scalarCubeDomain (Fin 1)) +
        (lip : ℝ) * 2) * ∑ j, (M j : ℝ) / H j + (lip : ℝ) * ε := by
  have hb := allocatedNormalizedLongJetDensity_parameter_bounds B U basis hR hσ S x
    (fun _ => id) s hA hMk hi hP hMkP hRP hRi hσi hcount u hσ1 z
  have hmeas := allocatedNormalizedLongJetDensity_measurable B U basis hR hσ S x u
    (fun _ => id) s hA hσ1
  have ht := hmeas.comp (measurable_id.prodMk (measurable_const (a := z)))
  exact oneCubePrincipalSlice_residue_riemann B degree grid L step H M c hL hstep hH hδ
    hsubset hdense modulus residue hm hmM hsize hsmall hε hmesh
    (fun y => allocatedNormalizedLongJetDensity B U basis S x u (fun _ => id) s hA y z)
    ht hb.2 (NNReal.coe_nonneg cap) (fun y _ => hb.1 y)

end Erdos3.VectorPolynomial

end

end OAI
