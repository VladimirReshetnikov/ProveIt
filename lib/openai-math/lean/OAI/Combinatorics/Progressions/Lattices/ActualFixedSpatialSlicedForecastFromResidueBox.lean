/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Linear.KernelPrincipalFiberSliceLaw
import OAI.Combinatorics.Progressions.Sampling.ActualFixedSpatialSlicedForecastSourceLaw

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod : ℕ} {Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice P Pbad Ppres : ℝ}

namespace ActualFixedSpatialForecastPath

variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

noncomputable def reparameterize
    (δslice' Ppres' : ℝ)
    (commonTuple : G → IntegerScalarCubeBox Empty S.value)
    (prescribed : ℕ → ℕ)
    (origin : ∀ p : path.primes, LayerSamplerLongVariables
      (allocatedShortAxis (I := I) U b S.value) G B → ZMod (p.val ^ path.exponent p.val))
    (hpres : ((∏ p : path.primes, p.val ^ prescribed p.val : ℕ) : ℝ) ≤ Real.exp Ppres')
    (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)
    (hwidth : ∀ a p, δslice' ≤ width a p)
    (hlower : ∀ a p, 0 ≤ lower a p)
    (hcontained : ∀ a p, |lower a p| + |width a p| ≤ 1) :
    ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
      Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice' P Pbad Ppres' where
  base := path.base
  noise := path.noise
  sample := path.sample
  hs := path.hs
  read := path.read
  readNoise := path.readNoise
  readProjection := path.readProjection
  center := path.center
  commonTuple := commonTuple
  primes := path.primes
  prime := path.prime
  exponent := path.exponent
  prescribed := prescribed
  origin := origin
  Rbad := path.Rbad
  hbad := path.hbad
  RbadBound := path.RbadBound
  presBound := hpres
  lower := lower
  width := width
  hwidth := hwidth
  hlower := hlower
  hcontained := hcontained
  detFalse := path.detFalse
  detTrue := path.detTrue
  hjac := path.hjac
  hinverse := path.hinverse

variable {keep : G ⊕ PrincipalTupleIndex B (layerSamplerDegree I n) → Prop} [DecidablePred keep]
variable {step : ℕ}
variable (box : ResidueBoxSlice
  (fun k : {k // keep k} => Sum.elim (fun _ : G => S.value)
    (allocatedPrincipalSides B U b S) k.val) step)
variable (hlen : ∀ k, 0 < box.length k)
variable (fixed : {k // ¬keep k} → ℤ)
variable (hfixed : ∀ k, 0 ≤ fixed k ∧ fixed k <
  ((Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S) k.val : ℕ) : ℤ))
variable (hkernel : ∀ g, keep (Sum.inl g))
variable (hactive : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  ∀ p : B a.val × Fin (layerSamplerDegree I n a.val), keep (Sum.inr ⟨a.val,p⟩))
variable (hstep : 0 < step)
variable (hkernelLength : ∀ g, 2 ≤ box.length ⟨Sum.inl g, hkernel g⟩)
variable (hprescribed : ∀ p, path.prescribed p = padicValNat p step)
variable (horigin : ∀ (p : path.primes) (v : LayerSamplerLongVariables
    (allocatedShortAxis (I := I) U b S.value) G B),
  path.origin p v = ((Sum.elim
    (fun g => (box.start ⟨Sum.inl g,hkernel g⟩ : ℤ))
    (fun a => box.fiberParameterStart fixed (Sum.inr ⟨a.1.val,a.2⟩)) v : ℤ) :
      ZMod (p.val ^ path.exponent p.val)))
variable (hlower : ∀ a p, path.lower a p =
  (box.fiberParameterStart fixed (Sum.inr ⟨a.val,p⟩) : ℝ) /
    allocatedPrincipalSides B U b S ⟨a.val,p⟩)
variable (hwidth : ∀ a p, path.width a p =
  (ResidueBoxSlice.fiberParameterStride (keep := keep) (q := step) (Sum.inr ⟨a.val,p⟩) : ℝ) *
    (box.fiberParameterLength (Sum.inr ⟨a.val,p⟩) - 1 : ℕ) /
      allocatedPrincipalSides B U b S ⟨a.val,p⟩)

noncomputable def withResidueBoxSlice :
    ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
      Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres where
  path := path
  step := step
  step_pos := hstep
  kernelLength g := box.length ⟨Sum.inl g, hkernel g⟩
  kernelStart g := box.start ⟨Sum.inl g, hkernel g⟩
  kernelLength_two := hkernelLength
  kernelInside g t := by
    constructor
    · positivity
    · exact_mod_cast box.inside ⟨Sum.inl g, hkernel g⟩ t.val t.isLt
  principalLength j := box.fiberParameterLength (Sum.inr j)
  principalStep j := ResidueBoxSlice.fiberParameterStride (keep := keep) (q := step) (Sum.inr j)
  principalStart j := box.fiberParameterStart fixed (Sum.inr j)
  principalLength_pos j := box.fiberParameterLength_pos hlen (Sum.inr j)
  principalInside := box.fiberPrincipalParameter_inside hlen fixed hfixed
  principalStep_active a p := by
    simp only [ResidueBoxSlice.fiberParameterStride, ite_eq_left (hactive a p)]
  prescribed_eq := hprescribed
  origin_eq := horigin
  lower_eq := hlower
  width_eq := hwidth

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial

end

end OAI
