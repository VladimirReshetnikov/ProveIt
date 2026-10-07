import OAI.Combinatorics.Progressions.Estimates.PreparedActualShearPatchEndpoint

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical NNReal Matrix

variable {X J₀ : Type} [Fintype X] [DecidableEq X]
variable {m : ℕ} (prep : RankPreparationFamily X J₀ m)
variable {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace ((fun j : Fin m => (prep j).space) j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B (fun j : Fin m => (prep j).space) b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) (fun j : Fin m => (prep j).space) b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice : ℝ}
variable {A : Type} [Fintype A] {selected : A → Σ j : Fin m, Fin (n j)}

variable (setup : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B (fun j : Fin m => (prep j).space) b S Dmod selected τ δslice)
variable (qnum : ActualFixedSpatialSlicedForecastNumerics setup)

namespace ActualFixedSpatialSlicedAdmissiblePath

variable (member : ActualFixedSpatialSlicedAdmissiblePath
  (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
  (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN) setup qnum)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace ((fun j : Fin m => (prep j).space) j)))
variable (bW : ∀ j, Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => (prep j).Coord) j)) (euclideanSubspace ((fun j : Fin m => (prep j).space) j))))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace ((fun j : Fin m => (prep j).space) j)))
variable {tagCount : ℕ} (e : Fin tagCount ≃ prep.PreparedCoordinate)

variable {Y : Type} {degree returned : ℕ}
    (patch : PolynomialPatch Y degree returned)
    (g : (polynomialShearFiltration patch.weight degree patch.weight_le).realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) (fun j => (prep j).Coord)))
    (c : ∀ j, (prep j).space)
    (hcenter : c = member.slice.path.center)
    (hmem : ∀ j α, coefficients (prep j).poly α ∈ (prep j).space)
    (χ : PatchKernel tagCount) (f : (X → ℤ) → ℝ) (lam : ℝ)

include hcenter in

theorem shear_forecast_mean_eq_prepared_buffered_mean :
    (𝔼 x : ↥(integerBox physicalN),
      (member.slice.target selected setup.hBactive o bW hb
        (fun j => (prep j).poly) hmem setup.κ x).re *
      bufferedScalarScore χ
        (fun x : ↥(integerBox physicalN) =>
          fullTaggedBufferedCoordinates e (fun j => (prep j).poly) (fun j => (c j).val) x.val)
        (fun x β => (patch.ofTaggedWeightedShearOrbit e g).value
          (Sum.elim (fun i => (x.val i : ℝ)) (fun i => (β i : ℝ))))
        (fun x : ↥(integerBox physicalN) => f x.val) lam x) =
    (𝔼 x : ↥(integerBox physicalN),
      (member.slice.targetAt selected setup.hBactive o bW hb
        (fun j => (prep j).poly) hmem setup.κ x.val).re *
      bufferedScalarScore χ
        (fullTaggedBufferedCoordinates e (fun j => (prep j).poly)
          (fun j => (member.slice.path.center j).val))
        (fun u β => (patch.ofTaggedWeightedShearOrbit e g).value
          (Sum.elim (fun i => (u i : ℝ)) (fun i => (β i : ℝ))))
        f lam x.val) := by
  subst c
  rfl

include hcenter in

theorem prepared_shear_buffered_score_of_actual_target {score : ℝ}
    (hscore : score / 2 ≤ 𝔼 x : ↥(integerBox physicalN),
      (member.slice.target selected setup.hBactive o bW hb
        (fun j => (prep j).poly) hmem setup.κ x).re *
      bufferedScalarScore χ
        (fullTaggedBufferedCoordinates e (fun j => (prep j).poly) (fun j => (c j).val))
        (fun u β => (patch.ofTaggedWeightedShearOrbit e g).value
          (Sum.elim (fun i => (u i : ℝ)) (fun i => (β i : ℝ)))) f lam x.val) :
    score / 2 ≤ 𝔼 x : ↥(integerBox physicalN),
      (member.slice.targetAt selected setup.hBactive o bW hb
        (fun j => (prep j).poly) hmem setup.κ x.val).re *
      bufferedScalarScore χ
        (fullTaggedBufferedCoordinates e (fun j => (prep j).poly)
          (fun j => (member.slice.path.center j).val))
        (fun u β => (patch.ofTaggedWeightedShearOrbit e g).value
          (Sum.elim (fun i => (u i : ℝ)) (fun i => (β i : ℝ)))) f lam x.val := by
  subst c
  exact hscore

include hcenter in

theorem prepared_shear_buffered_score_of_forecast
    {Pnative massLog capLog precision : ℝ}
    (data : ActualForecastData physicalN (fun j => (prep j).poly)
      Pnative massLog capLog precision)
    (htarget : data.target = member.slice.target selected setup.hBactive o bW hb
      (fun j => (prep j).poly) hmem setup.κ)
    {score : ℝ}
    (hscore : score / 2 ≤ 𝔼 x : ↥(integerBox physicalN),
      (data.target x).re *
      bufferedScalarScore χ
        (fun x : ↥(integerBox physicalN) =>
          fullTaggedBufferedCoordinates e (fun j => (prep j).poly) (fun j => (c j).val) x.val)
        (fun x β => (patch.ofTaggedWeightedShearOrbit e g).value
          (Sum.elim (fun i => (x.val i : ℝ)) (fun i => (β i : ℝ))))
        (fun x : ↥(integerBox physicalN) => f x.val) lam x) :
    score / 2 ≤ 𝔼 x : ↥(integerBox physicalN),
      (member.slice.targetAt selected setup.hBactive o bW hb
        (fun j => (prep j).poly) hmem setup.κ x.val).re *
      bufferedScalarScore χ
        (fullTaggedBufferedCoordinates e (fun j => (prep j).poly)
          (fun j => (member.slice.path.center j).val))
        (fun u β => (patch.ofTaggedWeightedShearOrbit e g).value
          (Sum.elim (fun i => (u i : ℝ)) (fun i => (β i : ℝ))))
        f lam x.val := by
  rw [htarget] at hscore
  exact hscore.trans_eq
    (member.shear_forecast_mean_eq_prepared_buffered_mean prep setup qnum o bW hb e
      patch g c hcenter hmem χ f lam)

omit [Fintype X] [DecidableEq X] in

theorem prepared_shear_returned_kernel_lip :
    (patch.ofTaggedWeightedShearOrbit e g).kernel.lip = patch.kernel.lip := rfl

end ActualFixedSpatialSlicedAdmissiblePath
end Erdos3.VectorPolynomial

end

end OAI
