import OAI.Combinatorics.Progressions.Geometry.ActualFixedSpatialDenseSliceCenter

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
variable {physicalN : X → ℕ} {τ δslice : ℝ}
variable {A : Type} [Fintype A] {selected : A → Σ j : Fin m, Fin (n j)}

variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)
variable (qnum : ActualFixedSpatialSlicedForecastNumerics s)

namespace ActualFixedSpatialSlicedAdmissiblePath

variable (member : ActualFixedSpatialSlicedAdmissiblePath
  (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
  (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN) s qnum)

omit [Fintype Tsp] in

theorem inactive_grid_mass_le (z : A → ℤ) :
    (∏ a, (basisAxisScale (b (selected a).1) (selected a).2 : ℝ)) *
      member.slice.principalLaw.fiberMean
        (forecastInactiveFixedOutput B U b S selected
          (allocatedOriginalSampleInactiveCoefficients B selected member.slice.path.sample)
          member.slice.path.commonTuple)
        (fun a _ => z a) (fun _ => 1) ≤ qnum.Ctail ^ Fintype.card A := by
  exact member.slice.inactive_grid_mass_le s qnum.δ qnum.Hchild qnum.hδ member.regular
    qnum.Ptail qnum.Ctail qnum.hPtail qnum.hprimitive member.stride qnum.hCtail qnum.htailactual z

end ActualFixedSpatialSlicedAdmissiblePath

namespace ActualFixedSpatialForecastPath

variable {δbase PpresBase : ℝ}
variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δbase s.P s.Pbad PpresBase)

omit [Fintype Tsp] in

theorem denseSlice_inactive_grid_mass_le (input : ActualFixedSpatialDenseSliceInput s qnum)
    (z : A → ℤ) :
    let slice := (path.toDenseSliceMember input).slice
    (∏ a, (basisAxisScale (b (selected a).1) (selected a).2 : ℝ)) *
      slice.principalLaw.fiberMean
        (forecastInactiveFixedOutput B U b S selected
          (allocatedOriginalSampleInactiveCoefficients B selected slice.path.sample)
          slice.path.commonTuple)
        (fun a _ => z a) (fun _ => 1) ≤ qnum.Ctail ^ Fintype.card A := by
  exact (path.toDenseSliceMember input).inactive_grid_mass_le s qnum z

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial

end

end OAI
