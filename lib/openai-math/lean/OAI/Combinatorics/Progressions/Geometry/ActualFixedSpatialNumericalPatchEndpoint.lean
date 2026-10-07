import OAI.Combinatorics.Progressions.Dynamics.ActualSlicedNumericsRecoveredBudget
import OAI.Combinatorics.Progressions.Linear.ActualFixedSpatialScaledRetainedKernelBounds
import OAI.Combinatorics.Progressions.Linear.RecoveredKernelScalarBudget
import OAI.Combinatorics.Progressions.Sampling.ActualFixedSpatialSlicedRetainedKernelGridCap

namespace OAI

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

variable {A : Type} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  4 ≤ Fintype.card (B a.val))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

variable {d : ℕ} (e : Fin d ≃ Σ j, J j)

theorem relativePatchSliceConclusion_of_primitive_retained_forecast_score
    (hmpos : 0 < m)
    (hD : Fintype.card X + ∑ j : Fin m, (Fintype.card (Eout j) + n j) ≤ Dmod)
    (cutoff : ℕ) (hcutoff : 0 < cutoff) (hsmall : 2 / (cutoff : ℝ) ≤ 1 / 2)
    (κ : ℝ≥0)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j q, coefficients (poly j) q ∈ U j)
    (hN : ∀ i, 0 < physicalN i)
    {s r E rankBound : ℕ}
    (w : Fin r → ℕ) (hw : ∀ j, 1 ≤ w j) (hws : ∀ j, w j ≤ s) (hmono : Monotone w)
    (Pscalar : Fin r → MvPolynomial X ℝ)
    (hP : ∀ j, Pscalar j ∈ weightedSupportLE (fun _ : X => 1) (w j))
    (p : Fin d → ℕ)
    (Bpatch : WeightedParameterPatch (X ⊕ Fin d) (Sum.elim (fun _ => 1) p) s E)
    (χ : PatchKernel d) (M : Fin d → Fin r → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K)
    (hweight : ∀ i j, M i j ≠ 0 → w j ≤ p i)
    (hcoords : ∀ x : X → ℤ,
      fullTaggedBufferedCoordinates e poly (fun j => (slice.path.center j).val) x =
        realIntegerMatrix M (fun j => MvPolynomial.aeval (fun i => (x i : ℝ)) (Pscalar j)))
    (hcol : ∀ j a, (standardEuclideanPoint (J j)
      (fun i => M (e.symm ⟨j,i⟩) a)).val ∈ euclideanSubspace (U j))
    (hdiv : ∀ i a, (slice.path.referenceRetainedCRTModulus cutoff : ℤ) ∣ M i a)
    (D Icap : ℝ≥0)
    (hdensity : ∀ y, slice.density hB y ∈ Set.Icc (0 : ℝ) D)
    (hDlip : LipschitzWith D (slice.density hB))
    (hgrid : ∀ z : A → ℤ,
      (∏ a, (basisAxisScale (b (selected a).1) (selected a).2 : ℝ)) *
        slice.principalLaw.fiberMean
          (forecastInactiveFixedOutput B U b S selected
            (allocatedOriginalSampleInactiveCoefficients B selected slice.path.sample)
            slice.path.commonTuple)
          (fun a _ => z a) (fun _ => 1) ≤ Icap)
    (Cchart : Fin m → ℝ≥0)
    (hchart : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤
      Cchart j * ‖z‖)
    (Kchart : ℝ≥0) (hKchart : ∀ j, (R j)⁻¹ ≤ Kchart) (hτ : 0 < τ)
    (f : (X → ℤ) → ℝ) (hf : ∀ x ∈ integerBox physicalN, f x ∈ Set.Icc (0 : ℝ) 1)
    {lam δ ε score budget : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1) (hδ : δ ∈ Set.Icc (0 : ℝ) 1)
    (haccuracy : 4 / (cutoff : ℝ) ≤ δ) (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hdiscount : (1 + δ) * (1 - ε) ≤ 1 - δ)
    (hscore : score / 2 ≤ 𝔼 x : ↥(integerBox physicalN),
      (slice.targetAt selected hB o bW hb poly hm κ x.val).re *
        bufferedScalarScore χ
          (fullTaggedBufferedCoordinates e poly (fun j => (slice.path.center j).val))
          (fun u β => Bpatch.value (Sum.elim (fun i => (u i : ℝ)) (fun i => (β i : ℝ))))
          f lam x.val)
    (hbudget : 1 ≤ budget)
    (hr : (r : ℝ) ≤ budget) (hE : (E : ℝ) ≤ budget)
    (hn : (Fintype.card X : ℝ) ≤ budget)
    (hOut : (Fintype.card (Sigma (AllocatedCongruenceRankOutput X Eout
      (allocatedShortAxis (I := I) U b S.value))) : ℝ) ≤ budget)
    (hKbudget : (K : ℝ) ≤ Real.exp budget)
    (hχbudget : (χ.lip : ℝ) ≤ Real.exp budget)
    (hBbudget : (Bpatch.kernel.lip : ℝ) ≤ Real.exp budget)
    (hjoint : (κ : ℝ) * (D : ℝ) * (Icap : ℝ) ≤ Real.exp budget)
    (hqbudget : (slice.path.referenceRetainedCRTModulus cutoff : ℝ) ≤ Real.exp budget)
    (hchartBudget : ((Kchart * ∑ j, Cchart j * Fintype.card (J j) : ℝ≥0) : ℝ) ≤
      Real.exp budget)
    (hτBudget : 8 / τ ≤ Real.exp budget)
    (hscoreLower : Real.exp (-budget) ≤ score)
    (hlarge : ∀ i, Real.exp (spatialPatchExtractionCost (recoveredKernelScalarBudget budget)) ≤
      (physicalN i : ℝ))
    (hrank : r + E ≤ rankBound) :
    RelativePatchSliceConclusion s physicalN f ((1 - ε) * lam) rankBound
      (spatialPatchExtractionCost (recoveredKernelScalarBudget budget)) := by
  let q := slice.path.referenceRetainedCRTModulus cutoff
  let outDim := Fintype.card (Sigma (AllocatedCongruenceRankOutput X Eout
    (allocatedShortAxis (I := I) U b S.value)))
  let Rcap : ℝ≥0 := Icap * (q : ℝ≥0) ^ outDim
  let L := recoveredKernelScalarBudget budget
  let C : ℝ≥0 := ⟨Real.exp L, Real.exp_nonneg _⟩
  have hL := (recoveredKernelScalarBudget_ge hbudget).1
  have hbudgetL := (recoveredKernelScalarBudget_ge hbudget).2
  have hexp : Real.exp budget ≤ Real.exp L := Real.exp_le_exp.mpr hbudgetL
  have hC : 1 ≤ C := Real.one_le_exp_iff.mpr (le_trans zero_le_one hL)
  have hcap : ∀ residue β,
      |slice.retainedRecoveredRationalFactor selected bW hb e cutoff residue β| ≤ Rcap := by
    intro residue β
    simpa only [Rcap, q, outDim, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_natCast] using
      (slice.retainedRecoveredRationalFactor_abs_le_grid_modulus_pow selected bW hb e
        cutoff hgrid residue β)
  have hconstants := recoveredKernel_joint_constants_le_exp hbudget κ D D D Icap
    (Kchart * ∑ j, Cchart j * Fintype.card (J j)) ⟨8 / τ, by positivity⟩ q outDim
    le_rfl le_rfl hjoint hqbudget hOut hchartBudget hτBudget
  have hCcap : κ * (D * Rcap) ≤ C := hconstants.1
  have hCspace : κ * (Rcap * (D * ⟨8 / τ, by positivity⟩)) ≤ C := hconstants.2.1
  have hClift : κ * (Rcap * (D * (Kchart * ∑ j, Cchart j * Fintype.card (J j)))) ≤ C :=
    hconstants.2.2
  apply slice.relativePatchSliceConclusion_of_actual_retained_forecast_score
    selected hB o bW hb e hmpos hD cutoff hcutoff hsmall κ κ.coe_nonneg poly hm hN
    w hw hws hmono Pscalar hP p Bpatch χ M K hM hweight hcoords
    C C C hC ?_ ?_ ?_ ?_ f hf hlam hδ.1 haccuracy hε hdiscount hscore
    hL (hr.trans hbudgetL) (hE.trans hbudgetL) (hn.trans hbudgetL)
    (hKbudget.trans hexp) le_rfl le_rfl le_rfl (hχbudget.trans hexp) (hBbudget.trans hexp)
    (hqbudget.trans hexp)
    (recoveredKernelScalarBudget_discounted_score hbudget hscoreLower hδ.1 hδ.2) hlarge hrank
  · intro residue β y
    exact (slice.scaledRetainedRecoveredG_spatial_lipschitz selected hB o bW hb e cutoff κ
      hτ hDlip hcap residue β y).weaken hCspace
  · intro v residue β
    exact (slice.scaledRetainedRecoveredG_lift_lipschitz selected hB o bW hb e cutoff κ
      Cchart hchart Kchart hKchart hDlip hcap v residue β).weaken hClift
  · intro v residue β y
    have h := slice.scaledRetainedRecoveredG_mem_Icc selected hB o bW hb e cutoff κ
      hdensity hcap v residue β y
    exact ⟨h.1, h.2.trans hCcap⟩
  · exact slice.scaledRetainedRecoveredG_recovered_invariant selected hB o bW hb e cutoff κ
      M hcol hdiv

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

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

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {d : ℕ} (e : Fin d ≃ Σ j, J j)

theorem relativePatchSliceConclusion_of_numerical_retained_forecast_score
    (cutoff : ℕ) (hcutoff : 0 < cutoff) (hsmall : 2 / (cutoff : ℝ) ≤ 1 / 2)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j q, coefficients (poly j) q ∈ U j)
    {degree r E rankBound : ℕ}
    (w : Fin r → ℕ) (hw : ∀ j, 1 ≤ w j) (hws : ∀ j, w j ≤ degree) (hmono : Monotone w)
    (Pscalar : Fin r → MvPolynomial X ℝ)
    (hP : ∀ j, Pscalar j ∈ weightedSupportLE (fun _ : X => 1) (w j))
    (p : Fin d → ℕ)
    (Bpatch : WeightedParameterPatch (X ⊕ Fin d) (Sum.elim (fun _ => 1) p) degree E)
    (χ : PatchKernel d) (M : Fin d → Fin r → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K)
    (hweight : ∀ i j, M i j ≠ 0 → w j ≤ p i)
    (hcoords : ∀ x : X → ℤ,
      fullTaggedBufferedCoordinates e poly (fun j => (member.slice.path.center j).val) x =
        realIntegerMatrix M (fun j => MvPolynomial.aeval (fun i => (x i : ℝ)) (Pscalar j)))
    (hcol : ∀ j a, (standardEuclideanPoint (J j)
      (fun i => M (e.symm ⟨j,i⟩) a)).val ∈ euclideanSubspace (U j))
    (hdiv : ∀ i a, (member.slice.path.referenceRetainedCRTModulus cutoff : ℤ) ∣ M i a)
    (f : (X → ℤ) → ℝ) (hf : ∀ x ∈ integerBox physicalN, f x ∈ Set.Icc (0 : ℝ) 1)
    {lam δ ε score budget : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1) (hδ : δ ∈ Set.Icc (0 : ℝ) 1)
    (haccuracy : 4 / (cutoff : ℝ) ≤ δ) (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hdiscount : (1 + δ) * (1 - ε) ≤ 1 - δ)
    (hscore : score / 2 ≤ 𝔼 x : ↥(integerBox physicalN),
      (member.slice.targetAt selected s.hBactive o bW hb poly hm s.κ x.val).re *
        bufferedScalarScore χ
          (fullTaggedBufferedCoordinates e poly (fun j => (member.slice.path.center j).val))
          (fun u β => Bpatch.value (Sum.elim (fun i => (u i : ℝ)) (fun i => (β i : ℝ))))
          f lam x.val)
    (hbudget : 1 ≤ budget)
    (hr : (r : ℝ) ≤ budget) (hE : (E : ℝ) ≤ budget)
    (hDmodBudget : (Dmod : ℝ) ≤ budget)
    (hKbudget : (K : ℝ) ≤ Real.exp budget)
    (hχbudget : (χ.lip : ℝ) ≤ Real.exp budget)
    (hBbudget : (Bpatch.kernel.lip : ℝ) ≤ Real.exp budget)
    (hcapLog : qnum.capLog ≤ budget) (hPnative : qnum.Pnative ≤ budget)
    (hqbudget : (member.slice.path.referenceRetainedCRTModulus cutoff : ℝ) ≤ Real.exp budget)
    (hscoreLower : Real.exp (-budget) ≤ score)
    (hlarge : ∀ i, Real.exp (spatialPatchExtractionCost (recoveredKernelScalarBudget budget)) ≤
      (physicalN i : ℝ))
    (hrank : r + E ≤ rankBound) :
    RelativePatchSliceConclusion degree physicalN f ((1 - ε) * lam) rankBound
      (spatialPatchExtractionCost (recoveredKernelScalarBudget budget)) := by
  let D : ℝ≥0 := ⟨actualSlicedForecastDensityBudget s qnum.v, Real.exp_nonneg _⟩
  let Icap : ℝ≥0 := ⟨qnum.Ctail ^ Fintype.card A, pow_nonneg qnum.hCtail _⟩
  have hN (i : X) : 0 < physicalN i := Nat.cast_pos.mp
    ((Real.exp_pos (spatialPatchExtractionCost (recoveredKernelScalarBudget budget))).trans_le
      (hlarge i))
  have hXnat : Fintype.card X ≤ Dmod :=
    (Nat.le_add_right (Fintype.card X) _).trans s.hDmod
  have hX : (Fintype.card X : ℝ) ≤ budget := (Nat.cast_le.mpr hXnat).trans hDmodBudget
  have hOutNat : Fintype.card (Sigma (AllocatedCongruenceRankOutput X Eout
      (allocatedShortAxis (I := I) U b S.value))) ≤ Dmod := by
    rw [Fintype.card_sigma]
    exact (allocatedCongruenceRankOutput_sum_card_le (X := X) (E := Eout)
      s.hm (allocatedShortAxis (I := I) U b S.value)).trans s.hDmod
  have hOut : (Fintype.card (Sigma (AllocatedCongruenceRankOutput X Eout
      (allocatedShortAxis (I := I) U b S.value))) : ℝ) ≤ budget :=
    (Nat.cast_le.mpr hOutNat).trans hDmodBudget
  exact member.slice.relativePatchSliceConclusion_of_primitive_retained_forecast_score
    selected s.hBactive o bW hb e s.hm s.hDmod cutoff hcutoff hsmall ⟨s.κ, s.hκ⟩
    poly hm hN w hw hws hmono Pscalar hP p Bpatch χ M K hM hweight hcoords hcol hdiv
    D Icap (member.density_mem_Icc s qnum) (member.density_lipschitz_nnreal s qnum)
    (member.inactive_grid_mass_le s qnum) s.forward s.hforward s.K s.hK s.hτ f hf
    hlam hδ haccuracy hε hdiscount hscore hbudget hr hE hX hOut
    hKbudget hχbudget hBbudget
    ((qnum.joint_density_grid_cap_le_exp s).trans (Real.exp_le_exp.mpr hcapLog))
    hqbudget (qnum.hcoord.trans (Real.exp_le_exp.mpr hPnative))
    ((qnum.spatial_inverse_factor_le_exp s).trans (Real.exp_le_exp.mpr hPnative))
    hscoreLower hlarge hrank

end ActualFixedSpatialSlicedAdmissiblePath
end Erdos3.VectorPolynomial

end

end OAI
