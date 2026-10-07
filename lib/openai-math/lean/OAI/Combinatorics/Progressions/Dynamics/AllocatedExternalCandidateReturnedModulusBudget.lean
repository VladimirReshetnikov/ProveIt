import OAI.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateDenseSliceInput
import OAI.Combinatorics.Progressions.Estimates.RetainedPatchCutoffChoice
import OAI.Combinatorics.Progressions.Geometry.ActualFixedSpatialRetainedModulusBudget

namespace OAI

section

namespace Erdos3

theorem retainedPatchModulusLog_le_cubic {ε B Ptest Pbad Ppres : ℝ}
    (hε : 0 < ε) (hεone : ε ≤ 1) (hB : 1 ≤ B)
    (hinv : ε⁻¹ ≤ B) (htest : Ptest ∈ Set.Icc 0 B)
    (hbad : Pbad ∈ Set.Icc 0 B) (hpres : Ppres ∈ Set.Icc 0 B) :
    (4 * Ptest + 2) * (Pbad + Ppres +
      ((retainedPatchCutoff ε + 1 : ℕ) : ℝ) * Real.log (retainedPatchCutoff ε + 1)) ≤
      2048 * B ^ 3 := by
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hBsq : B ≤ B ^ 2 := by nlinarith only [hB]
  have hcut : (retainedPatchCutoff ε : ℝ) ≤ 17 * B := by
    apply (retainedPatchCutoffChoice_bounds hε hεone).2.2.2.2.2.2.trans
    simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 17)
  let x : ℝ := (retainedPatchCutoff ε : ℝ) + 1
  have hx1 : 1 ≤ x := le_add_of_nonneg_left (Nat.cast_nonneg _)
  have hx0 : 0 ≤ x := zero_le_one.trans hx1
  have hx : x ≤ 18 * B := by
    dsimp only [x]
    linarith only [hcut, hB]
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hlog : Real.log x ≤ 18 * B :=
    (Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hx1)).trans
      ((sub_le_self x zero_le_one).trans hx)
  have hprod : x * Real.log x ≤ 324 * B ^ 2 := by
    calc
      _ ≤ (18 * B) * (18 * B) := mul_le_mul hx hlog hlog0 (by positivity)
      _ = _ := by ring
  have hsum0 : 0 ≤ Pbad + Ppres + x * Real.log x :=
    add_nonneg (add_nonneg hbad.1 hpres.1) (mul_nonneg hx0 hlog0)
  have hsum : Pbad + Ppres + x * Real.log x ≤ 326 * B ^ 2 := by
    linarith only [hbad.2, hpres.2, hprod, hBsq]
  have hfac : 4 * Ptest + 2 ≤ 6 * B := by linarith only [htest.2, hB]
  simp only [Nat.cast_add, Nat.cast_one]
  change (4 * Ptest + 2) * (Pbad + Ppres + x * Real.log x) ≤ _
  calc
    _ ≤ (6 * B) * (326 * B ^ 2) := mul_le_mul hfac hsum hsum0 (by positivity)
    _ ≤ 2048 * B ^ 3 := by nlinarith only [pow_nonneg hB0 3]

end Erdos3

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
variable {Dmod Lrank : ℕ}
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

omit [Fintype Tsp] in

theorem referenceRetainedCRTModulus_le_exp_discount
    {ε budget Ptest : ℝ} (hε : 0 < ε) (hεone : ε ≤ 1)
    (hbudget : 1 ≤ budget) (hinv : ε⁻¹ ≤ budget)
    (htest : Ptest ∈ Set.Icc 0 budget)
    (hbad : Pbad ∈ Set.Icc 0 budget) (hpres : Ppres ∈ Set.Icc 0 budget)
    (hexponent : ∀ p : path.primes,
      path.exponent p.val ≤ Nat.log p.val ⌈Real.exp (2 * Ptest)⌉₊) :
    (path.referenceRetainedCRTModulus (retainedPatchCutoff ε) : ℝ) ≤
      Real.exp (2048 * budget ^ 3) :=
  (path.referenceRetainedCRTModulus_le_exp_tested (retainedPatchCutoff ε)
    htest.1 hexponent).trans (Real.exp_le_exp.mpr
      (retainedPatchModulusLog_le_cubic hε hεone hbudget hinv htest hbad hpres))

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical NNReal Matrix TensorProduct

variable {m : ℕ} {G X J₀ : Type} [Fintype G] [Fintype X]
variable (prep : RankPreparationFamily X J₀ m)
variable {preparationP : ℝ} {Rprep : ℕ}
variable (hprep : prep.PreparedHeights preparationP Rprep)
variable {I Eout : Fin m → Type} [∀ j, Fintype (I j)]
  [∀ j, Fintype (Eout j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace ((fun j : Fin m => (prep j).space) j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B (fun j : Fin m => (prep j).space) b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {Dmod Lrank : ℕ} {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) (fun j : Fin m => (prep j).space) b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp] {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)}
variable {N : X → ℕ} {τ ξ cost : ℝ}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B (fun j : Fin m => (prep j).space) b S Dmod (allocatedShortIntegerSelection (fun j : Fin m => (prep j).space) b S.value) τ (Real.exp (-cost) / 2))
variable (qnum : ActualFixedSpatialSlicedForecastNumerics s)
variable {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace ((fun j : Fin m => (prep j).space) j))}
variable {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace ((fun j : Fin m => (prep j).space) j))}
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice ((fun j : Fin m => (prep j).Coord) j))
  (euclideanSubspace ((fun j : Fin m => (prep j).space) j)))]
variable {stride : X → ℕ}
variable {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
variable {center : CoefficientTorus (K := LayerSamplerVariables G I n B) (fun j : Fin m => (prep j).space)}
variable {A : AllocatedExternalCandidateSampler B (fun j : Fin m => (prep j).space) b S hb o hR hσ N (fun j : Fin m => (prep j).poly) (fun j => (hprep j).2.1)
  τ ξ stride cells center}

namespace AllocatedExternalCandidateProblem.Conclusion
variable {Y M : Type} [LieRing M] [LieAlgebra ℚ M] {degree d t : ℕ}
variable (patch : PolynomialPatch Y degree d) [Fintype (PolynomialShearIndex patch.weight)]
variable {Fmark : NilpotentLieFiltration M t}
variable {φ : PolynomialShearLieAlgebra patch.weight ℚ →ₗ⁅ℚ⁆ M}
variable {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) (fun j : Fin m => (prep j).Coord))}
variable (f : (X → ℤ) → ℝ) (lam : ℝ)
variable {chartCost massThreshold scoreThreshold outputMass outputScore : ℝ}
variable {P : AllocatedExternalCandidateProblem (E := Eout) A
  (polynomialShearNilmanifold patch.weight degree patch.weight_le) Fmark φ marked
  (fun _ z => (patch.shearObservable z : ℂ)) (fun x => ((f x - lam : ℝ) : ℂ))
  chartCost massThreshold scoreThreshold}
variable (out : P.Conclusion cost outputMass outputScore)
variable {δbase PpresBase : ℝ}
variable (path : ∀ _z : out.retained, ActualFixedSpatialForecastPath (Eout := Eout)
  B (fun j : Fin m => (prep j).space) b S hR hσ Dmod spatial kernel block spatialEquiv
  (allocatedPhysicalRootBudget B (fun j : Fin m => (prep j).space) b S (fun _ => 0)) (S.value : ℝ) N τ δbase s.P s.Pbad PpresBase)
variable (hkeep : ∀ z : out.retained, ∀ k,
  (P.chart ⟨z.val, out.subset z.property⟩).keep k ↔ qnum.Hchild ≤ A.sides k)
variable (hkernel : Nonempty G) (hcutoff : qnum.Hchild ≤ S.value)
variable (hlate : 2 ≤ Real.exp (-cost) * (S.value : ℝ))
variable (hdensity : qnum.δ ≤ Real.exp (-cost)) (hlog : cost + 1 ≤ qnum.v)
variable (hprescribed : cost + 1 ≤ s.Ppres) (hstride : 2 * Real.exp cost ≤ qnum.Ptail)

local notation "input" z => out.denseSliceInput s qnum z (hkeep z) (ActualFixedSpatialForecastPath.commonTuple (path z))
  hkernel hcutoff hlate hdensity le_rfl hlog hprescribed hstride
local notation "member" z => ActualFixedSpatialForecastPath.toDenseSliceMember (path z) (input z)

omit [Fintype Tsp] in

theorem returned_modulus_le_exp_discount
    {ε budget Ptest : ℝ} (hε : 0 < ε) (hεone : ε ≤ 1)
    (hbudget : 1 ≤ budget) (hinv : ε⁻¹ ≤ budget)
    (htest : Ptest ∈ Set.Icc 0 budget)
    (hbad : s.Pbad ∈ Set.Icc 0 budget) (hpres : s.Ppres ∈ Set.Icc 0 budget)
    (hexponent : ∀ z, (path z).exponent = fun p => Nat.log p ⌈Real.exp (2 * Ptest)⌉₊)
    (z : out.retained) :
    ((member z).slice.path.referenceRetainedCRTModulus (retainedPatchCutoff ε) : ℝ) ≤
      Real.exp (2048 * budget ^ 3) := by
  apply (member z).slice.path.referenceRetainedCRTModulus_le_exp_discount
    hε hεone hbudget hinv htest hbad hpres
  intro p
  change (path z).exponent p.val ≤ Nat.log p.val ⌈Real.exp (2 * Ptest)⌉₊
  rw [hexponent z]

end AllocatedExternalCandidateProblem.Conclusion
end Erdos3.VectorPolynomial

end

end OAI
