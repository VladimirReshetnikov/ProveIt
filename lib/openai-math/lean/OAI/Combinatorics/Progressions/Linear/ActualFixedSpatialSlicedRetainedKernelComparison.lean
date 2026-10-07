import OAI.Combinatorics.Progressions.Geometry.ActualFixedSpatialRetainedModulusBudget
import OAI.Combinatorics.Progressions.Geometry.AllocatedExternalCandidateBufferedCoordinates
import OAI.Combinatorics.Progressions.Probability.ActualFixedSpatialSlicedNumericalDensity
import OAI.Combinatorics.Progressions.Sampling.ForecastLawCenteredRecoveredKernel

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

noncomputable def recoveredG
    (v : X → ℝ) (r : X → ZMod slice.path.referenceModulus)
    (β : Fin d → ℤ) (y : Fin d → ℝ) : ℝ := by
  letI : NeZero slice.path.referenceModulus := ⟨slice.path.referenceModulus_pos.ne'⟩
  exact forecastLawRecoveredKernel B U b S slice.principalLaw
    (slice.density hB) selected slice.path.sample slice.path.commonTuple
    (fun _ => slice.path.referenceInputLaw)
    (fun z t j => integerLongPolynomialOutput slice.path.referencePolynomial
      (fun k => (z k.1 k.2 : ℤ)) slice.path.referenceModulus t j)
    slice.path.referenceModulus (∏ a, (basisAxisScale (b (selected a).1) (selected a).2 : ℝ))
    slice.path.base physicalN τ o hb bW v r
    (fun a => β (e.symm a)) (fun a => y (e.symm a))

theorem rawTarget_eq_recoveredG (κ : ℝ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j q, coefficients (poly j) q ∈ U j) (u : X → ℤ)
    (β : Fin d → ℤ) (y : Fin d → ℝ)
    (hpoint : ∀ j i, y (e.symm ⟨j,i⟩) + (β (e.symm ⟨j,i⟩) : ℝ) =
      eval (fun a => (u a : ℝ)) (poly j) i)
    (hquarter : ∀ i, |y i| ≤ 1 / 4) :
    slice.rawTarget selected hB o bW hb κ poly hm u =
      (κ : ℂ) * (slice.recoveredG selected hB o bW hb e
        (fun i => (u i : ℝ) / physicalN i)
        (fun i => (u i : ZMod slice.path.referenceModulus)) β y : ℂ) := by
  let : NeZero slice.path.referenceModulus := ⟨slice.path.referenceModulus_pos.ne'⟩
  apply congrArg (fun z : ℂ => (κ : ℂ) * z)
  exact forecastLawDensityPhysicalTarget_eq_recoveredKernel B U b S slice.principalLaw
    (slice.density hB) selected slice.path.sample slice.path.commonTuple
    (fun _ => slice.path.referenceInputLaw)
    (fun z t j => integerLongPolynomialOutput slice.path.referencePolynomial
      (fun k => (z k.1 k.2 : ℤ)) slice.path.referenceModulus t j)
    slice.path.referenceModulus (∏ a, (basisAxisScale (b (selected a).1) (selected a).2 : ℝ))
    slice.path.base physicalN τ o hb bW poly hm u
    (fun a => β (e.symm a)) (fun a => y (e.symm a)) hpoint
    (fun a => hquarter (e.symm a))

theorem targetAt_eq_recoveredG
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j q, coefficients (poly j) q ∈ U j) (κ : ℝ) (u : X → ℤ)
    (β : Fin d → ℤ) (y : Fin d → ℝ)
    (hpoint : ∀ i, y i + (β i : ℝ) =
      fullTaggedBufferedCoordinates e poly (fun j => (slice.path.center j).val) u i)
    (hquarter : ∀ i, |y i| ≤ 1 / 4) :
    slice.targetAt selected hB o bW hb poly hm κ u =
      (κ : ℂ) * (slice.recoveredG selected hB o bW hb e
        (fun i => (u i : ℝ) / physicalN i)
        (fun i => (u i : ZMod slice.path.referenceModulus)) β y : ℂ) := by
  rw [slice.targetAt_eq_rawTarget selected hB o bW hb poly hm κ u]
  apply slice.rawTarget_eq_recoveredG selected hB o bW hb e κ
    (slice.path.physicalPolynomial poly) (slice.path.physicalPolynomial_mem poly hm) u β y
    ?_ hquarter
  intro j i
  have hp := hpoint (e.symm ⟨j, i⟩)
  simp only [fullTaggedBufferedCoordinates] at hp
  rw [e.apply_symm_apply] at hp
  simpa only [ActualFixedSpatialForecastPath.physicalPolynomial,
    eval_subtractConstant, Pi.sub_apply] using hp

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

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

local instance fullReferenceNonzero : NeZero slice.path.referenceModulus :=
  ⟨slice.path.referenceModulus_pos.ne'⟩
local instance retainedReferenceNonzero (cutoff : ℕ) :
    NeZero (slice.path.referenceRetainedCRTModulus cutoff) :=
  ⟨by rw [slice.path.referenceRetainedCRTModulus_eq];
      exact (slice.path.referenceRetainedModulus_pos cutoff).ne'⟩

noncomputable def retainedRecoveredG (cutoff : ℕ)
    (v : X → ℝ) (r : X → ZMod (slice.path.referenceRetainedCRTModulus cutoff))
    (β : Fin d → ℤ) (y : Fin d → ℝ) : ℝ :=
  forecastLawRecoveredKernel B U b S slice.principalLaw
    (slice.density hB) selected slice.path.sample slice.path.commonTuple
    (fun _ => slice.path.referenceRetainedCRTInputLaw cutoff)
    (fun z t j => integerLongPolynomialOutput slice.path.referencePolynomial
      (fun k => (z k.1 k.2 : ℤ)) (slice.path.referenceRetainedCRTModulus cutoff) t j)
    (slice.path.referenceRetainedCRTModulus cutoff)
    (∏ a, (basisAxisScale (b (selected a).1) (selected a).2 : ℝ))
    slice.path.base physicalN τ o hb bW v r
    (fun a => β (e.symm a)) (fun a => y (e.symm a))

omit [Fintype Tsp] in
theorem retainedForecastOutput_reduce (cutoff : ℕ)
    (r : X → ZMod slice.path.referenceModulus) (labels : ∀ j, Fin (n j) ⊕ Eout j → ℤ) :
    (fun out => ZMod.castHom (slice.path.referenceRetainedCRTModulus_dvd cutoff)
      (ZMod (slice.path.referenceRetainedCRTModulus cutoff))
      (forecastCongruenceOutput (allocatedShortAxis (I := I) U b S.value) r
        (fun j i => (labels j i : ZMod slice.path.referenceModulus)) out)) =
      forecastCongruenceOutput (allocatedShortAxis (I := I) U b S.value)
        (fun i => ZMod.castHom (slice.path.referenceRetainedCRTModulus_dvd cutoff)
          (ZMod (slice.path.referenceRetainedCRTModulus cutoff)) (r i))
        (fun j i => (labels j i : ZMod (slice.path.referenceRetainedCRTModulus cutoff))) := by
  funext out
  rcases out with ⟨j, x | i | a⟩ <;>
    simp only [forecastCongruenceOutput, map_intCast]

noncomputable def recoveredRationalFactor
    (r : X → ZMod slice.path.referenceModulus) (β : Fin d → ℤ) : ℝ :=
  forecastLawRecoveredRationalFactor B U b S slice.principalLaw selected
    slice.path.sample slice.path.commonTuple (fun _ => slice.path.referenceInputLaw)
    (fun z t j => integerLongPolynomialOutput slice.path.referencePolynomial
      (fun k => (z k.1 k.2 : ℤ)) slice.path.referenceModulus t j)
    slice.path.referenceModulus (∏ a, (basisAxisScale (b (selected a).1) (selected a).2 : ℝ))
    hb bW r (fun a => β (e.symm a))

noncomputable def retainedRecoveredRationalFactor (cutoff : ℕ)
    (r : X → ZMod (slice.path.referenceRetainedCRTModulus cutoff)) (β : Fin d → ℤ) : ℝ :=
  forecastLawRecoveredRationalFactor B U b S slice.principalLaw selected
    slice.path.sample slice.path.commonTuple (fun _ => slice.path.referenceRetainedCRTInputLaw cutoff)
    (fun z t j => integerLongPolynomialOutput slice.path.referencePolynomial
      (fun k => (z k.1 k.2 : ℤ)) (slice.path.referenceRetainedCRTModulus cutoff) t j)
    (slice.path.referenceRetainedCRTModulus cutoff)
    (∏ a, (basisAxisScale (b (selected a).1) (selected a).2 : ℝ)) hb bW r
    (fun a => β (e.symm a))

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

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

local instance retainedBoundsReferenceNonzero (cutoff : ℕ) :
    NeZero (slice.path.referenceRetainedCRTModulus cutoff) :=
  ⟨(slice.path.referenceRetainedCRTModulus_pos cutoff).ne'⟩

local notation "Out" => Sigma (AllocatedCongruenceRankOutput X Eout
  (allocatedShortAxis (I := I) U b S.value))

noncomputable def retainedRationalBudget (cutoff depth : ℕ) (Pgrid : ℝ) : ℝ :=
  let _ := slice
  Pgrid + (Fintype.card Out : ℝ) * ((depth : ℝ) *
    (Pbad + Ppres + ((cutoff + 1 : ℕ) : ℝ) * Real.log (cutoff + 1)))

noncomputable def retainedRationalCap (cutoff depth : ℕ) (Pgrid : ℝ) : ℝ≥0 :=
  ⟨Real.exp (slice.retainedRationalBudget cutoff depth Pgrid), Real.exp_nonneg _⟩

variable (cutoff : ℕ)
local notation "q" => slice.path.referenceRetainedCRTModulus cutoff
local notation "vol" => (∏ a, (basisAxisScale (b (Sigma.fst (selected a))) (Sigma.snd (selected a)) : ℝ))
local notation "grid" => forecastInactiveFixedOutput B U b S selected
  (allocatedOriginalSampleInactiveCoefficients B selected slice.path.sample) slice.path.commonTuple
local notation "Y" => (fun z t j => integerLongPolynomialOutput slice.path.referencePolynomial
  (fun k => (z (Prod.fst k) (Prod.snd k) : ℤ)) q t j)
local notation "rat" => forecastLawRecoveredRationalFactor B U b S slice.principalLaw selected
  slice.path.sample slice.path.commonTuple (fun _ => slice.path.referenceRetainedCRTInputLaw cutoff)
  Y q vol hb bW
local notation "centered" => forecastLawCenteredRecoveredKernel B U b S slice.principalLaw
  (slice.density hB) selected slice.path.sample slice.path.commonTuple
  (fun _ => slice.path.referenceRetainedCRTInputLaw cutoff) Y q vol
  slice.path.base physicalN τ o hb bW e (fun _ => 0)

omit [Fintype Tsp] in
theorem retainedRecoveredRationalFactor_nonneg
    (r : X → ZMod q) (β : Fin d → ℤ) :
    0 ≤ slice.retainedRecoveredRationalFactor selected bW hb e cutoff r β :=
  forecastLawRecoveredRationalFactor_nonneg B U b S slice.principalLaw selected
    slice.path.sample slice.path.commonTuple (fun _ => slice.path.referenceRetainedCRTInputLaw cutoff)
    Y q vol hb bW (Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _))
    r (fun a => β (e.symm a))

omit [Fintype Tsp] in
theorem retainedRecoveredRationalFactor_le_exp_of_modulus
    (Pgrid Pmod : ℝ)
    (hgrid : ∀ z : A → ℤ, vol * slice.principalLaw.fiberMean grid
      (fun a _ => z a) (fun _ => 1) ≤ Real.exp Pgrid)
    (hq : (q : ℝ) ≤ Real.exp Pmod)
    (r : X → ZMod q) (β : Fin d → ℤ) :
    slice.retainedRecoveredRationalFactor selected bW hb e cutoff r β ≤
      Real.exp (Pgrid + (Fintype.card Out : ℝ) * Pmod) :=
  forecastLawRecoveredRationalFactor_le_exp_of_grid_modulus B U b S slice.principalLaw
    selected slice.path.sample slice.path.commonTuple
    (fun _ => slice.path.referenceRetainedCRTInputLaw cutoff) Y q vol hb bW
    (Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _)) hgrid hq r
    (fun a => β (e.symm a))

omit [Fintype Tsp] in
theorem retainedRecoveredRationalFactor_abs_le_exp_of_modulus
    (Pgrid Pmod : ℝ)
    (hgrid : ∀ z : A → ℤ, vol * slice.principalLaw.fiberMean grid
      (fun a _ => z a) (fun _ => 1) ≤ Real.exp Pgrid)
    (hq : (q : ℝ) ≤ Real.exp Pmod)
    (r : X → ZMod q) (β : Fin d → ℤ) :
    |slice.retainedRecoveredRationalFactor selected bW hb e cutoff r β| ≤
      Real.exp (Pgrid + (Fintype.card Out : ℝ) * Pmod) := by
  rw [abs_of_nonneg (slice.retainedRecoveredRationalFactor_nonneg selected bW hb e cutoff r β)]
  exact slice.retainedRecoveredRationalFactor_le_exp_of_modulus selected bW hb e cutoff
    Pgrid Pmod hgrid hq r β

omit [Fintype Tsp] in
theorem retainedRecoveredRationalFactor_le_exp
    (depth : ℕ) (hdepth : ∀ p : slice.path.primes, slice.path.exponent p.val ≤ depth)
    (Pgrid : ℝ)
    (hgrid : ∀ z : A → ℤ, vol * slice.principalLaw.fiberMean grid
      (fun a _ => z a) (fun _ => 1) ≤ Real.exp Pgrid)
    (r : X → ZMod q) (β : Fin d → ℤ) :
    slice.retainedRecoveredRationalFactor selected bW hb e cutoff r β ≤
      Real.exp (slice.retainedRationalBudget cutoff depth Pgrid) := by
  have hmod : (q : ℝ) ≤ Real.exp ((depth : ℝ) *
      (Pbad + Ppres + ((cutoff + 1 : ℕ) : ℝ) * Real.log (cutoff + 1))) := by
    rw [slice.path.referenceRetainedCRTModulus_eq]
    exact slice.path.referenceRetainedModulus_le_exp cutoff depth hdepth
  exact slice.retainedRecoveredRationalFactor_le_exp_of_modulus selected bW hb e cutoff
    Pgrid _ hgrid hmod r β

omit [Fintype Tsp] in
theorem retainedRecoveredRationalFactor_abs_le_cap
    (depth : ℕ) (hdepth : ∀ p : slice.path.primes, slice.path.exponent p.val ≤ depth)
    (Pgrid : ℝ)
    (hgrid : ∀ z : A → ℤ, vol * slice.principalLaw.fiberMean grid
      (fun a _ => z a) (fun _ => 1) ≤ Real.exp Pgrid)
    (r : X → ZMod q) (β : Fin d → ℤ) :
    |slice.retainedRecoveredRationalFactor selected bW hb e cutoff r β| ≤
      slice.retainedRationalCap cutoff depth Pgrid := by
  rw [abs_of_nonneg (slice.retainedRecoveredRationalFactor_nonneg selected bW hb e cutoff r β)]
  exact slice.retainedRecoveredRationalFactor_le_exp selected bW hb e cutoff depth hdepth Pgrid hgrid r β

private theorem retainedRecoveredG_eq_centered :
    slice.retainedRecoveredG selected hB o bW hb e cutoff = centered := by
  funext v r β y
  change forecastLawRecoveredKernel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (fun a => y (e.symm a)) =
    forecastLawRecoveredKernel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (fun a => y (e.symm a) + 0)
  simp only [add_zero]

omit [Fintype Tsp] in
private theorem retainedRational_abs_le_layered {Rcap : ℝ≥0}
    (hcap : ∀ r β, |slice.retainedRecoveredRationalFactor selected bW hb e cutoff r β| ≤ Rcap)
    (r : X → ZMod q) (β : (Σ j, J j) → ℤ) : |rat r β| ≤ Rcap := by
  have h := hcap r (fun i => β (e i))
  simpa only [retainedRecoveredRationalFactor, Equiv.apply_symm_apply] using h

theorem retainedRecoveredG_mem_Icc {Dcap Rcap : ℝ≥0}
    (hdensity : ∀ y, slice.density hB y ∈ Set.Icc (0 : ℝ) Dcap)
    (hcap : ∀ r β, |slice.retainedRecoveredRationalFactor selected bW hb e cutoff r β| ≤ Rcap)
    (v : X → ℝ) (r : X → ZMod q) (β : Fin d → ℤ) (y : Fin d → ℝ) :
    slice.retainedRecoveredG selected hB o bW hb e cutoff v r β y ∈
      Set.Icc (0 : ℝ) (Dcap * Rcap : ℝ≥0) := by
  rw [slice.retainedRecoveredG_eq_centered selected hB o bW hb e cutoff]
  apply forecastLawCenteredRecoveredKernel_mem_Icc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hdensity (Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _))
  intro r β
  exact (le_abs_self _).trans (slice.retainedRational_abs_le_layered selected bW hb e cutoff hcap r β)

theorem retainedRecoveredG_lift_lipschitz
    (C : Fin m → ℝ≥0)
    (hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    {Dlip Rcap : ℝ≥0} (hdensity : LipschitzWith Dlip (slice.density hB))
    (hcap : ∀ r β, |slice.retainedRecoveredRationalFactor selected bW hb e cutoff r β| ≤ Rcap)
    (v : X → ℝ) (r : X → ZMod q) (β : Fin d → ℤ) :
    LipschitzWith (Rcap * (Dlip * (K * ∑ j, C j * Fintype.card (J j))))
      (slice.retainedRecoveredG selected hB o bW hb e cutoff v r β) := by
  rw [slice.retainedRecoveredG_eq_centered selected hB o bW hb e cutoff]
  exact forecastLawCenteredRecoveredKernel_lift_lipschitz B U b S slice.principalLaw
    (slice.density hB) selected slice.path.sample slice.path.commonTuple
    (fun _ => slice.path.referenceRetainedCRTInputLaw cutoff) Y q vol
    slice.path.base physicalN τ o hb bW e (fun _ => 0) hR C hC K hK hdensity
    (slice.retainedRational_abs_le_layered selected bW hb e cutoff hcap) v r β

theorem retainedRecoveredG_spatial_lipschitz
    (hτ : 0 < τ) {Dlip Rcap : ℝ≥0} (hdensity : LipschitzWith Dlip (slice.density hB))
    (hcap : ∀ r β, |slice.retainedRecoveredRationalFactor selected bW hb e cutoff r β| ≤ Rcap)
    (r : X → ZMod q) (β : Fin d → ℤ) (y : Fin d → ℝ) :
    LipschitzWith (Rcap * (Dlip * ⟨8 / τ, by positivity⟩))
      (fun v => slice.retainedRecoveredG selected hB o bW hb e cutoff v r β y) := by
  simp only [slice.retainedRecoveredG_eq_centered selected hB o bW hb e cutoff]
  exact forecastLawCenteredRecoveredKernel_spatial_lipschitz B U b S slice.principalLaw
    (slice.density hB) selected slice.path.sample slice.path.commonTuple
    (fun _ => slice.path.referenceRetainedCRTInputLaw cutoff) Y q vol
    slice.path.base physicalN τ o hb bW e (fun _ => 0) hτ hdensity
    (slice.retainedRational_abs_le_layered selected bW hb e cutoff hcap) r β y

theorem retainedRecoveredG_recovered_invariant {d' : ℕ}
    (M : Fin d → Fin d' → ℤ)
    (hcol : ∀ j a, (standardEuclideanPoint (J j)
      (fun i => M (e.symm ⟨j,i⟩) a)).val ∈ euclideanSubspace (U j))
    (hdiv : ∀ i a, (q : ℤ) ∣ M i a)
    (v : X → ℝ) (r : X → ZMod q) (β : Fin d → ℤ) (k : Fin d' → ℤ) :
    slice.retainedRecoveredG selected hB o bW hb e cutoff v r (recoveredIntegerLift M β k) =
      slice.retainedRecoveredG selected hB o bW hb e cutoff v r β := by
  simp only [slice.retainedRecoveredG_eq_centered selected hB o bW hb e cutoff]
  exact forecastLawCenteredRecoveredKernel_recovered_invariant B U b S slice.principalLaw
    (slice.density hB) selected slice.path.sample slice.path.commonTuple
    (fun _ => slice.path.referenceRetainedCRTInputLaw cutoff) Y q vol
    slice.path.base physicalN τ o hb bW e (fun _ => 0) M hcol hdiv v r β k

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

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

local instance : NeZero slice.path.referenceModulus := ⟨slice.path.referenceModulus_pos.ne'⟩
local instance (cutoff : ℕ) : NeZero (slice.path.referenceRetainedCRTModulus cutoff) :=
  ⟨(slice.path.referenceRetainedCRTModulus_pos cutoff).ne'⟩

local notation "labels" => forecastRecoveredIntegerLabels U b hb bW
local notation "grid" => forecastInactiveFixedOutput B U b S selected
  (allocatedOriginalSampleInactiveCoefficients B selected slice.path.sample) slice.path.commonTuple
local notation "vol" => (∏ a, (basisAxisScale (b (Sigma.fst (selected a))) (Sigma.snd (selected a)) : ℝ))
local notation "raw" => (fun z : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U b S) =>
    fun k : PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty => (z (Prod.fst k) (Prod.snd k) : ℤ))
local notation "out" r:max β:max => forecastCongruenceOutput (allocatedShortAxis (I := I) U b S.value) r
  (fun j i => (labels (fun a => β (e.symm a)) j i : ZMod slice.path.referenceModulus))
local notation "gridAt" β:max => (fun a (_ : (Finset.univ : Finset (Finset Empty))) =>
  labels (fun a => β (e.symm a)) (Sigma.fst (selected a)) (Sum.inl (Sigma.snd (selected a))))
local notation "reduced" cutoff:max r:max => (fun i => ZMod.castHom
  (slice.path.referenceRetainedCRTModulus_dvd cutoff)
  (ZMod (slice.path.referenceRetainedCRTModulus cutoff)) (r i))

omit [Fintype Tsp] in

theorem retainedRecoveredRationalFactor_eq_reference (cutoff : ℕ)
    (r : X → ZMod slice.path.referenceModulus) (β : Fin d → ℤ) :
    slice.retainedRecoveredRationalFactor selected bW hb e cutoff (reduced cutoff r) β =
      slice.path.retainedCRTReferenceForecast slice.principalLaw grid raw cutoff vol
        (gridAt β) (out r β) := by
  unfold retainedRecoveredRationalFactor forecastLawRecoveredRationalFactor
    ActualFixedSpatialForecastPath.retainedCRTReferenceForecast
  rw [slice.retainedForecastOutput_reduce cutoff r]
  simp only [rationalInactiveForecast, rationalOutputDensity, ← Nat.card_eq_fintype_card]

omit [Fintype Tsp] in

theorem recoveredRationalFactor_retained_comparison
    (hm : 0 < m)
    (hD : Fintype.card X + ∑ j : Fin m, (Fintype.card (Eout j) + n j) ≤ Dmod)
    (cutoff : ℕ) (hcutoff : 0 < cutoff) (hsmall : 2 / (cutoff : ℝ) ≤ 1 / 2)
    {δ : ℝ} (hδ : 0 ≤ δ) (haccuracy : 4 / (cutoff : ℝ) ≤ δ)
    (r : X → ZMod slice.path.referenceModulus) (β : Fin d → ℤ) :
    (1 - δ) * slice.retainedRecoveredRationalFactor selected bW hb e cutoff (reduced cutoff r) β ≤
      slice.recoveredRationalFactor selected bW hb e r β ∧
    slice.recoveredRationalFactor selected bW hb e r β ≤
      (1 + δ) * slice.retainedRecoveredRationalFactor selected bW hb e cutoff (reduced cutoff r) β := by
  rw [slice.retainedRecoveredRationalFactor_eq_reference selected bW hb e cutoff r β]
  unfold recoveredRationalFactor forecastLawRecoveredRationalFactor
  have h := slice.path.reference_inactive_goodPrimeDeletion_retainedCRT hm hD slice.principalLaw
    grid raw cutoff hcutoff hsmall hδ haccuracy vol (by positivity) (gridAt β) (out r β)
  dsimp only at h
  simpa only [rationalInactiveForecast, rationalOutputDensity, ← Nat.card_eq_fintype_card] using h

private theorem mul_relative_bounds {w f g δ : ℝ} (hw : 0 ≤ w)
    (h : (1 - δ) * g ≤ f ∧ f ≤ (1 + δ) * g) :
    (1 - δ) * (w * g) ≤ w * f ∧ w * f ≤ (1 + δ) * (w * g) := by
  constructor
  · calc
      _ = w * ((1 - δ) * g) := by ring
      _ ≤ w * f := mul_le_mul_of_nonneg_left h.1 hw
  · calc
      _ ≤ w * ((1 + δ) * g) := mul_le_mul_of_nonneg_left h.2 hw
      _ = _ := by ring

theorem recoveredG_retained_comparison
    (hm : 0 < m)
    (hD : Fintype.card X + ∑ j : Fin m, (Fintype.card (Eout j) + n j) ≤ Dmod)
    (cutoff : ℕ) (hcutoff : 0 < cutoff) (hsmall : 2 / (cutoff : ℝ) ≤ 1 / 2)
    {δ : ℝ} (hδ : 0 ≤ δ) (haccuracy : 4 / (cutoff : ℝ) ≤ δ)
    (v : X → ℝ) (r : X → ZMod slice.path.referenceModulus)
    (β : Fin d → ℤ) (y : Fin d → ℝ) :
    (1 - δ) * slice.retainedRecoveredG selected hB o bW hb e cutoff v (reduced cutoff r) β y ≤
      slice.recoveredG selected hB o bW hb e v r β y ∧
    slice.recoveredG selected hB o bW hb e v r β y ≤
      (1 + δ) * slice.retainedRecoveredG selected hB o bW hb e cutoff v (reduced cutoff r) β y := by
  exact mul_relative_bounds (slice.density_nonneg hB _)
    (slice.recoveredRationalFactor_retained_comparison selected bW hb e hm hD cutoff hcutoff
      hsmall hδ haccuracy r β)

theorem recoveredG_retained_abs_sub_le
    (hm : 0 < m)
    (hD : Fintype.card X + ∑ j : Fin m, (Fintype.card (Eout j) + n j) ≤ Dmod)
    (cutoff : ℕ) (hcutoff : 0 < cutoff) (hsmall : 2 / (cutoff : ℝ) ≤ 1 / 2)
    {δ : ℝ} (hδ : 0 ≤ δ) (haccuracy : 4 / (cutoff : ℝ) ≤ δ)
    (v : X → ℝ) (r : X → ZMod slice.path.referenceModulus)
    (β : Fin d → ℤ) (y : Fin d → ℝ) :
    |slice.recoveredG selected hB o bW hb e v r β y -
      slice.retainedRecoveredG selected hB o bW hb e cutoff v (reduced cutoff r) β y| ≤
    δ * slice.retainedRecoveredG selected hB o bW hb e cutoff v (reduced cutoff r) β y := by
  have h := slice.recoveredG_retained_comparison selected hB o bW hb e hm hD cutoff
    hcutoff hsmall hδ haccuracy v r β y
  apply abs_le.mpr
  constructor
  · nlinarith only [h.1]
  · nlinarith only [h.2]

theorem recoveredG_retained_comparison_scaled
    (hm : 0 < m)
    (hD : Fintype.card X + ∑ j : Fin m, (Fintype.card (Eout j) + n j) ≤ Dmod)
    (cutoff : ℕ) (hcutoff : 0 < cutoff) (hsmall : 2 / (cutoff : ℝ) ≤ 1 / 2)
    {δ : ℝ} (hδ : 0 ≤ δ) (haccuracy : 4 / (cutoff : ℝ) ≤ δ)
    {κ : ℝ} (hκ : 0 ≤ κ)
    (v : X → ℝ) (r : X → ZMod slice.path.referenceModulus)
    (β : Fin d → ℤ) (y : Fin d → ℝ) :
    (1 - δ) * (κ * slice.retainedRecoveredG selected hB o bW hb e cutoff v
      (reduced cutoff r) β y) ≤ κ * slice.recoveredG selected hB o bW hb e v r β y ∧
    κ * slice.recoveredG selected hB o bW hb e v r β y ≤
      (1 + δ) * (κ * slice.retainedRecoveredG selected hB o bW hb e cutoff v
        (reduced cutoff r) β y) := by
  exact mul_relative_bounds hκ
    (slice.recoveredG_retained_comparison selected hB o bW hb e hm hD cutoff
      hcutoff hsmall hδ haccuracy v r β y)

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
