import OAI.Combinatorics.Progressions.Sampling.ActualFixedSpatialSlicedGridErrorIdentification

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {X : Type} [Fintype X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {A : Type} {Dmod : ℕ} {selected : A → Σ j : Fin m, Fin (n j)}
variable {τ δslice : ℝ}

namespace ActualFixedSpatialForecastSetup

variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)
variable (hR : ∀ j, 0 < R j)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

include s hR

theorem inverse_radius_le_one (j : Fin m) :
    s.inverse j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 := by
  have hnonneg : 0 ≤ s.inverse j * ((Fintype.card (I j) : ℝ) + 1) * R j :=
    mul_nonneg (mul_nonneg (s.hinverse j) (by positivity)) (hR j).le
  have hbudget := s.hbudget j
  have hcompare := mul_le_mul_of_nonneg_right
    (show (1 : ℝ) ≤ 2 * (s.radius : ℝ) by linarith [s.hr3]) hnonneg
  nlinarith

theorem nativeAmbientLip_le_one : forecastNativeAmbientLip U b o R ≤ 1 := by
  change ‖(forecastNativeAmbientLinear U b o R).toContinuousLinearMap‖ ≤ (1 : ℝ)
  apply (forecastNativeAmbientLinear U b o R).toContinuousLinearMap.opNorm_le_bound zero_le_one
  intro v
  rw [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr
  intro a
  have hcoord (k : LayerSamplerAxis I n) :
      |R a.1 * v k| ≤ R a.1 * ‖v‖ := by
    rw [abs_mul, abs_of_pos (hR a.1)]
    exact mul_le_mul_of_nonneg_left
      (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v k) (hR a.1).le
  have hrow := mixedRealPoint_norm_le (euclideanSubspace (U a.1)) (b a.1) (o a.1)
    (s.hinverse a.1) (mul_nonneg (hR a.1).le (norm_nonneg v)) (s.hchart a.1)
    (fun i => R a.1 * v ⟨a.1, Sum.inl i⟩)
    (fun i => R a.1 * v ⟨a.1, Sum.inr i⟩)
    (fun i => hcoord ⟨a.1, Sum.inl i⟩) (fun i => hcoord ⟨a.1, Sum.inr i⟩)
  have hpoint := (PiLp.norm_apply_le (mixedRealPoint (euclideanSubspace (U a.1))
    (b a.1) (o a.1) ((fun i => R a.1 * v ⟨a.1, Sum.inl i⟩),
      fun i => R a.1 * v ⟨a.1, Sum.inr i⟩)) a.2).trans hrow
  change ‖mixedRealPoint (euclideanSubspace (U a.1)) (b a.1) (o a.1)
    ((fun i => R a.1 * v ⟨a.1, Sum.inl i⟩),
      fun i => R a.1 * v ⟨a.1, Sum.inr i⟩) a.2‖ ≤ _
  apply hpoint.trans
  calc
    _ = (s.inverse a.1 * ((Fintype.card (I a.1) : ℝ) + 1) * R a.1) * ‖v‖ := by ring
    _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right (s.inverse_radius_le_one hR a.1) (norm_nonneg v)
    _ = ‖v‖ := one_mul _

theorem nativePullbackLip_le {Lip : ℝ≥0} (hτ1 : τ ≤ 1) :
    Lip * max ‖τ / 8‖₊ (forecastNativeAmbientLip U b o R) ≤ Lip := by
  have hτnorm : ‖τ / 8‖₊ ≤ (1 : ℝ≥0) := by
    change ‖τ / 8‖ ≤ (1 : ℝ)
    rw [Real.norm_of_nonneg (div_nonneg s.hτ.le (by norm_num))]
    linarith
  exact (mul_le_mul_of_nonneg_left (max_le hτnorm (s.nativeAmbientLip_le_one hR o))
    (show 0 ≤ Lip from zero_le)).trans_eq
    (mul_one _)

theorem nativePullback_lipschitz {periodCap coverCap : ℝ} {Lip : ℝ≥0}
    (hτ1 : τ ≤ 1)
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
    (P : LayerSamplerAxis I n → Prop) [DecidablePred P]
    (residue : X → ZMod W.modulus) (deck : (Σ j, J j) → ZMod W.cover)
    (center : X → ℝ) (frozen : {a : LayerSamplerAxis I n // P a} → ℝ) :
    LipschitzWith Lip (W.forecastPullback U b o R P residue deck center τ frozen) :=
  (W.forecastPullback_lipschitz U b o R P residue deck center τ frozen).weaken
    (s.nativePullbackLip_le hR o hτ1)

end ActualFixedSpatialForecastSetup
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
variable {Dmod Lrank : ℕ} {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp] {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)}
variable {physicalN : X → ℕ} {τ cost : ℝ}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod (allocatedShortIntegerSelection U b S.value) τ (Real.exp (-cost) / 2))
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv (allocatedPhysicalRootBudget B U b S (fun _ => 0))
  (S.value : ℝ) physicalN τ (Real.exp (-cost) / 2) s.P s.Pbad s.Ppres)

namespace ActualFixedSpatialSlicedForecastPath

omit [Fintype Tsp] in
theorem decayConstant_le_exp :
    slice.decayConstant ≤
      Real.exp ((s.Pbad + s.Ppres) * ((Dmod + 2 : ℕ) : ℝ) * modularRankChargeFactor m) :=
  forecastModularCharge_exp_bound m Dmod slice.path.Rbad
    (∏ p : slice.path.primes, p.val ^ slice.path.prescribed p.val)
    slice.path.RbadBound slice.path.presBound

omit [Fintype Tsp] in
theorem kernelWidth_lower_of_length
    (hHG : ∀ g, Real.exp (-cost) * S.value ≤ (slice.kernelLength g : ℝ)) :
    ∀ g, Real.exp (-(cost + 1)) ≤ slice.kernelWidth g := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hexp : Real.exp (-(cost + 1)) ≤ Real.exp (-cost) / 2 := by
    have he := mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg (-(cost + 1)))
    have heq : Real.exp 1 * Real.exp (-(cost + 1)) = Real.exp (-cost) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [heq] at he
    linarith
  intro g
  apply hexp.trans
  have hwidth := fixedPathSliceWidth_lower S.positive slice.step_pos (slice.kernelLength_two g) (hHG g)
  change Real.exp (-cost) / 2 ≤ (slice.step : ℝ) * ((slice.kernelLength g - 1 : ℕ) : ℝ) / S.value
  rw [Nat.cast_sub (show 1 ≤ slice.kernelLength g by have := slice.kernelLength_two g; omega), Nat.cast_one]
  exact hwidth

noncomputable def comparisonGridLog (Pu : ℝ) : ℝ :=
  max Pu (max (forecastOriginalSmoothBudget m (s.P + (Fintype.card X + 1) * (cost + 1)))
    ((s.Pbad + s.Ppres) * ((Dmod + 2 : ℕ) : ℝ) * modularRankChargeFactor m))

noncomputable def comparisonPrecisionFloor (d : ℕ) (Pu V E : ℝ) : ℕ :=
  max (fixedPathSlicedGridMeshFloor s.D 4 V cost (2 * Pu + (E + 4) + 14))
    (forecastJointGridSamplerFloor d (comparisonGridLog s Pu) (E + 4) V s.PK)

theorem comparisonError_le_exp
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Lip : ℝ≥0} {Pu V E Edata Q ξ Mmass : ℝ}
    (hcost : 0 ≤ cost) (hPu : 2 ≤ Pu) (hE : 0 ≤ E)
    (hDsq : s.D * s.D ≤ Pu) (hAL : (s.L : ℝ) ≤ Real.exp Pu)
    (hτ1 : τ ≤ 1) (hLip : (Lip : ℝ) ≤ Real.exp Pu)
    (q : ℕ) [NeZero q] (hq : (q : ℝ) ≤ Real.exp V)
    (hfloor : comparisonPrecisionFloor s (Dmod + Fintype.card (Σ j, I j)) Pu V E ≤ S.value)
    (hHP : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      ∀ p : B a.val × Fin (layerSamplerDegree I n a.val),
        Real.exp (-cost) * S.value ≤ (slice.principalLength ⟨a.val,p⟩ : ℝ))
    (hHG : ∀ g, Real.exp (-cost) * S.value ≤ (slice.kernelLength g : ℝ))
    (hξ0 : 0 ≤ ξ) (hξ : ξ ≤ Real.exp (-(2 * Pu + (E + 4) + 14)))
    (hM : Mmass ≤ Real.exp Q) (hEdata : E + 8 ≤ Edata) :
    let d := Dmod + Fintype.card (Σ j, I j)
    let F := 2 * Pu + (E + 4) + 14
    let η := Real.exp (-F)
    let t := Real.exp (-fixedPathSlicedPerturbationLog s.D (s.D + Pu + 4) (cost + 1) F m)
    let Pg := comparisonGridLog s Pu
    slice.comparisonError (Lip := Lip) (ξ := ξ) (t := t) (δ := Real.exp (-cost))
      (ε := 2 * Real.exp cost / S.value) (η := η) (q := q) (hδ := Real.exp_pos _)
      (o := o) (δnative := Real.exp (-Edata)) (M := Mmass) (Eprec := Q + E + 8)
      (cutoff := forecastJointGridCutoff Pg (E + 4))
      (δgrid := forecastJointGridMesh d Pg (E + 4)) ≤ Real.exp (-E) := by
  intro d F η t Pg
  obtain ⟨hdout, hdj, hdc⟩ := s.gridDimensions_le
  have hNative : ((Lip * max ‖τ / 8‖₊ (forecastNativeAmbientLip U b o R) : ℝ≥0) : ℝ) ≤
      Real.exp Pu := (show ((Lip * max ‖τ / 8‖₊ (forecastNativeAmbientLip U b o R) : ℝ≥0) : ℝ) ≤
        (Lip : ℝ) from s.nativePullbackLip_le hR o hτ1).trans hLip
  have hPu0 : 0 ≤ Pu := by linarith
  have hPg : 0 ≤ Pg := hPu0.trans (le_max_left _ _)
  have hE4 : 0 ≤ E + 4 := by linarith
  have hLift : (Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) : ℝ) * m ≤ Pu :=
    (mul_le_mul s.hD.tuples s.hD.degree (Nat.cast_nonneg _) s.hD.nonneg).trans hDsq
  have hsourceFloor : fixedPathSlicedGridMeshFloor s.D 4 V cost F ≤ S.value :=
    (le_max_left _ _).trans hfloor
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  have htdata := allocatedFixedPathSlicedPerturbation_chosen_tail (G := G) B U b
    s.hD.nonneg hPu0 hcost hF s.hD.tuples s.haxes s.L
    (Real.exp_pos (-F)) hAL (by rw [Real.exp_neg, inv_inv])
  have hL := allocatedOriginalSampleFullSliceLip_le_two_exp_of_allAxis B U b S
    htdata.1.le htdata.2.1 hLift
  let Kφ := Lip * max ‖τ / 8‖₊ (forecastNativeAmbientLip U b o R)
  have hKK : (Kφ : ℝ) * allocatedOriginalSampleFullSliceLip B U b S t ≤
      Real.exp (2 * Pu + 2) := by
    calc
      _ ≤ Real.exp Pu * (2 * Real.exp Pu) :=
        mul_le_mul hNative hL (NNReal.coe_nonneg _) (Real.exp_nonneg _)
      _ = 2 * Real.exp (2 * Pu) := by rw [two_mul Pu, Real.exp_add]; ring
      _ ≤ Real.exp 2 * Real.exp (2 * Pu) :=
        mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (2 : ℝ)]) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hNative' : (Kφ : ℝ) ≤ Real.exp (2 * Pu + 2) :=
    hNative.trans (Real.exp_le_exp.mpr (by linarith))
  let HP := fun j : PrincipalTupleIndex
    (fun a : {a // ¬allocatedShortAxis (I := I) U b S.value a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) => slice.principalLength ⟨j.1.val,j.2⟩
  have hcard : (Fintype.card (PrincipalTupleIndex
      (fun a : {a // ¬allocatedShortAxis (I := I) U b S.value a} => B a.val)
      (fun a => layerSamplerDegree I n a.val)) : ℝ) ≤ s.D :=
    (Nat.cast_le.mpr (allocatedOriginalSampleLiftInput_card_le_allAxis B U b S)).trans s.hD.tuples
  have hprec : F = (2 * Pu + 2) + (E + 4) + 12 := by dsimp only [F]; ring
  have hsrc := fixedPathSlicedSourceErrorBudget_of_floor s.hD.nonneg
    (by linarith : 2 ≤ 2 * Pu + 2) hE4 HP slice.kernelLength hcard s.hD.kernel_variables
    (NeZero.pos q) hq (by simpa only [hprec] using hsourceFloor)
    (fun j => hHP j.1 j.2) hHG (by positivity) Kφ.coe_nonneg hξ0 hKK hNative'
    (by simpa only [← hprec] using hξ)
  have hwidth := slice.kernelWidth_lower_of_length s hHG
  have hdensity := slice.density_uniform_budget s.hBactive s.hP s.hδslice s.hδsliceInv
    s.hX (s.haxes.trans s.hDP) s.hblocks (by linarith : 0 ≤ cost + 1) hwidth
  have hsm : forecastOriginalSmoothBudget m (s.P + (Fintype.card X + 1) * (cost + 1)) ≤ Pg :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hdec : (s.Pbad + s.Ppres) * ((Dmod + 2 : ℕ) : ℝ) * modularRankChargeFactor m ≤ Pg :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hC := (show (fixedSpatialOriginalForecastCap B (slice.slicedBlockEquiv true) s.hδslice : ℝ) ≤
      Real.exp (forecastOriginalSmoothBudget m (s.P + (Fintype.card X + 1) * (cost + 1))) by
        linarith [hdensity.1]).trans (Real.exp_le_exp.mpr hsm)
  have hLgrid := hdensity.2.1.trans (Real.exp_le_exp.mpr hsm)
  have hDgrid := (slice.decayConstant_le_exp s).trans (Real.exp_le_exp.mpr hdec)
  have hKgrid : (Kφ : ℝ) ≤ Real.exp Pg :=
    hNative.trans (Real.exp_le_exp.mpr (le_max_left _ _))
  unfold comparisonError
  rw [slice.ambientGridError_eq_forecastJointGridError,
    allocatedSlicedPhysicalComparisonError_eq_sourceError]
  have htotal := fixedPathSlicedAmbientScalarPrecision_error _ _ _ d hdout hdj hdc hPg hE
    hsrc.2.2 hM (Real.rpow_nonneg (Nat.cast_nonneg _) _) (NNReal.coe_nonneg _)
    (NNReal.coe_nonneg _) Kφ.coe_nonneg hDgrid hLgrid hC hKgrid
    (forecastJointGridMesh_bounds d hPg hE4).1.le le_rfl
  have hδnative : Real.exp (-Edata) ≤ Real.exp (-(E + 8)) :=
    Real.exp_le_exp.mpr (neg_le_neg hEdata)
  simp only [η, hprec, Kφ, HP, add_assoc, NNReal.coe_mul, decayConstant] at htotal ⊢
  linarith only [htotal, hδnative]

include hR in
omit [DecidableEq X] in
theorem comparisonPrecision_grid_mesh
    {Pu V E : ℝ} (hPu : 0 ≤ Pu) (hE : 0 ≤ E)
    (d q : ℕ) (hq : (q : ℝ) ≤ Real.exp V)
    (hfloor : comparisonPrecisionFloor s d Pu V E ≤ S.value)
    (hN : ∀ i, Real.exp (forecastJointGridAmbientLog d (comparisonGridLog s Pu)
      (E + 4) V s.Pτ) ≤ (physicalN i : ℝ)) :
    ∀ j, (((q * forecastJointGridCutoff (comparisonGridLog s Pu) (E + 4) : ℕ) : ℝ) /
      forecastJointGridScale U b R S.value physicalN τ j) ≤
      forecastJointGridMesh d (comparisonGridLog s Pu) (E + 4) := by
  apply forecastJointGridScale_mesh_of_floor U b d (hPu.trans (le_max_left _ _))
    (by linarith : 0 ≤ E + 4) hR s.hτ q S.value physicalN hq s.hτinv
    (fun j => (s.hK j).trans s.hKBound) _ hN
  exact (le_max_right _ _).trans hfloor

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
variable {Dmod Lrank : ℕ} {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp] {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)}
variable {physicalN : X → ℕ} {τ cost : ℝ}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod (allocatedShortIntegerSelection U b S.value) τ (Real.exp (-cost) / 2))
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv (allocatedPhysicalRootBudget B U b S (fun _ => 0))
  (S.value : ℝ) physicalN τ (Real.exp (-cost) / 2) s.P s.Pbad s.Ppres)

namespace ActualFixedSpatialSlicedForecastPath

omit [Fintype Tsp] in

theorem comparisonPrecision_geometry
    {Pu V E : ℝ} (hPu : 2 ≤ Pu) (hE : 0 ≤ E)
    (d q : ℕ) (hq0 : 0 < q) (hq : (q : ℝ) ≤ Real.exp V)
    (hfloor : comparisonPrecisionFloor s d Pu V E ≤ S.value)
    (hHP : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      ∀ p : B a.val × Fin (layerSamplerDegree I n a.val),
        Real.exp (-cost) * S.value ≤ (slice.principalLength ⟨a.val,p⟩ : ℝ))
    (hHG : ∀ g, Real.exp (-cost) * S.value ≤ (slice.kernelLength g : ℝ)) :
    (∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      ∀ p : B a.val × Fin (layerSamplerDegree I n a.val),
        2 ≤ slice.principalLength ⟨a.val,p⟩ ∧ q ≤ slice.principalLength ⟨a.val,p⟩ ∧
          scalarCubeGridBoundaryConstant Empty *
            ((q : ℝ) / slice.principalLength ⟨a.val,p⟩) < 1) ∧
    (∀ g, 2 ≤ slice.kernelLength g ∧ q ≤ slice.kernelLength g ∧
      scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / slice.kernelLength g) < 1) ∧
    (∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      ∀ p : B a.val × Fin (layerSamplerDegree I n a.val),
        Real.exp (-cost) * S.value ≤
          ((integerProgressionSupport (slice.principalStart ⟨a.val,p⟩) (slice.step : ℤ)
            (slice.principalLength ⟨a.val,p⟩)).card : ℝ)) := by
  let HP := fun j : PrincipalTupleIndex
    (fun a : {a // ¬allocatedShortAxis (I := I) U b S.value a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) => slice.principalLength ⟨j.1.val,j.2⟩
  have hcard : (Fintype.card (PrincipalTupleIndex
      (fun a : {a // ¬allocatedShortAxis (I := I) U b S.value a} => B a.val)
      (fun a => layerSamplerDegree I n a.val)) : ℝ) ≤ s.D :=
    (Nat.cast_le.mpr (allocatedOriginalSampleLiftInput_card_le_allAxis B U b S)).trans s.hD.tuples
  have hF : 0 ≤ 2 * Pu + (E + 4) + 14 := by linarith
  have hsource : fixedPathSlicedGridMeshFloor s.D 4 V cost (2 * Pu + (E + 4) + 14) ≤ S.value :=
    (le_max_left _ _).trans hfloor
  have hp := fixedPathSlicedGridMesh_of_floor s.hD.nonneg (by norm_num : (0 : ℝ) ≤ 4)
    hF HP hcard hq0 hq hsource (fun j => hHP j.1 j.2)
    (fun _ => (0 : ℝ)) (fun _ => by positivity)
  have hg := fixedPathSlicedGridMesh_of_floor s.hD.nonneg (by norm_num : (0 : ℝ) ≤ 4)
    hF slice.kernelLength s.hD.kernel_variables hq0 hq hsource hHG
    (fun _ => (0 : ℝ)) (fun _ => by positivity)
  refine ⟨fun a p => hp.2.2.2 ⟨a,p⟩, hg.2.2.2, ?_⟩
  intro a p
  rw [card_integerProgressionSupport _ _ _ slice.step_pos]
  exact hHP a p

omit [DecidableEq X] [Fintype Tsp] in

theorem comparisonPrecision_tail
    {Pu E : ℝ} (hcost : 0 ≤ cost) (hPu : 2 ≤ Pu) (hE : 0 ≤ E)
    (hAL : (s.L : ℝ) ≤ Real.exp Pu) :
    let F := 2 * Pu + (E + 4) + 14
    let η := Real.exp (-F)
    let t := Real.exp (-fixedPathSlicedPerturbationLog s.D (s.D + Pu + 4) (cost + 1) F m)
    0 < t ∧ t ≤ 1 ∧ 0 < η ∧ η ≤ 1 ∧
      |t| * polynomialMassC2Budget
        (Fintype.card (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
          B a.val × Fin (layerSamplerDegree I n a.val))) m 1 ≤
      slicedPrincipalC2Tolerance
        (Fintype.card (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
          B a.val × Fin (layerSamplerDegree I n a.val)))
        (Fintype.card {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a}) m 1
        (unitProfilePrincipalLowerBound B) (Real.exp (-cost) / 2) s.L η := by
  intro F η t
  have hF : 0 ≤ F := by dsimp only [F]; linarith
  have hη : 0 < η := Real.exp_pos _
  have ht := allocatedFixedPathSlicedPerturbation_chosen_tail (G := G) B U b
    s.hD.nonneg (by linarith : 0 ≤ Pu) hcost hF s.hD.tuples s.haxes s.L
    hη hAL (by dsimp only [η]; rw [Real.exp_neg, inv_inv])
  exact ⟨ht.1, ht.2.1, hη, Real.exp_le_one_iff.mpr (neg_nonpos.mpr hF), ht.2.2 S⟩

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath
open scoped BigOperators NNReal

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {X : Type} [Fintype X] {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod : ℕ} {τ cost : ℝ}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod (allocatedShortIntegerSelection U b S.value) τ (Real.exp (-cost) / 2))

theorem comparisonPrecisionFloor_pos (d : ℕ) (Pu V E : ℝ) :
    0 < comparisonPrecisionFloor s d Pu V E :=
  (fixedPathSlicedGridMeshFloor_pos _ _ _ _ _).trans_le (le_max_left _ _)

theorem comparisonPrecisionFloor_le_exp (d : ℕ) {Pu V E : ℝ}
    (hPu : 0 ≤ Pu) (hV : 0 ≤ V) (hcost : 0 ≤ cost) (hE : 0 ≤ E) :
    (comparisonPrecisionFloor s d Pu V E : ℝ) ≤
      Real.exp (allocatedFixedPathSlicedAmbientFloorLog d s.D Pu V cost E
        (comparisonGridLog s Pu) s.PK) := by
  have hfour : (4 : ℝ) ≤ Real.exp 2 := by
    have h := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    norm_num at h
    linarith
  have hF : 0 ≤ 2 * Pu + (E + 4) + 14 := by positivity
  have hsrc := fixedPathSlicedGridMeshFloor_le_exp_of_prefactor s.hD.nonneg
    (by norm_num : (0 : ℝ) ≤ 4) (by norm_num) hfour hV hcost hF
  have hgrid := forecastJointGridSamplerFloor_le_exp d
    (hPu.trans (le_max_left _ _) : 0 ≤ comparisonGridLog s Pu)
    (show 0 ≤ E + 4 by linarith) hV s.hPK
  unfold comparisonPrecisionFloor
  rw [Nat.cast_max]
  apply max_le
  · apply hsrc.trans (Real.exp_le_exp.mpr _)
    apply le_trans _ (le_max_left _ _)
    linarith
  · exact hgrid.trans (Real.exp_le_exp.mpr (le_max_right _ _))

end Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory BooleanCubeKernel
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
variable {Dmod Lrank : ℕ} {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp] {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)}
variable {physicalN : X → ℕ} {τ cost : ℝ}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod (allocatedShortIntegerSelection U b S.value) τ (Real.exp (-cost) / 2))
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv (allocatedPhysicalRootBudget B U b S (fun _ => 0))
  (S.value : ℝ) physicalN τ (Real.exp (-cost) / 2) s.P s.Pbad s.Ppres)

namespace ActualFixedSpatialSlicedForecastPath

variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
variable (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j)
variable (hdegree : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (originalpoly j))
variable (ξ : ℝ) (hξ : 0 < ξ)
variable (hbox : ∀ x, 0 < physicalN x)
variable (hframe : slice.path.noise ∈ rectangularWeightIndices 0
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n))
    (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ physicalN) 1)
variable {Pu V E : ℝ}
variable (hσbound : ∀ j, |σ j| ≤ Real.exp (-fixedPathSlicedPerturbationLog
  s.D (s.D + Pu + 4) (cost + 1) (2 * Pu + (E + 4) + 14) m))
variable (q : ℕ) [NeZero q]
variable (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
variable (hqN : q ∣ slice.path.referenceModulus)
variable [hlattice : ∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j))
  (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable [hcompact : CompactSpace (EuclideanJetLayers U (fun _ : Fin m => Unit))]
variable (hmargin : ∀ i, 2 * spatialTrimMargin τ physicalN i ≤ physicalN i)
variable (htrimbase : slice.path.base ∈ trimmedIntegerBox physicalN (spatialTrimMargin τ physicalN))

variable {Pnative massLog capLog Edata Ptest : ℝ}
variable (data : ActualForecastData physicalN originalpoly Pnative massLog capLog Edata)
variable (hcenter : data.centerConstant = fun j => (slice.path.center j).val)
variable (hκ : s.κ = forecastGeometricJacobian (X := X) (I := I) U b R S.value (∏ a, (basisAxisScale (b ((allocatedShortIntegerSelection U b S.value) a).1) ((allocatedShortIntegerSelection U b S.value) a).2 : ℝ)) τ)
variable (hUniversal : ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
  (hm : ∀ j d, coefficients (poly j) d ∈ U j) (u : X → ℤ),
  ‖slice.targetAt (allocatedShortIntegerSelection U b S.value) s.hBactive o bW hb poly hm s.κ u -
    ∑ i, data.coefficient i * (data.twists i).eval physicalN
      (fun j => subtractConstant (data.centerConstant j) (poly j)) u‖ ≤ Real.exp (-Edata))
variable (hPtest : 0 ≤ Ptest) (hLw : (Lip : ℝ) ≤ Real.exp Ptest)
variable (hpw : periodCap ≤ Real.exp Ptest) (hcw : coverCap ≤ Real.exp Ptest)
variable {Rrank : ℝ} (hEprec : 0 ≤ massLog + E + 8)
variable (hlarge : ∀ i, Real.exp ((max (max s.P (2 * max Ptest (3 * Pnative + 3) + 1)) (massLog + E + 8) + nativeForecastAmbientExponent m) ^
  nativeForecastAmbientExponent m) ≤ (physicalN i : ℝ))
variable (hRrank : Real.exp ((max (max s.P (2 * max Ptest (3 * Pnative + 3) + 1)) (massLog + E + 8) + nativeForecastAmbientExponent m) ^
  nativeForecastAmbientExponent m) ≤ Rrank)
variable (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (physicalN i : ℝ))
  Rrank (U j) (originalpoly j))
variable (C : ℝ)
variable {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
variable {sampleFn : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
  CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n}
variable {readFn : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
  AllocatedActualCoefficientIndex G X I Eout n B → ℤ}
variable (hglobal : AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ
  originalpoly hmem (allocatedShortAxis (I := I) U b S.value) spatial kernel block C
  center slice.path.center slice.path.base sampleFn readFn)
variable (hz : allocatedCenteredJointDensity B U b hb o hR hσ S originalpoly hmem
  center slice.path.base slice.path.noise ≠ 0)
variable (hsampleAt : sampleFn slice.path.noise = slice.path.sample)
variable (hreadAt : readFn slice.path.noise = slice.path.read)

variable (hfinite : (integerBox physicalN).Nonempty)
variable (htarget : data.target = slice.target (allocatedShortIntegerSelection U b S.value)
  s.hBactive o bW hb originalpoly hmem s.κ)
variable (hcost : 0 ≤ cost) (hPu : 2 ≤ Pu) (hE : 0 ≤ E)
variable (hDsq : s.D * s.D ≤ Pu) (hAL : (s.L : ℝ) ≤ Real.exp Pu)
variable (hτ1 : τ ≤ 1) (hLip : (Lip : ℝ) ≤ Real.exp Pu)
variable (hq : (q : ℝ) ≤ Real.exp V)
variable (hfloor : comparisonPrecisionFloor s (Dmod + Fintype.card (Σ j, I j)) Pu V E ≤ S.value)
variable (hHP : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  ∀ p : B a.val × Fin (layerSamplerDegree I n a.val),
    Real.exp (-cost) * S.value ≤ (slice.principalLength ⟨a.val,p⟩ : ℝ))
variable (hHG : ∀ g, Real.exp (-cost) * S.value ≤ (slice.kernelLength g : ℝ))
variable (hstep : (slice.step : ℝ) ≤ 2 * Real.exp cost)
variable (hξsmall : ξ ≤ Real.exp (-(2 * Pu + (E + 4) + 14)))
variable (hEdata : E + 8 ≤ Edata)
variable (hNgrid : ∀ i, Real.exp (forecastJointGridAmbientLog
  (Dmod + Fintype.card (Σ j, I j)) (comparisonGridLog s Pu)
  (E + 4) V s.Pτ) ≤ (physicalN i : ℝ))

include hR hσ hdegree hξ hbox hframe hσbound hperiod hcover hqN
  ν hlattice hcompact hmargin htrimbase hcenter hκ hUniversal hPtest hLw hpw hcw
  hEprec hlarge hRrank hrank hglobal hz hsampleAt hreadAt hfinite htarget
  hcost hPu hE hDsq hAL hτ1 hLip hq hfloor hHP hHG hstep hξsmall hEdata hNgrid in

theorem native_ambient_model_precision :
    ‖slice.nativeMean s W originalpoly -
      (FiniteProbabilityWeights.uniformFinset (integerBox physicalN) hfinite).complexMean
        (fun u => W.eval physicalN
          (fun j => subtractConstant (data.centerConstant j) (originalpoly j)) u.val *
            data.target u)‖ ≤ Real.exp (-E) := by
  have hPu0 : 0 ≤ Pu := by linarith
  have hE4 : 0 ≤ E + 4 := by linarith
  have hPg : 0 ≤ comparisonGridLog s Pu := hPu0.trans (le_max_left _ _)
  have hgeom := slice.comparisonPrecision_geometry s hPu hE
    (Dmod + Fintype.card (Σ j, I j)) q (NeZero.pos q) hq hfloor hHP hHG
  have htail := comparisonPrecision_tail s hcost hPu hE hAL
  have hgrid := comparisonPrecision_grid_mesh s (hR := hR) hPu0 hE
    (Dmod + Fintype.card (Σ j, I j)) q hq hfloor hNgrid
  have hgridbounds := forecastJointGridMesh_bounds
    (Dmod + Fintype.card (Σ j, I j)) hPg hE4
  have hcomp := slice.native_ambient_model_comparison
    (s := s) (hb := hb) (o := o) (bW := bW) (W := W) (originalpoly := originalpoly)
    (hmem := hmem) (hdegree := hdegree) (ξ := ξ) (hξ := hξ) (hbox := hbox)
    (hframe := hframe) (ht := htail.1) (hσbound := hσbound)
    (hδ := Real.exp_pos (-cost))
    (hδone := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hcost))
    (hdense := hgeom.2.2) (q := q) (hperiod := hperiod) (hcover := hcover) (hqN := hqN)
    (hsizeG := fun g => (hgeom.2.1 g).2.1)
    (hsmallG := fun g => (hgeom.2.1 g).2.2)
    (hsize := fun a p => (hgeom.1 a p).2.1)
    (hsmall := fun a p => (hgeom.1 a p).2.2)
    (ε := 2 * Real.exp cost / S.value) (hε := by positivity)
    (hmesh := div_le_div_of_nonneg_right hstep (Nat.cast_nonneg S.value))
    (hη := htail.2.2.1) (htail := htail.2.2.2.2)
    (ν := ν) (hmargin := hmargin) (htrimbase := htrimbase)
    (data := data) (hcenter := hcenter) (hκ := hκ) (hUniversal := hUniversal)
    (hPtest := hPtest) (hLw := hLw) (hpw := hpw) (hcw := hcw)
    (hEprec := hEprec) (hlarge := hlarge) (hRrank := hRrank) (hrank := hrank)
    (cutoff := forecastJointGridCutoff (comparisonGridLog s Pu) (E + 4))
    (hcutoff := forecastJointGridCutoff_pos hPg hE4)
    (hδgrid := hgridbounds.1.le) (hδgrid1 := hgridbounds.2) (hgridmesh := hgrid)
    (C := C) (hglobal := hglobal) (hz := hz) (hsampleAt := hsampleAt)
    (hreadAt := hreadAt) (hfinite := hfinite) (htarget := htarget)
  exact hcomp.trans (slice.comparisonError_le_exp s o hcost hPu hE hDsq hAL
    hτ1 hLip q hq hfloor hHP hHG hξ.le hξsmall le_rfl hEdata)

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
