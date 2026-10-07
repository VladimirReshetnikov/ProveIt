import OAI.Combinatorics.Progressions.Sampling.AllocatedFixedPathForecastErrorBudget
import OAI.Combinatorics.Progressions.Sampling.ForecastAmbientPrecision
import OAI.Combinatorics.Progressions.Sampling.ForecastJointScaleNormalization

namespace OAI

section

namespace Erdos3

def fixedPathComparisonPrecision (E : ℝ) : ℝ := E + 4

noncomputable def fixedPathForecastTolerance (E : ℝ) : ℝ :=
  Real.exp (-(E + 8))

def fixedPathAmbientPrecision (Q E : ℝ) : ℝ := Q + E + 8

theorem fixedPathAmbientScalarPrecision_parameters {Q E : ℝ}
    (hQ : 0 ≤ Q) (hE : 0 ≤ E) :
    0 ≤ fixedPathComparisonPrecision E ∧
    0 < fixedPathForecastTolerance E ∧ fixedPathForecastTolerance E ≤ 1 ∧
    0 ≤ fixedPathAmbientPrecision Q E ∧
    fixedPathForecastTolerance E ≤ Real.exp (-(fixedPathComparisonPrecision E + 4)) ∧
    Q + fixedPathComparisonPrecision E + 4 ≤ fixedPathAmbientPrecision Q E := by
  unfold fixedPathComparisonPrecision fixedPathForecastTolerance fixedPathAmbientPrecision
  refine ⟨by linarith, Real.exp_pos _, ?_, by linarith, ?_, by linarith⟩
  · exact Real.exp_le_one_iff.mpr (by linarith)
  · apply Real.exp_le_exp.mpr
    linarith

theorem fixedPathAmbientScalarPrecision_ambient {Q E M : ℝ}
    (hM : M ≤ Real.exp Q) :
    2 * fixedPathForecastTolerance E + M * Real.exp (-fixedPathAmbientPrecision Q E) ≤
      Real.exp (-fixedPathComparisonPrecision E) := by
  apply forecast_ambient_exp_error (Q := Q)
  · unfold fixedPathForecastTolerance fixedPathComparisonPrecision
    apply Real.exp_le_exp.mpr
    linarith
  · exact hM
  · unfold fixedPathComparisonPrecision fixedPathAmbientPrecision
    linarith

theorem fixedPathAmbientScalarPrecision_error {Q E M sourceError : ℝ}
    (hM : M ≤ Real.exp Q)
    (hsource : sourceError ≤ Real.exp (-fixedPathComparisonPrecision E)) :
    sourceError + Real.exp (-fixedPathComparisonPrecision E) +
      (2 * fixedPathForecastTolerance E + M * Real.exp (-fixedPathAmbientPrecision Q E)) ≤
      Real.exp (-E) := by
  have hambient := fixedPathAmbientScalarPrecision_ambient (E := E) hM
  have hthree : (3 : ℝ) ≤ Real.exp 4 := by
    linarith only [Real.add_one_le_exp (4 : ℝ)]
  calc
    _ ≤ 3 * Real.exp (-fixedPathComparisonPrecision E) := by
      linarith only [hsource, hambient]
    _ ≤ Real.exp 4 * Real.exp (-fixedPathComparisonPrecision E) :=
      mul_le_mul_of_nonneg_right hthree (Real.exp_nonneg _)
    _ = Real.exp (-E) := by
      rw [← Real.exp_add]
      unfold fixedPathComparisonPrecision
      congr 1
      ring

end Erdos3

end

section

namespace Erdos3

theorem fixedPathSlicedAmbientScalarPrecision_error
    (dout dj dc d : ℕ) (hdout : dout ≤ d) (hdj : dj ≤ d) (hdc : dc ≤ d)
    {Pg E Q Mmass sourceError Dgrid L C K δgrid : ℝ}
    (hPg : 0 ≤ Pg) (hE : 0 ≤ E)
    (hsource : sourceError ≤ Real.exp (-(E + 4))) (hM : Mmass ≤ Real.exp Q)
    (hD : 0 ≤ Dgrid) (hL : 0 ≤ L) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hDP : Dgrid ≤ Real.exp Pg) (hLP : L ≤ Real.exp Pg)
    (hCP : C ≤ Real.exp Pg) (hKP : K ≤ Real.exp Pg)
    (hδ : 0 ≤ δgrid) (hmesh : δgrid ≤ forecastJointGridMesh d Pg (E + 4)) :
    sourceError + (2 * Real.exp (-(E + 8)) + Mmass * Real.exp (-(Q + E + 8))) +
      forecastJointGridError dout dj dc (forecastJointGridCutoff Pg (E + 4))
        Dgrid L C K δgrid ≤ Real.exp (-E) := by
  have hgrid := (forecastJointGridErrorBudget d hPg (show 0 ≤ E + 4 by linarith)).2.2.2.2
    hdout hdj hdc hD hL hC hK hDP hLP hCP hKP hδ hmesh
  have htotal := fixedPathAmbientScalarPrecision_error hM hsource
  dsimp only [fixedPathComparisonPrecision, fixedPathForecastTolerance,
    fixedPathAmbientPrecision] at htotal
  linarith only [hgrid, htotal]

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators NNReal Classical

noncomputable def allocatedFixedPathAmbientFloorLog
    (d : ℕ) (D P V E Pg PR : ℝ) : ℝ :=
  max (8 * (D + P + 9) + V + E + 10)
    (forecastJointGridSamplerLog d Pg (E + 4) V PR + 1)

namespace VectorPolynomial
variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ}

theorem exists_allocatedFixedPathAmbientPrecision
    (d : ℕ) {D P V E Pg PR Q : ℝ}
    (hD : 0 ≤ D) (hP : 2 ≤ P) (hV : 0 ≤ V) (hE : 0 ≤ E)
    (hPg : 0 ≤ Pg) (hPR : 0 ≤ PR) (hQ : 0 ≤ Q)
    (hInput : (Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) : ℝ) ≤ D)
    (hG : (Fintype.card G : ℝ) ≤ D)
    (hLift : (Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) : ℝ) * m ≤ P) :
    let early := 8 * (D + P + 9)
    let η := Real.exp (-(early + E + 8))
    let δforecast := Real.exp (-(E + 8))
    let Aambient := Q + E + 8
    0 < δforecast ∧ 0 ≤ Aambient ∧
    ∃ Lmin : ℕ, 0 < Lmin ∧
      (Lmin : ℝ) ≤ Real.exp (allocatedFixedPathAmbientFloorLog d D P V E Pg PR) ∧
      ∀ (S : LayerSamplerScale (G := G) B U basis R σ) {t : ℝ},
      0 ≤ t → t ≤ 1 → ∀ (Kφ : ℝ≥0), (Kφ : ℝ) ≤ Real.exp P →
      ∀ {q : ℕ}, 0 < q → (q : ℝ) ≤ Real.exp V → Lmin ≤ S.value →
      ∀ {G' N X : Type*} [Fintype G'] [Fintype N] [Fintype X]
        {r Mperiod : ℕ} (selection : Fin r ↪ G') {p lateTarget : ℝ},
      early + E + 8 ≤ lateTarget →
      let ξ := normalizedTupleNarrowWidth X N selection Mperiod p lateTarget
      0 < η ∧ η ≤ 1 ∧ 0 < ξ ∧ ξ ≤ 1 ∧
      2 ≤ S.value ∧ q ≤ S.value ∧
      scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / S.value) < 1 ∧
      forecastJointGridSamplerFloor d Pg (E + 4) V PR ≤ S.value ∧
      ∀ {Mmass : ℝ}, Mmass ≤ Real.exp Q →
      fixedPathForecastError
        (Fintype.card (PrincipalTupleIndex
          (fun a : {a // ¬allocatedShortAxis (I := I) U basis S.value a} => B a.val)
          (fun a => layerSamplerDegree I n a.val)))
        (Fintype.card G) q S.value Kφ (scalarCubeGridBoundaryConstant Empty)
        (allocatedOriginalSampleFullSliceLip B U basis S t) η ξ +
        Real.exp (-(E + 4)) +
        (2 * δforecast + Mmass * Real.exp (-Aambient)) ≤ Real.exp (-E) := by
  intro early η δforecast Aambient
  have hE4 : 0 ≤ E + 4 := by linarith
  obtain ⟨Lsrc, hLsrc, hLbound, hbudget⟩ :=
    exists_allocatedFixedPathForecastErrorBudget B U basis hD hP hV hE4 hInput hG hLift
  let Lgrid := forecastJointGridSamplerFloor d Pg (E + 4) V PR
  refine ⟨Real.exp_pos _, by dsimp only [Aambient]; linarith, max Lsrc Lgrid,
    hLsrc.trans_le (le_max_left _ _), ?_, ?_⟩
  · rw [Nat.cast_max]
    apply max_le
    · refine hLbound.trans (Real.exp_le_exp.mpr ?_)
      dsimp only [allocatedFixedPathAmbientFloorLog]
      calc
        _ = 8 * (D + P + 9) + V + E + 10 := by ring
        _ ≤ _ := le_max_left _ _
    · exact (forecastJointGridSamplerFloor_le_exp d hPg hE4 hV hPR).trans
        (Real.exp_le_exp.mpr (le_max_right _ _))
  intro S t ht0 ht1 Kφ hK q hq hqV hLS G' N X _ _ _ r Mperiod selection p lateTarget hlate ξ
  have hsourceFloor : Lsrc ≤ S.value := (le_max_left _ _).trans hLS
  have hgridFloor : Lgrid ≤ S.value := (le_max_right _ _).trans hLS
  have hlate' : early + (E + 4) + 4 ≤ lateTarget := by linarith only [hlate]
  have h := hbudget S ht0 ht1 Kφ hK hq hqV hsourceFloor
    (G' := G') (N := N) (X := X) (M := Mperiod) (p := p) selection hlate'
  have heta : Real.exp (-(early + (E + 4) + 4)) = η := by
    dsimp only [η]
    congr 1
    ring
  rw [heta] at h
  change 0 < η ∧ η ≤ 1 ∧ 0 < ξ ∧ ξ ≤ 1 ∧ 2 ≤ S.value ∧ q ≤ S.value ∧
    scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / S.value) < 1 ∧
    fixedPathForecastError _ _ _ _ _ _ _ η ξ ≤ Real.exp (-(E + 4)) at h
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1, hgridFloor, ?_⟩
  intro Mmass hM
  exact fixedPathAmbientScalarPrecision_error hM h.2.2.2.2.2.2.2

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3
open scoped BigOperators NNReal Classical

namespace VectorPolynomial
variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

theorem exists_allocatedFixedPathAmbientUniformPrecision
    (d : ℕ) {D P V E Pg PR Q : ℝ}
    (hD : 0 ≤ D) (hP : 2 ≤ P) (hV : 0 ≤ V) (hE : 0 ≤ E)
    (hPg : 0 ≤ Pg) (hPR : 0 ≤ PR) (hQ : 0 ≤ Q)
    (hInput : (Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) : ℝ) ≤ D)
    (hG : (Fintype.card G : ℝ) ≤ D)
    (hLift : (Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) : ℝ) * m ≤ P) :
    let early := 8 * (D + P + 9)
    let η := Real.exp (-(early + E + 8))
    let δforecast := Real.exp (-(E + 8))
    let Aambient := Q + E + 8
    0 < δforecast ∧ 0 ≤ Aambient ∧
    ∃ Lmin : ℕ, 0 < Lmin ∧
      (Lmin : ℝ) ≤ Real.exp (allocatedFixedPathAmbientFloorLog d D P V E Pg PR + 1) ∧
      ∀ {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ) {t : ℝ},
      0 ≤ t → t ≤ 1 → ∀ (Kφ : ℝ≥0), (Kφ : ℝ) ≤ Real.exp P →
      ∀ {q : ℕ}, 0 < q → (q : ℝ) ≤ Real.exp V → Lmin ≤ S.value →
      ∀ {G' N X : Type*} [Fintype G'] [Fintype N] [Fintype X]
        {r Mperiod : ℕ} (selection : Fin r ↪ G') {p lateTarget : ℝ},
      early + E + 8 ≤ lateTarget →
      let ξ := normalizedTupleNarrowWidth X N selection Mperiod p lateTarget
      0 < η ∧ η ≤ 1 ∧ 0 < ξ ∧ ξ ≤ 1 ∧
      2 ≤ S.value ∧ q ≤ S.value ∧
      scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / S.value) < 1 ∧
      forecastJointGridSamplerFloor d Pg (E + 4) V PR ≤ S.value ∧
      ∀ {Mmass : ℝ}, Mmass ≤ Real.exp Q →
      fixedPathForecastError
        (Fintype.card (PrincipalTupleIndex
          (fun a : {a // ¬allocatedShortAxis (I := I) U basis S.value a} => B a.val)
          (fun a => layerSamplerDegree I n a.val)))
        (Fintype.card G) q S.value Kφ (scalarCubeGridBoundaryConstant Empty)
        (allocatedOriginalSampleFullSliceLip B U basis S t) η ξ +
        Real.exp (-(E + 4)) +
        (2 * δforecast + Mmass * Real.exp (-Aambient)) ≤ Real.exp (-E) := by
  intro early η δforecast Aambient
  let H := allocatedFixedPathAmbientFloorLog d D P V E Pg PR
  let Lmin : ℕ := ⌈Real.exp H⌉₊
  have hH : 0 ≤ H := by
    apply le_trans _ (le_max_left _ _)
    linarith
  have hLbound : (Lmin : ℝ) ≤ Real.exp (H + 1) := by
    calc
      _ ≤ Real.exp H + 1 := (Nat.ceil_lt_add_one (Real.exp_nonneg _)).le
      _ = 1 + Real.exp H := add_comm _ _
      _ ≤ _ := one_add_le_exp_succ hH le_rfl
  have hLpos : 0 < Lmin := by
    exact_mod_cast (Real.exp_pos H).trans_le (Nat.le_ceil (Real.exp H))
  refine ⟨Real.exp_pos _, by dsimp only [Aambient]; linarith, Lmin, hLpos, hLbound, ?_⟩
  intro R σ S t ht0 ht1 Kφ hK q hq hqV hLS
  obtain ⟨_, _, Lold, _, holdbound, hbudget⟩ :=
    exists_allocatedFixedPathAmbientPrecision (R := R) (σ := σ) B U basis
      d hD hP hV hE hPg hPR hQ hInput hG hLift
  have holdle : Lold ≤ Lmin := by
    exact_mod_cast holdbound.trans (Nat.le_ceil (Real.exp H))
  intro G' N X _ _ _ r Mperiod selection p lateTarget hlate ξ
  exact hbudget S ht0 ht1 Kφ hK hq hqV (holdle.trans hLS)
    (G' := G') (N := N) (X := X) (Mperiod := Mperiod) (p := p) selection hlate

end VectorPolynomial
end Erdos3

end

end OAI
